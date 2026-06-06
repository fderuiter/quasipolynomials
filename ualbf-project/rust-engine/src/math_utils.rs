#![allow(clippy::manual_is_multiple_of)]
#![allow(clippy::manual_abs_diff)]

use crate::types::{Int, Uint};
use crate::types::{IntExt, UintExt};
use prime_factorization::Factorization;
use std::collections::HashMap;
use std::sync::OnceLock;
use std::panic::catch_unwind;

use crate::bloom_filter::BloomFilter;

static BLOOM_FILTER: OnceLock<BloomFilter> = OnceLock::new();

pub fn get_bloom_filter() -> &'static BloomFilter {
    BLOOM_FILTER.get().expect("Bloom filter not initialized")
}

pub fn init_bloom_filter(sieve_limit: usize) {
    println!("Initializing Bloom filter for primes up to {}...", sieve_limit);
    let trial_sieve = primal::Sieve::new(10_000_000);
    let small_primes: Vec<u128> = trial_sieve.primes_from(2).map(|p| p as u128).collect();
    let sieve = primal::Sieve::new(sieve_limit);
    let primes: Vec<usize> = sieve.primes_from(3).collect();
    
    use rayon::prelude::*;
    let good_candidates: Vec<(u32, u8)> = primes.into_par_iter().flat_map(|p| {
        let p_u128 = p as u128;
        let mut results = Vec::new();
        for d in [3, 5, 7, 9] {
            let mut phi = match d {
                3 => p_u128*p_u128 + p_u128 + 1,
                5 => p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128 + p_u128*p_u128 + p_u128 + 1,
                7 => p_u128*p_u128*p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128 + p_u128*p_u128 + p_u128 + 1,
                9 => p_u128*p_u128*p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128 + 1,
                _ => 1,
            };
            
            let mut rejected = false;
            for &sp in &small_primes {
                if sp * sp > phi { break; }
                while phi % sp == 0 {
                    if sp % 8 == 5 || sp % 8 == 7 {
                        rejected = true;
                        break;
                    }
                    phi /= sp;
                }
                if rejected { break; }
            }
            if rejected { continue; }
            
            if phi > 1 {
                if is_prime_u128_local(phi) {
                    if phi % 8 == 5 || phi % 8 == 7 {
                        continue;
                    }
                } else {
                    // Composite with no small factors, we keep it as a GOOD candidate 
                    // (letting the sieve dynamically factorize it).
                }
            }
            results.push((p as u32, d as u8));
        }
        results
    }).collect();
    
    // Configurable false positive rate
    let fp_rate = std::env::var("UALBF_FP_RATE")
        .unwrap_or_else(|_| "0.01".to_string())
        .parse::<f64>()
        .unwrap();

    let mut bloom = BloomFilter::new(good_candidates.len().max(1), fp_rate);
    for item in &good_candidates {
        bloom.insert(item);
    }
    println!("Bloom filter initialized with {} good candidates.", good_candidates.len());
    BLOOM_FILTER.set(bloom).unwrap_or(());
}

fn mul_mod_u128(mut a: u128, mut b: u128, m: u128) -> u128 {
    let mut res = 0;
    a %= m;
    while b > 0 {
        if b % 2 == 1 {
            res = (res + a) % m;
        }
        a = (a * 2) % m;
        b /= 2;
    }
    res
}

fn pow_mod_u128(mut base: u128, mut exp: u128, m: u128) -> u128 {
    let mut res = 1;
    base %= m;
    while exp > 0 {
        if exp % 2 == 1 {
            res = mul_mod_u128(res, base, m);
        }
        base = mul_mod_u128(base, base, m);
        exp /= 2;
    }
    res
}

fn is_prime_u128_local(n: u128) -> bool {
    if n <= 1 { return false; }
    if n == 2 || n == 3 { return true; }
    if n % 2 == 0 { return false; }
    let mut d = n - 1;
    let mut r = 0;
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    let bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71];
    for &a in &bases {
        if a >= n { break; }
        let mut x = pow_mod_u128(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        let mut composite = true;
        for _ in 0..r - 1 {
            x = mul_mod_u128(x, x, n);
            if x == n - 1 {
                composite = false;
                break;
            }
        }
        if composite { return false; }
    }
    true
}


pub struct TrialSieve {
    pub small_primes: Vec<u64>,
}

impl TrialSieve {
    pub fn new(limit: u64) -> Self {
        let sieve = primal::Sieve::new(limit as usize);
        let small_primes: Vec<u64> = sieve.primes_from(2).map(|p| p as u64).collect();
        TrialSieve { small_primes }
    }

    pub fn factor(&self, mut n: Uint) -> Vec<Uint> {
        if n <= Uint::one() {
            return vec![];
        }
        let mut factors = Vec::new();
        for &p in &self.small_primes {
            let p_u = Uint::from_u128((p) as u128);
            if p_u * p_u > n {
                break;
            }
            while n % p_u == Uint::zero() {
                factors.push(p_u);
                n /= p_u;
            }
        }
        if n > Uint::one() {
            let limit_u = Uint::from_u128(self.small_primes.last().copied().unwrap_or(2) as u128);
            if n <= limit_u * limit_u {
                factors.push(n);
            } else {
                let rho_factors = rho_factor_u256(n);
                factors.extend(rho_factors);
            }
        }
        factors.sort_unstable();
        factors
    }
}

pub fn rho_factor_u256(n: Uint) -> Vec<Uint> {
    if n <= Uint::one() {
        return vec![];
    }
    if is_prime_u256(n) {
        return vec![n];
    }
    if let Some(d) = pollard_rho_brent_u256(n) {
        let mut factors = rho_factor_u256(d);
        factors.extend(rho_factor_u256(n / d));
        factors.sort_unstable();
        factors
    } else {
        if n <= Uint::from_u128((u128::MAX) as u128) {
            if let Ok(fact) = catch_unwind(|| Factorization::run(n.as_u128())) {
                fact.factors
                    .into_iter()
                    .map(|f| Uint::from_u128((f) as u128))
                    .collect()
            } else {
                panic!("Cannot factor large composite due to panic in prime_factorization: {}", n);
            }
        } else {
            panic!("Cannot factor large composite: {}", n);
        }
    }
}

pub fn pollard_rho_brent_u256(n: Uint) -> Option<Uint> {
    if n % Uint::from_u128((2u32) as u128) == Uint::zero() {
        return Some(Uint::from_u128((2u32) as u128));
    }
    for c in 1..40u32 {
        let mut x = Uint::from_u128((2u32) as u128);
        let mut y = Uint::from_u128((2u32) as u128);
        let mut d = Uint::one();

        let c_u = Uint::from_u128((c) as u128);
        let f = |x: Uint| -> Uint { add_mod_u256(mul_mod_u256(x, x, n), c_u, n) };

        let mut q = Uint::one();
        let mut ys = Uint::zero();
        let mut r = 1u32;

        while d == Uint::one() {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0u32;
            while k < r && d == Uint::one() {
                ys = y;
                let batch = r - k;
                let batch = if batch > 128 { 128 } else { batch };
                for _ in 0..batch {
                    y = f(y);
                    let diff = if x > y { x - y } else { y - x };
                    q = mul_mod_u256(q, diff, n);
                }
                d = gcd_u256(q, n);
                k += batch;
            }
            r *= 2;
            if r > 1_000_000 {
                break;
            }
        }

        if d != Uint::one() && d != n {
            return Some(d);
        }
        if d == n {
            loop {
                ys = f(ys);
                let diff = if x > ys { x - ys } else { ys - x };
                d = gcd_u256(diff, n);
                if d != Uint::one() {
                    break;
                }
            }
            if d != n {
                return Some(d);
            }
        }
    }
    None
}

pub type SigmaCache = HashMap<(Uint, u32), Uint>;

pub fn build_sigma_cache(max_prime: u64, max_two_e: u32) -> SigmaCache {
    let mut cache = HashMap::new();
    for p in 3..=max_prime {
        let mut is_prime = true;
        let mut d = 2u64;
        while d * d <= p {
            if p % d == 0 {
                is_prime = false;
                break;
            }
            d += 1;
        }
        if !is_prime {
            continue;
        }
        let p_uint = Uint::from_u128((p) as u128);
        for two_e in (2..=max_two_e).step_by(2) {
            if p_uint.checked_pow(two_e).is_none() {
                break;
            }
            cache.insert(
                (p_uint, two_e),
                crate::lean_ffi::compute_sigma(p, two_e)
            );
        }
    }
    cache
}

#[inline]
pub fn sigma_cached(cache: &SigmaCache, p: Uint, pow: u32) -> Uint {
    cache
        .get(&(p, pow))
        .copied()
        .unwrap_or_else(|| crate::lean_ffi::compute_sigma(p.as_u64(), pow))
}

pub fn mul_mod_u256(mut a: Uint, mut b: Uint, m: Uint) -> Uint {
    if m <= Uint::from_u128((0xFFFFFFFFFFFFFFFFu64) as u128) {
        return (a % m * (b % m)) % m;
    }
    let mut res = Uint::zero();
    a %= m;
    b %= m;
    while b > Uint::zero() {
        if b & Uint::one() == Uint::one() {
            res = add_mod_u256(res, a, m);
        }
        a = add_mod_u256(a, a, m);
        b >>= 1;
    }
    res
}

pub fn add_mod_u256(a: Uint, b: Uint, m: Uint) -> Uint {
    let a = a % m;
    let b = b % m;
    if a >= m - b {
        a - (m - b)
    } else {
        a + b
    }
}

pub fn modpow_u256(mut base: Uint, mut exp: Uint, modulus: Uint) -> Uint {
    if modulus <= Uint::one() {
        return Uint::zero();
    }
    let mut result = Uint::one();
    base %= modulus;
    while exp > Uint::zero() {
        if exp % Uint::from_u128((2u32) as u128) == Uint::one() {
            result = mul_mod_u256(result, base, modulus);
        }
        exp /= Uint::from_u128((2u32) as u128);
        base = mul_mod_u256(base, base, modulus);
    }
    result
}

pub fn is_prime_u256(n: Uint) -> bool {
    if n <= Uint::one() {
        return false;
    }
    if n == Uint::from_u128((2u32) as u128) || n == Uint::from_u128((3u32) as u128) {
        return true;
    }
    if n % Uint::from_u128((2u32) as u128) == Uint::zero() {
        return false;
    }
    let mut d = n - Uint::one();
    let mut r = 0;
    while d % Uint::from_u128((2u32) as u128) == Uint::zero() {
        d /= Uint::from_u128((2u32) as u128);
        r += 1;
    }
    let bases: [u32; 20] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    ];
    for &a_u32 in bases.iter() {
        let a = Uint::from_u128((a_u32) as u128);
        if a >= n {
            break;
        }
        let mut x = modpow_u256(a, d, n);
        if x == Uint::one() || x == n - Uint::one() {
            continue;
        }
        let mut composite = true;
        for _ in 0..(r - 1) {
            x = mul_mod_u256(x, x, n);
            if x == n - Uint::one() {
                composite = false;
                break;
            }
        }
        if composite {
            return false;
        }
    }
    true
}

fn gcd_u256(mut a: Uint, mut b: Uint) -> Uint {
    while b != Uint::zero() {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

pub fn quick_factor_u256(n: Uint) -> Vec<Uint> {
    if n <= Uint::one() {
        return vec![];
    }
    let mut remaining = n;
    let mut factors = Vec::new();
    for &p_u32 in &[2u32, 3, 5, 7, 11, 13] {
        let p = Uint::from_u128((p_u32) as u128);
        while remaining % p == Uint::zero() {
            factors.push(p);
            remaining /= p;
        }
    }
    let mut d = Uint::from_u128((17u32) as u128);
    while d * d <= remaining && d < Uint::from_u128((10_000u32) as u128) {
        while remaining % d == Uint::zero() {
            factors.push(d);
            remaining /= d;
        }
        d += Uint::from_u128((2u32) as u128);
        while remaining % d == Uint::zero() {
            factors.push(d);
            remaining /= d;
        }
        d += Uint::from_u128((4u32) as u128);
    }
    if remaining > Uint::one() {
        if remaining < Uint::from_u128((100_000_000u32) as u128) || is_prime_u256(remaining) {
            factors.push(remaining);
        } else {
            if remaining <= Uint::from_u128((u128::MAX) as u128) {
                if let Ok(res) = catch_unwind(|| Factorization::run(remaining.as_u128())) {
                    factors.extend(res.factors.into_iter().map(Uint::from_u128));
                } else {
                    factors.extend(rho_factor_u256(remaining));
                }
            } else {
                let ecm_factors = rho_factor_u256(remaining);
                factors.extend(ecm_factors);
            }
        }
    }
    factors.sort_unstable();
    factors
}

pub fn small_divisors_pub(n: u32) -> Vec<u32> {
    let mut divs = Vec::new();
    let mut d = 1;
    while d * d <= n {
        if n % d == 0 {
            divs.push(d);
            if d != n / d {
                divs.push(n / d);
            }
        }
        d += 1;
    }
    divs.sort_unstable();
    divs
}

fn moebius(n: u32) -> i32 {
    if n == 1 {
        return 1;
    }
    let mut remaining = n;
    let mut num_factors = 0u32;
    let mut d = 2u32;
    while d * d <= remaining {
        if remaining % d == 0 {
            remaining /= d;
            if remaining % d == 0 {
                return 0;
            }
            num_factors += 1;
        }
        d += 1;
    }
    if remaining > 1 {
        num_factors += 1;
    }
    if num_factors % 2 == 0 {
        1
    } else {
        -1
    }
}

pub fn cyclotomic_eval_pub(d: u32, p: Uint) -> Option<Uint> {
    crate::lean_ffi::cyclotomic_eval(d, p).map(|x| x)
}

pub fn factor_sigma_cyclotomic(p: u64, two_e: u32) -> Vec<Uint> {
    let n = two_e + 1;
    let divs = small_divisors_pub(n);
    let p_u = Uint::from_u128((p) as u128);

    let mut all_factors = Vec::new();
    for d in &divs {
        if *d == 1 {
            continue;
        }

        if let Some(phi_val) = cyclotomic_eval_pub(*d, p_u) {
            if phi_val > Uint::one() {
                all_factors.extend(quick_factor_u256(phi_val));
            }
        } else {
            let full_sigma = crate::lean_ffi::compute_sigma(p, two_e);
            return quick_factor_u256(full_sigma);
        }
    }
    all_factors.sort_unstable();
    all_factors
}

pub fn mod_inverse_big(a: Int, m: Int) -> Option<Int> {
    if m <= Int::zero() {
        return None;
    }
    
    let a_u = if a < Int::zero() {
        let a_pos = (-a) % m;
        if a_pos == Int::zero() {
            Uint::zero()
        } else {
            (m - a_pos).as_uint()
        }
    } else {
        (a % m).as_uint()
    };
    
    mod_inverse_u512(a_u, m.as_uint()).map(|x| x.as_int())
}

pub fn solve_crt(residues: &[Int], moduli: &[Int]) -> Option<Int> {
    let mut total_mod = Uint::one();
    for &m in moduli {
        total_mod *= m.as_uint();
    }

    let mut x = Uint::zero();
    for (&r, &m) in residues.iter().zip(moduli.iter()) {
        let m_u = m.as_uint();
        let r_u = {
            let mut val = r % m;
            if val < Int::zero() {
                val += m;
            }
            val.as_uint()
        };
        let m_i = total_mod / m_u;
        let m_i_mod_m = m_i % m_u;

        let y_i = mod_inverse_u512(m_i_mod_m, m_u)?;

        let term1 = (r_u * y_i) % total_mod;
        let term2 = (term1 * m_i) % total_mod;
        x = (x + term2) % total_mod;
    }

    Some(x.as_int())
}

pub fn tonelli_shanks(n: Int, p: Int) -> Option<Int> {
    if p <= Int::zero() {
        return None;
    }
    let mut n_mod_p = n % p;
    if n_mod_p < Int::zero() {
        n_mod_p += p;
    }

    if n_mod_p == Int::zero() {
        return Some(Int::zero());
    }
    if p == Int::from_u128((2u32) as u128) {
        return Some(n_mod_p);
    }

    let p_minus_one = p - Int::one();
    let mut q = p_minus_one;
    let mut s = 0u32;
    while q % Int::from_u128((2u32) as u128) == Int::zero() {
        q /= Int::from_u128((2u32) as u128);
        s += 1;
    }

    if modpow_u256(
        n_mod_p.as_uint(),
        (p_minus_one / Int::from_u128((2u32) as u128)).as_uint(),
        p.as_uint(),
    ) != Uint::one()
    {
        return None;
    }

    let mut z = Uint::from_u128((2u32) as u128);
    while modpow_u256(
        z,
        (p_minus_one / Int::from_u128((2u32) as u128)).as_uint(),
        p.as_uint(),
    ) != p_minus_one.as_uint()
    {
        z += Uint::one();
    }

    let mut m = s;
    let mut c = modpow_u256(z, q.as_uint(), p.as_uint()).as_int();
    let mut t = modpow_u256(n_mod_p.as_uint(), q.as_uint(), p.as_uint()).as_int();
    let mut r = modpow_u256(
        n_mod_p.as_uint(),
        ((q + Int::one()) / Int::from_u128((2u32) as u128)).as_uint(),
        p.as_uint(),
    )
    .as_int();

    loop {
        if t == Int::zero() {
            return Some(Int::zero());
        }
        if t == Int::one() {
            return Some(r.as_int());
        }

        let mut t2i = t;
        let mut i = 0u32;
        while i < m {
            if t2i == Int::one() {
                break;
            }
            t2i = mul_mod_u256(t2i.as_uint(), t2i.as_uint(), p.as_uint()).as_int();
            i += 1;
        }

        if i == m {
            return None;
        }

        let exp = 1u32 << (m - i - 1);
        let b = modpow_u256(c.as_uint(), Uint::from_u128((exp) as u128), p.as_uint()).as_int();

        m = i;
        c = mul_mod_u256(b.as_uint(), b.as_uint(), p.as_uint()).as_int();
        t = mul_mod_u256(t.as_uint(), c.as_uint(), p.as_uint()).as_int();
        r = mul_mod_u256(r.as_uint(), b.as_uint(), p.as_uint()).as_int();
    }
}

pub fn hensels_lift(root: Int, n: Int, p: Int, k: u32) -> Int {
    let mut current_r = root;
    let mut current_mod = p;

    for _ in 1..k {
        current_mod *= p;

        let r_sqr = mul_mod_u256(
            current_r.as_uint(),
            current_r.as_uint(),
            current_mod.as_uint(),
        )
        .as_int();
        let mut diff = (r_sqr.as_int() - n + current_mod) % current_mod;
        if diff < Int::zero() {
            diff += current_mod;
        }

        let two_r = (Int::from_u128((2u32) as u128) * current_r) % current_mod;

        if let Some(inv_two_r) = mod_inverse_big(two_r, current_mod) {
            let adjustment =
                mul_mod_u256(diff.as_uint(), inv_two_r.as_uint(), current_mod.as_uint()).as_int();
            current_r = (current_r - adjustment) % current_mod;
            if current_r < Int::zero() {
                current_r += current_mod;
            }
        } else {
            break;
        }
    }
    current_r
}

pub struct RootIterator {
    prime_roots: Vec<Vec<Int>>,
    moduli: Vec<Int>,
    indices: Vec<usize>,
    done: bool,
}

impl Iterator for RootIterator {
    type Item = Int;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done || self.prime_roots.is_empty() {
            return None;
        }

        loop {
            let current_residues: Vec<Int> = self
                .indices
                .iter()
                .enumerate()
                .map(|(i, &idx)| self.prime_roots[i][idx])
                .collect();

            let root_opt = solve_crt(&current_residues, &self.moduli);

            let mut carry = true;
            for i in 0..self.prime_roots.len() {
                if carry {
                    self.indices[i] += 1;
                    if self.indices[i] >= self.prime_roots[i].len() {
                        self.indices[i] = 0;
                    } else {
                        carry = false;
                    }
                }
            }
            if carry {
                self.done = true;
            }

            if let Some(combined_root) = root_opt {
                return Some(combined_root);
            }

            if self.done {
                return None;
            }
        }
    }
}

pub fn solve_mod_2_k(n: Int, k: u32) -> Vec<Int> {
    assert!(k < 256, "k must be < 256 for solve_mod_2_k");
    let mask = (Uint::one() << k) - Uint::one();
    let n_u256 = n.as_uint() & mask;

    if k == 1 {
        return vec![(n_u256 % Uint::from_u128((2u32) as u128)).as_int()];
    }
    if k == 2 {
        if n_u256 % Uint::from_u128((4u32) as u128) == Uint::one() {
            return vec![Int::one(), Int::from_u128((3u32) as u128)];
        } else if n_u256 % Uint::from_u128((4u32) as u128) == Uint::zero() {
            return vec![Int::zero(), Int::from_u128((2u32) as u128)];
        } else {
            return vec![];
        }
    }

    if n_u256 % Uint::from_u128((8u32) as u128) != Uint::one() {
        if n_u256 % Uint::from_u128((2u32) as u128) == Uint::zero() {
            if k <= 12 {
                let mut roots = vec![];
                let mod_k = Uint::one() << k;
                let mut i = Uint::zero();
                while i < mod_k {
                    if mul_mod_u256(i, i, mod_k) == n_u256 {
                        roots.push(i.as_int());
                    }
                    i += Uint::one();
                }
                return roots;
            }
        }
        return vec![];
    }

    let mut r = Uint::one();
    for m in 4..=k {
        let mod_m = Uint::one() << m;
        let r_sqr = mul_mod_u256(r, r, mod_m);
        let n_mod_m = n_u256 & ((Uint::one() << m) - Uint::one());
        if r_sqr != n_mod_m {
            r += Uint::one() << (m - 2);
        }
    }

    let mod_k = Uint::one() << k;
    let mut roots = vec![
        r.as_int(),
        (mod_k - r).as_int(),
        ((r + (Uint::one() << (k - 1))) % mod_k).as_int(),
        ((mod_k - ((r + (Uint::one() << (k - 1))) % mod_k)) % mod_k).as_int(),
    ];
    roots.sort_unstable();
    roots.dedup();
    roots
}

pub fn composite_tonelli_shanks(n: Int, m_factors: &[Uint]) -> RootIterator {
    let mut prime_counts: HashMap<Int, u32> = HashMap::new();
    for &f in m_factors {
        *prime_counts.entry(f.as_int()).or_insert(0) += 1;
    }

    let mut moduli = Vec::new();
    let mut prime_roots = Vec::new();

    for (p, k) in prime_counts {
        let p_pow_k = p.pow(k);

        if p == Int::from_u128((2u32) as u128) {
            let p_roots = solve_mod_2_k(n, k);
            if p_roots.is_empty() {
                return RootIterator {
                    prime_roots: vec![],
                    moduli: vec![],
                    indices: vec![],
                    done: true,
                };
            }
            prime_roots.push(p_roots);
            moduli.push(p_pow_k);
            continue;
        }

        let mut p_roots = Vec::new();
        if let Some(r) = tonelli_shanks(n, p) {
            let r_lifted = hensels_lift(r, n, p, k);
            p_roots.push(r_lifted);

            let mut neg_r = p_pow_k - r_lifted;
            neg_r %= p_pow_k;
            if neg_r != r_lifted {
                p_roots.push(neg_r);
            }
        } else {
            return RootIterator {
                prime_roots: vec![],
                moduli: vec![],
                indices: vec![],
                done: true,
            };
        }

        prime_roots.push(p_roots);
        moduli.push(p_pow_k);
    }

    let indices = vec![0; prime_roots.len()];
    let done = prime_roots.is_empty();

    RootIterator {
        prime_roots,
        moduli,
        indices,
        done,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_solve_mod_2_k_custom() {
        let n = Int::from_u32(1);
        let roots = solve_mod_2_k(n, 3);
        println!("roots for 1 mod 8: {:?}", roots);
        assert_eq!(roots.len(), 4);
    }
}
#[test]
fn test_solve_mod_2_k_custom_5() {
    let n = Int::from_u32(17);
    let roots = solve_mod_2_k(n, 5);
    println!("roots for 17 mod 32: {:?}", roots);
    assert_eq!(roots.len(), 4);
}

#[test]
fn test_solve_crt_128bit() {
    let m1 = Int::from_u128(0xFFFFFFFFFFFFFFFF);
    let m2 = Int::from_u128(0xFFFFFFFFFFFFFFFE);
    let r1 = Int::from_u128(12345);
    let r2 = Int::from_u128(67890);
    let res = solve_crt(&[r1, r2], &[m1, m2]);
    println!("CRT result: {:?}", res);
}

pub fn mod_inverse_u512(a: Uint, m: Uint) -> Option<Uint> {
    if m <= Uint::one() {
        return None;
    }
    let mut t = Uint::zero();
    let mut newt = Uint::one();
    let mut r = m;
    let mut newr = a % m;

    while newr != Uint::zero() {
        let q = r / newr;

        let temp_t = t;
        t = newt;
        let q_newt = (q * newt) % m;
        newt = if temp_t >= q_newt {
            temp_t - q_newt
        } else {
            m - (q_newt - temp_t)
        };

        let temp_r = r;
        r = newr;
        newr = temp_r - q * newr;
    }

    if r > Uint::one() {
        return None;
    }
    Some(t)
}
