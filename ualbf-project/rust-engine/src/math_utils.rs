#![allow(clippy::manual_is_multiple_of)]
#![allow(clippy::manual_abs_diff)]

use crate::types::{Int, Uint};
use prime_factorization::Factorization;
use std::collections::HashMap;

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
        if n <= Uint::ONE {
            return vec![];
        }
        let mut factors = Vec::new();
        for &p in &self.small_primes {
            let p_u = Uint::from(p);
            if p_u * p_u > n {
                break;
            }
            while n % p_u == Uint::ZERO {
                factors.push(p_u);
                n /= p_u;
            }
        }
        if n > Uint::ONE {
            let limit_u = Uint::from(self.small_primes.last().copied().unwrap_or(2));
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
    if n <= Uint::ONE {
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
        if n <= Uint::from(u128::MAX) {
            Factorization::run(n.as_u128())
                .factors
                .into_iter()
                .map(|f| Uint::from(f))
                .collect()
        } else {
            panic!("Cannot factor large composite: {}", n);
        }
    }
}

fn pollard_rho_brent_u256(n: Uint) -> Option<Uint> {
    if n % Uint::from(2u32) == Uint::ZERO {
        return Some(Uint::from(2u32));
    }
    for c in 1..40u32 {
        let mut x = Uint::from(2u32);
        let mut y = Uint::from(2u32);
        let mut d = Uint::ONE;

        let c_u = Uint::from(c);
        let f = |x: Uint| -> Uint { add_mod_u256(mul_mod_u256(x, x, n), c_u, n) };

        let mut q = Uint::ONE;
        let mut ys = Uint::ZERO;
        let mut r = 1u32;

        while d == Uint::ONE {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k = 0u32;
            while k < r && d == Uint::ONE {
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

        if d != Uint::ONE && d != n {
            return Some(d);
        }
        if d == n {
            loop {
                ys = f(ys);
                let diff = if x > ys { x - ys } else { ys - x };
                d = gcd_u256(diff, n);
                if d != Uint::ONE {
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
        let p_uint = Uint::from(p);
        for two_e in (2..=max_two_e).step_by(2) {
            if p_uint.checked_pow(two_e).is_none() {
                break;
            }
            cache.insert((p_uint, two_e), crate::lean_ffi::compute_sigma(p, two_e));
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
    if m <= Uint::from(0xFFFFFFFFFFFFFFFFu64) {
        return (a % m * (b % m)) % m;
    }
    let mut res = Uint::ZERO;
    a %= m;
    b %= m;
    while b > Uint::ZERO {
        if b & Uint::ONE == Uint::ONE {
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
    if modulus <= Uint::ONE {
        return Uint::ZERO;
    }
    let mut result = Uint::ONE;
    base %= modulus;
    while exp > Uint::ZERO {
        if exp % Uint::from(2u32) == Uint::ONE {
            result = mul_mod_u256(result, base, modulus);
        }
        exp /= Uint::from(2u32);
        base = mul_mod_u256(base, base, modulus);
    }
    result
}

pub fn is_prime_u256(n: Uint) -> bool {
    if n <= Uint::ONE {
        return false;
    }
    if n == Uint::from(2u32) || n == Uint::from(3u32) {
        return true;
    }
    if n % Uint::from(2u32) == Uint::ZERO {
        return false;
    }
    let mut d = n - Uint::ONE;
    let mut r = 0;
    while d % Uint::from(2u32) == Uint::ZERO {
        d /= Uint::from(2u32);
        r += 1;
    }
    let bases: [u32; 20] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    ];
    for &a_u32 in bases.iter() {
        let a = Uint::from(a_u32);
        if a >= n {
            break;
        }
        let mut x = modpow_u256(a, d, n);
        if x == Uint::ONE || x == n - Uint::ONE {
            continue;
        }
        let mut composite = true;
        for _ in 0..(r - 1) {
            x = mul_mod_u256(x, x, n);
            if x == n - Uint::ONE {
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
    while b != Uint::ZERO {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

pub fn quick_factor_u256(n: Uint) -> Vec<Uint> {
    if n <= Uint::ONE {
        return vec![];
    }
    let mut remaining = n;
    let mut factors = Vec::new();
    for &p_u32 in &[2u32, 3, 5, 7, 11, 13] {
        let p = Uint::from(p_u32);
        while remaining % p == Uint::ZERO {
            factors.push(p);
            remaining /= p;
        }
    }
    let mut d = Uint::from(17u32);
    while d * d <= remaining && d < Uint::from(10_000u32) {
        while remaining % d == Uint::ZERO {
            factors.push(d);
            remaining /= d;
        }
        d += Uint::from(2u32);
        while remaining % d == Uint::ZERO {
            factors.push(d);
            remaining /= d;
        }
        d += Uint::from(4u32);
    }
    if remaining > Uint::ONE {
        if remaining < Uint::from(100_000_000u32) || is_prime_u256(remaining) {
            factors.push(remaining);
        } else {
            if remaining <= Uint::from(u128::MAX) {
                let ecm_factors = Factorization::run(remaining.as_u128()).factors;
                factors.extend(ecm_factors.into_iter().map(Uint::from));
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
    crate::lean_ffi::cyclotomic_eval(d, p)
}

pub fn factor_sigma_cyclotomic(p: u64, two_e: u32) -> Vec<Uint> {
    let n = two_e + 1;
    let divs = small_divisors_pub(n);
    let p_u = Uint::from(p);

    let mut all_factors = Vec::new();
    for d in &divs {
        if *d == 1 {
            continue;
        }
        if let Some(phi_val) = cyclotomic_eval_pub(*d, p_u) {
            if phi_val > Uint::ONE {
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

fn egcd(mut a: Int, mut b: Int) -> (Int, Int, Int) {
    let mut x0 = Int::ONE;
    let mut y0 = Int::ZERO;
    let mut x1 = Int::ZERO;
    let mut y1 = Int::ONE;

    while b != Int::ZERO {
        let q = a / b;
        let r = a % b;
        a = b;
        b = r;

        let x2 = x0 - q * x1;
        let y2 = y0 - q * y1;
        x0 = x1;
        y0 = y1;
        x1 = x2;
        y1 = y2;
    }
    (a, x0, y0)
}

fn mod_inverse_big(a: Int, m: Int) -> Option<Int> {
    if m <= Int::ZERO {
        return None;
    }
    if let Some(inv) = crate::lean_ffi::mod_inverse_256(a, m) {
        return Some(inv);
    }
    let (g, x, _) = egcd(a, m);
    if g == Int::ONE || g == -Int::ONE {
        let mut res = x % m;
        if res < Int::ZERO {
            res += m;
        }
        Some(res)
    } else {
        None
    }
}

pub fn solve_crt(residues: &[Int], moduli: &[Int]) -> Option<Int> {
    let mut total_mod = Int::ONE;
    for &m in moduli {
        total_mod *= m;
    }

    let mut x = Int::ZERO;
    for (&r, &m) in residues.iter().zip(moduli.iter()) {
        let m_i = total_mod / m;
        let m_i_mod_m = m_i % m;

        let y_i = mod_inverse_big(m_i_mod_m, m)?;

        let mut r_pos = r % total_mod;
        if r_pos < Int::ZERO {
            r_pos += total_mod;
        }
        let mut y_i_pos = y_i % total_mod;
        if y_i_pos < Int::ZERO {
            y_i_pos += total_mod;
        }

        let term1 = (r_pos * y_i_pos) % total_mod;
        let term2 = (term1 * m_i) % total_mod;
        x = (x + term2) % total_mod;
    }

    if x < Int::ZERO {
        x += total_mod;
    }
    Some(x)
}

pub fn tonelli_shanks(n: Int, p: Int) -> Option<Int> {
    if p <= Int::ZERO {
        return None;
    }
    let mut n_mod_p = n % p;
    if n_mod_p < Int::ZERO {
        n_mod_p += p;
    }

    if n_mod_p == Int::ZERO {
        return Some(Int::ZERO);
    }
    if p == Int::from(2u32) {
        return Some(n_mod_p);
    }

    let p_minus_one = p - Int::ONE;
    let mut q = p_minus_one;
    let mut s = 0u32;
    while q % Int::from(2u32) == Int::ZERO {
        q /= Int::from(2u32);
        s += 1;
    }

    if modpow_u256(
        n_mod_p.as_u256(),
        (p_minus_one / Int::from(2u32)).as_u256(),
        p.as_u256(),
    ) != Uint::ONE
    {
        return None;
    }

    let mut z = Uint::from(2u32);
    while modpow_u256(z, (p_minus_one / Int::from(2u32)).as_u256(), p.as_u256())
        != p_minus_one.as_u256()
    {
        z += Uint::ONE;
    }

    let mut m = s;
    let mut c = modpow_u256(z, q.as_u256(), p.as_u256()).as_i256();
    let mut t = modpow_u256(n_mod_p.as_u256(), q.as_u256(), p.as_u256()).as_i256();
    let mut r = modpow_u256(
        n_mod_p.as_u256(),
        ((q + Int::ONE) / Int::from(2u32)).as_u256(),
        p.as_u256(),
    )
    .as_i256();

    loop {
        if t == Int::ZERO {
            return Some(Int::ZERO);
        }
        if t == Int::ONE {
            return Some(r);
        }

        let mut t2i = t;
        let mut i = 0u32;
        while i < m {
            if t2i == Int::ONE {
                break;
            }
            t2i = mul_mod_u256(t2i.as_u256(), t2i.as_u256(), p.as_u256()).as_i256();
            i += 1;
        }

        if i == m {
            return None;
        }

        let exp = 1u32 << (m - i - 1);
        let b = modpow_u256(c.as_u256(), Uint::from(exp), p.as_u256()).as_i256();

        m = i;
        c = mul_mod_u256(b.as_u256(), b.as_u256(), p.as_u256()).as_i256();
        t = mul_mod_u256(t.as_u256(), c.as_u256(), p.as_u256()).as_i256();
        r = mul_mod_u256(r.as_u256(), b.as_u256(), p.as_u256()).as_i256();
    }
}

pub fn hensels_lift(root: Int, n: Int, p: Int, k: u32) -> Int {
    let mut current_r = root;
    let mut current_mod = p;

    for _ in 1..k {
        current_mod *= p;

        let r_sqr = mul_mod_u256(
            current_r.as_u256(),
            current_r.as_u256(),
            current_mod.as_u256(),
        )
        .as_i256();
        let mut diff = (r_sqr - n) % current_mod;
        if diff < Int::ZERO {
            diff += current_mod;
        }

        let two_r = (Int::from(2u32) * current_r) % current_mod;

        if let Some(inv_two_r) = crate::lean_ffi::mod_inverse_256(two_r, current_mod) {
            let adjustment =
                mul_mod_u256(diff.as_u256(), inv_two_r.as_u256(), current_mod.as_u256()).as_i256();
            current_r = (current_r - adjustment) % current_mod;
            if current_r < Int::ZERO {
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
    let mask = (Uint::ONE << k) - Uint::ONE;
    let n_u256 = n.as_u256() & mask;

    if k == 1 {
        return vec![(n_u256 % Uint::from(2u32)).as_i256()];
    }
    if k == 2 {
        if n_u256 % Uint::from(4u32) == Uint::ONE {
            return vec![Int::ONE, Int::from(3u32)];
        } else if n_u256 % Uint::from(4u32) == Uint::ZERO {
            return vec![Int::ZERO, Int::from(2u32)];
        } else {
            return vec![];
        }
    }

    if n_u256 % Uint::from(8u32) != Uint::ONE {
        if n_u256 % Uint::from(2u32) == Uint::ZERO {
            if k <= 12 {
                let mut roots = vec![];
                let mod_k = Uint::ONE << k;
                let mut i = Uint::ZERO;
                while i < mod_k {
                    if mul_mod_u256(i, i, mod_k) == n_u256 {
                        roots.push(i.as_i256());
                    }
                    i += Uint::ONE;
                }
                return roots;
            }
        }
        return vec![];
    }

    let mut r = Uint::ONE;
    for m in 4..=k {
        let mod_m = Uint::ONE << m;
        let r_sqr = mul_mod_u256(r, r, mod_m);
        let n_mod_m = n_u256 & ((Uint::ONE << m) - Uint::ONE);
        if r_sqr != n_mod_m {
            r += Uint::ONE << (m - 2);
        }
    }

    let mod_k = Uint::ONE << k;
    let mut roots = vec![
        r.as_i256(),
        (mod_k - r).as_i256(),
        ((r + (Uint::ONE << (k - 1))) % mod_k).as_i256(),
        ((mod_k - ((r + (Uint::ONE << (k - 1))) % mod_k)) % mod_k).as_i256(),
    ];
    roots.sort_unstable();
    roots.dedup();
    roots
}

pub fn composite_tonelli_shanks(n: Int, m_factors: &[Uint]) -> RootIterator {
    let mut prime_counts: HashMap<Int, u32> = HashMap::new();
    for &f in m_factors {
        *prime_counts.entry(f.as_i256()).or_insert(0) += 1;
    }

    let mut moduli = Vec::new();
    let mut prime_roots = Vec::new();

    for (p, k) in prime_counts {
        let p_pow_k = p.pow(k);

        if p == Int::from(2u32) {
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
