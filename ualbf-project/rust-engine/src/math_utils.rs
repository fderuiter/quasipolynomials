#![allow(clippy::manual_is_multiple_of)]
#![allow(clippy::manual_abs_diff)]

use crate::types::{UintExt, IntExt};
use crate::types::{Int, Uint};
use prime_factorization::Factorization;
use std::collections::HashMap;
use std::sync::OnceLock;

static PRECOMPUTED_FACTORS: OnceLock<HashMap<(u32, u8), Vec<u128>>> = OnceLock::new();

pub fn get_precomputed_factors(p: u32, d: u8) -> Option<&'static Vec<u128>> {
    let map = PRECOMPUTED_FACTORS.get_or_init(|| {
        let bytes = include_bytes!(concat!(env!("OUT_DIR"), "/cyclotomic_factors.bin"));
        let mut m = HashMap::new();
        let mut offset = 0;
        let entries_count = u32::from_le_bytes(bytes[offset..offset+4].try_into().unwrap());
        offset += 4;
        for _ in 0..entries_count {
            let p_val = u32::from_le_bytes(bytes[offset..offset+4].try_into().unwrap());
            offset += 4;
            let d_val = bytes[offset];
            offset += 1;
            let num_factors = bytes[offset] as usize;
            offset += 1;
            let mut factors = Vec::with_capacity(num_factors);
            for _ in 0..num_factors {
                factors.push(u128::from_le_bytes(bytes[offset..offset+16].try_into().unwrap()));
                offset += 16;
            }
            m.insert((p_val, d_val), factors);
        }
        m
    });
    map.get(&(p, d))
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
        if n <= Uint::one_ext() {
            return vec![];
        }
        let mut factors = Vec::new();
        for &p in &self.small_primes {
            let p_u = Uint::from_u128_ext((p) as u128);
            if p_u.clone() * p_u.clone() > n.clone() {
                break;
            }
            while n.clone() % p_u.clone() == Uint::zero_ext() {
                factors.push(p_u.clone());
                n /= p_u.clone();
            }
        }
        if n > Uint::one_ext() {
            let limit_u = Uint::from_u128_ext(self.small_primes.last().cloned().unwrap_or(2) as u128);
            if n.clone() <= limit_u.clone() * limit_u.clone() {
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
    if n <= Uint::one_ext() {
        return vec![];
    }
    if is_prime_u256(n.clone()) {
        return vec![n];
    }
    if let Some(d) = pollard_rho_brent_u256(n.clone()) {
        let mut factors = rho_factor_u256(d.clone());
        factors.extend(rho_factor_u256(n.clone() / d.clone()));
        factors.sort_unstable();
        factors
    } else {
        if n <= Uint::from_u128_ext((u128::MAX) as u128) {
            Factorization::run(n.as_u128())
                .factors
                .into_iter()
                .map(|f| Uint::from_u128_ext((f) as u128))
                .collect()
        } else {
            panic!("Cannot factor large composite: {}", n);
        }
    }
}

pub fn pollard_rho_brent_u256(n: Uint) -> Option<Uint> {
    if n.clone() % Uint::from_u128_ext((2u32) as u128) == Uint::zero_ext() {
        return Some(Uint::from_u128_ext((2u32) as u128));
    }
    for c in 1..40u32 {
        let mut x = Uint::from_u128_ext((2u32) as u128);
        let mut y = Uint::from_u128_ext((2u32) as u128);
        let mut d = Uint::one_ext();

        let c_u = Uint::from_u128_ext((c) as u128);
        let n1 = n.clone(); let n2 = n.clone(); let c_u1 = c_u.clone(); let n1 = n.clone(); let f = move |x: Uint| -> Uint { add_mod_u256(mul_mod_u256(x.clone(), x.clone(), n1.clone()), c_u.clone(), n1.clone()) };

        let mut q = Uint::one_ext();
        let mut ys = Uint::zero_ext();
        let mut r = 1u32;

        while d == Uint::one_ext() {
            x = y.clone();
            for _ in 0..r {
                y = f(y.clone());
            }
            let mut k = 0u32;
            while k < r && d == Uint::one_ext() {
                ys = y.clone();
                let batch = r - k;
                let batch = if batch > 128 { 128 } else { batch };
                for _ in 0..batch {
                    y = f(y.clone());
                    let diff = if x > y.clone() { x.clone() - y.clone() } else { y.clone() - x.clone() };
                    q = mul_mod_u256(q, diff, n.clone());
                }
                d = gcd_u256(q.clone(), n.clone());
                k += batch;
            }
            r *= 2;
            if r > 1_000_000 {
                break;
            }
        }

        if d != Uint::one_ext() && d != n.clone() {
            return Some(d);
        }
        if d == n.clone() {
            loop {
                ys = f(ys.clone());
                let diff = if x > ys.clone() { x.clone() - ys.clone() } else { ys.clone() - x.clone() };
                d = gcd_u256(diff.clone(), n.clone());
                if d != Uint::one_ext() {
                    break;
                }
            }
            if d != n.clone() {
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
        let p_uint = Uint::from_u128_ext((p) as u128);
        for two_e in (2..=max_two_e).step_by(2) {
            if p_uint.clone().checked_pow(two_e).is_none() {
                break;
            }
            cache.insert((p_uint.clone(), two_e), crate::lean_ffi::compute_sigma(p, two_e));
        }
    }
    cache
}

#[inline]
pub fn sigma_cached(cache: &SigmaCache, p: Uint, pow: u32) -> Uint {
    cache
        .get(&(p.clone(), pow))
        .cloned()
        .unwrap_or_else(|| crate::lean_ffi::compute_sigma(p.clone().as_u64(), pow))
}

pub fn mul_mod_u256(mut a: Uint, mut b: Uint, m: Uint) -> Uint {
    if m <= Uint::from_u128_ext((0xFFFFFFFFFFFFFFFFu64) as u128) {
        return (a.clone() % m.clone() * (b.clone() % m.clone())) % m.clone();
    }
    let mut res = Uint::zero_ext();
    a %= m.clone();
    b %= m.clone();
    while b.clone() > Uint::zero_ext() {
        if b.clone() & Uint::one_ext() == Uint::one_ext() {
            res = add_mod_u256(res.clone(), a.clone(), m.clone());
        }
        a = add_mod_u256(a.clone(), a.clone(), m.clone());
        b >>= 1;
    }
    res
}

pub fn add_mod_u256(a: Uint, b: Uint, m: Uint) -> Uint {
    let a = a % m.clone();
    let b = b.clone() % m.clone();
    if a.clone() >= m.clone() - b.clone() {
        a.clone() - (m.clone() - b.clone())
    } else {
        a.clone() + b.clone()
    }
}

pub fn modpow_u256(mut base: Uint, mut exp: Uint, modulus: Uint) -> Uint {
    if modulus <= Uint::one_ext() {
        return Uint::zero_ext();
    }
    let mut result = Uint::one_ext();
    base %= modulus.clone();
    while exp.clone() > Uint::zero_ext() {
        if exp.clone() % Uint::from_u128_ext((2u32) as u128) == Uint::one_ext() {
            result = mul_mod_u256(result.clone(), base.clone(), modulus.clone());
        }
        exp /= Uint::from_u128_ext((2u32) as u128);
        base = mul_mod_u256(base.clone(), base.clone(), modulus.clone());
    }
    result
}

pub fn is_prime_u256(n: Uint) -> bool {
    if n <= Uint::one_ext() {
        return false;
    }
    if n == Uint::from_u128_ext((2u32) as u128) || n == Uint::from_u128_ext((3u32) as u128) {
        return true;
    }
    if n.clone() % Uint::from_u128_ext((2u32) as u128) == Uint::zero_ext() {
        return false;
    }
    let mut d = n.clone() - Uint::one_ext();
    let mut r = 0;
    while d.clone() % Uint::from_u128_ext((2u32) as u128) == Uint::zero_ext() {
        d /= Uint::from_u128_ext((2u32) as u128);
        r += 1;
    }
    let bases: [u32; 20] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    ];
    for &a_u32 in bases.iter() {
        let a = Uint::from_u128_ext((a_u32) as u128);
        if a.clone() >= n.clone() {
            break;
        }
        let mut x = modpow_u256(a.clone(), d.clone(), n.clone());
        if x == Uint::one_ext() || x == n.clone() - Uint::one_ext() {
            continue;
        }
        let mut composite = true;
        for _ in 0..(r - 1) {
            x = mul_mod_u256(x.clone(), x.clone(), n.clone());
            if x == n.clone() - Uint::one_ext() {
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
    while b != Uint::zero_ext() {
        let temp = b.clone();
        b = a.clone() % b.clone();
        a = temp;
    }
    a
}

pub fn quick_factor_u256(n: Uint) -> Vec<Uint> {
    if n <= Uint::one_ext() {
        return vec![];
    }
    let mut remaining = n;
    let mut factors = Vec::new();
    for &p_u32 in &[2u32, 3, 5, 7, 11, 13] {
        let p = Uint::from_u128_ext((p_u32) as u128);
        while remaining.clone() % p.clone() == Uint::zero_ext() {
            factors.push(p.clone());
            remaining /= p.clone();
        }
    }
    let mut d = Uint::from_u128_ext((17u32) as u128);
    while d.clone() * d.clone() <= remaining.clone() && d.clone() < Uint::from_u128_ext((10_000u32) as u128) {
        while remaining.clone() % d.clone() == Uint::zero_ext() {
            factors.push(d.clone());
            remaining /= d.clone();
        }
        d += Uint::from_u128_ext((2u32) as u128);
        while remaining.clone() % d.clone() == Uint::zero_ext() {
            factors.push(d.clone());
            remaining /= d.clone();
        }
        d += Uint::from_u128_ext((4u32) as u128);
    }
    if remaining > Uint::one_ext() {
        if remaining.clone() < Uint::from_u128_ext((100_000_000u32) as u128) || is_prime_u256(remaining.clone()) {
            factors.push(remaining);
        } else {
            if remaining.clone() <= Uint::from_u128_ext((u128::MAX) as u128) {
                let ecm_factors = Factorization::run(remaining.as_u128()).factors;
                factors.extend(ecm_factors.into_iter().map(Uint::from_u128_ext));
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
            if d != n.clone() / d {
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
    while d.clone() * d.clone() <= remaining.clone() {
        if remaining.clone() % d.clone() == 0 {
            remaining /= d.clone();
            if remaining.clone() % d.clone() == 0 {
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
    crate::lean_ffi::cyclotomic_eval(d, p.clone())
}

pub fn factor_sigma_cyclotomic(p: u64, two_e: u32) -> Vec<Uint> {
    let n = two_e + 1;
    let divs = small_divisors_pub(n);
    let p_u = Uint::from_u128_ext((p) as u128);

    let mut all_factors = Vec::new();
    for d in &divs {
        if *d == 1 {
            continue;
        }
        
        if let Some(factors) = get_precomputed_factors(p as u32, *d as u8) {
            if factors.len() == 1 && factors[0] == 0 {
                // If it was rejected because of a mod-8 failure, we don't have the full factorization!
                // But factor_sigma_cyclotomic expects ALL factors. 
                // However, wait, factor_sigma_cyclotomic is used to factor FULL sigma, which is used for what?
                // It's used to return all factors. If we return just some factors or no factors, it's incorrect.
                // We MUST compute the full factorization in this case if we don't have it!
                if let Some(phi_val) = cyclotomic_eval_pub(*d, p_u.clone()) {
                    if phi_val > Uint::one_ext() {
                        all_factors.extend(quick_factor_u256(phi_val));
                    }
                } else {
                    let full_sigma = crate::lean_ffi::compute_sigma(p, two_e);
                    return quick_factor_u256(full_sigma);
                }
            } else {
                all_factors.extend(factors.iter().cloned().map(Uint::from_u128_ext));
            }
            continue;
        }

        if let Some(phi_val) = cyclotomic_eval_pub(*d, p_u.clone()) {
            if phi_val > Uint::one_ext() {
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
    let mut x0 = Int::one_ext();
    let mut y0 = Int::zero_ext();
    let mut x1 = Int::zero_ext();
    let mut y1 = Int::one_ext();

    while b != Int::zero_ext() {
        let q = a.clone() / b.clone();
        let r = a.clone() % b.clone();
        a = b;
        b = r;

        let x2 = x0 - q.clone() * x1.clone();
        let y2 = y0 - q.clone() * y1.clone();
        x0 = x1.clone();
        y0 = y1.clone();
        x1 = x2;
        y1 = y2;
    }
    (a, x0, y0)
}

pub fn mod_inverse_big(a: Int, m: Int) -> Option<Int> {
    if m <= Int::zero_ext() {
        return None;
    }
    if let Some(inv) = crate::lean_ffi::mod_inverse_256(a.clone(), m.clone()) {
        return Some(inv);
    }
    let (g, x, _) = egcd(a, m.clone());
    if g == Int::one_ext() || g == -Int::one_ext() {
        let mut res = x % m.clone();
        if res < Int::zero_ext() {
            res += m.clone();
        }
        Some(res)
    } else {
        None
    }
}

pub fn solve_crt(residues: &[Int], moduli: &[Int]) -> Option<Int> {
    let mut total_mod = Int::one_ext();
    for m in moduli.clone() {
        total_mod *= m;
    }

    let mut x = Int::zero_ext();
    for (r, m) in residues.iter().zip(moduli.iter()) {
        let m_i = total_mod.clone() / m.clone();
        let m_i_mod_m = m_i.clone() % m.clone();

        let y_i = mod_inverse_big(m_i_mod_m, m.clone())?;

        let mut r_pos = r.clone() % total_mod.clone();
        if r_pos < Int::zero_ext() {
            r_pos += total_mod.clone();
        }
        let mut y_i_pos = y_i % total_mod.clone();
        if y_i_pos < Int::zero_ext() {
            y_i_pos += total_mod.clone();
        }

        let term1 = (r_pos * y_i_pos) % total_mod.clone();
        let term2 = (term1 * m_i.clone()) % total_mod.clone();
        x = (x + term2) % total_mod.clone();
    }

    if x < Int::zero_ext() {
        x += total_mod.clone();
    }
    Some(x)
}

pub fn tonelli_shanks(n: Int, p: Int) -> Option<Int> {
    if p <= Int::zero_ext() {
        return None;
    }
    let mut n_mod_p = n % p.clone();
    if n_mod_p < Int::zero_ext() {
        n_mod_p += p.clone();
    }

    if n_mod_p == Int::zero_ext() {
        return Some(Int::zero_ext());
    }
    if p == Int::from_u128_ext((2u32) as u128) {
        return Some(n_mod_p);
    }

    let p_minus_one = p.clone() - Int::one_ext();
    let mut q = p_minus_one.clone();
    let mut s = 0u32;
    while q.clone() % Int::from_u128_ext((2u32) as u128) == Int::zero_ext() {
        q /= Int::from_u128_ext((2u32) as u128);
        s += 1;
    }

    if modpow_u256(
        n_mod_p.clone().as_uint(),
        (p_minus_one.clone() / Int::from_u128_ext((2u32) as u128)).as_uint(),
        p.clone().as_uint(),
    ) != Uint::one_ext()
    {
        return None;
    }

    let mut z = Uint::from_u128_ext((2u32) as u128);
    while modpow_u256(z.clone(), (p_minus_one.clone() / Int::from_u128_ext((2u32) as u128)).as_uint(), p.clone().as_uint())
        != p_minus_one.clone().as_uint()
    {
        z += Uint::one_ext();
    }

    let mut m = s;
    let mut c = modpow_u256(z.clone(), q.as_uint(), p.clone().as_uint()).as_int();
    let mut t = modpow_u256(n_mod_p.clone().as_uint(), q.as_uint(), p.clone().as_uint()).as_int();
    let mut r = modpow_u256(
        n_mod_p.clone().as_uint(),
        ((q + Int::one_ext()) / Int::from_u128_ext((2u32) as u128)).as_uint(),
        p.clone().as_uint(),
    )
    .as_int();

    loop {
        if t == Int::zero_ext() {
            return Some(Int::zero_ext());
        }
        if t == Int::one_ext() {
            return Some(r.clone().as_int());
        }

        let mut t2i = t.clone();
        let mut i = 0u32;
        while i < m {
            if t2i == Int::one_ext() {
                break;
            }
            t2i = mul_mod_u256(t2i.as_uint(), t2i.as_uint(), p.clone().as_uint()).as_int();
            i += 1;
        }

        if i == m {
            return None;
        }

        let exp = 1u32 << (m - i - 1);
        let b = modpow_u256(c.as_uint(), Uint::from_u128_ext((exp) as u128), p.clone().as_uint()).as_int();

        m = i;
        c = mul_mod_u256(b.as_uint(), b.as_uint(), p.clone().as_uint()).as_int();
        t = mul_mod_u256(t.clone().as_uint(), c.as_uint(), p.clone().as_uint()).as_int();
        r = mul_mod_u256(r.as_uint(), b.as_uint(), p.clone().as_uint()).as_int();
    }
}

pub fn hensels_lift(root: Int, n: Int, p: Int, k: u32) -> Int {
    let mut current_r = root;
    let mut current_mod = p.clone();

    for _ in 1..k {
        current_mod *= p.clone();

        let r_sqr = mul_mod_u256(
            current_r.as_uint(),
            current_r.as_uint(),
            current_mod.as_uint(),
        )
        .as_int();
        let mut diff = (r_sqr.clone().as_int() - n.clone() + current_mod.clone()) % current_mod.clone();
        if diff < Int::zero_ext() {
            diff += current_mod.clone();
        }

        let two_r = (Int::from_u128_ext((2u32) as u128) * current_r.clone()) % current_mod.clone();

        if let Some(inv_two_r) = crate::lean_ffi::mod_inverse_256(two_r.clone(), current_mod.clone()) {
            let adjustment =
                mul_mod_u256(diff.as_uint(), inv_two_r.as_uint(), current_mod.as_uint()).as_int();
            current_r = (current_r - adjustment) % current_mod.clone();
            if current_r < Int::zero_ext() {
                current_r += current_mod.clone();
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
                .map(|(i, &idx)| self.prime_roots[i][idx].clone())
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
    let mask = (Uint::one_ext() << k) - Uint::one_ext();
    let n_u256 = n.as_uint() & mask;

    if k == 1 {
        return vec![(n_u256.clone() % Uint::from_u128_ext((2u32) as u128)).as_int()];
    }
    if k == 2 {
        if n_u256.clone() % Uint::from_u128_ext((4u32) as u128) == Uint::one_ext() {
            return vec![Int::one_ext(), Int::from_u128_ext((3u32) as u128)];
        } else if n_u256.clone() % Uint::from_u128_ext((4u32) as u128) == Uint::zero_ext() {
            return vec![Int::zero_ext(), Int::from_u128_ext((2u32) as u128)];
        } else {
            return vec![];
        }
    }

    if n_u256.clone() % Uint::from_u128_ext((8u32) as u128) != Uint::one_ext() {
        if n_u256.clone() % Uint::from_u128_ext((2u32) as u128) == Uint::zero_ext() {
            if k <= 12 {
                let mut roots = vec![];
                let mod_k = Uint::one_ext() << k;
                let mut i = Uint::zero_ext();
                while i.clone() < mod_k.clone() {
                    if mul_mod_u256(i.clone(), i.clone(), mod_k.clone()) == n_u256.clone() {
                        roots.push(i.as_int());
                    }
                    i += Uint::one_ext();
                }
                return roots;
            }
        }
        return vec![];
    }

    let mut r = Uint::one_ext();
    for m in 4..=k {
        let mod_m = Uint::one_ext() << m;
        let r_sqr = mul_mod_u256(r.clone(), r.clone(), mod_m.clone());
        let n_mod_m = n_u256.clone() & ((Uint::one_ext() << m) - Uint::one_ext());
        if r_sqr != n_mod_m {
            r += Uint::one_ext() << (m - 2);
        }
    }

    let mod_k = Uint::one_ext() << k;
    let mut roots = vec![
        r.clone().as_int(),
        (mod_k.clone() - r.clone()).as_int(),
        ((r.clone() + (Uint::one_ext() << (k - 1))) % mod_k.clone()).as_int(),
        ((mod_k.clone() - ((r.clone() + (Uint::one_ext() << (k - 1))) % mod_k.clone())) % mod_k.clone()).as_int(),
    ];
    roots.sort_unstable();
    roots.dedup();
    roots
}

pub fn composite_tonelli_shanks(n: Int, m_factors: &[Uint]) -> RootIterator {
    let mut prime_counts: HashMap<Int, u32> = HashMap::new();
    for f in m_factors.clone() {
        *prime_counts.entry(f.as_int()).or_insert(0) += 1;
    }

    let mut moduli = Vec::new();
    let mut prime_roots = Vec::new();

    for (p, k) in prime_counts {
        let p_pow_k = p.pow(k);

        if p == Int::from_u128_ext((2u32) as u128) {
            let p_roots = solve_mod_2_k(n.clone(), k);
            if p_roots.is_empty() {
                return RootIterator {
                    prime_roots: vec![],
                    moduli: vec![],
                    indices: vec![],
                    done: true,
                };
            }
            prime_roots.push(p_roots);
            moduli.push(p_pow_k.clone());
            continue;
        }

        let mut p_roots = Vec::new();
        if let Some(r) = tonelli_shanks(n.clone(), p.clone()) {
            let r_lifted = hensels_lift(r, n.clone(), p.clone(), k);
            p_roots.push(r_lifted.clone());

            let mut neg_r = p_pow_k.clone() - r_lifted.clone();
            neg_r %= p_pow_k.clone();
            if neg_r != r_lifted.clone() {
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
        moduli.push(p_pow_k.clone());
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
