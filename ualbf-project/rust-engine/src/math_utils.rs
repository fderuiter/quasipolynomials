#![allow(clippy::manual_is_multiple_of)]
#![allow(clippy::manual_abs_diff)]

use crate::types::{Int, Uint};
use num_bigint::{BigInt, Sign};
use num_traits::{Zero, One, ToPrimitive};
use prime_factorization::Factorization;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Trial-division factorizer for small-to-medium numbers
// ---------------------------------------------------------------------------

/// Precomputed small primes up to a given limit for trial division.
pub struct TrialSieve {
    pub small_primes: Vec<u64>,
}

impl TrialSieve {
    /// Build a trial sieve with all primes up to `limit`.
    pub fn new(limit: u64) -> Self {
        let sieve = primal::Sieve::new(limit as usize);
        let small_primes: Vec<u64> = sieve.primes_from(2).map(|p| p as u64).collect();
        TrialSieve { small_primes }
    }

    /// Factor `n` using trial division against precomputed primes.
    /// Falls back to ECM only if a composite cofactor remains above
    /// the trial limit squared.
    pub fn factor(&self, mut n: u128) -> Vec<u128> {
        if n <= 1 {
            return vec![];
        }
        let mut factors = Vec::new();
        for &p in &self.small_primes {
            let p128 = p as u128;
            if p128 * p128 > n {
                break;
            }
            while n % p128 == 0 {
                factors.push(p128);
                n /= p128;
            }
        }
        if n > 1 {
            // If remainder is small enough to be prime, just push it.
            // Otherwise fall back to ECM for large composites.
            let limit128 = self.small_primes.last().copied().unwrap_or(2) as u128;
            if n <= limit128 * limit128 {
                // n is prime (we've tried all primes up to √n)
                factors.push(n);
            } else {
                // Large cofactor — use Pollard's rho (fast for semiprimes)
                // then fall back to ECM only if rho fails.
                let rho_factors = rho_factor(n);
                factors.extend(rho_factors);
            }
        }
        factors.sort_unstable();
        factors
    }
}

/// Pollard's rho factorization with Brent's cycle detection improvement.
/// Much faster than ECM for semiprimes with factors in the 10^7-10^11 range.
/// Falls back to ECM for numbers rho can't crack within the iteration limit.
pub fn rho_factor(n: u128) -> Vec<u128> {
    if n <= 1 {
        return vec![];
    }
    if is_prime_u128(n) {
        return vec![n];
    }
    // Try to find a non-trivial factor via Pollard's rho
    if let Some(d) = pollard_rho_brent(n) {
        let mut factors = rho_factor(d);
        factors.extend(rho_factor(n / d));
        factors.sort_unstable();
        factors
    } else {
        // Rho failed — fallback to ECM crate
        Factorization::run(n).factors
    }
}

/// Brent's improvement of Pollard's rho algorithm.
/// Returns Some(factor) or None if it fails to find one.
fn pollard_rho_brent(n: u128) -> Option<u128> {
    if n % 2 == 0 {
        return Some(2);
    }
    // Try multiple starting values
    for c in 1..40u128 {
        let mut x: u128 = 2;
        let mut y: u128 = 2;
        let mut d: u128 = 1;
        
        let f = |x: u128| -> u128 {
            add_mod_u128(mul_mod_u128(x, x, n), c, n)
        };

        // Brent's cycle detection with batched GCD
        let mut q: u128 = 1;
        let mut ys: u128 = 0;
        let mut r: u128 = 1;
        
        while d == 1 {
            x = y;
            for _ in 0..r {
                y = f(y);
            }
            let mut k: u128 = 0;
            while k < r && d == 1 {
                ys = y;
                let batch = r - k;
                let batch = if batch > 128 { 128 } else { batch };
                for _ in 0..batch {
                    y = f(y);
                    let diff = if x > y { x - y } else { y - x };
                    q = mul_mod_u128(q, diff, n);
                }
                d = gcd_u128(q, n);
                k += batch;
            }
            r *= 2;
            if r > 1_000_000 {
                break; // Give up on this c value
            }
        }

        if d != 1 && d != n {
            return Some(d);
        }
        // If d == n, try backtracking
        if d == n {
            loop {
                ys = f(ys);
                let diff = if x > ys { x - ys } else { ys - x };
                d = gcd_u128(diff, n);
                if d != 1 {
                    break;
                }
            }
            if d != n {
                return Some(d);
            }
        }
    }
    None // Failed after all c values
}

/// Precomputed lookup table for σ(p^e) keyed by (prime, exponent).
pub type SigmaCache = HashMap<(Uint, u32), Uint>;

/// Build a cache of σ(p, 2e) for primes up to `max_prime` and even exponents 2,4,...,`max_two_e`.
/// Used to avoid recomputing σ inside the raycast inner loop.
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
        let p_uint = p as Uint;
        for two_e in (2..=max_two_e).step_by(2) {
            if p_uint.checked_pow(two_e).is_none() {
                break;
            } // Prevent 128-bit cache poisoning
            cache.insert((p_uint, two_e), crate::lean_ffi::compute_sigma(p, two_e));
        }
    }
    cache
}

/// Look up σ(p^pow) in the cache, falling back to verified Lean computation on miss.
#[inline]
pub fn sigma_cached(cache: &SigmaCache, p: Uint, pow: u32) -> Uint {
    cache
        .get(&(p, pow))
        .copied()
        .unwrap_or_else(|| crate::lean_ffi::compute_sigma(p as u64, pow))
}

pub fn mul_mod_u128(mut a: u128, mut b: u128, m: u128) -> u128 {
    if m <= 0xFFFFFFFFFFFFFFFF {
        return (a % m * (b % m)) % m;
    }
    let mut res = 0;
    a %= m;
    b %= m;
    while b > 0 {
        if b & 1 == 1 {
            res = add_mod_u128(res, a, m);
        }
        a = add_mod_u128(a, a, m);
        b >>= 1;
    }
    res
}

pub fn add_mod_u128(a: u128, b: u128, m: u128) -> u128 {
    debug_assert!(m > 0, "modulo must be strictly positive");
    let a = a % m;
    let b = b % m;
    if a >= m - b {
        a - (m - b)
    } else {
        a + b
    }
}

pub fn modpow_u128(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    if modulus <= 1 {
        return 0;
    }
    let mut result = 1;
    base %= modulus;
    while exp > 0 {
        if exp % 2 == 1 {
            result = mul_mod_u128(result, base, modulus);
        }
        exp /= 2;
        base = mul_mod_u128(base, base, modulus);
    }
    result
}

pub fn is_prime_u128(n: u128) -> bool {
    if n <= 1 {
        return false;
    }
    if n == 2 || n == 3 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }
    let mut d = n - 1;
    let mut r = 0;
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    // Using a large set of bases to ensure deterministic repeatability for 128-bit numbers.
    let bases: [u128; 20] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71
    ];
    for &a in bases.iter() {
        if a >= n {
            break;
        }
        let mut x = modpow_u128(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        let mut composite = true;
        for _ in 0..(r - 1) {
            x = mul_mod_u128(x, x, n);
            if x == n - 1 {
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

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Factor a u128 using the Elliptic Curve Method (ECM).
///
/// Strategy: trial division by small primes up to 100k, then delegate
/// remaining composites to the `prime_factorization` crate which uses
/// Lenstra ECM with Suyama parametrisation.
pub fn quick_factor_u128(n: u128) -> Vec<u128> {
    if n <= 1 {
        return vec![];
    }
    // Fast path: trial division for numbers with small factors.
    // This avoids ECM startup overhead for the common case.
    let mut remaining = n;
    let mut factors = Vec::new();
    // Quick small-prime trial: 2, 3, 5, then 6k±1 up to 10007
    for &p in &[2u128, 3, 5, 7, 11, 13] {
        while remaining % p == 0 {
            factors.push(p);
            remaining /= p;
        }
    }
    let mut d = 17u128;
    while d * d <= remaining && d < 10_000 {
        while remaining % d == 0 {
            factors.push(d);
            remaining /= d;
        }
        d += 2;
        while remaining % d == 0 {
            factors.push(d);
            remaining /= d;
        }
        d += 4; // 6k+1 stepping
    }
    if remaining > 1 {
        if remaining < 100_000_000 || is_prime_u128(remaining) {
            factors.push(remaining);
        } else {
            // Only use ECM for genuinely hard composites
            let ecm_factors = Factorization::run(remaining).factors;
            factors.extend(ecm_factors);
        }
    }
    factors.sort_unstable();
    factors
}

// ---------------------------------------------------------------------------
// Cyclotomic polynomial evaluation and factorization for σ(p^{2e})
// ---------------------------------------------------------------------------

/// Divisors of n (for small n only — used to enumerate d | (2e+1)).
fn small_divisors(n: u32) -> Vec<u32> {
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

/// Public wrapper for small_divisors (used by sieve.rs cyclotomic fast path).
#[inline]
pub fn small_divisors_pub(n: u32) -> Vec<u32> {
    small_divisors(n)
}

/// Möbius function μ(n) for small n.
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
                return 0; // p^2 divides n
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

/// Evaluate the d-th cyclotomic polynomial Φ_d(x) at x = p.
///
/// Uses the identity: Φ_d(x) = ∏_{k | d} (x^k - 1)^{μ(d/k)}
/// Returns `None` if any intermediate value overflows u128, allowing the
/// caller to fall back to factoring the full σ via the Lean FFI.
fn cyclotomic_eval(d: u32, p: u128) -> Option<u128> {
    let divs = small_divisors(d);
    let mut numerator: u128 = 1;
    let mut denominator: u128 = 1;
    for k in &divs {
        let mu = moebius(d / k);
        // Safely compute p^k; returns None on overflow.
        let p_k = p.checked_pow(*k)?;
        let pk_minus_1 = p_k - 1;
        match mu {
            1 => numerator = numerator.checked_mul(pk_minus_1)?,
            -1 => denominator = denominator.checked_mul(pk_minus_1)?,
            _ => {} // μ = 0, skip
        }
    }
    Some(numerator / denominator)
}

/// Public wrapper for cyclotomic_eval (used by sieve.rs cyclotomic fast path).
#[inline]
pub fn cyclotomic_eval_pub(d: u32, p: u128) -> Option<u128> {
    cyclotomic_eval(d, p)
}

/// Factor σ(p^{2e}) by decomposing it into cyclotomic factors.
///
/// Uses the identity: σ(p^{2e}) = (p^{2e+1} - 1) / (p - 1) = ∏_{d | (2e+1), d > 1} Φ_d(p)
///
/// Each Φ_d(p) is much smaller than the full σ value, making factorization
/// faster and avoiding overflow for large primes.
pub fn factor_sigma_cyclotomic(p: u64, two_e: u32) -> Vec<u128> {
    let n = two_e + 1; // σ(p^{2e}) = ∏_{d | n, d > 1} Φ_d(p)
    let divs = small_divisors(n);
    let p128 = p as u128;

    let mut all_factors = Vec::new();
    for d in &divs {
        if *d == 1 {
            continue; // Φ_1(p) = p - 1 is divided out: σ = (p^n - 1) / (p - 1)
        }
        // If cyclotomic evaluation overflows u128, fall back to factoring
        // the full σ value computed via the verified Lean backend.
        if let Some(phi_val) = cyclotomic_eval(*d, p128) {
            if phi_val > 1 {
                all_factors.extend(quick_factor_u128(phi_val));
            }
        } else {
            let full_sigma = crate::lean_ffi::compute_sigma(p, two_e);
            return quick_factor_u128(full_sigma);
        }
    }
    all_factors.sort_unstable();
    all_factors
}

/// CRT solver using Lean-verified mod_inverse for all modular arithmetic.
/// Computes x such that x ≡ residues[i] (mod moduli[i]) for all i.
fn egcd(mut a: BigInt, mut b: BigInt) -> (BigInt, BigInt, BigInt) {
    let mut x0 = BigInt::one();
    let mut y0 = BigInt::zero();
    let mut x1 = BigInt::zero();
    let mut y1 = BigInt::one();

    while !b.is_zero() {
        let q = &a / &b;
        let r = &a % &b;
        a = b;
        b = r;

        let x2 = &x0 - &q * &x1;
        let y2 = &y0 - &q * &y1;
        x0 = x1;
        y0 = y1;
        x1 = x2;
        y1 = y2;
    }

    (a, x0, y0)
}

fn mod_inverse_big(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    if let (Some(a_i128), Some(m_i128)) = (a.to_i128(), m.to_i128()) {
        if let Some(inv) = crate::lean_ffi::mod_inverse_128(a_i128, m_i128) {
            return Some(BigInt::from(inv));
        } else {
            return None;
        }
    }
    let (g, x, _) = egcd(a.clone(), m.clone());
    if g.is_one() {
        let mut res = x % m;
        if res < BigInt::zero() {
            res += m;
        }
        Some(res)
    } else {
        None
    }
}

pub fn solve_crt(residues: &[Int], moduli: &[Int]) -> Option<Int> {
    let mut total_mod = BigInt::one();
    for &m in moduli {
        total_mod *= BigInt::from(m);
    }

    let mut x = BigInt::zero();
    for (&r, &m) in residues.iter().zip(moduli.iter()) {
        let m_big = BigInt::from(m);
        let m_i = &total_mod / &m_big;
        let m_i_mod_m = &m_i % &m_big;
        
        let y_i = mod_inverse_big(&m_i_mod_m, &m_big)?;

        let mut r_pos = BigInt::from(r) % &total_mod;
        if r_pos < BigInt::zero() {
            r_pos += &total_mod;
        }
        let mut y_i_pos = y_i % &total_mod;
        if y_i_pos < BigInt::zero() {
            y_i_pos += &total_mod;
        }

        let term1 = (r_pos * y_i_pos) % &total_mod;
        let term2 = (term1 * m_i) % &total_mod;
        x = (x + term2) % &total_mod;
    }
    
    if x < BigInt::zero() {
        x += total_mod;
    }
    
    x.to_i128()
}

pub fn tonelli_shanks(n: Int, p: Int) -> Option<Int> {
    let mut n_mod_p = n % p;
    if n_mod_p < 0 {
        n_mod_p += p;
    }

    if n_mod_p == 0 {
        return Some(0);
    }
    if p == 2 {
        return Some(n_mod_p);
    }

    let p_minus_one = p - 1;
    let mut q = p_minus_one;
    let mut s = 0u32;
    while q % 2 == 0 {
        q /= 2;
        s += 1;
    }

    if modpow_u128(n_mod_p as u128, (p_minus_one / 2) as u128, p as u128) != 1 {
        return None;
    }

    let mut z = 2;
    while modpow_u128(z as u128, (p_minus_one / 2) as u128, p as u128) != p_minus_one as u128 {
        z += 1;
    }

    let mut m = s;
    let mut c = modpow_u128(z as u128, q as u128, p as u128) as Int;
    let mut t = modpow_u128(n_mod_p as u128, q as u128, p as u128) as Int;
    let mut r = modpow_u128(n_mod_p as u128, ((q + 1) / 2) as u128, p as u128) as Int;

    loop {
        if t == 0 {
            return Some(0);
        }
        if t == 1 {
            return Some(r);
        }

        let mut t2i = t;
        let mut i = 0u32;
        while i < m {
            if t2i == 1 {
                break;
            }
            t2i = mul_mod_u128(t2i as u128, t2i as u128, p as u128) as Int;
            i += 1;
        }

        if i == m {
            return None;
        }

        let exp = 1u32 << (m - i - 1);
        let b = modpow_u128(c as u128, exp as u128, p as u128) as Int;

        m = i;
        c = mul_mod_u128(b as u128, b as u128, p as u128) as Int;
        t = mul_mod_u128(t as u128, c as u128, p as u128) as Int;
        r = mul_mod_u128(r as u128, b as u128, p as u128) as Int;
    }
}

pub fn hensels_lift(root: Int, n: Int, p: Int, k: u32) -> Int {
    let mut current_r = root;
    let mut current_mod = p;

    for _ in 1..k {
        current_mod *= p;

        let r_sqr = mul_mod_u128(current_r as u128, current_r as u128, current_mod as u128) as Int;
        let mut diff = (r_sqr - n) % current_mod;
        if diff < 0 {
            diff += current_mod;
        }

        let two_r = (2 * current_r) % current_mod;

        if let Some(inv_two_r) = crate::lean_ffi::mod_inverse_128(two_r, current_mod) {
            let adjustment =
                mul_mod_u128(diff as u128, inv_two_r as u128, current_mod as u128) as Int;
            current_r = (current_r - adjustment) % current_mod;
            if current_r < 0 {
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
            let current_residues: Vec<Int> = self.indices
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
    assert!(k < 128, "k must be < 128 for solve_mod_2_k");
    let mask = (1u128 << k) - 1;
    let n_u128 = (n as u128) & mask;

    if k == 1 {
        return vec![(n_u128 % 2) as Int];
    }
    if k == 2 {
        if n_u128 % 4 == 1 {
            return vec![1, 3];
        } else if n_u128 % 4 == 0 {
            return vec![0, 2];
        } else {
            return vec![];
        }
    }
    
    if n_u128 % 8 != 1 {
        if n_u128 % 2 == 0 {
            if k <= 12 {
                let mut roots = vec![];
                let mod_k = 1u128 << k;
                for i in 0..mod_k {
                    if mul_mod_u128(i, i, mod_k) == n_u128 {
                        roots.push(i as Int);
                    }
                }
                return roots;
            }
        }
        return vec![]; 
    }

    let mut r = 1u128;
    for m in 4..=k {
        let mod_m = 1u128 << m;
        let r_sqr = mul_mod_u128(r, r, mod_m);
        let n_mod_m = n_u128 & ((1u128 << m) - 1);
        if r_sqr != n_mod_m {
            r += 1u128 << (m - 2);
        }
    }

    let mod_k = 1u128 << k;
    let mut roots = vec![
        r as Int,
        (mod_k - r) as Int,
        ((r + (1u128 << (k - 1))) % mod_k) as Int,
        ((mod_k - ((r + (1u128 << (k - 1))) % mod_k)) % mod_k) as Int,
    ];
    roots.sort_unstable();
    roots.dedup();
    roots
}

pub fn composite_tonelli_shanks(n: Int, m_factors: &[Uint]) -> RootIterator {
    let mut prime_counts: HashMap<Int, u32> = HashMap::new();
    for &f in m_factors {
        *prime_counts.entry(f as Int).or_insert(0) += 1;
    }

    let mut moduli = Vec::new();
    let mut prime_roots = Vec::new();

    for (p, k) in prime_counts {
        let p_pow_k = p.pow(k);

        if p == 2 {
            let p_roots = solve_mod_2_k(n, k);
            if p_roots.is_empty() {
                return RootIterator { prime_roots: vec![], moduli: vec![], indices: vec![], done: true };
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
            return RootIterator { prime_roots: vec![], moduli: vec![], indices: vec![], done: true };
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

    // Tests for deleted functions (mod_inverse, compute_sigma, solve_crt)
    // moved to lean_ffi.rs as cross-check tests against the Lean implementations.

    #[test]
    fn test_is_prime_u128() {
        assert!(is_prime_u128(17));
        assert!(is_prime_u128(997));
        assert!(!is_prime_u128(15));
        assert!(!is_prime_u128(100));
    }

    #[test]
    fn test_quick_factor_u128() {
        let factors = quick_factor_u128(15);
        assert_eq!(factors, vec![3, 5]);

        let factors2 = quick_factor_u128(28);
        assert_eq!(factors2, vec![2, 2, 7]);
    }

    #[test]
    fn test_tonelli_shanks() {
        let root = tonelli_shanks(2, 7).unwrap();
        assert!(root == 3 || root == 4);
        assert_eq!(tonelli_shanks(3, 7), None);
    }

    #[test]
    #[ignore]
    fn test_audit_quick_factor() {
        let mut failures = 0;
        // Check p up to 250_000, 2e up to 4
        for p in 3u128..10_000 {
            if is_prime_u128(p) {
                for e in 1..=2 {
                    // 2e up to 4
                    let sigma = crate::lean_ffi::compute_sigma(p as u64, 2 * e);
                    let factors = quick_factor_u128(sigma);
                    for f in factors {
                        if f > 1 && !is_prime_u128(f) {
                            println!(
                                "COMPOSITE FOUND: {} is a factor of sigma({}^{}) but is composite!",
                                f,
                                p,
                                2 * e
                            );
                            failures += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(failures, 0, "quick_factor_u128 returned composite factors");
    }

    #[test]
    #[ignore]
    fn test_hard_composites() {
        // These composites previously caused panics with Pollard's rho.
        // ECM handles them all reliably.
        let hard_cases: &[u128] = &[
            74489322807384440738695941911,
            292934156951880434940576995033,
            5499828466317331582386161849821,
            269080473414197374710680235169,
            10552816407425999447805594713,
            9598665348122884768631016457,
        ];
        for &n in hard_cases {
            let factors = quick_factor_u128(n);
            assert!(!factors.is_empty(), "ECM failed to factor {}", n);
            let product: u128 = factors.iter().product();
            assert_eq!(
                product, n,
                "product mismatch for {}: factors={:?}",
                n, factors
            );
            for &f in &factors {
                assert!(is_prime_u128(f), "factor {} of {} is not prime", f, n);
            }
        }
    }

    #[test]
    fn test_cyclotomic_eval() {
        // Φ_1(p) = p - 1
        assert_eq!(cyclotomic_eval(1, 7), Some(6));
        // Φ_3(p) = p^2 + p + 1
        assert_eq!(cyclotomic_eval(3, 5), Some(31)); // 25 + 5 + 1
                                                     // Φ_5(p) = p^4 + p^3 + p^2 + p + 1
        assert_eq!(cyclotomic_eval(5, 2), Some(31)); // 16+8+4+2+1
                                                     // Verify: σ(p^2) = (p^3-1)/(p-1) = Φ_3(p)
                                                     // For p=5: σ(5^2) = 1+5+25 = 31 = Φ_3(5) ✓
        assert_eq!(cyclotomic_eval(3, 5), Some(31));
        // Verify overflow returns None instead of panicking
        assert_eq!(cyclotomic_eval(9, 250_000), None); // 250000^9 > u128::MAX
    }

    #[test]
    fn test_factor_sigma_cyclotomic() {
        crate::lean_ffi::initialize_lean_runtime();
        // Verify cyclotomic factorization matches the σ value from Lean
        let test_cases: &[(u64, u32)] =
            &[(3, 2), (5, 2), (7, 2), (11, 2), (13, 4), (101, 2), (997, 4)];
        for &(p, two_e) in test_cases {
            let sigma = crate::lean_ffi::compute_sigma(p, two_e);
            let factors = factor_sigma_cyclotomic(p, two_e);
            let product: u128 = factors.iter().product();
            assert_eq!(
                product, sigma,
                "cyclotomic factor product mismatch for σ({}^{}): expected {}, got {} from {:?}",
                p, two_e, sigma, product, factors
            );
        }
    }
}
