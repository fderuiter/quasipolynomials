#![allow(clippy::manual_is_multiple_of)]
#![allow(clippy::manual_abs_diff)]

use crate::types::{Int, Uint};
use std::collections::HashMap;

/// Precomputed lookup table for σ(p^e) keyed by (prime, exponent).
pub type SigmaCache = HashMap<(Uint, u32), Uint>;

/// Build a cache of σ(p, 2e) for primes up to `max_prime` and even exponents 2,4,...,`max_two_e`.
/// Used to avoid recomputing σ inside the raycast inner loop.
pub fn build_sigma_cache(max_prime: u64, max_two_e: u32) -> SigmaCache {
    let mut cache = HashMap::new();
    for p in 2..=max_prime {
        let mut is_prime = p == 2;
        if !is_prime && p > 2 {
            is_prime = true;
            let mut d = 2u64;
            while d * d <= p {
                if p % d == 0 {
                    is_prime = false;
                    break;
                }
                d += 1;
            }
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

pub fn is_prime_u128(n: u128, k: u32) -> bool {
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
    let bases: [u128; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    for &a in bases.iter().take(k as usize) {
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

/// Brent's improvement of Pollard's rho with batched-product GCD.
///
/// Uses one `f()` evaluation per step (vs two for Floyd), and accumulates
/// `|x − y|` products mod `n` in batches of `BATCH` before computing a
/// single GCD, drastically cutting the number of expensive gcd calls.
pub fn pollards_rho_u128(n: u128, c_val: u128) -> Option<u128> {
    if n % 2 == 0 {
        return Some(2);
    }
    if n <= 1 {
        return None;
    }

    const BATCH: u64 = 128;
    const MAX_ITERS: u64 = 10_000_000;

    let f = |val: u128| -> u128 { add_mod_u128(mul_mod_u128(val, val, n), c_val, n) };

    let mut y: u128 = 2; // slow (tortoise) — Brent names this y
    let mut q: u128 = 1; // accumulated product
    let mut r: u64 = 1; // current power-of-two cycle length
    let mut iters: u64 = 0;

    'outer: loop {
        let x = y; // snapshot at start of this power-of-two block
                   // Advance y by r steps (to the end of the current power-of-two block)
        for _ in 0..r {
            y = f(y);
            iters += 1;
            if iters >= MAX_ITERS {
                break 'outer;
            }
        }

        // Now do the detection phase for the next r steps, in batches of BATCH
        let mut steps_left = r;
        while steps_left > 0 {
            let ys_backup = y; // save in case we need step-by-step fallback
            let batch_size = steps_left.min(BATCH);

            for _ in 0..batch_size {
                y = f(y);
                let diff = if y > x { y - x } else { x - y };
                q = mul_mod_u128(q, diff, n);
                iters += 1;
                if iters >= MAX_ITERS {
                    break 'outer;
                }
            }
            steps_left -= batch_size;

            let d = gcd_u128(q, n);
            if d == 1 {
                continue;
            }

            if d == n {
                // Over-accumulated — fall back to step-by-step within this batch
                let mut yy = ys_backup;
                loop {
                    yy = f(yy);
                    let diff = if yy > x { yy - x } else { x - yy };
                    let d2 = gcd_u128(diff, n);
                    if d2 != 1 && d2 != n {
                        return Some(d2);
                    }
                    if d2 == n {
                        break; // truly degenerate for this c_val
                    }
                }
                return None; // this c_val is degenerate, try the next
            }

            // Found a non-trivial factor
            return Some(d);
        }
        r *= 2;
    }

    None
}

pub fn quick_factor_u128(mut n: u128) -> Vec<u128> {
    let mut factors = Vec::new();
    while n % 2 == 0 {
        factors.push(2);
        n /= 2;
    }
    let mut queue = vec![n];
    while let Some(mut current) = queue.pop() {
        if current <= 1 {
            continue;
        }
        let mut d = 3u128;
        while d * d <= current && d < 100_000 {
            while current % d == 0 {
                factors.push(d);
                current /= d;
            }
            d += 2;
        }
        if current <= 1 {
            continue;
        }
        if is_prime_u128(current, 15) {
            factors.push(current);
        } else {
            let mut found = false;
            for c in 1..=100u128 {
                if let Some(divisor) = pollards_rho_u128(current, c) {
                    queue.push(divisor);
                    queue.push(current / divisor);
                    found = true;
                    break;
                }
            }
            if !found {
                eprintln!(
                    "quick_factor_u128: Pollard's rho failed to factor composite {}. \
                     Skipping this candidate.",
                    current
                );
                return vec![];
            }
        }
    }
    factors.sort_unstable();
    factors
}

/// CRT solver using Lean-verified mod_inverse for all modular arithmetic.
/// Computes x such that x ≡ residues[i] (mod moduli[i]) for all i.
pub fn solve_crt(residues: &[Int], moduli: &[Int]) -> Option<Int> {
    let mut total_mod = 1;
    for &m in moduli {
        total_mod *= m;
    }

    let mut x: Int = 0;
    for (&r, &m) in residues.iter().zip(moduli.iter()) {
        let m_i = total_mod / m;
        if let Some(y_i) = crate::lean_ffi::mod_inverse_128(m_i, m) {
            let mut r_pos = r % total_mod;
            if r_pos < 0 {
                r_pos += total_mod;
            }
            let mut y_i_pos = y_i % total_mod;
            if y_i_pos < 0 {
                y_i_pos += total_mod;
            }

            let term1 = mul_mod_u128(r_pos as u128, y_i_pos as u128, total_mod as u128);
            let term2 = mul_mod_u128(term1, m_i as u128, total_mod as u128) as Int;
            x = (x + term2) % total_mod;
        } else {
            return None;
        }
    }
    if x < 0 {
        x += total_mod;
    }
    Some(x)
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

pub fn composite_tonelli_shanks(n: Int, m_factors: &[Uint]) -> Vec<Int> {
    let mut prime_counts: HashMap<Int, u32> = HashMap::new();
    for &f in m_factors {
        *prime_counts.entry(f as Int).or_insert(0) += 1;
    }

    let mut moduli = Vec::new();
    let mut prime_roots = Vec::new();

    for (p, k) in prime_counts {
        let p_pow_k = p.pow(k);
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
            return vec![]; // System has no roots
        }

        prime_roots.push(p_roots);
        moduli.push(p_pow_k);
    }

    let mut all_roots = vec![];
    let mut indices = vec![0; prime_roots.len()];

    if prime_roots.is_empty() {
        return all_roots;
    }

    loop {
        let current_residues: Vec<Int> = indices
            .iter()
            .enumerate()
            .map(|(i, &idx)| prime_roots[i][idx])
            .collect();

        if let Some(combined_root) = solve_crt(&current_residues, &moduli) {
            all_roots.push(combined_root);
        }

        let mut carry = true;
        for i in 0..prime_roots.len() {
            if carry {
                indices[i] += 1;
                if indices[i] >= prime_roots[i].len() {
                    indices[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            break;
        }
    }
    all_roots
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests for deleted functions (mod_inverse, compute_sigma, solve_crt)
    // moved to lean_ffi.rs as cross-check tests against the Lean implementations.

    #[test]
    fn test_is_prime_u128() {
        assert!(is_prime_u128(17, 10));
        assert!(is_prime_u128(997, 10));
        assert!(!is_prime_u128(15, 10));
        assert!(!is_prime_u128(100, 10));
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
        for p in 3u128..250_000 {
            if is_prime_u128(p, 10) {
                for e in 1..=2 {
                    // 2e up to 4
                    let sigma = crate::lean_ffi::compute_sigma(p as u64, 2 * e);
                    let factors = quick_factor_u128(sigma);
                    for f in factors {
                        if f > 1 && !is_prime_u128(f, 10) {
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
        // These are the exact composites that caused panics in the old Pollard's rho.
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
            assert!(!factors.is_empty(), "failed to factor {}", n);
            // Verify product of factors equals n
            let product: u128 = factors.iter().product();
            assert_eq!(
                product, n,
                "product mismatch for {}: factors={:?}",
                n, factors
            );
            // Verify all factors are prime
            for &f in &factors {
                assert!(is_prime_u128(f, 15), "factor {} of {} is not prime", f, n);
            }
        }
    }
}
