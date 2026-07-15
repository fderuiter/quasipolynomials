#![allow(clippy::manual_is_multiple_of)]
#![allow(clippy::manual_abs_diff)]

use crate::residue::IsValidMod8;
use crate::types::{Int, Uint};
use crate::types::{IntExt, UintExt};
use prime_factorization::Factorization;
use std::collections::HashMap;
use std::panic::catch_unwind;
use std::sync::OnceLock;

use crate::bloom_filter::BloomFilter;
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactorizationResult {
    Complete(Vec<Uint>),
    Partial {
        known_factors: Vec<Uint>,
        remaining: Uint,
    },
    Failure(Uint),
}

impl FactorizationResult {
    /// Reports whether this `FactorizationResult` represents a complete factorization.
    ///
    /// # Returns
    ///
    /// `true` if the value is `FactorizationResult::Complete(_)`, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// let complete = FactorizationResult::Complete(vec![]);
    /// let partial = FactorizationResult::Partial { known_factors: vec![], remaining: 2u128.into() };
    /// assert!(complete.is_complete());
    /// assert!(!partial.is_complete());
    /// ```
    pub fn is_complete(&self) -> bool {
        matches!(self, FactorizationResult::Complete(_))
    }
    /// Retrieve the known factors contained in this `FactorizationResult`.
    ///
    /// For `Complete` and `Partial` variants this returns a cloned list of the discovered factors;
    /// for `Failure` it returns an empty vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let c = FactorizationResult::Complete(vec![Uint::from(2u64), Uint::from(3u64)]);
    /// assert_eq!(c.factors(), vec![Uint::from(2u64), Uint::from(3u64)]);
    ///
    /// let p = FactorizationResult::Partial { known_factors: vec![Uint::from(5u64)], remaining: Uint::from(7u64) };
    /// assert_eq!(p.factors(), vec![Uint::from(5u64)]);
    ///
    /// let f = FactorizationResult::Failure(Uint::from(11u64));
    /// assert_eq!(f.factors(), Vec::<Uint>::new());
    /// ```
    pub fn factors(&self) -> Vec<Uint> {
        match self {
            FactorizationResult::Complete(f) => f.clone(),
            FactorizationResult::Partial { known_factors, .. } => known_factors.clone(),
            FactorizationResult::Failure(_) => vec![],
        }
    }
}

static BLOOM_FILTER: OnceLock<BloomFilter> = OnceLock::new();

/// Access the global BloomFilter instance initialized by `init_bloom_filter`.
///
/// Panics if the bloom filter has not been initialized.
///
/// # Examples
///
/// ```
/// init_bloom_filter(100);
/// let _ = get_bloom_filter();
/// ```
pub fn get_bloom_filter() -> &'static BloomFilter {
    BLOOM_FILTER.get().expect("Bloom filter not initialized")
}

/// Initializes the global Bloom filter of "good" (prime, d) candidates using primes up to the given sieve limit.
///
/// The function builds a set of candidate pairs `(p as u32, d as u8)` by enumerating primes produced from the provided
/// sieve limit and applying the module's candidate-selection heuristics; it then constructs a Bloom filter with a false
/// positive rate taken from the `UALBF_FP_RATE` environment variable (default `"0.01"`) and stores it in the global
/// `BLOOM_FILTER` once-initialized state.
///
/// # Parameters
///
/// - `sieve_limit`: upper bound used to generate primes for candidate construction.
///
/// # Examples
///
/// ```
/// // Initialize the global Bloom filter for primes up to 1000.
/// init_bloom_filter(1000);
/// // Afterwards the global filter is available:
/// let _bf = get_bloom_filter();
/// ```
pub fn init_bloom_filter(sieve_limit: usize) {
    println!(
        "Initializing Bloom filter for primes up to {}...",
        sieve_limit
    );
    let trial_sieve = primal::Sieve::new(10_000_000);
    let small_primes: Vec<u128> = trial_sieve.primes_from(2).map(|p| p as u128).collect();
    let sieve = primal::Sieve::new(sieve_limit);
    let primes: Vec<usize> = sieve.primes_from(3).collect();

    use rayon::prelude::*;
    let good_candidates: Vec<(u32, u8)> = primes
        .into_par_iter()
        .flat_map(|p| {
            let p_u128 = p as u128;
            let mut results = Vec::new();
            for d in (3..=31).step_by(2) {
                let p_uint = Uint::from_u128(p_u128);
                let phi_opt = cyclotomic_eval_pub(d, p_uint);
                if phi_opt.is_none() {
                    continue;
                }
                let mut phi = phi_opt.unwrap();

                let mut rejected = false;
                for &sp in &small_primes {
                    let sp_uint = Uint::from_u128(sp);
                    if sp_uint * sp_uint > phi {
                        break;
                    }
                    while phi % sp_uint == Uint::zero() {
                        use crate::residue::IsValidMod8;
                        if !sp.is_valid_mod_8() {
                            rejected = true;
                            break;
                        }
                        phi /= sp_uint;
                    }
                    if rejected {
                        break;
                    }
                }
                if rejected {
                    continue;
                }

                if phi > Uint::one() {
                    if verified_is_prime(phi) {
                        if !phi.is_valid_mod_8() {
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
        })
        .collect();

    // Configurable false positive rate
    let fp_rate = crate::policy::get_safe_config().fp_rate;

    let mut bloom = match BloomFilter::try_new(good_candidates.len().max(1), fp_rate) {
        Ok(b) => b,
        Err(e) => {
            println!("Warning: Failed to initialize optimal Bloom filter: {}. Falling back to default configuration.", e);
            BloomFilter::try_new(1, 0.01).unwrap()
        }
    };
    for item in &good_candidates {
        bloom.insert(item);
    }
    println!(
        "Bloom filter initialized with {} good candidates.",
        good_candidates.len()
    );
    BLOOM_FILTER.set(bloom).unwrap_or(());
}

/// Computes the product of `a` and `b` modulo `m` without overflowing `u128`.
///
/// This returns `(a * b) % m` while avoiding direct multiplication that could overflow `u128`.
///
/// # Panics
///
/// Panics if `m == 0`.
///
/// # Examples
///
/// ```
/// let r = mul_mod_u128(1_000_000_000_000_000_000_000u128, 3_000_000_000_000_000_000_000u128, 1_000_000_000u128);
/// assert_eq!(r, ((1_000_000_000_000_000_000_000u128 % 1_000_000_000u128) * (3_000_000_000_000_000_000_000u128 % 1_000_000_000u128)) % 1_000_000_000u128);
/// ```
fn mul_mod_u128(mut a: u128, mut b: u128, m: u128) -> u128 {
    let mut res: u128 = 0;
    a %= m;
    while b > 0 {
        if b % 2 == 1 {
            if res >= m - a {
                res = res - (m - a);
            } else {
                res += a;
            }
        }
        if a >= m - a {
            a = a - (m - a);
        } else {
            a += a;
        }
        b /= 2;
    }
    res
}

/// Compute modular exponentiation: base^exp modulo m.
///
/// Returns the value of `base` raised to `exp` modulo `m`.
///
/// # Examples
///
/// ```
/// let r = pow_mod_u128(3u128, 13u128, 100u128);
/// assert_eq!(r, 3u128.pow(13) % 100);
/// ```
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

/// Determines whether a 128-bit unsigned integer is prime using a deterministic Miller–Rabin test with fixed bases up to 71.
///

pub struct TrialSieve {
    pub small_primes: Vec<u64>,
}

impl TrialSieve {
    /// Builds a TrialSieve containing all primes up to the given limit.
    ///
    /// The returned `TrialSieve` stores the list of prime numbers >= 2 and <= `limit`.
    ///
    /// # Examples
    ///
    /// ```
    /// let ts = TrialSieve::new(100);
    /// // 97 is the largest prime <= 100
    /// assert!(ts.small_primes.contains(&97));
    /// ```
    pub fn new(limit: u64) -> Self {
        let sieve = primal::Sieve::new(limit as usize);
        let small_primes: Vec<u64> = sieve.primes_from(2).map(|p| p as u64).collect();
        TrialSieve { small_primes }
    }

    /// Performs trial division on `n` using the sieve's stored small primes and, if a nontrivial cofactor remains, delegates further factoring to the rho-based factorizer.
    ///
    /// On success this returns `FactorizationResult::Complete` with a sorted list of prime factors. If trial division finds some factors but a remaining composite cofactor could not be fully factored by the rho step, this returns `FactorizationResult::Partial { known_factors, remaining }` where `known_factors` contains the discovered primes (sorted) and `remaining` is the unfactored cofactor. If the rho step reports a failure for the remaining cofactor, that failure is propagated as a `Partial` with the failure value in `remaining`.
    ///
    /// # Examples
    ///
    /// ```
    /// let sieve = TrialSieve::new(100);
    /// let res = sieve.factor(Uint::from_u128(12));
    /// match res {
    ///     FactorizationResult::Complete(factors) => {
    ///         assert_eq!(factors, vec![Uint::from_u128(2), Uint::from_u128(2), Uint::from_u128(3)]);
    ///     }
    ///     _ => panic!("expected complete factorization"),
    /// }
    /// ```
    pub fn factor(&self, mut n: Uint) -> FactorizationResult {
        if n <= Uint::one() {
            return FactorizationResult::Complete(vec![]);
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
                return FactorizationResult::Complete(factors);
            } else {
                let rho_res = rho_factor_u256(n);
                match rho_res {
                    FactorizationResult::Complete(v) => {
                        factors.extend(v);
                        factors.sort_unstable();
                        return FactorizationResult::Complete(factors);
                    }
                    FactorizationResult::Partial {
                        known_factors,
                        remaining,
                    } => {
                        factors.extend(known_factors);
                        factors.sort_unstable();
                        return FactorizationResult::Partial {
                            known_factors: factors,
                            remaining,
                        };
                    }
                    FactorizationResult::Failure(u) => {
                        factors.sort_unstable();
                        return FactorizationResult::Partial {
                            known_factors: factors,
                            remaining: u,
                        };
                    }
                }
            }
        }
        factors.sort_unstable();
        FactorizationResult::Complete(factors)
    }
}

/// Factorizes `n` using Pollard–Rho (Brent) recursion and fallback factorization strategies.
///
/// The result is a `FactorizationResult`:
/// - `Complete(Vec<Uint>)` when all prime factors were found (vector is sorted).
/// - `Partial { known_factors, remaining }` when some factors were found but a composite remainder could not be fully factored; `remaining` is the unfactored cofactor (>= 2).
/// - `Failure(Uint)` when factorization could not proceed (for example, when Pollard–Rho fails and no safe fallback is available).
///
/// # Examples
///
/// ```
/// let n = Uint::from_u64(15);
/// match rho_factor_u256(n) {
///     FactorizationResult::Complete(factors) => {
///         assert_eq!(factors, vec![Uint::from_u64(3), Uint::from_u64(5)]);
///     }
///     _ => panic!("expected complete factorization"),
/// }
/// ```
pub fn rho_factor_u256(n: Uint) -> FactorizationResult {
    if n <= Uint::one() {
        return FactorizationResult::Complete(vec![]);
    }
    if verified_is_prime(n) {
        return FactorizationResult::Complete(vec![n]);
    }
    if let Some(d) = pollard_rho_brent_u256(n) {
        let res_d = rho_factor_u256(d);
        let res_rem = rho_factor_u256(n / d);

        match (res_d, res_rem) {
            (FactorizationResult::Complete(mut f1), FactorizationResult::Complete(f2)) => {
                f1.extend(f2);
                f1.sort_unstable();
                FactorizationResult::Complete(f1)
            }
            (f1, f2) => {
                let mut known = Vec::new();
                let mut rem = Uint::one();

                match f1 {
                    FactorizationResult::Complete(v) => known.extend(v),
                    FactorizationResult::Partial {
                        known_factors,
                        remaining,
                    } => {
                        known.extend(known_factors);
                        rem *= remaining;
                    }
                    FactorizationResult::Failure(u) => rem *= u,
                };
                match f2 {
                    FactorizationResult::Complete(v) => known.extend(v),
                    FactorizationResult::Partial {
                        known_factors,
                        remaining,
                    } => {
                        known.extend(known_factors);
                        rem *= remaining;
                    }
                    FactorizationResult::Failure(u) => rem *= u,
                };

                known.sort_unstable();
                if rem > Uint::one() {
                    FactorizationResult::Partial {
                        known_factors: known,
                        remaining: rem,
                    }
                } else {
                    FactorizationResult::Complete(known)
                }
            }
        }
    } else {
        if n <= Uint::from_u128((u128::MAX) as u128) {
            if let Ok(fact) = catch_unwind(|| Factorization::run(n.as_u128())) {
                FactorizationResult::Complete(
                    fact.factors
                        .into_iter()
                        .map(|f| Uint::from_u128((f) as u128))
                        .collect(),
                )
            } else {
                FactorizationResult::Failure(n)
            }
        } else {
            FactorizationResult::Failure(n)
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
                let batch = if batch > crate::profile::get_profile().pollard_rho_batch_size {
                    crate::profile::get_profile().pollard_rho_batch_size
                } else {
                    batch
                };
                for _ in 0..batch {
                    y = f(y);
                    let diff = if x > y { x - y } else { y - x };
                    q = mul_mod_u256(q, diff, n);
                }
                d = gcd_u256(q, n);
                k += batch;
            }
            r *= 2;
            if r > crate::lean_ffi::get_pollard_rho_iteration_limit() {
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
        debug_assert!(
            a.checked_add(b).is_some(),
            "Overflow detected in add_mod_u256"
        );
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

pub fn verified_is_prime(n: Uint) -> bool {
    if n <= Uint::one() {
        return false;
    }
    if n == Uint::from_u128(2) || n == Uint::from_u128(3) {
        return true;
    }
    if n % Uint::from_u128(2) == Uint::zero() {
        return false;
    }
    let threshold = Uint::from_u128(1u128 << 64);
    if n < threshold {
        let mut d = n - Uint::one();
        let mut r = 0;
        while d % Uint::from_u128(2) == Uint::zero() {
            d /= Uint::from_u128(2);
            r += 1;
        }
        let bases: [u32; 3] = [2, 13, 23];
        for &a_u32 in bases.iter() {
            let a = Uint::from_u128(a_u32 as u128);
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

        // Pocklington Verification
        let n_u128 = n.as_u128();
        let n_minus_1 = n_u128 - 1;
        if let Ok(res) = catch_unwind(|| prime_factorization::Factorization::run(n_minus_1)) {
            let mut prime_factors = res.factors.clone();
            prime_factors.sort_unstable();
            prime_factors.dedup();

            let mut a = 2u128;
            loop {
                if modpow_u256(Uint::from_u128(a), Uint::from_u128(n_minus_1), n) != Uint::one() {
                    a += 1;
                    continue;
                }
                let mut valid = true;
                for &q in &prime_factors {
                    let exp = n_minus_1 / q as u128;
                    let a_exp = modpow_u256(Uint::from_u128(a), Uint::from_u128(exp), n);
                    let diff = if a_exp > Uint::one() {
                        a_exp - Uint::one()
                    } else {
                        Uint::zero()
                    };
                    if gcd_u256(diff, n) != Uint::one() {
                        valid = false;
                        break;
                    }
                }
                if valid {
                    return true;
                }
                a += 1;
                if a > 10000 {
                    break;
                }
            }
        }

        // Fallback if Pocklington fails (should not happen for primes)
        let mut d = Uint::from_u128(3);
        while d * d <= n {
            if n % d == Uint::zero() {
                return false;
            }
            d += Uint::from_u128(2);
        }
        true
    } else {
        let mut d_td = Uint::from_u128(3);
        // Synthesizing main and HEAD: cap trial division at a much smaller threshold (1000)
        // to prevent thread starvation (main's concern), and safely break to the
        // deterministic Miller-Rabin test (HEAD's implementation) instead of panicking.
        let limit = std::cmp::min(crate::policy::get_safe_config().trial_division_limit, 1000);
        let mut iterations = 0;

        while d_td * d_td <= n {
            if iterations >= limit {
                break;
            }
            if n % d_td == Uint::zero() {
                return false;
            }
            d_td += Uint::from_u128(2);
            iterations += 1;
        }

        if d_td * d_td > n {
            return true;
        }

        let mut d = n - Uint::one();
        let mut s = 0;
        while d % Uint::from_u128(2) == Uint::zero() {
            d /= Uint::from_u128(2);
            s += 1;
        }
        let bases: [u32; 20] = [
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        ];
        for &a_u32 in bases.iter() {
            let a = Uint::from_u128(a_u32 as u128);
            let mut x = modpow_u256(a, d, n);
            if x == Uint::one() || x == n - Uint::one() {
                continue;
            }
            let mut composite = true;
            for _ in 0..(s - 1) {
                x = mul_mod_u256(x, x, n);
                if x == n - Uint::one() {
                    composite = false;
                    break;
                }
                if x == Uint::one() {
                    return false;
                }
            }
            if composite {
                return false;
            }
        }
        true
    }
}

/// Compute the greatest common divisor of two unsigned integers using the Euclidean algorithm.
///
/// # Examples
///
/// ```
/// let a = Uint::from(48u64);
/// let b = Uint::from(18u64);
/// let g = gcd_u256(a, b);
/// assert_eq!(g, Uint::from(6u64));
/// ```
///
/// # Returns
///
/// The greatest common divisor of `a` and `b`.
fn gcd_u256(mut a: Uint, mut b: Uint) -> Uint {
    while b != Uint::zero() {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Performs a fast, primarily trial-based factorization of `n`, returning any discovered prime factors
/// and indicating if a remainder remained unfactored or if factorization failed.
///
/// This function:
/// - Removes small prime factors (2,3,5,7,11,13) and continues trial division with an incremental
///   pattern up to a small bound (trial divisors < 10_000).
/// - If a nontrivial remainder remains, accepts it as a factor when it is small or prime; otherwise
///   delegates to heavier factorization routines (u128-based `Factorization::run` when applicable,
///   or `rho_factor_u256`). If those routines cannot fully factor the remainder or fail, this
///   function returns a `Partial` result containing all known factors and the unfactored remainder.
///
/// # Returns
///
/// - `FactorizationResult::Complete(factors)` when all prime factors of `n` were found (possibly an
///   empty vector for `n <= 1`).
/// - `FactorizationResult::Partial { known_factors, remaining }` when some factors were found but a
///   nontrivial cofactor could not be fully factored; `known_factors` are the discovered factors
///   (sorted) and `remaining` is the unfactored cofactor.
/// - `FactorizationResult::Failure(u)` when factorization ultimately failed and `u` is the
///   remaining unfactored value (this variant is propagated as `Partial` by this function when
///   appropriate).
///
/// # Examples
///
/// ```
/// # use crate::math_utils::{quick_factor_u256, FactorizationResult};
/// # use crate::Uint;
/// let n = Uint::from_u128(60);
/// match quick_factor_u256(n) {
///     FactorizationResult::Complete(mut v) => {
///         v.sort_unstable();
///         let expected = vec![Uint::from_u128(2), Uint::from_u128(2), Uint::from_u128(3), Uint::from_u128(5)];
///         assert_eq!(v, expected);
///     }
///     other => panic!("unexpected result: {:?}", other),
/// }
/// ```
pub fn quick_factor_u256(n: Uint) -> FactorizationResult {
    if n <= Uint::one() {
        return FactorizationResult::Complete(vec![]);
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
        if remaining < Uint::from_u128((100_000_000u32) as u128) || verified_is_prime(remaining) {
            factors.push(remaining);
        } else {
            if remaining <= Uint::from_u128((u128::MAX) as u128) {
                if let Ok(res) = catch_unwind(|| Factorization::run(remaining.as_u128())) {
                    factors.extend(res.factors.into_iter().map(Uint::from_u128));
                } else {
                    let rho_res = rho_factor_u256(remaining);
                    match rho_res {
                        FactorizationResult::Complete(v) => factors.extend(v),
                        FactorizationResult::Partial {
                            known_factors,
                            remaining: r,
                        } => {
                            factors.extend(known_factors);
                            factors.sort_unstable();
                            return FactorizationResult::Partial {
                                known_factors: factors,
                                remaining: r,
                            };
                        }
                        FactorizationResult::Failure(u) => {
                            factors.sort_unstable();
                            return FactorizationResult::Partial {
                                known_factors: factors,
                                remaining: u,
                            };
                        }
                    }
                }
            } else {
                let ecm_factors = rho_factor_u256(remaining);
                match ecm_factors {
                    FactorizationResult::Complete(v) => factors.extend(v),
                    FactorizationResult::Partial {
                        known_factors,
                        remaining: r,
                    } => {
                        factors.extend(known_factors);
                        factors.sort_unstable();
                        return FactorizationResult::Partial {
                            known_factors: factors,
                            remaining: r,
                        };
                    }
                    FactorizationResult::Failure(u) => {
                        factors.sort_unstable();
                        return FactorizationResult::Partial {
                            known_factors: factors,
                            remaining: u,
                        };
                    }
                }
            }
        }
    }
    factors.sort_unstable();
    FactorizationResult::Complete(factors)
}

/// Return all positive divisors of `n` in ascending order.
///
/// The result includes `1` and `n` when applicable. For `n == 0` the function returns an empty vector.
///
/// # Examples
///
/// ```
/// assert_eq!(small_divisors_pub(1), vec![1]);
/// assert_eq!(small_divisors_pub(12), vec![1, 2, 3, 4, 6, 12]);
/// assert_eq!(small_divisors_pub(13), vec![13, 1].into_iter().collect::<Vec<_>>().iter().cloned().collect::<Vec<u32>>()); // demonstrate prime handling
/// ```
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

pub fn proof_verify_zsigmondy_preconditions(p: u64, d: u32) -> bool {
    p >= 3 && p % 2 != 0 && d >= 3
}

pub fn cyclotomic_eval_pub(d: u32, p: Uint) -> Option<Uint> {
    use crate::types::UintExt;

    // Attempt to extract as u64 to use the Verus-verified helper
    let p_u64 = if p <= Uint::from_u64(u64::MAX) {
        p.as_u64()
    } else {
        0
    };

    if p_u64 != 0 {
        if proof_verify_zsigmondy_preconditions(p_u64, d) {
            println!(
                "Zsigmondy preconditions (p >= 3, odd, d >= 3) successfully verified for p={}, d={}",
                p_u64, d
            );
        } else {
            println!(
                "WARN: Zsigmondy precondition violated for p={}, d={}",
                p_u64, d
            );
            return None; // Reject gracefully if preconditions fail
        }
    } else {
        // Safe fallback for extremely large `p`
        let bytes = p.to_le_bytes();
        let is_odd = (bytes[0] & 1) != 0;
        let is_ge_3 = p >= Uint::from_u64(3);
        if is_odd && is_ge_3 && d >= 3 {
            println!(
                "Zsigmondy preconditions (p >= 3, odd, d >= 3) successfully verified for large p"
            );
        } else {
            println!("WARN: Zsigmondy precondition violated for large p, d={}", d);
            return None;
        }
    }

    crate::lean_ffi::cyclotomic_eval(d, p)
}

/// Factorizes σ(p, two_e) by evaluating its cyclotomic components and factoring each result.
///
/// For each divisor `d` of `two_e + 1` (excluding `1`), this function attempts to evaluate the
/// `d`-th cyclotomic polynomial at `p` and factor the value. If a cyclotomic evaluation is
/// unavailable (`None`), the function falls back to factoring the full value returned by
/// `crate::lean_ffi::compute_sigma(p, two_e)`. Found prime factors are collected and returned in
/// sorted order. If any component factorization is incomplete or fails, known factors are returned
/// along with a remaining unfactored cofactor in the `Partial` variant; a total failure for a
/// component is accumulated into the remaining cofactor and also yields `Partial`.
///
/// # Returns
///
/// `FactorizationResult::Complete(factors)` when all cyclotomic components were fully factored;
/// `FactorizationResult::Partial { known_factors, remaining }` when one or more components could
/// not be fully factored (with `remaining` being the product of unfactored cofactors); or
/// `FactorizationResult::Failure(u)` only when the fallback full-sigma factoring produced a failure
/// (propagated from the underlying factoring routine).
///
/// # Examples
///
/// ```
/// let p = 3u64;
/// let two_e = 2u32;
/// let res = factor_sigma_cyclotomic(p, two_e);
/// match res {
///     FactorizationResult::Complete(factors) => {
///         let prod = factors.into_iter().fold(Uint::one(), |acc, x| acc * x);
///         assert_eq!(prod, crate::lean_ffi::compute_sigma(p, two_e));
///     }
///     _ => panic!("expected complete factorization for this example"),
/// }
/// ```
pub fn factor_sigma_cyclotomic(p: u64, two_e: u32) -> FactorizationResult {
    let n = two_e + 1;
    let divs = small_divisors_pub(n);
    let p_u = Uint::from_u128((p) as u128);

    let mut all_factors = Vec::new();
    let mut failure_remaining = Uint::one();
    let mut has_failure = false;

    for d in &divs {
        if *d == 1 {
            continue;
        }

        if let Some(phi_val) = cyclotomic_eval_pub(*d, p_u) {
            if phi_val > Uint::one() {
                match quick_factor_u256(phi_val) {
                    FactorizationResult::Complete(v) => all_factors.extend(v),
                    FactorizationResult::Partial {
                        known_factors,
                        remaining,
                    } => {
                        all_factors.extend(known_factors);
                        failure_remaining *= remaining;
                        has_failure = true;
                    }
                    FactorizationResult::Failure(u) => {
                        failure_remaining *= u;
                        has_failure = true;
                    }
                }
            }
        } else {
            let full_sigma = crate::lean_ffi::compute_sigma(p, two_e);
            return quick_factor_u256(full_sigma);
        }
    }
    all_factors.sort_unstable();
    if has_failure {
        FactorizationResult::Partial {
            known_factors: all_factors,
            remaining: failure_remaining,
        }
    } else {
        FactorizationResult::Complete(all_factors)
    }
}

/// Computes the modular inverse of `a` modulo `m`, returning `None` if no inverse exists or if `m <= 0`.
///
/// The result `x` satisfies `0 <= x < m` and `(a * x) % m == 1` when present.
///
/// # Examples
///
/// ```
/// // 3 * 4 ≡ 1 (mod 11)
/// assert_eq!(mod_inverse_big(Int::from(3), Int::from(11)), Some(Int::from(4)));
///
/// // 2 has no inverse modulo 4
/// assert_eq!(mod_inverse_big(Int::from(2), Int::from(4)), None);
/// ```
pub fn mod_inverse_big(a: Int, m: Int) -> Option<Int> {
    if m <= Int::zero() {
        return None;
    }

    let a_neg = a < Int::zero();
    let a_abs = if a_neg { -a } else { a }.as_uint();

    crate::lean_ffi::compute_mod_inverse(&a_abs, a_neg, &m.as_uint()).map(|x| x.as_int())
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

pub fn hensels_lift(root: Int, n: Int, p: Int, k: u32) -> Option<Int> {
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
            return None;
        }
    }
    Some(current_r)
}

pub struct RootIterator {
    prime_roots: Vec<Vec<Int>>,
    moduli: Vec<Int>,
    indices: Vec<usize>,
    done: bool,
    pub math_interruption: bool,
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
                    math_interruption: true,
                };
            }
            prime_roots.push(p_roots);
            moduli.push(p_pow_k);
            continue;
        }

        let mut p_roots = Vec::new();
        if let Some(r) = tonelli_shanks(n, p) {
            if let Some(r_lifted) = hensels_lift(r, n, p, k) {
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
                    math_interruption: true,
                };
            }
        } else {
            return RootIterator {
                prime_roots: vec![],
                moduli: vec![],
                indices: vec![],
                done: true,
                math_interruption: false,
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
        math_interruption: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mod_negate_u512() {
        let m = Uint::from_u32(10);
        assert_eq!(mod_negate_u512(Uint::from_u32(3), m), Uint::from_u32(7));
        assert_eq!(mod_negate_u512(Uint::from_u32(0), m), Uint::from_u32(0));
        assert_eq!(mod_negate_u512(Uint::from_u32(10), m), Uint::from_u32(0));
        assert_eq!(mod_negate_u512(Uint::from_u32(13), m), Uint::from_u32(7));
    }

    #[test]
    fn test_mod_negate_big() {
        let m = Int::from_u32(10);
        assert_eq!(mod_negate_big(Int::from_u32(3), m), Int::from_u32(7));
        assert_eq!(mod_negate_big(Int::from_u32(0), m), Int::from_u32(0));
        assert_eq!(mod_negate_big(Int::from_u32(10), m), Int::from_u32(0));
        assert_eq!(mod_negate_big(Int::from_u32(13), m), Int::from_u32(7));
    }

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

#[cfg_attr(unverified_build, ignore)]
#[test]
fn test_solve_crt_128bit() {
    let m1 = Int::from_u128(0xFFFFFFFFFFFFFFFF);
    let m2 = Int::from_u128(0xFFFFFFFFFFFFFFFE);
    let r1 = Int::from_u128(12345);
    let r2 = Int::from_u128(67890);
    let res = solve_crt(&[r1, r2], &[m1, m2]).expect("CRT should find a solution");
    assert_eq!(res % m1, r1);
    assert_eq!(res % m2, r2);
}

#[cfg_attr(unverified_build, ignore)]
#[test]
fn test_hensels_lift_basic() {
    // x^2 = 2 (mod 7), x = 3 or 4
    // Lift x=3 to mod 49: x^2 = 2 (mod 49). x = 10
    let root = Int::from_u128(3);
    let n = Int::from_u128(2);
    let p = Int::from_u128(7);
    let k = 2;
    let lifted = hensels_lift(root, n, p, k).unwrap();
    assert_eq!(lifted, Int::from_u128(10));
}

#[cfg_attr(unverified_build, ignore)]
#[test]
fn test_hensels_lift_k3() {
    // Lift x=3 to mod 343: x^2 = 2 (mod 343). x = 108
    let root = Int::from_u128(3);
    let n = Int::from_u128(2);
    let p = Int::from_u128(7);
    let k = 3;
    let lifted = hensels_lift(root, n, p, k).unwrap();
    assert_eq!(lifted, Int::from_u128(108));
}

#[test]
fn test_hensels_lift_residue_failure() {
    // trigger a residue failure
    // We want `mod_inverse_big(two_r, current_mod)` to return None.
    // two_r = (2 * current_r) % current_mod.
    // If p=2, current_mod = 2^k, two_r is even, so gcd(two_r, current_mod) >= 2.
    // So `mod_inverse_big(two_r, current_mod)` will return `None`.
    let root = Int::from_u128(1);
    let n = Int::from_u128(1);
    let p = Int::from_u128(2);
    let k = 3;
    assert_eq!(hensels_lift(root, n, p, k), None);
}

/// Compute the multiplicative inverse of `a` modulo `m`, if one exists.
///
/// Returns `Some(x)` such that `(a * x) % m == 1` when `gcd(a, m) == 1`; returns `None` if `m <= 1` or no inverse exists.
///
/// # Examples
///
/// ```
/// let a = Uint::from(3u64);
/// let m = Uint::from(11u64);
/// let inv = mod_inverse_u512(a, m).expect("inverse exists");
/// assert_eq!((a * inv) % m, Uint::one());
/// ```
pub fn mod_inverse_u512(a: Uint, m: Uint) -> Option<Uint> {
    if m <= Uint::one() {
        return None;
    }
    crate::lean_ffi::compute_mod_inverse(&a, false, &m)
}

/// Compute the modular negation of `val` modulo `m`.
///
/// If `m == 0`, returns `val` unchanged. Otherwise returns `0` when `val % m == 0`,
/// or `m - (val % m)` for the modular negation in the range `1..m-1`.
///
/// # Examples
///
/// ```
/// let a = mod_negate_u512(3u128.into(), 7u128.into());
/// assert_eq!(a, 4u128.into());
///
/// let b = mod_negate_u512(8u128.into(), 8u128.into());
/// assert_eq!(b, 0u128.into());
///
/// let c = mod_negate_u512(5u128.into(), 0u128.into());
/// assert_eq!(c, 5u128.into());
/// ```
pub fn mod_negate_u512(val: Uint, m: Uint) -> Uint {
    if m == Uint::zero() {
        return val;
    }
    let v = val % m;
    if v == Uint::zero() {
        Uint::zero()
    } else {
        m - v
    }
}

/// Compute the modular negation of `val` modulo `m`.
///
/// Returns the unique value `r` in the range `[0, m)` such that `(val + r) % m == 0`. If `m <= 0`,
/// the input `val` is returned unchanged.
///
/// # Examples
///
/// ```
/// let a = Int::from(3);
/// let m = Int::from(7);
/// assert_eq!(mod_negate_big(a, m), Int::from(4)); // 3 + 4 ≡ 0 (mod 7)
/// ```
pub fn mod_negate_big(val: Int, m: Int) -> Int {
    if m <= Int::zero() {
        return val;
    }
    let mut v = val % m;
    if v < Int::zero() {
        v += m;
    }
    if v == Int::zero() {
        Int::zero()
    } else {
        m - v
    }
}
