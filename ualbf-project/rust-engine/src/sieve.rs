use crate::math_utils::{SigmaCache, TrialSieve};
use crate::types::{PrimePower, Uint};
use primal::Sieve;
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Mutex;

/// Phase 1 sieve result: valid components + prebuilt sigma cache.
pub struct SieveResult {
    pub components: Vec<PrimePower>,
    pub sigma_cache: SigmaCache,
}

pub fn phase1_global_annihilation_sieve(limit: usize, max_e: u32) -> SieveResult {
    println!("PROGRESS|PHASE|1|Legendre-Cattaneo Sieve");
    let phase1_start = std::time::Instant::now();
    let sieve = Sieve::new(limit);
    let pruned = AtomicUsize::new(0);
    let ecm_calls = AtomicUsize::new(0);
    let trial_only = AtomicUsize::new(0);

    let total_primes = sieve.prime_pi(limit);
    let count = AtomicUsize::new(0);

    let primes: Vec<usize> = sieve.primes_from(3).collect();

    // Build a trial-division sieve — shared across all Rayon threads.
    // 10M covers √(Φ_d(p)) for all relevant cyclotomic values (10M² = 10^14).
    let trial_limit = 10_000_000u64;
    println!(
        "Sieve|DIAG|Building trial sieve to {} ({} primes total to evaluate)",
        trial_limit, total_primes
    );
    let trial_sieve = TrialSieve::new(trial_limit);
    println!(
        "Sieve|DIAG|Trial sieve ready: {} small primes loaded",
        trial_sieve.small_primes.len()
    );

    // Thread-safe sigma cache collector
    let sigma_cache_mu: Mutex<SigmaCache> = Mutex::new(HashMap::new());

    // Timing diagnostics: track cumulative factorization time per thread
    let total_factor_ns = AtomicU64::new(0);

    let mut valid_components: Vec<PrimePower> = primes
        .into_par_iter()
        .flat_map(|p| {
            let mut local_components = Vec::new();
            let mut local_cache: Vec<((Uint, u32), Uint)> = Vec::new();
            let current_count = count.fetch_add(1, Ordering::Relaxed) + 1;
            if current_count % 500 == 0 {
                let elapsed = phase1_start.elapsed().as_secs_f64();
                let rate = current_count as f64 / elapsed;
                let ecm_n = ecm_calls.load(Ordering::Relaxed);
                let trial_n = trial_only.load(Ordering::Relaxed);
                let factor_ms = total_factor_ns.load(Ordering::Relaxed) / 1_000_000;
                println!(
                    "PROGRESS|UPDATE|{}|{}|p={} | {:.0} p/s | trial={} ecm={} | factor_time={}ms",
                    current_count, total_primes, p, rate, trial_n, ecm_n, factor_ms
                );
            }
            let p_bu = Uint::from(p as u32);
            for e in 1..=max_e {
                let two_e = 2 * e;
                let val = match p_bu.checked_pow(two_e) {
                    Some(v) => v,
                    None => break,
                };
                if val > 10_u128.pow(37) {
                    break;
                }
                // ⚡ Verified Lean FFI call for exact computation
                // Local pure rust compute sigma to speed up Phase 1
                let mut sum: Uint = Uint::ONE;
                let mut p_pow: Uint = Uint::ONE;
                for _ in 0..two_e {
                    p_pow *= Uint::from(p as u64);
                    sum += p_pow;
                }
                let sigma = sum;
                if sigma == 0 {
                    continue; // overflow
                }

                // Collect into sigma cache for later reuse in raycast
                local_cache.push(((p_bu, two_e), Uint::from(sigma)));

                // ⚡ Two-pass approach:
                // Pass 1: Quick mod-8 screening via cyclotomic + trial division (early exit)
                // Pass 2: Full factorization only for survivors
                let t0 = std::time::Instant::now();
                let screen_result =
                    screen_mod8_cyclotomic(p as u64, two_e, &trial_sieve, &ecm_calls, &trial_only);
                total_factor_ns.fetch_add(t0.elapsed().as_nanos() as u64, Ordering::Relaxed);

                match screen_result {
                    ScreenResult::Rejected => {
                        pruned.fetch_add(1, Ordering::Relaxed);
                    }
                    ScreenResult::Accepted(factors) => {
                        let sigma_u256 = Uint::from(sigma);
                        let shifted = sigma_u256 << 64;
                        let mut abundance_fp = (shifted / val).as_u128();
                        if shifted % val != Uint::ZERO {
                            abundance_fp += 1;
                        }
                        local_components.push(PrimePower {
                            p: p as u64,
                            two_e,
                            val,
                            sigma: Uint::from(sigma),
                            sigma_factors: factors,
                            abundance_fp,
                        });
                    }
                }
            }
            // Flush local sigma cache into shared cache
            if !local_cache.is_empty() {
                if let Ok(mut cache) = sigma_cache_mu.lock() {
                    for (k, v) in local_cache {
                        cache.insert(k, v);
                    }
                }
            }
            local_components
        })
        .collect();

    let elapsed = phase1_start.elapsed();
    let ecm_n = ecm_calls.load(Ordering::Relaxed);
    let trial_n = trial_only.load(Ordering::Relaxed);
    println!(
        "Sieve|DIAG|Phase 1 complete in {:.1}s | {} retained, {} pruned | trial={} ecm_fallback={}",
        elapsed.as_secs_f64(),
        valid_components.len(),
        pruned.load(Ordering::Relaxed),
        trial_n,
        ecm_n
    );

    // Sort by abundance ratio descending (small primes first — they have highest σ/val ratios)
    valid_components.sort_by(|a, b| {
        b.abundance_fp.cmp(&a.abundance_fp)
    });
    println!(
        "Retained: {}, Pruned: {}",
        valid_components.len(),
        pruned.load(Ordering::Relaxed)
    );

    // Telemetry Export: Dump valid components
    for comp in &valid_components {
        let factors_str = comp
            .sigma_factors
            .iter()
            .map(|f| f.to_string())
            .collect::<Vec<_>>()
            .join(",");
        println!(
            "DATA|COMP|{}|{}|{:.6}|{}",
            comp.p, comp.two_e, comp.abundance_fp, factors_str
        );
    }

    let sigma_cache = sigma_cache_mu.into_inner().unwrap();
    SieveResult {
        components: valid_components,
        sigma_cache,
    }
}

// ---------------------------------------------------------------------------
// Two-pass mod-8 screening
// ---------------------------------------------------------------------------

enum ScreenResult {
    Rejected,
    Accepted(Vec<Uint>),
}

/// Screen σ(p^{2e}) for the mod-8 obstruction using cyclotomic decomposition.
///
/// For each cyclotomic factor Φ_d(p):
///   1. Trial-divide to extract small prime factors, checking mod-8 as we go.
///   2. If a bad factor (≡ 5 or 7 mod 8) is found, return Rejected immediately.
///   3. If a large composite cofactor remains, check IT mod 8 — if it's ≡ 5 or 7
///      mod 8 AND prime, reject. If composite, we must factor it (ECM fallback).
///
/// This avoids full ECM factorization for the ~60% of components that get pruned.
fn screen_mod8_cyclotomic(
    p: u64,
    two_e: u32,
    trial: &TrialSieve,
    ecm_calls: &AtomicUsize,
    trial_only: &AtomicUsize,
) -> ScreenResult {
    use crate::math_utils::{cyclotomic_eval_pub, is_prime_u256, small_divisors_pub};
    let n = two_e + 1;
    let divs = small_divisors_pub(n);
    let p128 = p as u128;

    let mut all_factors: Vec<Uint> = Vec::new();
    let mut needed_ecm = false;

    for d in &divs {
        if *d == 1 {
            continue;
        }
        
        // Attempt fast path with precomputed factors
        if let Some(factors) = crate::math_utils::get_precomputed_factors(p as u32, *d as u8) {
            if factors.len() == 1 && factors[0] == 0 {
                return ScreenResult::Rejected;
            }
            let mut bad_found = false;
            for &f in factors {
                let q_mod_8 = (f % 8) as u32;
                if q_mod_8 == 5 || q_mod_8 == 7 {
                    bad_found = true;
                    break;
                }
                all_factors.push(Uint::from(f));
            }
            if bad_found {
                return ScreenResult::Rejected;
            }
            continue; // Skip the manual evaluation/factorization since we already handled this cyclotomic divisor
        }

        let phi_val = match cyclotomic_eval_pub(*d, Uint::from(p128)) {
            Some(v) if v > 1 => v,
            Some(_) => continue,
            None => {
                // Overflow — factor full σ
                let full_sigma = crate::lean_ffi::compute_sigma(p, two_e);
                let factors = trial.factor(full_sigma);
                ecm_calls.fetch_add(1, Ordering::Relaxed);
                for q in &factors {
                    let q_mod_8 = (q % Uint::from(8u32)).as_u32();
                    if q_mod_8 == 5 || q_mod_8 == 7 {
                        return ScreenResult::Rejected;
                    }
                }
                return ScreenResult::Accepted(factors);
            }
        };

        // Trial-divide this cyclotomic value, checking mod-8 as we extract factors
        let mut remaining = phi_val;
        for &sp in &trial.small_primes {
            let sp128 = sp as u128;
            if sp128 * sp128 > remaining {
                break;
            }
            while remaining % sp128 == 0 {
                // Check mod-8 immediately
                let q_mod_8 = (sp % 8) as u32;
                if q_mod_8 == 5 || q_mod_8 == 7 {
                    return ScreenResult::Rejected;
                }
                all_factors.push(Uint::from(sp128));
                remaining /= sp128;
            }
        }

        if remaining > 1 {
            // Check the cofactor's mod-8 residue
            let r_mod_8 = (remaining % Uint::from(8u32)).as_u32();

            let limit128 = trial.small_primes.last().copied().unwrap_or(2) as u128;
            if remaining <= limit128 * limit128 {
                // It's prime (we've exhausted trial primes up to √remaining)
                if r_mod_8 == 5 || r_mod_8 == 7 {
                    return ScreenResult::Rejected;
                }
                all_factors.push(remaining);
            } else if is_prime_u256(Uint::from(remaining)) {
                // Miller-Rabin says prime
                if r_mod_8 == 5 || r_mod_8 == 7 {
                    return ScreenResult::Rejected;
                }
                all_factors.push(remaining);
            } else {
                // Composite cofactor: use mod-8 subgroup property.
                // {1,3} is closed under multiplication mod 8, so if the
                // composite ≡ 5 or 7 (mod 8), it MUST have a bad prime factor.
                if r_mod_8 == 5 || r_mod_8 == 7 {
                    return ScreenResult::Rejected;
                }
                // Composite ≡ 1 or 3 (mod 8) could still hide bad factors
                // (e.g., 5×7=35≡3 mod 8). Must factor to be sure.
                needed_ecm = true;
                ecm_calls.fetch_add(1, Ordering::Relaxed);
                let rho_factors = crate::math_utils::rho_factor_u256(remaining);
                for &q in &rho_factors {
                    let q_mod_8 = (q % Uint::from(8u32)).as_u32();
                    if q_mod_8 == 5 || q_mod_8 == 7 {
                        return ScreenResult::Rejected;
                    }
                }
                all_factors.extend(rho_factors);
            }
        }
    }

    if !needed_ecm {
        trial_only.fetch_add(1, Ordering::Relaxed);
    }
    all_factors.sort_unstable();
    ScreenResult::Accepted(all_factors)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_utils::quick_factor_u256;

    #[test]
    fn test_phase1_sieve_logic() {
        let limit = 50;
        let max_e = 2;
        let result = phase1_global_annihilation_sieve(limit, max_e);

        assert!(!result.components.is_empty());
        for comp in result.components {
            let factors = quick_factor_u256(comp.sigma);
            for q in &factors {
                let q_mod_8 = (q % Uint::from(8u32)).as_u32();
                assert!(
                    q_mod_8 != 5 && q_mod_8 != 7,
                    "Invalid sigma component leaked into valid_components!"
                );
            }
        }
    }
}
