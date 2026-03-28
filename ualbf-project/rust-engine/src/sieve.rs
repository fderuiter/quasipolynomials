use crate::math_utils::{sigma_pure_rust, TrialSieve, SigmaCache};
use crate::types::{PrimePower, Uint};
use primal::Sieve;
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

/// Phase 1 sieve result: valid components + prebuilt sigma cache.
pub struct SieveResult {
    pub components: Vec<PrimePower>,
    pub sigma_cache: SigmaCache,
}

pub fn phase1_global_annihilation_sieve(limit: usize, max_e: u32) -> SieveResult {
    println!("PROGRESS|PHASE|1|Legendre-Cattaneo Sieve");
    let sieve = Sieve::new(limit);
    let pruned = AtomicUsize::new(0);

    let total_primes = sieve.prime_pi(limit);
    let count = AtomicUsize::new(0);

    let primes: Vec<usize> = sieve.primes_from(3).collect();

    // Build a trial-division sieve once — shared across all Rayon threads
    let trial_sieve = TrialSieve::new(100_000);

    // Thread-safe sigma cache collector
    let sigma_cache_mu: Mutex<SigmaCache> = Mutex::new(HashMap::new());

    let mut valid_components: Vec<PrimePower> = primes
        .into_par_iter()
        .flat_map(|p| {
            let mut local_components = Vec::new();
            let mut local_cache: Vec<((Uint, u32), Uint)> = Vec::new();
            let current_count = count.fetch_add(1, Ordering::Relaxed) + 1;
            if current_count % 100 == 0 {
                println!(
                    "PROGRESS|UPDATE|{}|{}|Evaluating prime {}",
                    current_count, total_primes, p
                );
            }
            let p_bu = p as Uint;
            for e in 1..=max_e {
                let two_e = 2 * e;
                let val = match p_bu.checked_pow(two_e) {
                    Some(v) => v,
                    None => break,
                };
                if val > 10_u128.pow(37) {
                    break;
                }
                // ⚡ Pure-Rust σ — no FFI overhead
                let sigma = sigma_pure_rust(p as u64, two_e);
                if sigma == 0 {
                    continue; // overflow
                }

                // Collect into sigma cache for later reuse in raycast
                local_cache.push(((p_bu, two_e), sigma));

                // ⚡ Factor via cyclotomic decomposition + trial division
                let factors = factor_sigma_cyclotomic_fast(p as u64, two_e, &trial_sieve);
                if factors.is_empty() {
                    continue;
                }
                let mut is_valid = true;
                for q in &factors {
                    let q_mod_8 = (q % 8) as u32;
                    if q_mod_8 == 5 || q_mod_8 == 7 {
                        is_valid = false;
                        pruned.fetch_add(1, Ordering::Relaxed);
                        break;
                    }
                }

                if is_valid {
                    let abundance_ratio = sigma as f64 / val as f64;
                    local_components.push(PrimePower {
                        p: p as u64,
                        val,
                        sigma,
                        sigma_factors: factors,
                        abundance_ratio,
                    });
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

    // Sort by abundance ratio descending (small primes first — they have highest σ/val ratios)
    valid_components.sort_by(|a, b| {
        b.abundance_ratio
            .partial_cmp(&a.abundance_ratio)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    println!(
        "Retained: {}, Pruned: {}",
        valid_components.len(),
        pruned.load(Ordering::Relaxed)
    );

    let sigma_cache = sigma_cache_mu.into_inner().unwrap();
    SieveResult {
        components: valid_components,
        sigma_cache,
    }
}

/// Factor σ(p^{2e}) using cyclotomic decomposition + fast trial division.
/// Each Φ_d(p) is much smaller than the full σ, making trial division effective.
fn factor_sigma_cyclotomic_fast(p: u64, two_e: u32, trial: &TrialSieve) -> Vec<u128> {
    use crate::math_utils::{cyclotomic_eval_pub, small_divisors_pub};
    let n = two_e + 1;
    let divs = small_divisors_pub(n);
    let p128 = p as u128;

    let mut all_factors = Vec::new();
    for d in &divs {
        if *d == 1 {
            continue;
        }
        if let Some(phi_val) = cyclotomic_eval_pub(*d, p128) {
            if phi_val > 1 {
                all_factors.extend(trial.factor(phi_val));
            }
        } else {
            // Overflow — fall back to factoring full σ
            let full_sigma = sigma_pure_rust(p, two_e);
            return trial.factor(full_sigma);
        }
    }
    all_factors.sort_unstable();
    all_factors
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_utils::quick_factor_u128;

    #[test]
    fn test_phase1_sieve_logic() {
        let limit = 50;
        let max_e = 2;
        let result = phase1_global_annihilation_sieve(limit, max_e);

        assert!(!result.components.is_empty());
        for comp in result.components {
            let factors = quick_factor_u128(comp.sigma);
            for q in &factors {
                let q_mod_8 = (q % 8) as u32;
                assert!(
                    q_mod_8 != 5 && q_mod_8 != 7,
                    "Invalid sigma component leaked into valid_components!"
                );
            }
        }
    }
}
