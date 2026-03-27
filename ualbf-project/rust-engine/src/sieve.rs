use crate::math_utils::{factor_sigma_cyclotomic, quick_factor_u128};
use crate::types::{PrimePower, Uint};
use primal::Sieve;
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};

pub fn phase1_global_annihilation_sieve(limit: usize, max_e: u32) -> Vec<PrimePower> {
    println!("PROGRESS|PHASE|1|Legendre-Cattaneo Sieve");
    let sieve = Sieve::new(limit);
    let pruned = AtomicUsize::new(0);

    let total_primes = sieve.prime_pi(limit);
    let count = AtomicUsize::new(0);

    let primes: Vec<usize> = sieve.primes_from(3).collect();

    let mut valid_components: Vec<PrimePower> = primes
        .into_par_iter()
        .flat_map(|p| {
            let mut local_components = Vec::new();
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
                let sigma = crate::lean_ffi::compute_sigma(p as u64, two_e);

                // Use cyclotomic decomposition for faster factorization (ENG-201)
                let factors = factor_sigma_cyclotomic(p as u64, two_e);
                if factors.is_empty() {
                    continue;
                } // factorisation failed — skip
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
    valid_components
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_utils::quick_factor_u128;

    #[test]
    fn test_phase1_sieve_logic() {
        let limit = 50;
        let max_e = 2;
        let components = phase1_global_annihilation_sieve(limit, max_e);

        assert!(!components.is_empty());
        for comp in components {
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
