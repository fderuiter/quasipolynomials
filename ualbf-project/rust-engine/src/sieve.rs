use num_bigint::BigUint;
use num_traits::ToPrimitive;
use primal::Sieve;
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::math_utils::{compute_sigma, quick_factor};
use crate::types::PrimePower;

pub fn phase1_global_annihilation_sieve(limit: usize, max_e: u32) -> Vec<PrimePower> {
    println!("PROGRESS|PHASE|1|Legendre-Cattaneo Sieve");
    let sieve = Sieve::new(limit);
    let pruned = AtomicUsize::new(0);
    
    let total_primes = sieve.prime_pi(limit);
    let count = AtomicUsize::new(0);

    let primes: Vec<usize> = sieve.primes_from(3).collect();

    let mut valid_components: Vec<PrimePower> = primes.into_par_iter().flat_map(|p| {
        let mut local_components = Vec::new();
        let current_count = count.fetch_add(1, Ordering::Relaxed) + 1;
        if current_count % 100 == 0 {
            println!("PROGRESS|UPDATE|{}|{}|Evaluating prime {}", current_count, total_primes, p);
        }
        let p_bu = BigUint::from(p as u64);
        for e in 1..=max_e {
            let two_e = 2 * e;
            let val = p_bu.pow(two_e);
            let sigma = compute_sigma(&p_bu, two_e);
            
            let factors = quick_factor(sigma.clone());
            let mut is_valid = true;
            for q in factors {
                let q_mod_8 = (&q % 8u32).to_u32().unwrap();
                if q_mod_8 == 5 || q_mod_8 == 7 {
                    is_valid = false;
                    pruned.fetch_add(1, Ordering::Relaxed);
                    break;
                }
            }

            if is_valid {
                local_components.push(PrimePower { p: p as u64, val, sigma });
            }
        }
        local_components
    }).collect();

    valid_components.sort_by(|a, b| b.val.cmp(&a.val));
    println!("Retained: {}, Pruned: {}", valid_components.len(), pruned.load(Ordering::Relaxed));
    valid_components
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_utils::quick_factor;

    #[test]
    fn test_phase1_sieve_logic() {
        let limit = 50;
        let max_e = 2;
        let components = phase1_global_annihilation_sieve(limit, max_e);
        
        assert!(!components.is_empty());
        for comp in components {
            let factors = quick_factor(comp.sigma.clone());
            for q in factors {
                let q_mod_8 = (&q % 8u32).to_u32().unwrap();
                assert!(q_mod_8 != 5 && q_mod_8 != 7, "Invalid sigma component leaked into valid_components!");
            }
        }
    }
}
