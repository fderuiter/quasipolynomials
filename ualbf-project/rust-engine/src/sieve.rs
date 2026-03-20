use num_bigint::BigUint;
use num_traits::ToPrimitive;
use primal::Sieve;
use crate::math_utils::{compute_sigma, quick_factor};
use crate::types::PrimePower;

pub fn phase1_global_annihilation_sieve(limit: usize, max_e: u32) -> Vec<PrimePower> {
    println!("PROGRESS|PHASE|1|Legendre-Cattaneo Sieve");
    let sieve = Sieve::new(limit);
    let mut valid_components = Vec::new();
    let mut pruned = 0;
    
    let total_primes = sieve.prime_pi(limit);
    let mut count = 0;

    for p in sieve.primes_from(3) {
        count += 1;
        if count % 100 == 0 {
            println!("PROGRESS|UPDATE|{}|{}|Evaluating prime {}", count, total_primes, p);
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
                    pruned += 1;
                    break;
                }
            }

            if is_valid {
                valid_components.push(PrimePower { p: p as u64, val, sigma });
            }
        }
    }
    valid_components.sort_by(|a, b| b.val.cmp(&a.val));
    println!("Retained: {}, Pruned: {}", valid_components.len(), pruned);
    valid_components
}
