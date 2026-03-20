use num_bigint::BigUint;
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::types::{PrimePower, Prefix};
use crate::raycast::phase4_exact_ray_casting;

pub fn phase2_and_4_fused(
    components: &[PrimePower],
    stop_threshold: &BigUint,
    target_bound: &BigUint,
    illegal_primes: &[u64],
) {
    println!("PROGRESS|PHASE|2|Fused DFS Construction & Ray-Casting");
    
    let count = AtomicUsize::new(0);

    // Initial states
    (0..components.len()).into_par_iter().for_each(|i| {
        let comp = &components[i];
        let curr = Prefix {
            n_l: comp.val.clone(),
            s_l: comp.sigma.clone(),
            last_idx: i + 1,
            factors: vec![comp.p],
        };
        
        explore_prefix(curr, components, stop_threshold, target_bound, illegal_primes, &count);
    });
}

fn explore_prefix(
    curr: Prefix,
    components: &[PrimePower],
    stop_threshold: &BigUint,
    target_bound: &BigUint,
    illegal_primes: &[u64],
    count: &AtomicUsize,
) {
    if &curr.n_l >= stop_threshold {
        let c = count.fetch_add(1, Ordering::Relaxed) + 1;
        if c % 1000 == 0 {
             println!("PROGRESS|UPDATE|{}|0|Processed {} prefixes...", c, c);
        }
        
        phase4_exact_ray_casting(&curr, target_bound, illegal_primes);
        return;
    }

    // Continue DFS in parallel
    (curr.last_idx..components.len()).into_par_iter().for_each(|i| {
        let comp = &components[i];
        if !curr.factors.contains(&comp.p) {
            let mut next_factors = curr.factors.clone();
            next_factors.push(comp.p);
            
            let next_prefix = Prefix {
                n_l: &curr.n_l * &comp.val,
                s_l: &curr.s_l * &comp.sigma,
                last_idx: i + 1,
                factors: next_factors,
            };
            
            explore_prefix(next_prefix, components, stop_threshold, target_bound, illegal_primes, count);
        }
    });
}
