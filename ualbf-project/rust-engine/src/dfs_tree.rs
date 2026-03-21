use crate::types::{PrimePower, Prefix, Uint, Int};
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::raycast::phase4_exact_ray_casting;

pub fn phase2_and_4_fused(
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
) {
    println!("PROGRESS|PHASE|2|Fused DFS Construction & Ray-Casting");
    
    let count = AtomicUsize::new(0);
    let pruned_count = AtomicUsize::new(0);
    let completed_weight_scaled = AtomicUsize::new(0);
    let total_weight_scaled: usize = components.iter().map(|c| (10_000_000.0 / ((c.p as f64) * (c.p as f64))) as usize).sum();
    let active_primes = Arc::new(Mutex::new(Vec::<u64>::new()));

    // Initial states
    (0..components.len()).into_par_iter().for_each(|i| {
        let comp = &components[i];
        
        {
            let mut ap = active_primes.lock().unwrap();
            ap.push(comp.p);
            ap.sort_unstable();
        }
        let curr = Prefix {
            n_l: comp.val,
            s_l: comp.sigma,
            last_idx: i + 1,
            factors: vec![comp.p],
            sigma_factors: comp.sigma_factors.clone(),
        };
        
        explore_prefix(curr, components, stop_threshold, target_bound, illegal_valuations, &count, &pruned_count, &completed_weight_scaled, total_weight_scaled, &active_primes);
        
        let w = (10_000_000.0 / ((comp.p as f64) * (comp.p as f64))) as usize;
        completed_weight_scaled.fetch_add(w, Ordering::Relaxed);
        
        {
            let mut ap = active_primes.lock().unwrap();
            if let Some(idx) = ap.iter().position(|&x| x == comp.p) {
                ap.remove(idx);
            }
        }
    });
}

fn explore_prefix(
    curr: Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<Mutex<Vec<u64>>>,
) {
    if curr.n_l > *target_bound {
        return;
    }

    if curr.n_l >= *stop_threshold {
        let c = count.fetch_add(1, Ordering::Relaxed) + 1;
        if c % 1000 == 0 {
             let pr = pruned_count.load(Ordering::Relaxed);
             let comp = completed_weight_scaled.load(Ordering::Relaxed);
             
             let active_str = {
                 let ap = active_primes.lock().unwrap();
                 let active_count = ap.len();
                 let display = ap.iter().take(4).map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
                 if active_count > 4 {
                     format!("{}... ({} total)", display, active_count)
                 } else {
                     display
                 }
             };
             
             println!("PROGRESS|UPDATE|{}|{}|{}|{}|P-Active: {} | Prefixes: {}", c, total_weight_scaled, comp, pr, active_str, c);
        }
        
        phase4_exact_ray_casting(&curr, target_bound, illegal_valuations, pruned_count);
    }

    // Continue DFS in parallel
    (curr.last_idx..components.len()).into_par_iter().for_each(|i| {
        let comp = &components[i];
        if !curr.factors.contains(&comp.p) {
            if let (Some(next_n_l), Some(next_s_l)) = (curr.n_l.checked_mul(comp.val), curr.s_l.checked_mul(comp.sigma)) {
                if next_n_l <= *target_bound {
                    let mut next_factors = curr.factors.clone();
                    next_factors.push(comp.p);
                    
                    let mut next_sigma_factors = curr.sigma_factors.clone();
                    next_sigma_factors.extend(comp.sigma_factors.iter().cloned());
                    
                    let next_prefix = Prefix {
                        n_l: next_n_l,
                        s_l: next_s_l,
                        last_idx: i + 1,
                        factors: next_factors,
                        sigma_factors: next_sigma_factors,
                    };
                    
                    explore_prefix(next_prefix, components, stop_threshold, target_bound, illegal_valuations, count, pruned_count, completed_weight_scaled, total_weight_scaled, active_primes);
                }
            }
        }
    });
}
