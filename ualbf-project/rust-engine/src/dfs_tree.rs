use num_bigint::BigUint;
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::types::{PrimePower, Prefix};

pub fn phase2_build_prefix_tree(components: &[PrimePower], stop_threshold: &BigUint) -> Vec<Prefix> {
    println!("PROGRESS|PHASE|2|Dynamic Prefix DFS Construction");
    
    // Create the first level of branches sequentially to seed our parallel traversal.
    let initial_states: Vec<Prefix> = components.iter().enumerate().map(|(i, comp)| {
        Prefix {
            n_l: comp.val.clone(),
            s_l: comp.sigma.clone(),
            last_idx: i + 1,
            factors: vec![comp.p],
        }
    }).collect();

    let count = AtomicUsize::new(0);

    let pool: Vec<Prefix> = initial_states.into_par_iter().flat_map(|start_node| {
        let mut stack = vec![start_node];
        let mut local_pool = Vec::new();

        while let Some(curr) = stack.pop() {
            let c = count.fetch_add(1, Ordering::Relaxed) + 1;
            if c % 10000 == 0 {
                println!("PROGRESS|UPDATE|{}|0|Building DFS Tree: {} nodes explored", c, c);
            }
            if &curr.n_l >= stop_threshold {
                local_pool.push(curr);
                continue;
            }

            for i in curr.last_idx..components.len() {
                let comp = &components[i];
                if curr.factors.contains(&comp.p) { continue; }

                let mut next_factors = curr.factors.clone();
                next_factors.push(comp.p);

                stack.push(Prefix {
                    n_l: &curr.n_l * &comp.val,
                    s_l: &curr.s_l * &comp.sigma,
                    last_idx: i + 1,
                    factors: next_factors,
                });
            }
        }
        local_pool
    }).collect();

    println!("Generated Prefix Leaves: {}", pool.len());
    pool
}
