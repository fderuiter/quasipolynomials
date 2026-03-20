use num_bigint::BigUint;
use num_traits::One;
use crate::types::{PrimePower, Prefix};

pub fn phase2_build_prefix_tree(components: &[PrimePower], stop_threshold: &BigUint) -> Vec<Prefix> {
    println!("[PHASE 2] Dynamic Prefix DFS Construction...");
    let mut pool = Vec::new();
    let mut stack = vec![Prefix {
        n_l: BigUint::one(),
        s_l: BigUint::one(),
        last_idx: 0,
        factors: vec![],
    }];

    while let Some(curr) = stack.pop() {
        if &curr.n_l >= stop_threshold {
            pool.push(curr);
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
    println!("Generated Prefix Leaves: {}", pool.len());
    pool
}
