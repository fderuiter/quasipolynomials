use crate::types::{Int, Uint, IntExt, UintExt};
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct VectorizedEngine;

impl VectorizedEngine {
    pub fn raycast_sieve(
        c_min: usize,
        c_max: usize,
        r_i: Int,
        s_l_int: Int,
        illegal_z_valuations: &[(Int, Int)],
        pruned_count: &AtomicUsize,
    ) -> Vec<usize> {
        let pruned_local = AtomicUsize::new(0);

        let valid_indices: Vec<usize> = (c_min..=c_max)
            .into_par_iter()
            .filter_map(|c| {
                let z = r_i + Int::from_u64(c as u64) * s_l_int;
                if z % Int::from_u32(2) == Int::zero() {
                    pruned_local.fetch_add(1, Ordering::Relaxed);
                    return None;
                }

                let mut passed_sieve = true;
                for &(pe, pe1) in illegal_z_valuations {
                    let rem = z % pe1;
                    if rem % pe == Int::zero() && rem != Int::zero() {
                        passed_sieve = false;
                        break;
                    }
                }

                if passed_sieve {
                    Some(c)
                } else {
                    pruned_local.fetch_add(1, Ordering::Relaxed);
                    None
                }
            })
            .collect();

        pruned_count.fetch_add(pruned_local.into_inner(), Ordering::Relaxed);
        valid_indices
    }
}
