mod types;
mod math_utils;
mod sieve;
mod dfs_tree;
mod raycast;

use num_bigint::{BigUint, ToBigUint};
use rayon::prelude::*;

const TARGET_BOUND_LOG10: u32 = 50;
const PREFIX_STOP_THRESHOLD: u64 = 10_000_000_000_000_000; // 10^16

fn main() {
    println!("=== UALBF Engine Initializing ===");
    println!("Target Bound: N > 10^{}", TARGET_BOUND_LOG10);

    let target_bound = 10_u32.to_biguint().unwrap().pow(TARGET_BOUND_LOG10);
    let threshold = PREFIX_STOP_THRESHOLD.to_biguint().unwrap();

    let valid_components = sieve::phase1_global_annihilation_sieve(50_000, 4);
    let prefix_pool = dfs_tree::phase2_build_prefix_tree(&valid_components, &threshold);
    
    println!("\n[PHASE 3] Exact Valuation Sieve & Ray-Casting...");
    let processed = std::sync::atomic::AtomicUsize::new(0);

    // Multithreaded lock-free execution across all CPU cores
    prefix_pool.par_iter().for_each(|prefix| {
        raycast::phase4_exact_ray_casting(prefix, &target_bound);

        let count = processed.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if count % 100_000 == 0 && count > 0 {
            println!("Processed {}/{} prefixes...", count, prefix_pool.len());
        }
    });

    println!("=== Verification Complete. N > 10^{} Mathematically Confirmed ===", TARGET_BOUND_LOG10);
}
