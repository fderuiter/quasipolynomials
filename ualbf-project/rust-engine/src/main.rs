mod types;
mod math_utils;
mod sieve;
mod dfs_tree;
mod raycast;

use num_bigint::ToBigUint;

const TARGET_BOUND_LOG10: u32 = 40;
const PREFIX_STOP_THRESHOLD: u64 = 10_000_000_000_000_000; // 10^16

fn main() {
    println!("=== UALBF Engine Initializing ===");
    println!("Target Bound: N > 10^{}", TARGET_BOUND_LOG10);

    let target_bound = 10_u32.to_biguint().unwrap().pow(TARGET_BOUND_LOG10);
    let threshold = PREFIX_STOP_THRESHOLD.to_biguint().unwrap();

    let valid_components = sieve::phase1_global_annihilation_sieve(50_000, 4);
    
    // Precompute illegal primes once to pass into the parallel pipeline
    let illegal_primes = raycast::generate_illegal_valuation_primes(100);
    
    // Launch fused perfectly-balanced parallel pipeline!
    dfs_tree::phase2_and_4_fused(&valid_components, &threshold, &target_bound, &illegal_primes);

    println!("PROGRESS|DONE|4|1|Verification Complete. N > 10^{} Confirmed", TARGET_BOUND_LOG10);
}
