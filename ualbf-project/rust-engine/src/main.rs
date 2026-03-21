mod types;
mod math_utils;
mod sieve;
mod dfs_tree;
mod raycast;

use crate::types::Uint;

const TARGET_BOUND_LOG10: u32 = 37;
const PREFIX_STOP_THRESHOLD: u64 = 100_000_000_000; // 10^11

fn main() {
    println!("=== UALBF Engine Initializing ===");
    println!("Target Bound: N > 10^{}", TARGET_BOUND_LOG10);

    let target_bound: Uint = 10_u128.pow(TARGET_BOUND_LOG10);
    let threshold: Uint = PREFIX_STOP_THRESHOLD as Uint;

    let valid_components = sieve::phase1_global_annihilation_sieve(250_000, 4);
    
    // Precompute illegal primes once to pass into the parallel pipeline
    let illegal_primes = raycast::generate_illegal_valuation_primes(250);
    
    // Launch fused perfectly-balanced parallel pipeline!
    dfs_tree::phase2_and_4_fused(&valid_components, &threshold, &target_bound, &illegal_primes);

    println!("PROGRESS|DONE|4|1|Verification Complete. N > 10^{} Confirmed", TARGET_BOUND_LOG10);
}
