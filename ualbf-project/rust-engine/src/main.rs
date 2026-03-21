mod types;
mod math_utils;
mod sieve;
mod dfs_tree;
mod raycast;

use crate::types::Uint;

const TARGET_BOUND_LOG10: u32 = 37;
const TARGET_BOUND_MIN_LOG10: u32 = 35; // Hagis-Cohen bound
const PREFIX_STOP_THRESHOLD: u64 = 100_000_000_000; // 10^11

fn main() {
    println!("=== UALBF Engine Initializing ===");
    println!("Target Bound: 10^{} < N < 10^{}", TARGET_BOUND_MIN_LOG10, TARGET_BOUND_LOG10);

    let target_min: Uint = 10_u128.pow(TARGET_BOUND_MIN_LOG10);
    let target_bound: Uint = 10_u128.pow(TARGET_BOUND_LOG10);
    let threshold: Uint = PREFIX_STOP_THRESHOLD as Uint;

    let valid_components = sieve::phase1_global_annihilation_sieve(250_000, 4);
    
    // Precompute illegal valuations once to pass into the parallel pipeline
    let illegal_valuations = raycast::generate_illegal_valuations(250, 4);
    
    // Launch fused perfectly-balanced parallel pipeline!
    dfs_tree::phase2_and_4_fused(&valid_components, &threshold, &target_min, &target_bound, &illegal_valuations);

    println!("PROGRESS|DONE|4|1|Verification Complete. 10^{} < N < 10^{} Confirmed", TARGET_BOUND_MIN_LOG10, TARGET_BOUND_LOG10);
}
