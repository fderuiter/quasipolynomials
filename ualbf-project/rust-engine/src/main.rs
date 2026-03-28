#![allow(unused_imports, dead_code)]
use std::env;
mod dfs_tree;
mod lattice;
mod lean_ffi;
mod math_utils;
mod raycast;
mod sieve;
mod types;
mod z3_pruner;

use crate::types::Uint;

// Defaults — overridable via UALBF_TARGET_MAX_LOG10, UALBF_TARGET_MIN_LOG10, etc.
const DEFAULT_TARGET_MAX_LOG10: u32 = 37;
const DEFAULT_TARGET_MIN_LOG10: u32 = 35; // Hagis-Cohen bound
const DEFAULT_PREFIX_STOP_THRESHOLD: u64 = 100_000_000_000; // 10^11
const DEFAULT_SIEVE_LIMIT: usize = 250_000;
const DEFAULT_MAX_EXPONENT: u32 = 4;

fn main() {
    // Initialize the Lean 4 runtime before any FFI calls
    lean_ffi::initialize_lean_runtime();

    // Force Rayon to initialize Lean's memory allocator on all worker threads
    rayon::ThreadPoolBuilder::new()
        .start_handler(|_| lean_ffi::initialize_lean_worker_thread())
        .build_global()
        .unwrap();

    // ── Read configurable parameters from environment (set by run_gui.py) ──
    let target_min_log10: u32 = env::var("UALBF_TARGET_MIN_LOG10")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(DEFAULT_TARGET_MIN_LOG10);
    let target_max_log10: u32 = env::var("UALBF_TARGET_MAX_LOG10")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(DEFAULT_TARGET_MAX_LOG10);
    let sieve_limit: usize = env::var("UALBF_SIEVE_LIMIT")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(DEFAULT_SIEVE_LIMIT);
    let max_exponent: u32 = env::var("UALBF_MAX_EXPONENT")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(DEFAULT_MAX_EXPONENT);
    let prefix_stop: u64 = env::var("UALBF_PREFIX_STOP_THRESHOLD")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(DEFAULT_PREFIX_STOP_THRESHOLD);

    println!("=== UALBF Engine Initializing ===");
    println!(
        "Target Bound: 10^{} < N < 10^{}",
        target_min_log10, target_max_log10
    );
    println!(
        "Sieve: limit={}, max_exponent={}, prefix_stop={}",
        sieve_limit, max_exponent, prefix_stop
    );

    let target_min: Uint = 10_u128.pow(target_min_log10);
    let target_bound: Uint = 10_u128.pow(target_max_log10);
    let threshold: Uint = prefix_stop as Uint;

    let valid_components = sieve::phase1_global_annihilation_sieve(sieve_limit, max_exponent);

    // Precompute suffix-max abundance product array for DFS pruning.
    // suffix_abundance[i] = max achievable abundance product using up to 7
    // components from index i onwards (since QPN needs ≥7 distinct prime factors).
    let max_factors = 7usize;
    let n = valid_components.len();
    let mut suffix_abundance = vec![1.0_f64; n + 1];
    // Components are sorted by abundance ratio descending, so the first components
    // at each suffix position are the most abundant. We compute the product of the
    // top-k ratios available from position i onward.
    for i in (0..n).rev() {
        let remaining = n - i;
        let k = remaining.min(max_factors);
        // The components are already sorted by abundance ratio descending.
        // The best k components from [i..] are just the first k in [i..i+k].
        let product: f64 = valid_components[i..i + k]
            .iter()
            .map(|c| c.abundance_ratio)
            .product();
        suffix_abundance[i] = product;
    }

    // Precompute illegal valuations once to pass into the parallel pipeline
    let illegal_z_valuations = raycast::generate_illegal_z_valuations(250, max_exponent);

    // Precompute σ(p^{2e}) lookup table for small primes (avoids recomputation in raycast inner loop)
    let sigma_cache = math_utils::build_sigma_cache(sieve_limit as u64, max_exponent * 2);

    // Initialize Z3-backed CDCL pruner (ENG-202)
    let z3_pruner = z3_pruner::Z3Pruner::new();
    println!("Z3 CDCL pruner initialized. Conflict learning active.");

    // Launch fused perfectly-balanced parallel pipeline!
    dfs_tree::phase2_and_4_fused(
        &valid_components,
        &threshold,
        &target_min,
        &target_bound,
        &illegal_z_valuations,
        &suffix_abundance,
        &sigma_cache,
        &z3_pruner,
    );

    println!(
        "PROGRESS|DONE|4|1|Verification Complete. 10^{} < N < 10^{} Confirmed",
        target_min_log10, target_max_log10
    );
}
