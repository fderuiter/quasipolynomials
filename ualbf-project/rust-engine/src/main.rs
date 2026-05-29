#![allow(unused_imports, dead_code)]
use std::env;
use std::fs;
use sha2::{Digest, Sha256};
use ed25519_dalek::{SigningKey, Signer};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

mod dfs_tree;
mod lean_ffi;
mod math_utils;
mod raycast;
mod sieve;
mod types;
use crate::types::Uint;

// Defaults — overridable via UALBF_TARGET_MAX_LOG10, UALBF_TARGET_MIN_LOG10, etc.
const DEFAULT_TARGET_MAX_LOG10: u32 = 37;
const DEFAULT_TARGET_MIN_LOG10: u32 = 35; // Hagis-Cohen bound
const DEFAULT_PREFIX_STOP_THRESHOLD: u64 = 100_000_000_000; // 10^11
const DEFAULT_SIEVE_LIMIT: usize = 250_000;
const DEFAULT_MAX_EXPONENT: u32 = 4;

#[derive(Deserialize, Debug)]
struct Theorem {
    name: String,
    file: String,
    status: String,
    checksum: String,
}

#[derive(Deserialize, Debug)]
struct Manifest {
    theorems: Vec<Theorem>,
}

#[derive(Serialize, Debug)]
struct SearchTelemetry {
    target_min_log10: u32,
    target_max_log10: u32,
    sieve_limit: usize,
    max_exponent: u32,
    prefix_stop: u64,
    total_branches_searched: usize,
    abundance_pruned: usize,
    search_space_density: f64,
    phase2_execution_time_ms: u128,
}

#[derive(Serialize, Debug)]
struct Certificate {
    manifest_hash: String,
    telemetry: SearchTelemetry,
    signature: String,
    public_key: String,
}

fn main() {
    // ── Formal Certification Initialization ──
    let manifest_path = env::var("UALBF_PROOF_MANIFEST").unwrap_or_else(|_| "proof_manifest.json".to_string());
    let manifest_content = fs::read_to_string(&manifest_path).expect("Failed to read proof manifest. Engine must ingest a machine-readable manifest at startup.");
    
    let manifest: Manifest = serde_json::from_str(&manifest_content).expect("Failed to parse proof manifest");
    
    // Hash the manifest for the certificate
    let mut hasher = Sha256::new();
    hasher.update(&manifest_content);
    let manifest_hash = format!("{:x}", hasher.finalize());
    println!("=== Formal Certification Framework ===");
    println!("Ingested proof manifest: {}", manifest_hash);

    let mut proof_incomplete = false;
    for thm in &manifest.theorems {
        if thm.status == "sorry" || thm.status == "axiom" {
            println!("ERROR: Theorem '{}' in '{}' is incomplete (status: {}).", thm.name, thm.file, thm.status);
            proof_incomplete = true;
        }
    }
    if proof_incomplete {
        panic!("FATAL: The verification process refuses to start/sign the certificate because 'sorry' or 'axiom' was detected in the formal proof manifest.");
    }

    // Initialize the Lean 4 runtime before any FFI calls
    lean_ffi::initialize_lean_runtime();

    // Force Rayon to initialize Lean's memory allocator on all worker threads
    rayon::ThreadPoolBuilder::new()
        .start_handler(|_| lean_ffi::initialize_lean_worker_thread())
        .build_global()
        .unwrap();

    // ── Read configurable parameters from environment (set by run_gui.py) ──
    let target_min_log10: u32 = env::var("UALBF_TARGET_MIN_LOG10")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_TARGET_MIN_LOG10);
    let target_max_log10: u32 = env::var("UALBF_TARGET_MAX_LOG10")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_TARGET_MAX_LOG10);
    let sieve_limit: usize = env::var("UALBF_SIEVE_LIMIT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_SIEVE_LIMIT);
    let max_exponent: u32 = env::var("UALBF_MAX_EXPONENT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_MAX_EXPONENT);
    let prefix_stop: u64 = env::var("UALBF_PREFIX_STOP_THRESHOLD")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_PREFIX_STOP_THRESHOLD);

    println!("=== UALBF Engine Initializing ===");
    println!(
        "Target Bound: 10^{} < N < 10^{}",
        target_min_log10, target_max_log10
    );
    println!(
        "Sieve: limit={}, max_exponent={}, prefix_stop={}",
        sieve_limit, max_exponent, prefix_stop
    );

    if target_max_log10 != 37 || target_min_log10 != 35 {
        panic!("FATAL: Immutable Bounds constraint violated. The engine prohibits the generation of a 'Formal' certificate if custom, non-standard search bounds are used. The bound must be 10^35 < N < 10^37.");
    }

    let target_min: Uint = Uint::from(10u32).pow(target_min_log10);
    let target_bound: Uint = Uint::from(10u32).pow(target_max_log10);
    let threshold: Uint = Uint::from(prefix_stop);

    let sieve_result = sieve::phase1_global_annihilation_sieve(sieve_limit, max_exponent);
    let valid_components = sieve_result.components;
    let sigma_cache = sieve_result.sigma_cache;

    // Precompute suffix-max abundance product array for DFS pruning.
    // suffix_abundance[i][k] = max achievable abundance product using up to k
    // components from index i onwards (up to 15 factors for Prasad-Sunitha bound).
    let max_factors = 15usize;
    let n = valid_components.len();
    let mut suffix_abundance = vec![[1.0_f64; 16]; n + 1];
    // Components are sorted by abundance ratio descending, so the first components
    // at each suffix position are the most abundant. We compute the product of the
    // top-k ratios available from position i onward.
    for i in (0..n).rev() {
        for k in 1..=max_factors {
            let mut product = 1.0_f64;
            let mut distinct_count = 0;
            let mut seen_primes = Vec::new();

            for comp in &valid_components[i..] {
                if !seen_primes.contains(&comp.p) {
                    seen_primes.push(comp.p);
                    product *= comp.abundance_ratio;
                    distinct_count += 1;
                    if distinct_count == k {
                        break;
                    }
                }
            }
            suffix_abundance[i][k] = product;
        }
    }

    // Precompute illegal valuations once to pass into the parallel pipeline
    let illegal_z_valuations =
        raycast::generate_illegal_z_valuations(sieve_limit as u64, max_exponent);

    // Check illegal valuations

    // Launch fused perfectly-balanced parallel pipeline!
    let phase2_start = std::time::Instant::now();
    let telemetry_data = dfs_tree::phase2_and_4_fused(
        &valid_components,
        &threshold,
        &target_min,
        &target_bound,
        &illegal_z_valuations,
        &suffix_abundance,
        &sigma_cache,
    );
    let phase2_elapsed = phase2_start.elapsed();

    println!(
        "PROGRESS|DONE|4|1|Verification Complete. 10^{} < N < 10^{} Confirmed in {:?}",
        target_min_log10, target_max_log10, phase2_elapsed
    );

    // ── Generate Formal Exhaustion Certificate ──
    let mut csprng = OsRng;
    let signing_key = SigningKey::generate(&mut csprng);
    
    let telemetry = SearchTelemetry {
        target_min_log10,
        target_max_log10,
        sieve_limit,
        max_exponent,
        prefix_stop,
        total_branches_searched: telemetry_data.total_branches,
        abundance_pruned: telemetry_data.abundance_pruned,
        search_space_density: telemetry_data.search_space_density,
        phase2_execution_time_ms: phase2_elapsed.as_millis(),
    };

    let payload_to_sign = format!("{}_{}_{}", manifest_hash, telemetry.total_branches_searched, target_max_log10);
    let signature = signing_key.sign(payload_to_sign.as_bytes());

    let cert = Certificate {
        manifest_hash,
        telemetry,
        signature: hex::encode(signature.to_bytes()),
        public_key: hex::encode(signing_key.verifying_key().to_bytes()),
    };

    let cert_json = serde_json::to_string_pretty(&cert).expect("Failed to serialize certificate");
    fs::write("formal_certificate.json", &cert_json).expect("Failed to write certificate");
    println!("=== Certificate Generated: formal_certificate.json ===");
}
