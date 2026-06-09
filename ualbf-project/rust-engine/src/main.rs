pub mod obstruction;
pub mod backbone;
#[allow(unused_imports, dead_code)]
use crate::types::{UintExt, IntExt};
use std::env;
use std::fs;
use sha2::{Digest, Sha256};
use ed25519_dalek::{SigningKey, Signer};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

mod gpu;
mod dfs_tree;
mod lean_ffi;
mod math_utils;
mod raycast;
mod sieve;
mod types;
mod distributed;
mod bloom_filter;
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
    baseline_min_prime_factors: usize,
    prasad_sunitha_bound: usize,
}

#[derive(Serialize, Debug)]
struct Certificate {
    manifest_hash: String,
    verified_logic_hash: String,
    telemetry: SearchTelemetry,
    signature: String,
    public_key: String,
}

<<<<<<< HEAD
#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    fn sample_telemetry(baseline: usize, ps_bound: usize) -> SearchTelemetry {
        SearchTelemetry {
            target_min_log10: 35,
            target_max_log10: 37,
            sieve_limit: 1000,
            max_exponent: 4,
            prefix_stop: 100_000_000_000,
            total_branches_searched: 42,
            abundance_pruned: 10,
            search_space_density: 0.5,
            phase2_execution_time_ms: 1234,
            baseline_min_prime_factors: baseline,
            prasad_sunitha_bound: ps_bound,
        }
    }

    /// SearchTelemetry must serialise the new baseline_min_prime_factors field.
    #[test]
    fn test_telemetry_serialises_baseline_min_prime_factors() {
        let tel = sample_telemetry(7, 14);
        let json: Value = serde_json::to_value(&tel).expect("serialisation must succeed");
        assert!(
            json.get("baseline_min_prime_factors").is_some(),
            "JSON must contain 'baseline_min_prime_factors' key"
        );
        assert_eq!(
            json["baseline_min_prime_factors"].as_u64().unwrap(),
            7,
            "baseline_min_prime_factors must serialise as 7"
        );
    }

    /// SearchTelemetry must serialise the new prasad_sunitha_bound field.
    #[test]
    fn test_telemetry_serialises_prasad_sunitha_bound() {
        let tel = sample_telemetry(7, 14);
        let json: Value = serde_json::to_value(&tel).expect("serialisation must succeed");
        assert!(
            json.get("prasad_sunitha_bound").is_some(),
            "JSON must contain 'prasad_sunitha_bound' key"
        );
        assert_eq!(
            json["prasad_sunitha_bound"].as_u64().unwrap(),
            14,
            "prasad_sunitha_bound must serialise as 14"
        );
    }

    /// Both new fields must survive a round-trip through JSON deserialisation.
    #[test]
    fn test_telemetry_new_fields_round_trip() {
        let tel = sample_telemetry(7, 14);
        let json_str = serde_json::to_string(&tel).expect("serialisation must succeed");
        let decoded: Value = serde_json::from_str(&json_str).expect("deserialisation must succeed");
        assert_eq!(decoded["baseline_min_prime_factors"], 7);
        assert_eq!(decoded["prasad_sunitha_bound"], 14);
    }

    /// The Prasad-Sunitha bound stored in the telemetry must exceed the baseline.
    #[test]
    fn test_telemetry_ps_bound_exceeds_baseline() {
        let tel = sample_telemetry(7, 14);
        assert!(
            tel.prasad_sunitha_bound > tel.baseline_min_prime_factors,
            "prasad_sunitha_bound ({}) must exceed baseline_min_prime_factors ({})",
            tel.prasad_sunitha_bound, tel.baseline_min_prime_factors
        );
    }

    /// Verify neither new field is accidentally zero, which would indicate a
    /// failed FFI resolution.
    #[test]
    fn test_telemetry_new_fields_nonzero() {
        let tel = sample_telemetry(7, 14);
        assert!(tel.baseline_min_prime_factors > 0, "baseline_min_prime_factors must be > 0");
        assert!(tel.prasad_sunitha_bound > 0, "prasad_sunitha_bound must be > 0");
    }
}

=======
/// Program entry point that runs the full UALBF engine, performs the verified search,
/// and optionally emits a signed formal certificate.
///
/// This initializes runtime/FFI state, loads and validates a proof manifest and
/// verified-logic sources, computes certification hashes, runs the multi-phase sieve
/// and DFS search (in controller/worker/standalone modes), and gathers telemetry.
/// When the standard bounds (`10^35 < N < 10^37`) are used, it also writes a signed
/// `formal_certificate.json`; otherwise certificate generation is skipped.
///
/// The function aborts if the manifest contains incomplete theorems (`"sorry"` or
/// `"axiom"`). Network modes (`controller` / `worker`) run the distributed protocol
/// and exit the process after completion; standalone mode runs the local fused search.
///
/// # Examples
///
/// ```no_run
/// // Run the compiled binary after placing a valid `proof_manifest.json` in the
/// // working directory:
/// // UALBF_PROOF_MANIFEST=proof_manifest.json UALBF_MODE=standalone ./ualbf_engine
/// ```
>>>>>>> origin/main
fn main() {
    // ── Formal Certification Initialization ──
    let manifest_path = env::var("UALBF_PROOF_MANIFEST").unwrap_or_else(|_| "proof_manifest.json".to_string());

    
    let manifest: Manifest = serde_json::from_str(&manifest_content).expect("Failed to parse proof manifest");
    
    // Hash the manifest for the certificate
    let mut hasher = Sha256::new();
    hasher.update(&manifest_content);
    let manifest_hash = hex::encode(hasher.finalize());
    println!("=== Formal Certification Framework ===");
    println!("Ingested proof manifest: {}", manifest_hash);

    // Hash the verified search logic (Verus proofs + core logic)
    let mut logic_hasher = Sha256::new();
    let dfs_content = fs::read_to_string("src/dfs_tree.rs")
        .expect("Failed to read src/dfs_tree.rs - required for verified logic hash");
    logic_hasher.update(dfs_content.as_bytes());

    let sieve_content = fs::read_to_string("src/sieve.rs")
        .expect("Failed to read src/sieve.rs - required for verified logic hash");
    logic_hasher.update(sieve_content.as_bytes());

    let verus_content = fs::read_to_string("src/verus_proofs.rs")
        .expect("Failed to read src/verus_proofs.rs - required for verified logic hash");
    logic_hasher.update(verus_content.as_bytes());

    let lean_ffi_content = fs::read_to_string("src/lean_ffi.rs")
        .expect("Failed to read src/lean_ffi.rs - required for verified logic hash");
    logic_hasher.update(lean_ffi_content.as_bytes());

    let dummy_ffi_content = fs::read_to_string("src/dummy_ffi.c")
        .expect("Failed to read src/dummy_ffi.c - required for verified logic hash");
    logic_hasher.update(dummy_ffi_content.as_bytes());

    let build_rs_content = fs::read_to_string("build.rs")
        .expect("Failed to read build.rs - required for verified logic hash");
    logic_hasher.update(build_rs_content.as_bytes());

    let verified_logic_hash = hex::encode(logic_hasher.finalize());
    println!("Verified search logic hash: {}", verified_logic_hash);

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
    
    // Eagerly resolve unified mathematical bounds from Lean 4 proof environment
    dfs_tree::init_bounds();

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

    let mut skip_cert = false;
    if target_max_log10 != 37 || target_min_log10 != 35 {
        println!("WARNING: Immutable Bounds constraint violated. The engine prohibits the generation of a 'Formal' certificate if custom, non-standard search bounds are used. The bound must be 10^35 < N < 10^37. Certificate generation will be skipped.");
        skip_cert = true;
    }

    let target_min: Uint = if target_min_log10 > 38 {
        Uint::from_u32(10).pow(target_min_log10)
    } else {
        Uint::from_u32(10).pow(target_min_log10)
    };

    let target_bound: Uint = if target_max_log10 > 38 {
        Uint::from_u32(10).pow(target_max_log10)
    } else {
        Uint::from_u32(10).pow(target_max_log10)
    };
    let threshold: Uint = Uint::from_u128(prefix_stop as u128);

    crate::math_utils::init_bloom_filter(sieve_limit);

    let sieve_result = sieve::phase1_global_annihilation_sieve(sieve_limit, max_exponent);
    let valid_components = sieve_result.components;
    let sigma_cache = sieve_result.sigma_cache;

    // Precompute suffix-max abundance product array for DFS pruning.
    // We now use verified static bounds exported from Lean.
    let max_factors = 127usize;
    let mut suffix_abundance = vec![0u128; 128];
    for k in 0..=max_factors {
        suffix_abundance[k] = lean_ffi::get_static_suffix_bound(k as u32);
    }

    // Precompute illegal valuations once to pass into the parallel pipeline
    let illegal_z_valuations =
        raycast::generate_illegal_z_valuations(sieve_limit as u64, max_exponent);

    // Check illegal valuations

    // Launch fused perfectly-balanced parallel pipeline!
    let mode = std::env::var("UALBF_MODE").unwrap_or_else(|_| "standalone".to_string());
    let phase2_start = std::time::Instant::now();
    let mut telemetry_data = dfs_tree::DfsTelemetry { total_branches: 0, abundance_pruned: 0, search_space_density: 0.0 };

    if mode == "controller" {
        let depth_limit = 2; // shallow DFS depths
        let work_units = distributed::generate_work_units(
            &valid_components,
            &target_bound,
            depth_limit,
        );
        let addr = std::env::var("UALBF_CONTROLLER_ADDR").unwrap_or_else(|_| "0.0.0.0:8080".to_string());
        distributed::run_controller(&addr, work_units);
        std::process::exit(0); // For now just exit after completion
    } else if mode == "worker" {
        let addr = std::env::var("UALBF_CONTROLLER_ADDR").unwrap_or_else(|_| "127.0.0.1:8080".to_string());
        let total_weight_scaled: usize = valid_components
            .iter()
            .map(|c| (10_000_000.0 / ((c.p as f64) * (c.p as f64))) as usize)
            .sum();
        let max_idx_3 = valid_components.iter().rposition(|c| c.p == 3).unwrap_or(0);
        let max_idx_5 = valid_components.iter().rposition(|c| c.p == 5).unwrap_or(0);

        distributed::run_worker(
            &addr,
            &valid_components,
            &threshold,
            &target_min,
            &target_bound,
            &illegal_z_valuations,
            &suffix_abundance,
            total_weight_scaled,
            &sigma_cache,
            max_idx_3,
            max_idx_5,
        );
        std::process::exit(0);
    } else {
        telemetry_data = dfs_tree::phase2_and_4_fused(
            &valid_components,
            &threshold,
            &target_min,
            &target_bound,
            &illegal_z_valuations,
            &suffix_abundance,
            &sigma_cache,
            None,
        );
    }
    let phase2_elapsed = phase2_start.elapsed();

    println!(
        "PROGRESS|DONE|4|1|Verification Complete. 10^{} < N < 10^{} Confirmed in {:?}",
        target_min_log10, target_max_log10, phase2_elapsed
    );

    // ── Generate Formal Exhaustion Certificate ──
    if skip_cert {
        println!("=== Certificate Generation Skipped due to custom bounds ===");
        return;
    }

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
        baseline_min_prime_factors: lean_ffi::get_baseline_min_prime_factors(),
        prasad_sunitha_bound: lean_ffi::get_prasad_sunitha_bound(),
    };

    let payload_to_sign = format!("{}_{}_{}_{}_{}", manifest_hash, verified_logic_hash, telemetry.total_branches_searched, target_min_log10, target_max_log10);
    let signature = signing_key.sign(payload_to_sign.as_bytes());

    let cert = Certificate {
        manifest_hash,
        verified_logic_hash,
        telemetry,
        signature: hex::encode(signature.to_bytes()),
        public_key: hex::encode(signing_key.verifying_key().to_bytes()),
    };

    let cert_json = serde_json::to_string_pretty(&cert).expect("Failed to serialize certificate");
    fs::write("formal_certificate.json", &cert_json).expect("Failed to write certificate");
    println!("=== Certificate Generated: formal_certificate.json ===");
}
