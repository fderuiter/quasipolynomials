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

#[derive(Serialize, Debug, Clone)]
struct EnvironmentProvenance {
    cargo_lock_hash: String,
    lake_manifest_hash: String,
    lean_version: String,
    rustc_version: String,
    verus_version: String,
}

#[derive(Serialize, Debug, Clone)]
struct SearchTelemetry {
    abundance_pruned: usize,
    max_exponent: u32,
    phase2_execution_time_ms: u128,
    prefix_stop: u64,
    search_space_density: f64,
    sieve_limit: usize,
    target_max_log10: u32,
    target_min_log10: u32,
    total_branches_searched: usize,
}

#[derive(Serialize, Debug)]
struct DeterministicTelemetry {
    abundance_pruned: usize,
    max_exponent: u32,
    phase2_execution_time_ms: u128,
    prefix_stop: u64,
    search_space_density: String,  // Fixed-precision decimal string for deterministic signing
    sieve_limit: usize,
    target_max_log10: u32,
    target_min_log10: u32,
    total_branches_searched: usize,
}

#[derive(Serialize, Debug)]
struct CertificatePayload {
    environment: EnvironmentProvenance,
    manifest_hash: String,
    telemetry: DeterministicTelemetry,
    verified_logic_hash: String,
}

#[derive(Serialize, Debug)]
struct Certificate {
    environment: EnvironmentProvenance,
    manifest_hash: String,
    public_key: String,
    signature: String,
    telemetry: SearchTelemetry,
    verified_logic_hash: String,
}

fn get_command_version(cmd: &str, args: &[&str]) -> String {
    if let Ok(output) = std::process::Command::new(cmd).args(args).output() {
        if output.status.success() {
            return String::from_utf8_lossy(&output.stdout).trim().to_string();
        }
    }
    "unknown".to_string()
}

fn hash_file(path: &str) -> String {
    if let Ok(content) = fs::read_to_string(path) {
        let mut hasher = Sha256::new();
        hasher.update(content.as_bytes());
        hex::encode(hasher.finalize())
    } else {
        "missing".to_string()
    }
}

fn main() {
    // ── Formal Certification Initialization ──
    let manifest_path = env::var("UALBF_PROOF_MANIFEST").unwrap_or_else(|_| "proof_manifest.json".to_string());
    let manifest_content = fs::read_to_string(&manifest_path).expect("Failed to read proof manifest. Engine must ingest a machine-readable manifest at startup.");
    
    let manifest: Manifest = serde_json::from_str(&manifest_content).expect("Failed to parse proof manifest");
    
    // Hash the manifest for the certificate
    let mut hasher = Sha256::new();
    hasher.update(&manifest_content);
    let manifest_hash = hex::encode(hasher.finalize());
    println!("=== Formal Certification Framework ===");
    println!("Ingested proof manifest: {}", manifest_hash);

    // Hash the verified search logic (Verus proofs + core logic)
    let mut logic_hasher = Sha256::new();
    if let Ok(dfs_content) = fs::read_to_string("src/dfs_tree.rs") {
        logic_hasher.update(dfs_content.as_bytes());
    }
    if let Ok(sieve_content) = fs::read_to_string("src/sieve.rs") {
        logic_hasher.update(sieve_content.as_bytes());
    }
    if let Ok(verus_content) = fs::read_to_string("src/verus_proofs.rs") {
        logic_hasher.update(verus_content.as_bytes());
    }
    if let Ok(ffi_content) = fs::read_to_string("src/lean_ffi.rs") {
        logic_hasher.update(ffi_content.as_bytes());
    }
    if let Ok(dummy_ffi_content) = fs::read_to_string("src/dummy_ffi.c") {
        logic_hasher.update(dummy_ffi_content.as_bytes());
    }
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
    
    let environment = EnvironmentProvenance {
        cargo_lock_hash: hash_file("Cargo.lock"),
        lake_manifest_hash: hash_file("../lean4-proofs/lake-manifest.json"),
        lean_version: get_command_version("lean", &["--version"]),
        rustc_version: get_command_version("rustc", &["-V"]),
        verus_version: get_command_version("verus", &["--version"]),
    };

    let telemetry = SearchTelemetry {
        abundance_pruned: telemetry_data.abundance_pruned,
        max_exponent,
        phase2_execution_time_ms: phase2_elapsed.as_millis(),
        prefix_stop,
        search_space_density: telemetry_data.search_space_density,
        sieve_limit,
        target_max_log10,
        target_min_log10,
        total_branches_searched: telemetry_data.total_branches,
    };

    let deterministic_telemetry = DeterministicTelemetry {
        abundance_pruned: telemetry.abundance_pruned,
        max_exponent: telemetry.max_exponent,
        phase2_execution_time_ms: telemetry.phase2_execution_time_ms,
        prefix_stop: telemetry.prefix_stop,
        search_space_density: format!("{:.15}", telemetry.search_space_density),
        sieve_limit: telemetry.sieve_limit,
        target_max_log10: telemetry.target_max_log10,
        target_min_log10: telemetry.target_min_log10,
        total_branches_searched: telemetry.total_branches_searched,
    };

    let payload = CertificatePayload {
        environment: environment.clone(),
        manifest_hash: manifest_hash.clone(),
        telemetry: deterministic_telemetry,
        verified_logic_hash: verified_logic_hash.clone(),
    };

    let payload_to_sign = serde_json::to_string(&payload).unwrap();
    let signature = signing_key.sign(payload_to_sign.as_bytes());

    let cert = Certificate {
        environment,
        manifest_hash,
        public_key: hex::encode(signing_key.verifying_key().to_bytes()),
        signature: hex::encode(signature.to_bytes()),
        telemetry,
        verified_logic_hash,
    };

    let cert_json = serde_json::to_string_pretty(&cert).expect("Failed to serialize certificate");
    fs::write("formal_certificate.json", &cert_json).expect("Failed to write certificate");
    println!("=== Certificate Generated: formal_certificate.json ===");
}
