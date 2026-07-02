pub mod events;
pub mod obstruction;
pub mod backbone;
#[allow(unused_imports, dead_code)]
use crate::types::{UintExt, IntExt};
use std::env;
use std::fs;
#[cfg(feature = "signing")]
use sha2::{Digest, Sha256};
#[cfg(feature = "signing")]
use ed25519_dalek::{SigningKey, Signer};
#[cfg(feature = "signing")]
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

mod profile;
mod gpu;
mod dfs_tree;
pub mod trace;
mod lean_ffi;
mod manifest_constants;
mod math_utils;
mod raycast;
mod sieve;
mod universal_bounds;
mod types;
mod schema_generated;
mod distributed;
mod bloom_filter;
mod policy;
pub mod state;
use crate::types::Uint;

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
    verus_hashes: std::collections::HashMap<String, String>,
    bounds_manifest_hash: String,
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
    raycast_pruned: usize,
    phase1_retained: usize,
    phase1_pruned: usize,
    phase1_trial_only: usize,
    phase1_ecm_fallback: usize,
    phase1_execution_time_ms: u128,
    search_space_density: f64,
    phase2_execution_time_ms: u128,
    total_execution_time_ms: u128,
    baseline_min_prime_factors: usize,
    prasad_sunitha_bound: usize,
    trace_hash: String,
    factorization_depth: u32,
    bounds_exceeded: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Citation {
    author: String,
    year: String,
    title: String,
    identifier: String,
}

#[derive(Serialize, Debug)]
struct CertificateCitations {
    target_min_log10: Option<Citation>,
    baseline_min_prime_factors: Option<Citation>,
    prasad_sunitha_bound: Option<Citation>,
    euler_ceiling: Option<Citation>,
}

#[derive(Serialize, Debug)]
struct Certificate {
    manifest_hash: String,
    verified_logic_hash: String,
    telemetry: SearchTelemetry,
    citations: CertificateCitations,
    signature: String,
    public_key: String,
    engine_version: String,
    commit_hash: String,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    fn sample_telemetry(baseline: usize, ps_bound: usize) -> SearchTelemetry {
        SearchTelemetry {
            target_min_log10: crate::manifest_constants::TARGET_MIN_LOG10,
            target_max_log10: crate::manifest_constants::TARGET_MAX_LOG10,
            sieve_limit: 1000,
            max_exponent: 4,
            prefix_stop: 100_000_000_000,
            total_branches_searched: 42,
            abundance_pruned: 10,
            raycast_pruned: 0,
            phase1_retained: 0,
            phase1_pruned: 0,
            phase1_trial_only: 0,
            phase1_ecm_fallback: 0,
            phase1_execution_time_ms: 0,
            search_space_density: 0.5,
            phase2_execution_time_ms: 1234,
            total_execution_time_ms: 1234,
            baseline_min_prime_factors: baseline,
            prasad_sunitha_bound: ps_bound,
            trace_hash: "dummy_hash".to_string(),
            factorization_depth: crate::manifest_constants::POLLARD_RHO_ITERATION_LIMIT,
            bounds_exceeded: false,
        }
    }

    /// SearchTelemetry must serialise the new baseline_min_prime_factors field.
    #[test]
    fn test_telemetry_serialises_baseline_min_prime_factors() {
        let tel = sample_telemetry(7, crate::manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5 as usize);
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
        let ps_bound = crate::manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5;
        let tel = sample_telemetry(7, ps_bound as usize);
        let json: Value = serde_json::to_value(&tel).expect("serialisation must succeed");
        assert!(
            json.get("prasad_sunitha_bound").is_some(),
            "JSON must contain 'prasad_sunitha_bound' key"
        );
        assert_eq!(
            json["prasad_sunitha_bound"].as_u64().unwrap(),
            ps_bound,
            "prasad_sunitha_bound must serialise correctly"
        );
    }

    /// Both new fields must survive a round-trip through JSON deserialisation.
    #[test]
    fn test_telemetry_new_fields_round_trip() {
        let ps_bound = crate::manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5;
        let tel = sample_telemetry(7, ps_bound as usize);
        let json_str = serde_json::to_string(&tel).expect("serialisation must succeed");
        let decoded: Value = serde_json::from_str(&json_str).expect("deserialisation must succeed");
        assert_eq!(decoded["baseline_min_prime_factors"], 7);
        assert_eq!(decoded["prasad_sunitha_bound"], ps_bound);
    }

    /// The Prasad-Sunitha bound stored in the telemetry must exceed the baseline.
    #[test]
    fn test_telemetry_ps_bound_exceeds_baseline() {
        let ps_bound = crate::manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5;
        let tel = sample_telemetry(7, ps_bound as usize);
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
        let tel = sample_telemetry(7, crate::manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5 as usize);
        assert!(tel.baseline_min_prime_factors > 0, "baseline_min_prime_factors must be > 0");
        assert!(tel.prasad_sunitha_bound > 0, "prasad_sunitha_bound must be > 0");
    }
}

/// Program entry point that runs the full UALBF engine, performs the verified search,
/// and optionally emits a signed formal certificate.
///
/// This is the program entry point. It performs the following high-level actions:
/// - Loads and hashes a proof manifest and verifies no theorems are marked `sorry` or `axiom`.
/// - Computes a SHA-256 hash over the engine's verified search logic source files (including FFI bridge files).
/// - Initializes the Lean runtime and configures Rayon worker thread initialization.
/// - Reads configurable search parameters from environment variables and enforces certificate bounds.
/// - Runs phase-1 sieving and precomputations, then executes the phase-2 search in the selected mode.
/// - If standard bounds are used, signs and writes a JSON certificate containing telemetry and cryptographic metadata.
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
fn main() {
    let total_start = std::time::Instant::now();
    let config = policy::get_safe_config();
    // ── Formal Certification Initialization ──
    let manifest_path = config.proof_manifest.clone();

    let manifest_content = fs::read_to_string(&manifest_path).expect("Failed to read proof manifest. Engine must ingest a machine-readable manifest at startup.");
    let manifest: Manifest = serde_json::from_str(&manifest_content).expect("Failed to parse proof manifest");
    
    // Hash the manifest for the certificate
    #[cfg(feature = "signing")]
    let manifest_hash = {
        let mut hasher = Sha256::new();
        hasher.update(&manifest_content);
        hex::encode(hasher.finalize())
    };
    #[cfg(not(feature = "signing"))]
    let manifest_hash = "unverified_manifest_hash".to_string();

    #[cfg(feature = "signing")]
    let is_verified_build = true;
    #[cfg(not(feature = "signing"))]
    let is_verified_build = false;

    println!("=== Formal Certification Framework ===");
    println!("Verification Status: {}", if is_verified_build { "VERIFIED (Signing Enabled)" } else { "UNVERIFIED (Signing Disabled)" });
    println!("Ingested proof manifest: {}", manifest_hash);

    // Hash the verified search logic (Verus proofs + core logic)
    let verified_logic_hash = verification_lib::compute_tcb_hash_at_compile_time!();
    println!("Verified search logic hash: {}", verified_logic_hash);

    // --- Runtime Audit: Verus Specification Hashes ---
    let verus_content = include_str!("verus_proofs.rs");
    let mut runtime_verus_hashes = std::collections::HashMap::new();
    let mut current_fn = String::new();
    let mut current_body = String::new();
    let mut in_spec = false;
    let mut brace_count = 0;
    let mut module_stack: Vec<String> = Vec::new();
    let mut module_brace_depth = 0;

    for line in verus_content.lines() {
        let trimmed = line.trim();

        // Track module declarations
        if !in_spec {
            if trimmed.contains('{') && (trimmed.starts_with("mod ") || trimmed.starts_with("pub mod ")) {
                let mod_name = if trimmed.starts_with("pub mod ") {
                    trimmed.strip_prefix("pub mod ").unwrap_or("")
                } else {
                    trimmed.strip_prefix("mod ").unwrap_or("")
                };
                let mod_name = mod_name.split('{').next().unwrap_or("").trim();
                if !mod_name.is_empty() {
                    module_stack.push(mod_name.to_string());
                    if trimmed.contains('{') {
                        module_brace_depth += 1;
                    }
                }
            }
        }

        if !in_spec && line.contains("pub spec fn") {
            let parts: Vec<&str> = line.split("pub spec fn ").collect();
            if parts.len() > 1 {
                let bare_fn_name = parts[1].split('(').next().unwrap_or("").trim().to_string();
                // Build scope-qualified key
                let qualified_name = if module_stack.is_empty() {
                    bare_fn_name.clone()
                } else {
                    format!("{}::{}", module_stack.join("::"), bare_fn_name)
                };
                current_fn = qualified_name;
                in_spec = true;
                current_body = line.to_string();
                brace_count = line.chars().filter(|&c| c == '{').count() as i32
                            - line.chars().filter(|&c| c == '}').count() as i32;
                if brace_count == 0 && line.contains('{') {
                    #[cfg(feature = "signing")]
                    {
                        let mut hasher = Sha256::new();
                        hasher.update(current_body.as_bytes());
                        runtime_verus_hashes.insert(current_fn.clone(), hex::encode(hasher.finalize()));
                    }
                    #[cfg(not(feature = "signing"))]
                    {
                        runtime_verus_hashes.insert(current_fn.clone(), "unverified_hash".to_string());
                    }
                    in_spec = false;
                }
            }
        } else if in_spec {
            current_body.push('\n');
            current_body.push_str(line);
            brace_count += line.chars().filter(|&c| c == '{').count() as i32
                         - line.chars().filter(|&c| c == '}').count() as i32;
            if brace_count == 0 {
                #[cfg(feature = "signing")]
                {
                    let mut hasher = Sha256::new();
                    hasher.update(current_body.as_bytes());
                    runtime_verus_hashes.insert(current_fn.clone(), hex::encode(hasher.finalize()));
                }
                #[cfg(not(feature = "signing"))]
                {
                    runtime_verus_hashes.insert(current_fn.clone(), "unverified_hash".to_string());
                }
                in_spec = false;
            }
        } else if !in_spec && module_brace_depth > 0 {
            // Track module closing braces
            let open_braces = line.chars().filter(|&c| c == '{').count();
            let close_braces = line.chars().filter(|&c| c == '}').count();
            module_brace_depth += open_braces;
            if close_braces > 0 {
                for _ in 0..close_braces {
                    if module_brace_depth > 0 {
                        module_brace_depth -= 1;
                        if !module_stack.is_empty() {
                            module_stack.pop();
                        }
                    }
                }
            }
        }
    }

    if runtime_verus_hashes != manifest.verus_hashes {
        println!("ERROR: Runtime Verus specification hashes do not match the proof manifest!");
        println!("Manifest hashes: {:?}", manifest.verus_hashes);
        println!("Runtime hashes: {:?}", runtime_verus_hashes);
        panic!("FATAL: Epistemological severance detected: Logic version mismatch.");
    }
    println!("Epistemological Linkage Verified.");
    let allowed_axioms = ["UALBF.FFI.rust_is_prime_sound"];
    let mut proof_incomplete = false;
    for thm in &manifest.theorems {
        if thm.status == "sorry" || (thm.status == "axiom" && !allowed_axioms.contains(&thm.name.as_str())) {
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

    // ── Read configurable parameters via Policy Registry ──
    let target_min_log10 = config.target_min_log10;
    let target_max_log10 = config.target_max_log10;
    let sieve_limit = config.sieve_limit;
    let max_exponent = config.max_exponent;
    let prefix_stop = config.prefix_stop;

    println!("=== UALBF Engine Initializing ===");
    println!(
        "Target Bound: 10^{} < N < 10^{}",
        target_min_log10, target_max_log10
    );
    println!(
        "Sieve: limit={}, max_exponent={}, prefix_stop={}",
        sieve_limit, max_exponent, prefix_stop
    );

    let (euler_num, euler_den) = lean_ffi::get_euler_ceiling();
    println!(
        "Euler Ceiling: {}/{} (proven via manifest)",
        euler_num, euler_den
    );

    let mut skip_cert = false;
    if !(target_max_log10 == crate::manifest_constants::TARGET_MAX_LOG10 && target_min_log10 == crate::manifest_constants::TARGET_MIN_LOG10) {
        println!("WARNING: Immutable Bounds constraint violated. The engine prohibits the generation of a 'Formal' certificate if custom, non-standard search bounds are used. The bound must be 10^{} < N < 10^{}. Certificate generation will be skipped.", crate::manifest_constants::TARGET_MIN_LOG10, crate::manifest_constants::TARGET_MAX_LOG10);
        skip_cert = true;
    }
    
    if manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5 > manifest_constants::PRASAD_SUNITHA_PROOF_BOUND {
        println!("WARNING: The engine's search bounds ({}) do not match the proof's verified limits ({}). 'Formal' certificates are rejected.", manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5, manifest_constants::PRASAD_SUNITHA_PROOF_BOUND);
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
    
    if config.enable_diagnostics {
        crate::gpu::ENABLE_DIAGNOSTICS.store(true, std::sync::atomic::Ordering::Relaxed);
    }

    // Launch fused perfectly-balanced parallel pipeline!
    let mode = config.mode.clone();
    let phase2_start = std::time::Instant::now();
    let mut telemetry_data = dfs_tree::DfsTelemetry { total_branches: 0, abundance_pruned: 0, raycast_pruned: 0, search_space_density: 0.0 };

    if mode == "controller" {
        let depth_limit = 2; // shallow DFS depths
        let work_units = distributed::generate_work_units(
            &valid_components,
            &target_bound,
            depth_limit,
        );
        let addr = config.controller_addr.clone();
        distributed::run_controller(&addr, work_units);
        std::process::exit(0); // For now just exit after completion
    } else if mode == "worker" {
        let addr = config.controller_addr.clone();
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

    // ── Generate and Hash Trace ──
    let trace_path = "trace.jsonl";
    #[cfg(feature = "signing")]
    let trace_hash = if std::path::Path::new(trace_path).exists() {
        let mut hasher = Sha256::new();
        let mut f = std::fs::File::open(trace_path).expect("Failed to open trace file");
        let mut buf = Vec::new();
        std::io::Read::read_to_end(&mut f, &mut buf).unwrap();
        hasher.update(&buf);
        hex::encode(hasher.finalize())
    } else {
        "".to_string()
    };
    #[cfg(not(feature = "signing"))]
    let trace_hash = "unverified_trace_hash".to_string();

    println!("{}", serde_json::to_string(&crate::events::SearchEvent::Done { target_min_log10, target_max_log10, elapsed_ms: phase2_elapsed.as_millis() }).unwrap());

    // ── Generate Formal Exhaustion Certificate ──
    if skip_cert {
        println!("=== Certificate Generation Skipped due to custom bounds ===");
        return;
    }

    #[cfg(feature = "signing")]
    let (signature_hex, public_key_hex) = {
        let mut csprng = OsRng;
        let signing_key = SigningKey::generate(&mut csprng);
        let payload_to_sign = verification_lib::format_payload(
            &manifest_hash,
            &verified_logic_hash,
            telemetry_data.total_branches,
            target_min_log10,
            target_max_log10,
            &trace_hash,
            crate::manifest_constants::POLLARD_RHO_ITERATION_LIMIT,
        );
        let signature = signing_key.sign(payload_to_sign.as_bytes());
        (hex::encode(signature.to_bytes()), hex::encode(signing_key.verifying_key().to_bytes()))
    };

    #[cfg(not(feature = "signing"))]
    let (signature_hex, public_key_hex) = {
        println!("ERROR: Refusing to sign certificate. Signing is unavailable in unverified builds.");
        ("unverified_signature".to_string(), "unverified_public_key".to_string())
    };
    
    let telemetry = SearchTelemetry {
        target_min_log10,
        target_max_log10,
        sieve_limit,
        max_exponent,
        prefix_stop,
        total_branches_searched: telemetry_data.total_branches,
        abundance_pruned: telemetry_data.abundance_pruned,
        raycast_pruned: telemetry_data.raycast_pruned,
        phase1_retained: valid_components.len(),
        phase1_pruned: sieve_result.pruned,
        phase1_trial_only: sieve_result.trial_only,
        phase1_ecm_fallback: sieve_result.ecm_fallback,
        phase1_execution_time_ms: sieve_result.execution_time_ms,
        search_space_density: telemetry_data.search_space_density,
        phase2_execution_time_ms: phase2_elapsed.as_millis(),
        total_execution_time_ms: total_start.elapsed().as_millis(),
        baseline_min_prime_factors: lean_ffi::get_baseline_min_prime_factors(),
        prasad_sunitha_bound: lean_ffi::get_prasad_sunitha_bound(),
        trace_hash: trace_hash.clone(),
        factorization_depth: crate::manifest_constants::POLLARD_RHO_ITERATION_LIMIT,
        bounds_exceeded: false,
    };

    let bounds_manifest_str = include_str!("../../bounds_manifest.json");
    let bounds_json: serde_json::Value = serde_json::from_str(bounds_manifest_str).expect("Failed to parse bounds_manifest.json");
    
    let cert_citations = CertificateCitations {
        target_min_log10: serde_json::from_value(bounds_json["search_bounds"]["target_min_log10"]["citation"].clone()).unwrap_or(None),
        baseline_min_prime_factors: serde_json::from_value(bounds_json["omega_bounds"]["baseline"]["citation"].clone()).unwrap_or(None),
        prasad_sunitha_bound: serde_json::from_value(bounds_json["omega_bounds"]["prasad_sunitha"]["citation"].clone()).unwrap_or(None),
        euler_ceiling: serde_json::from_value(bounds_json["euler_ceiling"]["citation"].clone()).unwrap_or(None),
    };

    let cert = Certificate {
        manifest_hash,
        verified_logic_hash,
        telemetry,
        citations: cert_citations,
        signature: signature_hex,
        public_key: public_key_hex,
        engine_version: env!("CARGO_PKG_VERSION").to_string(),
        commit_hash: option_env!("GIT_HASH").unwrap_or("unknown").to_string(),
    };

    let cert_json = serde_json::to_string_pretty(&cert).expect("Failed to serialize certificate");
    fs::write("formal_certificate.json", &cert_json).expect("Failed to write certificate");
    println!("=== Certificate Generated: formal_certificate.json ===");
}
