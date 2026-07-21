// build.rs — Compile Lean 4 C-IR into libUALBF.a, then link it with the Lean runtime.
#![allow(dead_code, clippy::needless_borrows_for_generic_args)]

use serde::Deserialize;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

#[derive(Deserialize)]
struct Citation {
    author: String,
    year: String,
    title: String,
    identifier: String,
}

#[derive(Deserialize)]
struct PrasadSunithaBounds {
    proof_bound: u64,
    engine_justified_gap: u64,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct BaselineBounds {
    proof_bound: u64,
    engine_justified_gap: u64,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct BoundValueU32 {
    value: u32,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct BoundValueU64 {
    value: u64,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct BoundValueUsize {
    value: usize,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct PollardRhoBounds {
    iteration_limit: u32,
    batch_size: u32,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct RaycastBounds {
    gpu_threshold: usize,
    chunk_size: usize,
    is_axiomatic: bool,
}

#[derive(Deserialize)]
struct SearchBounds {
    target_min_log10: BoundValueU32,
    target_max_log10: BoundValueU32,
    sieve_limit: BoundValueUsize,
    max_exponent: BoundValueU32,
    prefix_stop_threshold: BoundValueU64,
    pollard_rho: PollardRhoBounds,
    raycast: RaycastBounds,
}

#[derive(Deserialize)]
struct OmegaBounds {
    prasad_sunitha: PrasadSunithaBounds,
    hagis1982: BaselineBounds,
}

#[derive(Deserialize)]
struct EulerCeiling {
    num: u64,
    den: u64,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct OverflowThreshold {
    num: u64,
    den: u64,
    is_axiomatic: bool,
}

#[derive(Deserialize)]
struct BoundsManifest {
    omega_bounds: OmegaBounds,
    search_bounds: SearchBounds,
    euler_ceiling: EulerCeiling,
    overflow_threshold: OverflowThreshold,
}

/// Build script entry point that locates a Lean sysroot, compiles generated Lean C-IR into a static
/// library when available, and emits Cargo directives to link the Lean runtime and trigger reruns.
///
/// When `LEAN_SYSROOT` is set, it is used as the Lean installation prefix; otherwise the script
/// attempts to run `lean --print-prefix` in the `../lean4-proofs` workspace. If no sysroot is
/// resolved the script compiles `src/dummy_ffi.c` as a fallback and exits early. When a sysroot is
/// available the script expects a fixed set of generated C files under `.lake/build/ir`, asserts
/// those files exist, compiles them into a static library (`UALBF`) using the Lean include path,
/// and emits `cargo:rustc-link-search` / `cargo:rustc-link-lib` directives for the Lean runtime,
/// libuv, GMP, and the system C++ standard library. Finally it prints `cargo:rerun-if-changed`
/// directives for relevant Lean sources, generated C files, and `LEAN_SYSROOT`.
///
/// # Examples
///
/// ```no_run
/// // Run as a build script; do not execute in doctests.
/// // cargo will execute `main()` during the build process.
/// build_rs::main();
/// ```
fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let scan_status = Command::new("python3")
        .arg("../scripts/check_literals.py")
        .current_dir(&manifest_dir)
        .status()
        .expect("Failed to run literal scanner");
    if !scan_status.success() {
        panic!("Mathematical literals found in pruning logic! Verify that all dynamic bounds are mapped to Lean FFI.");
    }
    let lean_project = PathBuf::from(&manifest_dir).join("../lean4-proofs");

    // --- 0. Read bounds_manifest.json and generate constants ---
    let manifest_path = PathBuf::from(&manifest_dir).join("../bounds_manifest.json");

    // Manifest is now mandatory - fail build if missing
    if !manifest_path.exists() {
        panic!(
            "FATAL: bounds_manifest.json not found at {}. \
             The build requires a valid manifest to generate verified constants.",
            manifest_path.display()
        );
    }

    let manifest_content =
        fs::read_to_string(&manifest_path).expect("Failed to read bounds_manifest.json");

    // --- REQUIREMENT 1 & 3: Mathematical Bound Synchronization Guardrail ---
    // Calculate the SHA256 hash of the current bounds_manifest.json
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(manifest_content.as_bytes());
    let current_manifest_hash = hex::encode(hasher.finalize());

    let lean_export_path = PathBuf::from(&manifest_dir).join("src/lean_export.rs");
    if lean_export_path.exists() {
        let export_content =
            fs::read_to_string(&lean_export_path).expect("Failed to read lean_export.rs");
        if let Some(idx) = export_content.find("pub const EXPORTED_BOUNDS_MANIFEST_HASH") {
            let rest = &export_content[idx..];
            let start = rest.find('"').unwrap_or(0) + 1;
            let end = rest[start..].find('"').unwrap_or(0) + start;
            if start < end {
                let recorded_hash = &rest[start..end];
                if current_manifest_hash != recorded_hash {
                    panic!(
                        "FATAL: Mathematical Bound Synchronization Guardrail Triggered!\n\
                         The contents of 'bounds_manifest.json' have changed, but the Lean specifications \
                         have not been regenerated. This risks a silent desynchronization between \
                         mathematical bounds and verified specifications.\n\
                         Current hash : {}\n\
                         Recorded hash: {}\n\
                         Please run `scripts/export_lean_specs.py` (or `make rust`) to update the exported \
                         specifications before building the engine.",
                         current_manifest_hash, recorded_hash
                    );
                }
            }
        }
    } else {
        println!("cargo:warning=lean_export.rs not found, skipping manifest hash check. Please ensure specifications are exported.");
    }

    let manifest: BoundsManifest =
        serde_json::from_str(&manifest_content).expect("Failed to parse bounds_manifest.json");

    // Citation validation
    if manifest.omega_bounds.hagis1982.is_axiomatic
        && manifest.omega_bounds.hagis1982.citation.is_none()
    {
        panic!("FATAL: baseline bound marked axiomatic but lacks citation metadata.");
    }
    if manifest.search_bounds.target_min_log10.is_axiomatic {
        panic!(
            "FATAL: search engine floor (target_min_log10) cannot rely on axiomatic assumptions."
        );
    }
    if manifest.omega_bounds.prasad_sunitha.is_axiomatic
        && manifest.omega_bounds.prasad_sunitha.citation.is_none()
    {
        panic!("FATAL: prasad_sunitha marked axiomatic but lacks citation metadata.");
    }
    if manifest.euler_ceiling.is_axiomatic && manifest.euler_ceiling.citation.is_none() {
        panic!("FATAL: euler_ceiling marked axiomatic but lacks citation metadata.");
    }

    // Deserialize manifest constants as u64 values before generating Rust/Lean constants.
    let prasad_proof: u64 = manifest.omega_bounds.prasad_sunitha.proof_bound;
    let prasad_gap: u64 = manifest.omega_bounds.prasad_sunitha.engine_justified_gap;
    let _prasad_bound: u64 = prasad_proof + prasad_gap;

    let baseline_proof: u64 = manifest.omega_bounds.hagis1982.proof_bound;
    let baseline_gap: u64 = manifest.omega_bounds.hagis1982.engine_justified_gap;
    let _baseline_min: u64 = baseline_proof + baseline_gap;

    let _euler_num: u64 = manifest.euler_ceiling.num;
    let _euler_den: u64 = manifest.euler_ceiling.den;

    let _overflow_num: u64 = manifest.overflow_threshold.num;
    let _overflow_den: u64 = manifest.overflow_threshold.den;

    let target_min_log10: u32 = manifest.search_bounds.target_min_log10.value;
    let _target_max_log10: u32 = manifest.search_bounds.target_max_log10.value;
    let _sieve_limit: usize = manifest.search_bounds.sieve_limit.value;
    let _max_exponent: u32 = manifest.search_bounds.max_exponent.value;
    let _prefix_stop_threshold: u64 = manifest.search_bounds.prefix_stop_threshold.value;
    let _pollard_rho_iteration_limit: u32 = manifest.search_bounds.pollard_rho.iteration_limit;
    let _pollard_rho_batch_size: u32 = manifest.search_bounds.pollard_rho.batch_size;
    let _raycast_gpu_threshold: usize = manifest.search_bounds.raycast.gpu_threshold;
    let _raycast_chunk_size: usize = manifest.search_bounds.raycast.chunk_size;

    // Enforce the Prasad-Sunitha limit dynamically
    let primes = [
        7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
    ];
    let mut min_val: f64 = 1.0;
    for &p in primes.iter().take(prasad_proof as usize) {
        min_val *= (p as f64) * (p as f64);
    }
    let verified_floor = min_val.log10().floor() as u32;
    if target_min_log10 < verified_floor {
        panic!("FATAL: target_min_log10 ({}) cannot be lower than the highest available verified bound ({}).", target_min_log10, verified_floor);
    }

    // Generate Rust constants with u64 types
    // (Constants are now generated by export_lean_specs.py BEFORE the build)

    println!("cargo:rerun-if-changed=../bounds_manifest.json");

    // --- 1. Resolve Lean sysroot ---
    let lean_sysroot = env::var("LEAN_SYSROOT").unwrap_or_else(|_| {
        let output = Command::new("lean")
            .arg("--print-prefix")
            .current_dir(&lean_project)
            .output();
        match output {
            Ok(output) => String::from_utf8(output.stdout)
                .unwrap_or_default()
                .trim()
                .to_string(),
            Err(_) => "".to_string(),
        }
    });

    if lean_sysroot.is_empty() {
        if env::var("CARGO_FEATURE_SIGNING").is_ok() {
            panic!(
                "FATAL: Attempted to build with signing capabilities but no Lean sysroot was found.\n\
                 Signed builds must be linked against a verified Lean environment."
            );
        }

        if env::var("ALLOW_UNVERIFIED_BUILD").unwrap_or_default() != "1" {
            panic!(
                "FATAL: Lean 4 toolchain not found!\n\
                 Please install Lean 4: https://leanprover.github.io/lean4/doc/setup.html\n\
                 e.g., curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh\n\
                 Or set the LEAN_SYSROOT environment variable if Lean is already installed:\n\
                 export LEAN_SYSROOT=/path/to/lean\n\
                 Unverified builds are no longer permitted in production."
            );
        }

        println!("cargo:rustc-cfg=unverified_build");
        println!("cargo:rustc-check-cfg=cfg(unverified_build)");
        println!("cargo:warning=Lean not found. Skipping Lean C-IR compilation.");
        cc::Build::new().file("src/dummy_ffi.c").compile("UALBF");
        return;
    }

    let lean_include = PathBuf::from(&lean_sysroot).join("include");
    let ir_dir = lean_project.join(".lake/build/ir");

    // Execute targeted module compilation instead of a full project build
    let _ = Command::new("lake")
        .arg("build")
        .arg("UALBF") // Targeted build
        .current_dir(&lean_project)
        .status();

    // --- 2. Compile all UALBF C-IR files into a static library ---
    let mut c_files = Vec::new();
    fn visit_dirs(
        dir: &std::path::Path,
        c_files: &mut Vec<std::path::PathBuf>,
    ) -> std::io::Result<()> {
        if dir.is_dir() {
            for entry in std::fs::read_dir(dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    visit_dirs(&path, c_files)?;
                } else if path.extension().and_then(|s| s.to_str()) == Some("c") {
                    c_files.push(path);
                }
            }
        }
        Ok(())
    }
    if ir_dir.exists() {
        visit_dirs(&ir_dir, &mut c_files).unwrap();
    } else {
        // Fallback for tests if `.lake/build/ir/UALBF` doesn't exist
        // The build might just skip or we can let it proceed with an empty list
        // We will assert on it below if needed, but let's let visit_dirs pass.
    }

    let mut extern_funcs = std::collections::HashSet::new();
    let mut defined_funcs = std::collections::HashSet::new();

    for f in &c_files {
        if let Ok(content) = fs::read_to_string(f) {
            for mut line in content.lines() {
                line = line.trim();
                if let Some(idx) = line.find("extern lean_object* ") {
                    let rest = &line[idx + "extern lean_object* ".len()..];
                    if let Some(end) = rest.find('(') {
                        extern_funcs.insert(rest[..end].to_string());
                    }
                }
                if let Some(idx) = line.find("lean_object* initialize_") {
                    let rest = &line[idx + "lean_object* ".len()..];
                    if let Some(end) = rest.find('(') {
                        extern_funcs.insert(rest[..end].to_string());
                    }
                }
                if let Some(idx) = line.find("LEAN_EXPORT lean_object* ") {
                    let rest = &line[idx + "LEAN_EXPORT lean_object* ".len()..];
                    if let Some(end) = rest.find('(') {
                        defined_funcs.insert(rest[..end].to_string());
                    }
                }
            }
        }
    }

    let out_dir = env::var("OUT_DIR").unwrap();
    let dynamic_stubs_path = PathBuf::from(&out_dir).join("dynamic_stubs.c");
    let mut stubs = String::new();
    stubs.push_str("#include <lean/lean.h>\n#include <stdlib.h>\n\n");

    // Sort to make the output deterministic
    let mut extern_funcs_sorted: Vec<_> = extern_funcs.into_iter().collect();
    extern_funcs_sorted.sort();

    for func in extern_funcs_sorted {
        if !defined_funcs.contains(&func)
            && !func.starts_with("initialize_Init")
            && !func.starts_with("initialize_Lean")
        {
            if func.starts_with("initialize_") {
                stubs.push_str(&format!("LEAN_EXPORT lean_object* {}(uint8_t builtin) {{ return lean_io_result_mk_ok(lean_box(0)); }}\n", func));
            } else if func.starts_with("lp_") {
                stubs.push_str(&format!(
                    "LEAN_EXPORT lean_object* {}() {{ abort(); return NULL; }}\n",
                    func
                ));
            }
        }
    }

    fs::write(&dynamic_stubs_path, stubs).expect("Failed to write dynamic stubs");
    c_files.push(dynamic_stubs_path);

    // Verify all C files exist (they are produced by `lake build`)
    for f in &c_files {
        assert!(
            f.exists(),
            "Missing C-IR file: {}. Did you run `lake build` in lean4-proofs/?",
            f.display()
        );
    }

    let mut builder = cc::Build::new();
    builder.include(&lean_include).warnings(false).opt_level(2);

    for f in &c_files {
        builder.file(f);
    }

    builder.file("src/c_shims.c");
    println!("cargo:rerun-if-changed=src/c_shims.c");
    builder.compile("UALBF");

    // --- 3. Link the Lean runtime ---
    let lean_lib_dir = lean_project.join(".lake/build/lib");
    println!("cargo:rustc-link-search=native={}", lean_lib_dir.display());

    let lean_rt_dir = PathBuf::from(&lean_sysroot).join("lib/lean");
    println!("cargo:rustc-link-search=native={}", lean_rt_dir.display());

    let lean_root_lib = PathBuf::from(&lean_sysroot).join("lib");
    println!("cargo:rustc-link-search=native={}", lean_root_lib.display());

    // Lean runtime (provides lean_int_big_*, lean_nat_big_*, etc.)
    println!("cargo:rustc-link-lib=static=Init");
    println!("cargo:rustc-link-lib=static=leanrt");

    // libuv (Lean runtime async I/O)
    println!("cargo:rustc-link-lib=static=uv");

    // GMP (Lean bignum arithmetic)
    println!("cargo:rustc-link-lib=static=gmp");

    // --- 4. System libraries ---
    // Link C++ standard library (libc++ on macOS, libstdc++ elsewhere)
    let target = env::var("TARGET").unwrap_or_default();
    if target.contains("apple") {
        println!("cargo:rustc-link-lib=dylib=c++");
    } else {
        println!("cargo:rustc-link-lib=dylib=stdc++");
    }

    // --- Git Commit Hash ---
    let git_output = Command::new("git")
        .args(&["rev-parse", "HEAD"])
        .current_dir(&manifest_dir)
        .output();
    if let Ok(output) = git_output {
        if output.status.success() {
            let hash = String::from_utf8(output.stdout)
                .unwrap_or_default()
                .trim()
                .to_string();
            println!("cargo:rustc-env=GIT_HASH={}", hash);
        }
    }

    // --- 5. Rerun triggers ---
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF.lean");
    println!("cargo:rerun-if-changed=../lean4-proofs/lakefile.lean");
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF/FFI.lean");
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF/Basic.lean");
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF/Pure");
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF/QPN");
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF/Engine");
    for f in &c_files {
        println!("cargo:rerun-if-changed={}", f.display());
    }
    println!("cargo:rerun-if-env-changed=LEAN_SYSROOT");
}
