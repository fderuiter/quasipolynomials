// build.rs — Compile Lean 4 C-IR into libUALBF.a, then link it with the Lean runtime.

use std::env;
use std::path::PathBuf;
use std::process::Command;
use std::fs;
use serde::Deserialize;

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
struct SearchBounds {
    target_min_log10: BoundValueU32,
    target_max_log10: BoundValueU32,
    sieve_limit: BoundValueUsize,
    max_exponent: BoundValueU32,
    prefix_stop_threshold: BoundValueU64,
    pollard_rho: PollardRhoBounds,
}

#[derive(Deserialize)]
struct OmegaBounds {
    prasad_sunitha: PrasadSunithaBounds,
    baseline: BaselineBounds,
}

#[derive(Deserialize)]
struct EulerCeiling {
    num: u64,
    den: u64,
    is_axiomatic: bool,
    citation: Option<Citation>,
}

#[derive(Deserialize)]
struct BoundsManifest {
    omega_bounds: OmegaBounds,
    search_bounds: SearchBounds,
    euler_ceiling: EulerCeiling,
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

    let manifest_content = fs::read_to_string(&manifest_path)
        .expect("Failed to read bounds_manifest.json");
    let manifest: BoundsManifest = serde_json::from_str(&manifest_content)
        .expect("Failed to parse bounds_manifest.json");

    // Citation validation
    if manifest.omega_bounds.baseline.is_axiomatic && manifest.omega_bounds.baseline.citation.is_none() {
        panic!("FATAL: baseline bound marked axiomatic but lacks citation metadata.");
    }
    if manifest.search_bounds.target_min_log10.is_axiomatic {
        panic!("FATAL: search engine floor (target_min_log10) cannot rely on axiomatic assumptions.");
    }
    if manifest.omega_bounds.prasad_sunitha.is_axiomatic && manifest.omega_bounds.prasad_sunitha.citation.is_none() {
        panic!("FATAL: prasad_sunitha marked axiomatic but lacks citation metadata.");
    }
    if manifest.euler_ceiling.is_axiomatic && manifest.euler_ceiling.citation.is_none() {
        panic!("FATAL: euler_ceiling marked axiomatic but lacks citation metadata.");
    }

    // Deserialize manifest constants as u64 values before generating Rust/Lean constants.
    let prasad_proof: u64 = manifest.omega_bounds.prasad_sunitha.proof_bound;
    let prasad_gap: u64 = manifest.omega_bounds.prasad_sunitha.engine_justified_gap;
    let prasad_bound: u64 = prasad_proof + prasad_gap;
    
    let baseline_proof: u64 = manifest.omega_bounds.baseline.proof_bound;
    let baseline_gap: u64 = manifest.omega_bounds.baseline.engine_justified_gap;
    let baseline_min: u64 = baseline_proof + baseline_gap;

    let euler_num: u64 = manifest.euler_ceiling.num;
    let euler_den: u64 = manifest.euler_ceiling.den;

    let target_min_log10: u32 = manifest.search_bounds.target_min_log10.value;
    let target_max_log10: u32 = manifest.search_bounds.target_max_log10.value;
    let sieve_limit: usize = manifest.search_bounds.sieve_limit.value;
    let max_exponent: u32 = manifest.search_bounds.max_exponent.value;
    let prefix_stop_threshold: u64 = manifest.search_bounds.prefix_stop_threshold.value;
    let pollard_rho_iteration_limit: u32 = manifest.search_bounds.pollard_rho.iteration_limit;
    let pollard_rho_batch_size: u32 = manifest.search_bounds.pollard_rho.batch_size;

    // Enforce the Prasad-Sunitha limit dynamically
    let primes = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83];
    let mut min_val: f64 = 1.0;
    for &p in primes.iter().take(prasad_proof as usize) {
        min_val *= (p as f64) * (p as f64);
    }
    let verified_floor = min_val.log10().floor() as u32;
    if target_min_log10 < verified_floor {
        panic!("FATAL: target_min_log10 ({}) cannot be lower than the highest available verified bound ({}).", target_min_log10, verified_floor);
    }

    // Generate Rust constants with u64 types
    let rust_out_path = PathBuf::from(&manifest_dir).join("src/manifest_constants.rs");
    let rust_code = format!(
        "// AUTO-GENERATED from bounds_manifest.json. DO NOT EDIT.\n\
         pub const PRASAD_SUNITHA_PROOF_BOUND: u64 = {0};\n\
         pub const PRASAD_SUNITHA_BOUND_NO_3_5: u64 = {1};\n\
         pub const BASELINE_MIN_PRIME_FACTORS: u64 = {2};\n\
         pub const EULER_CEILING_NUM: u64 = {3};\n\
         pub const EULER_CEILING_DEN: u64 = {4};\n\
         pub const TARGET_MIN_LOG10: u32 = {5};\n\
         pub const TARGET_MAX_LOG10: u32 = {6};\n\
         pub const SIEVE_LIMIT: usize = {7};\n\
         pub const MAX_EXPONENT: u32 = {8};\n\
         pub const PREFIX_STOP_THRESHOLD: u64 = {9};\n\
         pub const POLLARD_RHO_ITERATION_LIMIT: u32 = {10};\n\
         pub const POLLARD_RHO_BATCH_SIZE: u32 = {11};\n",
        prasad_proof,
        prasad_bound,
        baseline_min,
        euler_num,
        euler_den,
        target_min_log10,
        target_max_log10,
        sieve_limit,
        max_exponent,
        prefix_stop_threshold,
        pollard_rho_iteration_limit,
        pollard_rho_batch_size
    );
    fs::write(&rust_out_path, rust_code).expect("Failed to write Rust constants");

    // Generate Lean constants
    let lean_out_path = lean_project.join("UALBF/ManifestConstants.lean");
    let lean_code = format!(
        "-- AUTO-GENERATED from bounds_manifest.json. DO NOT EDIT.\n\
         namespace UALBF.Manifest\n\n\
         def PRASAD_SUNITHA_PROOF_BOUND : Nat := {0}\n\
         def PRASAD_SUNITHA_BOUND_NO_3_5 : Nat := {1}\n\
         def BASELINE_MIN_PRIME_FACTORS : Nat := {2}\n\
         def EULER_CEILING_NUM : Nat := {3}\n\
         def EULER_CEILING_DEN : Nat := {4}\n\
         def TARGET_MIN_LOG10 : Nat := {5}\n\
         def TARGET_MAX_LOG10 : Nat := {6}\n\
         def SIEVE_LIMIT : Nat := {7}\n\
         def MAX_EXPONENT : Nat := {8}\n\
         def PREFIX_STOP_THRESHOLD : Nat := {9}\n\
         def POLLARD_RHO_ITERATION_LIMIT : Nat := {10}\n\
         def POLLARD_RHO_BATCH_SIZE : Nat := {11}\n\n\
         end UALBF.Manifest\n",
        prasad_proof,
        prasad_bound,
        baseline_min,
        euler_num,
        euler_den,
        target_min_log10,
        target_max_log10,
        sieve_limit,
        max_exponent,
        prefix_stop_threshold,
        pollard_rho_iteration_limit,
        pollard_rho_batch_size
    );
    fs::write(&lean_out_path, lean_code).expect("Failed to write Lean constants");

    println!("cargo:rerun-if-changed=../bounds_manifest.json");

    // --- 1. Resolve Lean sysroot ---
    let lean_sysroot = env::var("LEAN_SYSROOT").unwrap_or_else(|_| {
        let output = Command::new("lean")
            .arg("--print-prefix")
            .current_dir(&lean_project)
            .output();
        match output {
            Ok(output) => {
                String::from_utf8(output.stdout)
                    .unwrap_or_default()
                    .trim()
                    .to_string()
            }
            Err(_) => {
                "".to_string()
            }
        }
    });


    if lean_sysroot.is_empty() {
        if env::var("ALLOW_UNVERIFIED_BUILD").unwrap_or_default() != "1" {
            panic!(
                "FATAL: Lean 4 toolchain not found!\n\
                 Please install Lean 4: https://leanprover.github.io/lean4/doc/setup.html\n\
                 e.g., curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh\n\
                 Or set the LEAN_SYSROOT environment variable if Lean is already installed:\n\
                 export LEAN_SYSROOT=/path/to/lean\n\
                 To build without verified Lean logic (not for production), set ALLOW_UNVERIFIED_BUILD=1"
            );
        }

        println!("cargo:warning=Lean not found. Skipping Lean C-IR compilation.");
        cc::Build::new()
            .file("src/dummy_ffi.c")
            .define("PRASAD_SUNITHA_BOUND_NO_3_5", prasad_bound.to_string().as_str())
            .define("BASELINE_MIN_PRIME_FACTORS", baseline_min.to_string().as_str())
            .define("EULER_CEILING_NUM", euler_num.to_string().as_str())
            .define("EULER_CEILING_DEN", euler_den.to_string().as_str())
            .define("POLLARD_RHO_ITERATION_LIMIT", pollard_rho_iteration_limit.to_string().as_str())
            .define("POLLARD_RHO_BATCH_SIZE", pollard_rho_batch_size.to_string().as_str())
            .compile("ualbf_lean");
        return;
    }


    let lean_include = PathBuf::from(&lean_sysroot).join("include");
    let ir_dir = lean_project.join(".lake/build/ir");

    // --- 2. Compile all UALBF C-IR files into a static library ---
    let mut c_files = Vec::new();
    fn visit_dirs(dir: &std::path::Path, c_files: &mut Vec<std::path::PathBuf>) -> std::io::Result<()> {
        if dir.is_dir() {
            for entry in std::fs::read_dir(dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    visit_dirs(&path, c_files)?;
                } else if path.extension().and_then(|s| s.to_str()) == Some("c") {
                    c_files.push(PathBuf::from("src/mathlib_stubs.c"));
        c_files.push(path);
                }
            }
        }
        Ok(())
    }
    visit_dirs(&ir_dir, &mut c_files).unwrap();

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
    println!("cargo:rustc-link-lib=dylib=c++");
    println!("cargo:rustc-link-lib=dylib=c++abi");

    // --- Git Commit Hash ---
    let git_output = Command::new("git")
        .args(&["rev-parse", "HEAD"])
        .current_dir(&manifest_dir)
        .output();
    if let Ok(output) = git_output {
        if output.status.success() {
            let hash = String::from_utf8(output.stdout).unwrap_or_default().trim().to_string();
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
