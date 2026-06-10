// build.rs — Compile Lean 4 C-IR into libUALBF.a, then link it with the Lean runtime.

use std::env;
use std::path::PathBuf;
use std::process::Command;
use std::fs;
use serde::Deserialize;

#[derive(Deserialize)]
struct ManifestConstants {
    #[serde(rename = "PRASAD_SUNITHA_BOUND_NO_3_5")]
    prasad_sunitha_bound_no_3_5: u64,
    #[serde(rename = "BASELINE_MIN_PRIME_FACTORS")]
    baseline_min_prime_factors: u64,
    #[serde(rename = "EULER_CEILING_NUM")]
    euler_ceiling_num: u64,
    #[serde(rename = "EULER_CEILING_DEN")]
    euler_ceiling_den: u64,
}

#[derive(Deserialize)]
struct Manifest {
    constants: ManifestConstants,
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
    
    // --- 0. Read proof_manifest.json and generate constants ---
    let manifest_path = PathBuf::from(&manifest_dir).join("../proof_manifest.json");

    // Manifest is now mandatory - fail build if missing
    if !manifest_path.exists() {
        panic!(
            "FATAL: proof_manifest.json not found at {}. \
             The build requires a valid manifest to generate verified constants.",
            manifest_path.display()
        );
    }

    let manifest_content = fs::read_to_string(&manifest_path)
        .expect("Failed to read proof_manifest.json");
    let manifest: Manifest = serde_json::from_str(&manifest_content)
        .expect("Failed to parse proof_manifest.json");

    // Deserialize manifest constants as u64 values before generating Rust/Lean constants.
    let prasad_bound: u64 = manifest.constants.prasad_sunitha_bound_no_3_5;
    let baseline_min: u64 = manifest.constants.baseline_min_prime_factors;
    let euler_num: u64 = manifest.constants.euler_ceiling_num;
    let euler_den: u64 = manifest.constants.euler_ceiling_den;

    // Generate Rust constants with u64 types
    let rust_out_path = PathBuf::from(&manifest_dir).join("src/manifest_constants.rs");
    let rust_code = format!(
        "// AUTO-GENERATED from proof_manifest.json. DO NOT EDIT.\n\
         pub const PRASAD_SUNITHA_BOUND_NO_3_5: u64 = {};\n\
         pub const BASELINE_MIN_PRIME_FACTORS: u64 = {};\n\
         pub const EULER_CEILING_NUM: u64 = {};\n\
         pub const EULER_CEILING_DEN: u64 = {};\n",
        prasad_bound,
        baseline_min,
        euler_num,
        euler_den
    );
    fs::write(&rust_out_path, rust_code).expect("Failed to write Rust constants");

    // Generate Lean constants
    let lean_out_path = lean_project.join("UALBF/ManifestConstants.lean");
    let lean_code = format!(
        "-- AUTO-GENERATED from proof_manifest.json. DO NOT EDIT.\n\
         namespace UALBF.Manifest\n\n\
         def PRASAD_SUNITHA_BOUND_NO_3_5 : Nat := {}\n\
         def BASELINE_MIN_PRIME_FACTORS : Nat := {}\n\
         def EULER_CEILING_NUM : Nat := {}\n\
         def EULER_CEILING_DEN : Nat := {}\n\n\
         end UALBF.Manifest\n",
        prasad_bound,
        baseline_min,
        euler_num,
        euler_den
    );
    fs::write(&lean_out_path, lean_code).expect("Failed to write Lean constants");

    println!("cargo:rerun-if-changed=../proof_manifest.json");

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
        println!("cargo:warning=Lean not found. Skipping Lean C-IR compilation.");
        cc::Build::new()
            .file("src/dummy_ffi.c")
            .compile("ualbf_lean");
        return;
    }


    let lean_include = PathBuf::from(&lean_sysroot).join("include");
    let ir_dir = lean_project.join(".lake/build/ir");

    // --- 2. Compile all UALBF C-IR files into a static library ---
    let c_files = vec![
        ir_dir.join("UALBF.c"),
        ir_dir.join("UALBF/FFI.c"),
        ir_dir.join("UALBF/Basic.c"),
    ];

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
