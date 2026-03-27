// build.rs — Compile Lean 4 C-IR into libUALBF.a, then link it with the Lean runtime.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let lean_project = PathBuf::from(&manifest_dir).join("../lean4-proofs");

    // --- 1. Resolve Lean sysroot ---
    let lean_sysroot = env::var("LEAN_SYSROOT").ok().unwrap_or_else(|| {
        let output = Command::new("lean")
            .arg("--print-prefix")
            .current_dir(&lean_project)
            .output()
            .expect("Failed to run `lean --print-prefix`. Is elan/lean on your PATH?");
        String::from_utf8(output.stdout)
            .expect("Invalid UTF-8 from lean --print-prefix")
            .trim()
            .to_string()
    });

    let lean_include = PathBuf::from(&lean_sysroot).join("include");
    let ir_dir = lean_project.join(".lake/build/ir");

    // --- 2. Compile all UALBF C-IR files into a static library ---
    let c_files = [
        ir_dir.join("UALBF.c"),
        ir_dir.join("UALBF/Basic.c"),
        ir_dir.join("UALBF/Bipartition.c"),
        ir_dir.join("UALBF/FFI.c"),
        ir_dir.join("UALBF/Obstruction.c"),
        ir_dir.join("UALBF/Valuation.c"),
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
    println!("cargo:rustc-link-lib=dylib=c++");

    // --- 5. Rerun triggers ---
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF/FFI.lean");
    println!("cargo:rerun-if-changed=../lean4-proofs/lakefile.lean");
    for f in &c_files {
        println!("cargo:rerun-if-changed={}", f.display());
    }
    println!("cargo:rerun-if-env-changed=LEAN_SYSROOT");
}
