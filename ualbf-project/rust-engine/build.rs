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
    let c_files = vec![
        ir_dir.join("UALBF.c"),
        ir_dir.join("UALBF/FFI.c"),
        ir_dir.join("UALBF/Basic.c"),
        ir_dir.join("UALBF/Pure/Zsigmondy.c"),
        ir_dir.join("UALBF/Pure/Arithmetic.c"),
        ir_dir.join("UALBF/Pure/Cyclotomic.c"),
        ir_dir.join("UALBF/Pure/EulerProduct.c"),
        ir_dir.join("UALBF/Pure/RationalBounds.c"),
        ir_dir.join("UALBF/QPN/BasicProperties.c"),
        ir_dir.join("UALBF/QPN/AbundancyBound.c"),
        ir_dir.join("UALBF/QPN/Obstruction.c"),
        ir_dir.join("UALBF/QPN/PrasadSunitha.c"),
        ir_dir.join("UALBF/Engine/Bipartition.c"),
        ir_dir.join("UALBF/Engine/SieveSoundness.c"),
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
    if cfg!(target_os = "macos") {
        if let Ok(prefix) = std::process::Command::new("brew").arg("--prefix").output() {
            let homebrew_prefix = String::from_utf8(prefix.stdout)
                .unwrap_or_default()
                .trim()
                .to_string();
            if !homebrew_prefix.is_empty() {
                println!("cargo:rustc-link-search=native={}/lib", homebrew_prefix);
            }
        }
        println!("cargo:rustc-link-lib=dylib=c++");
    } else {
        println!("cargo:rustc-link-lib=dylib=stdc++");
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
