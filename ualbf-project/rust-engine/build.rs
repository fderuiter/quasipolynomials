// build.rs — Link the Lean 4 static library and runtime into the Rust engine.

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

    // --- 2. Search paths ---
    let lean_lib_dir = lean_project.join(".lake/build/lib");
    println!("cargo:rustc-link-search=native={}", lean_lib_dir.display());

    let lean_rt_dir = PathBuf::from(&lean_sysroot).join("lib/lean");
    println!("cargo:rustc-link-search=native={}", lean_rt_dir.display());

    let lean_root_lib = PathBuf::from(&lean_sysroot).join("lib");
    println!("cargo:rustc-link-search=native={}", lean_root_lib.display());

    // --- 3. Link libraries ---
    // Our FFI library
    println!("cargo:rustc-link-lib=static=UALBF");

    // Lean runtime (provides lean_int_big_*, lean_nat_big_*, etc.)
    // We only need leanrt and Init — NOT leancpp (which pulls in the
    // full Lean kernel: expressions, levels, declarations, etc.).
    // Our FFI functions only use primitive UInt64/Bool/Int operations.
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
    println!("cargo:rerun-if-env-changed=LEAN_SYSROOT");
}
