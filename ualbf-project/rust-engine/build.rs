// build.rs — Link the Lean 4 static library and runtime into the Rust engine.
//
// This script tells Cargo where to find:
//   1. libualbf_core.a  — our compiled Lean library (from `lake build`)
//   2. leanrt / leancpp  — the Lean runtime libraries (from the elan toolchain)
//
// The Lean sysroot is auto-detected from `lean --print-prefix`, but can be
// overridden by setting LEAN_SYSROOT.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let lean_project = PathBuf::from(&manifest_dir).join("../lean4-proofs");

    // --- 1. Link our custom Lean library ---
    // After `lake build`, native .o files land in .lake/build/lib/.
    // We assemble them into a static lib via a post-build ar step (see below).
    let lean_lib_dir = lean_project.join(".lake/build/lib");
    println!("cargo:rustc-link-search=native={}", lean_lib_dir.display());

    // Also check the native lib dir that Lake may use
    let lean_native_dir = lean_project.join(".lake/build/lib/native");
    if lean_native_dir.exists() {
        println!("cargo:rustc-link-search=native={}", lean_native_dir.display());
    }

    // --- 2. Auto-detect Lean sysroot ---
    let lean_sysroot = env::var("LEAN_SYSROOT").ok().unwrap_or_else(|| {
        let output = Command::new("lean")
            .arg("--print-prefix")
            .output()
            .expect("Failed to run `lean --print-prefix`. Is elan/lean on your PATH?");
        String::from_utf8(output.stdout)
            .expect("Invalid UTF-8 from lean --print-prefix")
            .trim()
            .to_string()
    });

    let lean_lib_path = PathBuf::from(&lean_sysroot).join("lib/lean");
    println!("cargo:rustc-link-search=native={}", lean_lib_path.display());

    // --- 3. Link Lean runtime libraries ---
    // leanrt: Lean runtime (memory allocator, task runtime, etc.)
    // leancpp: C++ interop layer used by Lean
    // leanrt_initial: initialization stubs
    println!("cargo:rustc-link-lib=static=leanrt");
    println!("cargo:rustc-link-lib=static=leancpp");
    println!("cargo:rustc-link-lib=static=leanrt_initial");

    // --- 4. System libraries required by Lean runtime ---
    #[cfg(target_os = "macos")]
    {
        println!("cargo:rustc-link-lib=dylib=c++");
    }
    #[cfg(target_os = "linux")]
    {
        println!("cargo:rustc-link-lib=dylib=stdc++");
    }

    // gmp is required by Lean's arbitrary-precision arithmetic
    println!("cargo:rustc-link-lib=dylib=gmp");

    // --- 5. Rerun triggers ---
    println!("cargo:rerun-if-changed=../lean4-proofs/UALBF/FFI.lean");
    println!("cargo:rerun-if-changed=../lean4-proofs/lakefile.lean");
    println!("cargo:rerun-if-env-changed=LEAN_SYSROOT");
}
