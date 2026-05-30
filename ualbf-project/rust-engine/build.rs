// build.rs — Compile Lean 4 C-IR into libUALBF.a, then link it with the Lean runtime.

use std::env;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use rayon::prelude::*;

fn mul_mod_u128(mut a: u128, mut b: u128, m: u128) -> u128 {
    let mut res = 0;
    a %= m;
    while b > 0 {
        if b % 2 == 1 {
            res = (res + a) % m;
        }
        a = (a * 2) % m;
        b /= 2;
    }
    res
}

fn pow_mod_u128(mut base: u128, mut exp: u128, m: u128) -> u128 {
    let mut res = 1;
    base %= m;
    while exp > 0 {
        if exp % 2 == 1 {
            res = mul_mod_u128(res, base, m);
        }
        base = mul_mod_u128(base, base, m);
        exp /= 2;
    }
    res
}

fn is_prime_u128(n: u128) -> bool {
    if n <= 1 { return false; }
    if n == 2 || n == 3 { return true; }
    if n % 2 == 0 { return false; }
    let mut d = n - 1;
    let mut r = 0;
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    let bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71];
    for &a in &bases {
        if a >= n { break; }
        let mut x = pow_mod_u128(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        let mut composite = true;
        for _ in 0..r - 1 {
            x = mul_mod_u128(x, x, n);
            if x == n - 1 {
                composite = false;
                break;
            }
        }
        if composite { return false; }
    }
    true
}

fn generate_factors() {
    println!("cargo:warning=Generating cyclotomic factors table for primes up to 250,000 in parallel...");
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = PathBuf::from(out_dir).join("cyclotomic_factors.bin");
    
    let mut file = File::create(dest_path).unwrap();

    let sieve = primal::Sieve::new(250_000);
    let primes: Vec<usize> = sieve.primes_from(3).collect();
    let trial_sieve = primal::Sieve::new(10_000_000);
    let small_primes: Vec<u128> = trial_sieve.primes_from(2).map(|p| p as u128).collect();
    
    let mut entries = primes.into_par_iter().map(|p| {
        let p_u128 = p as u128;
        let mut results = Vec::new();
        for d in [3, 5, 7, 9] {
            let mut phi = match d {
                3 => p_u128*p_u128 + p_u128 + 1,
                5 => p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128 + p_u128*p_u128 + p_u128 + 1,
                7 => p_u128*p_u128*p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128 + p_u128*p_u128 + p_u128 + 1,
                9 => p_u128*p_u128*p_u128*p_u128*p_u128*p_u128 + p_u128*p_u128*p_u128 + 1,
                _ => 1,
            };
            
            let mut factors = Vec::new();
            let mut rejected = false;
            
            for &sp in &small_primes {
                if sp * sp > phi {
                    break;
                }
                while phi % sp == 0 {
                    if sp % 8 == 5 || sp % 8 == 7 {
                        rejected = true;
                        break;
                    }
                    factors.push(sp);
                    phi /= sp;
                }
                if rejected { break; }
            }
            
            if rejected {
                results.push((p as u32, d as u8, vec![0u128]));
                continue;
            }
            
            if phi > 1 {
                if is_prime_u128(phi) {
                    if phi % 8 == 5 || phi % 8 == 7 {
                        results.push((p as u32, d as u8, vec![0u128]));
                        continue;
                    }
                    factors.push(phi);
                } else {
                    // It's a composite with no small factors <= 10M.
                    // This is extremely rare, so we simply omit it from the precalculated table!
                    // The engine will gracefully fall back to runtime factorization for this rare case.
                    continue;
                }
            }
            
            factors.sort_unstable();
            results.push((p as u32, d as u8, factors));
        }
        results
    }).flatten().collect::<Vec<_>>();
    
    // Ensure deterministic ordering
    entries.sort_unstable_by_key(|e| (e.0, e.1));

    let mut data = Vec::new();
    let entries_count = entries.len() as u32;
    for (p, d, factors) in entries {
        data.extend_from_slice(&p.to_le_bytes());
        data.push(d);
        data.push(factors.len() as u8);
        for f in factors {
            data.extend_from_slice(&f.to_le_bytes());
        }
    }
    
    file.write_all(&entries_count.to_le_bytes()).unwrap();
    file.write_all(&data).unwrap();
    println!("cargo:warning=Successfully generated cyclotomic factors table ({} entries).", entries_count);
}

fn main() {
    generate_factors();

    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let lean_project = PathBuf::from(&manifest_dir).join("../lean4-proofs");

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
