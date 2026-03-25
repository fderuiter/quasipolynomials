// lean_ffi.rs — FFI bindings to the Lean 4 compiled static library.
//
// The Lean runtime MUST be initialized before calling any exported Lean
// function. Call `initialize_lean_runtime()` exactly once at the start of main().

// ---------------------------------------------------------------------------
// Raw extern declarations
// ---------------------------------------------------------------------------

extern "C" {
    // Lean runtime initialization (must be called before any Lean code)
    fn lean_initialize_runtime_module();

    // Exported from UALBF/FFI.lean:
    //   @[export ualbf_check_mod_8]
    //   def ualbf_check_mod_8_impl (q : UInt64) : Bool
    fn ualbf_check_mod_8(q: u64) -> u8; // Lean Bool → C uint8_t

    //   @[export ualbf_ambs_target]
    //   def ualbf_ambs_target_impl (n_l : UInt64) (s_l : UInt64) : UInt64
    fn ualbf_ambs_target(n_l: u64, s_l: u64) -> u64;

    // --- ENG-102: Verified compute_sigma (128-bit result via hi/lo split) ---
    //   @[export ualbf_compute_sigma_lo]
    fn ualbf_compute_sigma_lo(p: u64, pow: u64) -> u64;
    //   @[export ualbf_compute_sigma_hi]
    fn ualbf_compute_sigma_hi(p: u64, pow: u64) -> u64;

    // --- ENG-102: Verified mod_inverse for 128-bit values (hi/lo split) ---
    //   a is encoded as |a| in (a_lo, a_hi) + sign flag a_neg (0=positive, 1=negative)
    //   m is encoded as (m_lo, m_hi), always positive
    //   @[export ualbf_mod_inverse_lo]
    fn ualbf_mod_inverse_lo(a_lo: u64, a_hi: u64, a_neg: u64, m_lo: u64, m_hi: u64) -> u64;
    //   @[export ualbf_mod_inverse_hi]
    fn ualbf_mod_inverse_hi(a_lo: u64, a_hi: u64, a_neg: u64, m_lo: u64, m_hi: u64) -> u64;
    //   @[export ualbf_mod_inverse_ok]
    fn ualbf_mod_inverse_ok(a_lo: u64, a_hi: u64, a_neg: u64, m_lo: u64, m_hi: u64) -> u8;
}

// ---------------------------------------------------------------------------
// Safe wrappers
// ---------------------------------------------------------------------------

/// Initialize the Lean 4 runtime. Must be called exactly once, at the very
/// start of `main()`, before any other Lean FFI call.
pub fn initialize_lean_runtime() {
    unsafe {
        lean_initialize_runtime_module();
    }
}

/// Check whether `q % 8 ∈ {1, 3}` — the Legendre–Cattaneo mod-8 obstruction.
/// Returns `true` if `q` passes the check (i.e., is NOT obstructed).
pub fn check_mod_8(q: u64) -> bool {
    unsafe { ualbf_check_mod_8(q) != 0 }
}

/// Compute the AMBS suffix target: `mod_inverse(-2 * n_l, s_l)`.
/// Returns `0` if the inverse does not exist (coprimality violation).
pub fn ambs_target(n_l: u64, s_l: u64) -> u64 {
    unsafe { ualbf_ambs_target(n_l, s_l) }
}

/// Verified σ(p^pow) via Lean. Returns the divisor-sum as u128.
/// The Lean side computes (p^(pow+1) - 1) / (p - 1) using arbitrary-precision Nat.
pub fn compute_sigma(p: u64, pow: u32) -> u128 {
    unsafe {
        let lo = ualbf_compute_sigma_lo(p, pow as u64) as u128;
        let hi = ualbf_compute_sigma_hi(p, pow as u64) as u128;
        lo | (hi << 64)
    }
}

/// Verified modular inverse of `a` mod `m` via Lean.
/// Returns `Some(inverse)` if gcd(a, m) == 1, else `None`.
/// Both `a` and `m` are i128; the Lean side uses arbitrary-precision Int.
pub fn mod_inverse_128(a: i128, m: i128) -> Option<i128> {
    let a_abs = a.unsigned_abs();
    let a_lo = a_abs as u64;
    let a_hi = (a_abs >> 64) as u64;
    let a_neg: u64 = if a < 0 { 1 } else { 0 };

    let m_abs = m.unsigned_abs();
    let m_lo = m_abs as u64;
    let m_hi = (m_abs >> 64) as u64;

    unsafe {
        let ok = ualbf_mod_inverse_ok(a_lo, a_hi, a_neg, m_lo, m_hi);
        if ok != 0 {
            let lo = ualbf_mod_inverse_lo(a_lo, a_hi, a_neg, m_lo, m_hi) as u128;
            let hi = ualbf_mod_inverse_hi(a_lo, a_hi, a_neg, m_lo, m_hi) as u128;
            Some((lo | (hi << 64)) as i128)
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // NOTE: These tests require the Lean library to be linked.
    // Run with: cargo test (after `lake build` in lean4-proofs/)

    #[test]
    fn test_check_mod_8() {
        initialize_lean_runtime();

        // q ≡ 1 mod 8 → passes
        assert!(check_mod_8(17));  // 17 % 8 = 1
        assert!(check_mod_8(41));  // 41 % 8 = 1

        // q ≡ 3 mod 8 → passes
        assert!(check_mod_8(3));   //  3 % 8 = 3
        assert!(check_mod_8(11));  // 11 % 8 = 3
        assert!(check_mod_8(19));  // 19 % 8 = 3

        // q ≡ 5 mod 8 → fails
        assert!(!check_mod_8(5));  //  5 % 8 = 5
        assert!(!check_mod_8(13)); // 13 % 8 = 5
        assert!(!check_mod_8(29)); // 29 % 8 = 5

        // q ≡ 7 mod 8 → fails
        assert!(!check_mod_8(7));  //  7 % 8 = 7
        assert!(!check_mod_8(23)); // 23 % 8 = 7
    }

    #[test]
    fn test_ambs_target() {
        // Don't re-init if test_check_mod_8 already ran;
        // in practice these run in separate processes so it's fine.
        initialize_lean_runtime();

        // mod_inverse(-2 * 3, 7) = mod_inverse(-6, 7) = mod_inverse(1, 7) = 1
        assert_eq!(ambs_target(3, 7), 1);

        // mod_inverse(-2 * 1, 5) = mod_inverse(-2, 5) = mod_inverse(3, 5) = 2
        assert_eq!(ambs_target(1, 5), 2);
    }

    /// Cross-check: exhaustively verify check_mod_8 for all residues 0..7
    #[test]
    fn test_check_mod_8_exhaustive() {
        initialize_lean_runtime();

        for q in 0u64..256 {
            let expected = q % 8 == 1 || q % 8 == 3;
            assert_eq!(check_mod_8(q), expected,
                "Mismatch at q={}: expected {}, got {}", q, expected, check_mod_8(q));
        }
    }

    /// Cross-check: verify ambs_target against a pure-Rust mod_inverse
    #[test]
    fn test_ambs_target_crosscheck() {
        initialize_lean_runtime();

        let cases: &[(u64, u64)] = &[
            (3, 7), (1, 5), (5, 13), (7, 11), (100, 97),
            (12345, 67891), (999, 1000003), (1, 3),
            (17, 31), (255, 65537),
        ];

        for &(n_l, s_l) in cases {
            let lean_result = ambs_target(n_l, s_l);

            // Rust: mod_inverse(-2 * n_l, s_l)
            let a = (-(2i128 * n_l as i128)).rem_euclid(s_l as i128);
            let rust_result = rust_mod_inverse(a as u64, s_l);

            match rust_result {
                Some(v) => {
                    assert_eq!(lean_result, v,
                        "Mismatch for n_l={}, s_l={}: Lean={}, Rust={}",
                        n_l, s_l, lean_result, v);
                    // Verify: (result * (-2 * n_l)) ≡ 1 (mod s_l)
                    let check = ((lean_result as i128) * (-2i128 * n_l as i128)).rem_euclid(s_l as i128);
                    assert_eq!(check, 1,
                        "Inverse check failed: {} * {} mod {} = {} (expected 1)",
                        lean_result, -2i64 * n_l as i64, s_l, check);
                }
                None => {
                    assert_eq!(lean_result, 0,
                        "Mismatch for n_l={}, s_l={}: Lean={}, Rust=None",
                        n_l, s_l, lean_result);
                }
            }
        }
    }

    /// Pure-Rust iterative mod_inverse for cross-checking
    fn rust_mod_inverse(a: u64, m: u64) -> Option<u64> {
        let (mut old_r, mut r) = (a as i128, m as i128);
        let (mut old_s, mut s) = (1i128, 0i128);
        while r != 0 {
            let q = old_r / r;
            let tmp = r; r = old_r - q * r; old_r = tmp;
            let tmp = s; s = old_s - q * s; old_s = tmp;
        }
        if old_r == 1 {
            Some(old_s.rem_euclid(m as i128) as u64)
        } else {
            None
        }
    }
}
