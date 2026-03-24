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
}
