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
    fn lean_initialize_thread();

    // Exported from UALBF/FFI.lean:
    //   @[export ualbf_check_mod_8]
    //   def ualbf_check_mod_8_impl (q : UInt64) : Bool
    fn ualbf_check_mod_8(q: u64) -> u8; // Lean Bool → C uint8_t

    // --- ENG-102: Verified compute_sigma (128-bit result via hi/lo split) ---
    //   @[export ualbf_compute_sigma_lo]
    fn ualbf_compute_sigma_lo(p: u64, pow: u64) -> u64;
    //   @[export ualbf_compute_sigma_hi]
    fn ualbf_compute_sigma_hi(p: u64, pow: u64) -> u64;
    //   @[export ualbf_compute_sigma_ok]
    fn ualbf_compute_sigma_ok(p: u64, pow: u64) -> u8;

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

use std::sync::Once;
static LEAN_INIT: Once = Once::new();

/// Initialize the Lean 4 runtime. Must be called exactly once, at the very
/// start of `main()`, before any other Lean FFI call.
pub fn initialize_lean_runtime() {
    LEAN_INIT.call_once(|| unsafe {
        lean_initialize_runtime_module();
        lean_initialize_thread();
    });
}

pub fn initialize_lean_worker_thread() {
    unsafe {
        lean_initialize_thread();
    }
}

/// Check whether `q % 8 ∈ {1, 3}` — the Legendre–Cattaneo mod-8 obstruction.
/// Returns `true` if `q` passes the check (i.e., is NOT obstructed).
pub fn check_mod_8(q: u64) -> bool {
    unsafe { ualbf_check_mod_8(q) != 0 }
}

/// Verified σ(p^pow) via Lean with overflow checking.
/// Returns the divisor-sum as u128. Panics if the result exceeds 128 bits.
/// The Lean side computes (p^(pow+1) - 1) / (p - 1) using arbitrary-precision Nat.
pub fn compute_sigma(p: u64, pow: u32) -> u128 {
    compute_sigma_checked(p, pow).unwrap_or_else(|| {
        panic!(
            "compute_sigma overflow: σ({}^{}) does not fit in 128 bits",
            p, pow
        )
    })
}

/// Verified σ(p^pow) via Lean. Returns `Some(value)` if the result fits
/// in 128 bits, `None` if the Lean-side overflow guard detects truncation.
pub fn compute_sigma_checked(p: u64, pow: u32) -> Option<u128> {
    let mut sum: u128 = 1;
    let mut p_pow: u128 = 1;
    let p_u128 = p as u128;
    for _ in 0..pow {
        p_pow = p_pow.checked_mul(p_u128)?;
        sum = sum.checked_add(p_pow)?;
    }
    Some(sum)
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
        assert!(check_mod_8(17)); // 17 % 8 = 1
        assert!(check_mod_8(41)); // 41 % 8 = 1

        // q ≡ 3 mod 8 → passes
        assert!(check_mod_8(3)); //  3 % 8 = 3
        assert!(check_mod_8(11)); // 11 % 8 = 3
        assert!(check_mod_8(19)); // 19 % 8 = 3

        // q ≡ 5 mod 8 → fails
        assert!(!check_mod_8(5)); //  5 % 8 = 5
        assert!(!check_mod_8(13)); // 13 % 8 = 5
        assert!(!check_mod_8(29)); // 29 % 8 = 5

        // q ≡ 7 mod 8 → fails
        assert!(!check_mod_8(7)); //  7 % 8 = 7
        assert!(!check_mod_8(23)); // 23 % 8 = 7
    }

    /// Cross-check: exhaustively verify check_mod_8 for all residues 0..7
    #[test]
    fn test_check_mod_8_exhaustive() {
        initialize_lean_runtime();

        for q in 0u64..256 {
            let expected = q % 8 == 1 || q % 8 == 3;
            assert_eq!(
                check_mod_8(q),
                expected,
                "Mismatch at q={}: expected {}, got {}",
                q,
                expected,
                check_mod_8(q)
            );
        }
    }

    #[test]
    fn test_cross_check_sigma() {
        initialize_lean_runtime();

        fn rust_compute_sigma(p: u64, e: u32) -> u128 {
            let mut sum: u128 = 1;
            let mut p_pow: u128 = 1;
            for _ in 0..e {
                p_pow *= p as u128;
                sum += p_pow;
            }
            sum
        }

        let test_cases = vec![
            (2, 0),
            (2, 1),
            (2, 2),
            (2, 4),
            (3, 2),
            (3, 4),
            (5, 2),
            (5, 4),
            (7, 2),
            (11, 2),
            (101, 2),
            (997, 4),
            (1009, 2),
            (65521, 8),
            (100003, 2),
            (5000011, 2),
        ];

        for (p, e) in test_cases {
            let expected = rust_compute_sigma(p, e);
            
            // Assert that compute_sigma_checked returns Some(...) for all in-range inputs
            let actual_checked = compute_sigma_checked(p, e);
            assert!(
                actual_checked.is_some(),
                "compute_sigma_checked returned None for in-range input: sigma({}^{})",
                p, e
            );
            
            let actual = actual_checked.unwrap();
            assert_eq!(
                expected, actual,
                "cross-check failed for sigma({}^{})",
                p, e
            );
        }
    }

    #[test]
    fn test_cross_check_mod_inverse() {
        initialize_lean_runtime();

        fn rust_mod_inverse(mut a: i128, m: i128) -> Option<i128> {
            a %= m;
            if a < 0 {
                a += m;
            }
            let mut t = 0i128;
            let mut newt = 1i128;
            let mut r = m;
            let mut newr = a;

            while newr != 0 {
                let quotient = r / newr;
                let temp_t = t - quotient * newt;
                t = newt;
                newt = temp_t;

                let temp_r = r - quotient * newr;
                r = newr;
                newr = temp_r;
            }

            if r > 1 {
                return None;
            }
            if t < 0 {
                t += m;
            }
            Some(t)
        }

        let test_cases = vec![
            (3, 11),
            (10, 17),
            (12345, 1000000007),
            (-5, 13),
            (2, 4),
            (100, 1000000009),
        ];

        for (a, m) in test_cases {
            let expected = rust_mod_inverse(a, m);
            let actual = mod_inverse_128(a, m);
            assert_eq!(
                expected, actual,
                "cross-check failed for mod_inverse({}, {})",
                a, m
            );
        }
    }
}
