use crate::types::{Uint, Int};
use std::sync::Once;
use std::ffi::c_void;

#[repr(C)]
pub struct lean_object {
    _priv: [u8; 0],
}

#[repr(C)]
pub struct lean_external_class {
    _priv: [u8; 0],
}

extern "C" {
    fn lean_initialize_runtime_module();
    fn lean_initialize_thread();

    pub fn lean_register_external_class(
        finalize: extern "C" fn(*mut c_void),
        foreach: extern "C" fn(*mut c_void, usize),
    ) -> *mut lean_external_class;

    pub fn rs_lean_alloc_external(
        cls: *mut lean_external_class,
        data: *mut c_void,
    ) -> *mut lean_object;

    pub fn rs_lean_get_external_data(obj: *mut lean_object) -> *mut c_void;

    pub fn rs_lean_inc(obj: *mut lean_object);
    pub fn rs_lean_dec(obj: *mut lean_object);
    pub fn initialize_ualbf_UALBF(builtin: u8) -> *mut lean_object;


}

include!("ffi_generated.rs");

pub struct LeanObjectWrapper(pub *mut lean_object);

impl LeanObjectWrapper {
    pub fn new(obj: *mut lean_object) -> Self {
        Self(obj)
    }

    pub fn as_ptr(&self) -> *mut lean_object {
        self.0
    }

    pub fn into_raw(self) -> *mut lean_object {
        let ptr = self.0;
        std::mem::forget(self);
        ptr
    }
}

impl Drop for LeanObjectWrapper {
    fn drop(&mut self) {
        unsafe {
            if !self.0.is_null() {
                rs_lean_dec(self.0);
            }
        }
    }
}

pub trait FromLean {
    fn from_lean(obj: *mut lean_object) -> Self;
}

pub trait ToLean {
    fn to_lean(&self) -> LeanObjectWrapper;
}

impl FromLean for Uint {
    fn from_lean(obj: *mut lean_object) -> Self {
        let w = get_u512(obj);
        let mut bytes = [0u8; 64];
        for i in 0..8 {
            bytes[i * 8..(i + 1) * 8].copy_from_slice(&w[i].to_le_bytes());
        }
        Uint::from_le_slice(&bytes).unwrap()
    }
}

impl ToLean for Uint {
    fn to_lean(&self) -> LeanObjectWrapper {
        let bytes = self.to_le_bytes();
        let mut w = [0u64; 8];
        for i in 0..8 {
            let mut b = [0u8; 8];
            b.copy_from_slice(&bytes[i * 8..(i + 1) * 8]);
            w[i] = u64::from_le_bytes(b);
        }
        LeanObjectWrapper::new(alloc_u512(w))
    }
}


static mut U512_CLASS: *mut lean_external_class = std::ptr::null_mut();

extern "C" fn u512_finalize(ptr: *mut c_void) {
    unsafe {
        let _ = Box::from_raw(ptr as *mut [u64; 8]);
    }
}

extern "C" fn u512_foreach(_ptr: *mut c_void, _fn: usize) {}

fn init_u512_class() {
    unsafe {
        U512_CLASS = lean_register_external_class(u512_finalize, u512_foreach);
    }
}

pub const ZERO_U512: [u64; 8] = [0; 8];
pub const ZERO_U256: [u64; 8] = [0; 8];

pub fn alloc_u512(data: [u64; 8]) -> *mut lean_object {
    unsafe {
        let ptr = Box::into_raw(Box::new(data));
        rs_lean_alloc_external(U512_CLASS, ptr as *mut c_void)
    }
}

pub fn get_u512(obj: *mut lean_object) -> [u64; 8] {
    unsafe {
        let ptr = rs_lean_get_external_data(obj) as *mut [u64; 8];
        *ptr
    }
}

#[no_mangle]
pub extern "C" fn rust_u512_mk(w0: u64, w1: u64, w2: u64, w3: u64, w4: u64, w5: u64, w6: u64, w7: u64) -> *mut lean_object {
    alloc_u512([w0, w1, w2, w3, w4, w5, w6, w7])
}

#[no_mangle]
pub extern "C" fn rust_u256_mk(w0: u64, w1: u64, w2: u64, w3: u64) -> *mut lean_object {
    alloc_u512([w0, w1, w2, w3, 0, 0, 0, 0])
}

#[inline(always)]
pub fn is_none(obj: *mut lean_object) -> bool {
    (obj as usize) & 1 == 1
}

#[inline(always)]
pub fn get_some(obj: *mut lean_object) -> *mut lean_object {
    unsafe {
        let ptr = (obj as *mut u8).add(8) as *mut *mut lean_object;
        *ptr
    }
}











static LEAN_INIT: Once = Once::new();

thread_local! {
    static IS_LEAN_THREAD_INIT: std::cell::Cell<bool> = std::cell::Cell::new(false);
}

pub fn initialize_lean_runtime() {
    LEAN_INIT.call_once(|| unsafe {
        lean_initialize_runtime_module();
        init_u512_class();
        let res = initialize_ualbf_UALBF(1);
        rs_lean_dec(res);
    });
    IS_LEAN_THREAD_INIT.with(|init| {
        if !init.get() {
            unsafe { lean_initialize_thread(); }
            init.set(true);
        }
    });
}

pub fn initialize_lean_worker_thread() {
    unsafe {
        lean_initialize_thread();
    }
}

pub fn check_mod_8(q: u64) -> bool {
    unsafe { ualbf_check_mod_8(q) != 0 }
}

pub fn check_mod_3(p: u64, two_e: u32) -> bool {
    unsafe { ualbf_check_mod_3(p, two_e) != 0 }
}

pub fn check_mod_5(p: u64, two_e: u32) -> bool {
    unsafe { ualbf_check_mod_5(p, two_e) != 0 }
}

pub fn check_mod_9(p: u64, two_e: u32) -> bool {
    unsafe { ualbf_check_mod_9(p, two_e) != 0 }
}

pub fn scale_bound_ceil(bound: u128, p: u128) -> u128 {
    (bound * p + p - 2) / (p - 1)
}

pub fn get_static_suffix_bound(k: u32) -> u128 {
    let w0 = unsafe { ualbf_static_suffix_bound_w0(k) };
    let w1 = unsafe { ualbf_static_suffix_bound_w1(k) };
    ((w1 as u128) << 64) | (w0 as u128)
}

pub fn get_euler_ceiling() -> (Uint, Uint) {
    unsafe {
        use crate::types::UintExt;
        let num = ualbf_euler_ceiling_num();
        let den = ualbf_euler_ceiling_den();
        if (num & (1 << 63)) == 0 || (den & (1 << 63)) == 0 {
            panic!("FATAL: Unverified constant detected over FFI. Missing verified bit for euler_ceiling.");
        }
        (Uint::from_u64(num & !(1 << 63)), Uint::from_u64(den & !(1 << 63)))
    }
}

pub fn verify_identity_lean(n_l: &Uint, x_l_abs: &Uint, x_l_neg: bool, s_l: &Uint) -> bool {
    let n_l_obj = n_l.to_lean();
    let x_l_obj = x_l_abs.to_lean();
    let s_l_obj = s_l.to_lean();

    unsafe {
        let ok = ualbf_verify_identity(n_l_obj.as_ptr(), x_l_obj.as_ptr(), if x_l_neg { 1 } else { 0 }, s_l_obj.as_ptr());
        ok != 0
    }
}

pub fn get_baseline_min_prime_factors() -> usize {
    unsafe {
        let val = ualbf_baseline_min_prime_factors();
        if (val & (1 << 63)) == 0 {
            panic!("FATAL: Unverified constant detected over FFI. Missing verified bit for baseline_min_prime_factors.");
        }
        (val & !(1 << 63)) as usize
    }
}

pub fn get_prasad_sunitha_bound() -> usize {
    unsafe {
        let val = ualbf_prasad_sunitha_bound();
        if (val & (1 << 63)) == 0 {
            panic!("FATAL: Unverified constant detected over FFI. Missing verified bit for prasad_sunitha_bound.");
        }
        (val & !(1 << 63)) as usize
    }
}

pub fn get_target_abundance_num() -> u64 {
    unsafe {
        let val = ualbf_target_abundance_num();
        if (val & (1 << 63)) == 0 {
            panic!("FATAL: Unverified constant detected over FFI. Missing verified bit for target_abundance_num.");
        }
        val & !(1 << 63)
    }
}

pub fn get_target_abundance_den() -> u64 {
    unsafe {
        let val = ualbf_target_abundance_den();
        if (val & (1 << 63)) == 0 {
            panic!("FATAL: Unverified constant detected over FFI. Missing verified bit for target_abundance_den.");
        }
        val & !(1 << 63)
    }
}

pub fn compute_sigma(p: u64, pow: u32) -> Uint {
    compute_sigma_checked(p, pow).unwrap_or_else(|| {
        panic!(
            "compute_sigma overflow: σ({}^{}) does not fit in 512 bits",
            p, pow
        )
    })
}

pub fn compute_sigma_checked(p: u64, pow: u32) -> Option<Uint> {
    unsafe {
        let opt_obj = ualbf_compute_sigma(p, pow as u64);
        if !is_none(opt_obj) {
            let obj = get_some(opt_obj);
            let w = get_u512(obj);
            rs_lean_dec(opt_obj);
            let mut b = [0u8; 64];
            b[0..8].copy_from_slice(&w[0].to_le_bytes());
            b[8..16].copy_from_slice(&w[1].to_le_bytes());
            b[16..24].copy_from_slice(&w[2].to_le_bytes());
            b[24..32].copy_from_slice(&w[3].to_le_bytes());
            b[32..40].copy_from_slice(&w[4].to_le_bytes());
            b[40..48].copy_from_slice(&w[5].to_le_bytes());
            b[48..56].copy_from_slice(&w[6].to_le_bytes());
            b[56..64].copy_from_slice(&w[7].to_le_bytes());
            Some(Uint::from_le_slice(&b).unwrap())
        } else {
            None
        }
    }
}

pub fn cyclotomic_eval(d: u32, p: Uint) -> Option<Uint> {
    let mut w = [0u64; 8];
    let bytes = p.to_le_bytes();
    for i in 0..8 {
        let mut b = [0u8; 8];
        b.copy_from_slice(&bytes[i * 8..(i + 1) * 8]);
        w[i] = u64::from_le_bytes(b);
    }

    unsafe {
        let p_obj = alloc_u512([w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]);
        let opt_obj = ualbf_cyclotomic_eval(d, p_obj);
        if !is_none(opt_obj) {
            let obj = get_some(opt_obj);
            let out_w = get_u512(obj);
            rs_lean_dec(opt_obj);
            rs_lean_dec(p_obj);

            let mut b = [0u8; 64];
            b[0..8].copy_from_slice(&out_w[0].to_le_bytes());
            b[8..16].copy_from_slice(&out_w[1].to_le_bytes());
            b[16..24].copy_from_slice(&out_w[2].to_le_bytes());
            b[24..32].copy_from_slice(&out_w[3].to_le_bytes());
            b[32..40].copy_from_slice(&out_w[4].to_le_bytes());
            b[40..48].copy_from_slice(&out_w[5].to_le_bytes());
            b[48..56].copy_from_slice(&out_w[6].to_le_bytes());
            b[56..64].copy_from_slice(&out_w[7].to_le_bytes());
            Some(Uint::from_le_slice(&b).unwrap())
        } else {
            rs_lean_dec(p_obj);
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_signature_and_alignment_guarantees() {
        assert_eq!(std::mem::size_of::<[u64; 4]>(), 32, "Lean 256-bit integer must be exactly 32 bytes");
        assert_eq!(std::mem::align_of::<[u64; 4]>(), 8, "Lean 256-bit integer must have 8-byte alignment");

        // Native rust engine Uint mapping (bnum U512 is an array of bytes, align 1)
        assert_eq!(std::mem::size_of::<Uint>(), 64, "Rust engine Uint (512-bit) must be exactly 64 bytes");
        assert!(std::mem::align_of::<Uint>() >= 1, "Rust engine Uint alignment is sufficient");
    }

    /// get_baseline_min_prime_factors must return a positive value.
    /// When built without Lean (dummy_ffi.c), the stub returns 7.
    #[test]
    fn test_get_baseline_min_prime_factors_nonzero() {
        let value = get_baseline_min_prime_factors();
        assert!(value > 0, "baseline_min_prime_factors must be positive, got {}", value);
    }

    /// get_prasad_sunitha_bound must return a positive value.
    /// When built without Lean (dummy_ffi.c), the stub returns 15.
    #[test]
    fn test_get_prasad_sunitha_bound_nonzero() {
        let value = get_prasad_sunitha_bound();
        assert!(value > 0, "prasad_sunitha_bound must be positive, got {}", value);
    }

    /// The Prasad-Sunitha bound must exceed the baseline minimum prime factors.
    /// This invariant reflects the mathematical requirement that the Prasad-Sunitha
    /// result (coprime-to-15 case) forces a strictly higher prime count floor.
    #[test]
    fn test_prasad_sunitha_bound_exceeds_baseline() {
        let baseline = get_baseline_min_prime_factors();
        let ps_bound = get_prasad_sunitha_bound();
        assert!(
            ps_bound > baseline,
            "prasad_sunitha_bound ({}) must be strictly greater than baseline_min_prime_factors ({})",
            ps_bound,
            baseline
        );
    }

    /// Verify the dummy stub value for baseline_min_prime_factors.
    /// When Lean is not present, dummy_ffi.c provides the return value 7.
    #[test]
    fn test_dummy_baseline_min_prime_factors_value() {
        let value = get_baseline_min_prime_factors();
        // The dummy stub (dummy_ffi.c) returns 7. The real Lean proof also exports 7.
        assert_eq!(value, 7, "expected baseline_min_prime_factors == 7, got {}", value);
    }

    /// Verify the dummy stub value for prasad_sunitha_bound.
    #[test]
    fn test_dummy_prasad_sunitha_bound_value() {
        let value = get_prasad_sunitha_bound();
        assert_eq!(value, crate::manifest_constants::PRASAD_SUNITHA_BOUND_NO_3_5 as usize, "expected prasad_sunitha_bound to match manifest");
    }

    /// Repeated calls to get_baseline_min_prime_factors must return the same value,
    /// since the result comes from a constant C export (or a Lean proof constant).
    #[test]
    fn test_get_baseline_min_prime_factors_idempotent() {
        let first = get_baseline_min_prime_factors();
        let second = get_baseline_min_prime_factors();
        assert_eq!(first, second, "get_baseline_min_prime_factors must be deterministic");
    }

    /// Repeated calls to get_prasad_sunitha_bound must return the same value.
    #[test]
    fn test_get_prasad_sunitha_bound_idempotent() {
        let first = get_prasad_sunitha_bound();
        let second = get_prasad_sunitha_bound();
        assert_eq!(first, second, "get_prasad_sunitha_bound must be deterministic");
    }

    // -----------------------------------------------------------------------
    // Tests for get_static_suffix_bound (PR change: now computes locally)
    // -----------------------------------------------------------------------

    /// k=0 means no primes accumulated; the bound is just ceil(2^64), which as
    /// a u128 value equals 2^64.
    #[test]

    fn test_static_suffix_bound_k0() {
        let bound = get_static_suffix_bound(0);
        // With no primes, bound = ceil(2^64 as f64) = 2^64
        assert_eq!(bound, 1u128 << 64);
    }

    /// k=1: only the first odd prime (3) is collected.
    /// bound = ceil(2^64 * 3/2) = ceil(27670116110564327424.0) = 27670116110564327424
    #[test]

    fn test_static_suffix_bound_k1() {
        let bound = get_static_suffix_bound(1);
        let expected = ((1u128 << 64) as f64 * 3.0 / 2.0).ceil() as u128;
        assert_eq!(bound, expected);
        // Must be strictly larger than 2^64
        assert!(bound > 1u128 << 64);
    }

    /// k=2: primes [3, 5].
    /// bound = ceil(2^64 * 3/2 * 5/4)
    #[test]

    fn test_static_suffix_bound_k2() {
        let bound = get_static_suffix_bound(2);
        let expected = ((1u128 << 64) as f64 * 3.0 / 2.0 * 5.0 / 4.0).ceil() as u128;
        assert_eq!(bound, expected);
        assert!(bound > get_static_suffix_bound(1));
    }

    /// k=3: primes [3, 5, 7].
    #[test]

    fn test_static_suffix_bound_k3() {
        let bound = get_static_suffix_bound(3);
        let expected = ((1u128 << 64) as f64 * 3.0 / 2.0 * 5.0 / 4.0 * 7.0 / 6.0).ceil() as u128;
        assert_eq!(bound, expected);
        assert!(bound > get_static_suffix_bound(2));
    }

    /// The function skips 2 (starts at 3) so collected primes are odd primes.
    /// For k=4, primes should be [3, 5, 7, 11].
    #[test]

    fn test_static_suffix_bound_k4_uses_odd_primes_starting_at_3() {
        let bound = get_static_suffix_bound(4);
        // Primes collected: 3, 5, 7, 11 (not 2)
        let expected = ((1u128 << 64) as f64
            * 3.0 / 2.0
            * 5.0 / 4.0
            * 7.0 / 6.0
            * 11.0 / 10.0
        ).ceil() as u128;
        assert_eq!(bound, expected);
    }

    /// The bound must be monotonically non-decreasing as k grows, because each
    /// additional prime p contributes a factor p/(p-1) >= 1.
    #[test]

    fn test_static_suffix_bound_monotone_increasing() {
        let bounds: Vec<u128> = (0..=8).map(get_static_suffix_bound).collect();
        for w in bounds.windows(2) {
            assert!(
                w[1] >= w[0],
                "bound should be non-decreasing: bounds[k+1]={} < bounds[k]={}",
                w[1], w[0]
            );
        }
    }

    /// Each factor p/(p-1) is strictly > 1 for any prime p >= 2, so bounds are
    /// strictly increasing.
    #[test]

    fn test_static_suffix_bound_strictly_increasing_for_k_gt_0() {
        for k in 1..=6u32 {
            assert!(
                get_static_suffix_bound(k) > get_static_suffix_bound(k - 1),
                "bound(k={}) should be strictly greater than bound(k={})",
                k, k - 1
            );
        }
    }

    /// check_mod_8 edge cases covering mod-8 residues 5 and 7 (the "difficult" cases).
    #[test]
    fn test_check_mod_8_returns_true_for_1_mod_8() {
        assert!(check_mod_8(1));   // 1 % 8 = 1
        assert!(check_mod_8(9));   // 9 % 8 = 1
        assert!(check_mod_8(17));  // 17 % 8 = 1
    }

    #[test]
    fn test_check_mod_8_returns_true_for_3_mod_8() {
        assert!(check_mod_8(3));   // 3 % 8 = 3
        assert!(check_mod_8(11));  // 11 % 8 = 3
        assert!(check_mod_8(19));  // 19 % 8 = 3
    }

    #[test]
    fn test_check_mod_8_returns_false_for_other_residues() {
        assert!(!check_mod_8(5));  // 5 % 8 = 5
        assert!(!check_mod_8(2));  // 2 % 8 = 2
        assert!(!check_mod_8(7));  // 7 % 8 = 7
        assert!(!check_mod_8(8));  // 8 % 8 = 0
        assert!(!check_mod_8(13)); // 13 % 8 = 5
        assert!(!check_mod_8(15)); // 15 % 8 = 7
    }

    #[test]
    fn test_check_mod_8_boundary_zero() {
        assert!(!check_mod_8(0));  // 0 % 8 = 0
    }

    #[test]
    fn test_cyclotomic_eval_arbitrary_degrees() {
        use crate::types::UintExt;
        // Test evaluation for degrees > 9 outside the original {3, 5, 7, 9} set.
        let p = Uint::from_u128(2);
        // Phi_10(2) = 2^4 - 2^3 + 2^2 - 2 + 1 = 16 - 8 + 4 - 2 + 1 = 11
        assert_eq!(cyclotomic_eval(10, p).unwrap(), Uint::from_u128(11));
        // Phi_11(2) = 2^10 + 2^9 + ... + 1 = 2047
        assert_eq!(cyclotomic_eval(11, p).unwrap(), Uint::from_u128(2047));
        // Phi_13(2) = 2^12 + ... + 1 = 8191
        assert_eq!(cyclotomic_eval(13, p).unwrap(), Uint::from_u128(8191));
        // Phi_14(2) = 2^6 - 2^5 + 2^3 - 2^2 + 1? No, Phi_14 is cyclotomic(14). Phi_14(x) = X^6 - X^5 + X^4 - X^3 + X^2 - X + 1
        // For x=2: 64 - 32 + 16 - 8 + 4 - 2 + 1 = 43
        assert_eq!(cyclotomic_eval(14, p).unwrap(), Uint::from_u128(43));
        // Phi_15(2) = X^8 - X^7 + X^5 - X^4 + X^3 - X + 1
        // For x=2: 256 - 128 + 32 - 16 + 8 - 2 + 1 = 151
        assert_eq!(cyclotomic_eval(15, p).unwrap(), Uint::from_u128(151));
    }
}

use ualbf_macros::lean_ffi_export;
#[lean_ffi_export]
pub fn rust_dummy_macro_test(a: Uint, b: Uint) -> Uint {
    a + b
}

pub fn get_pollard_rho_iteration_limit() -> u32 {
    unsafe {
        let val = ualbf_pollard_rho_iteration_limit();
        if (val & (1 << 31)) == 0 {
            panic!("FATAL: Unverified constant detected over FFI. Missing verified bit for pollard_rho_iteration_limit.");
        }
        val & !(1 << 31)
    }
}

pub fn get_pollard_rho_batch_size() -> u32 {
    unsafe {
        let val = ualbf_pollard_rho_batch_size();
        if (val & (1 << 31)) == 0 {
            panic!("FATAL: Unverified constant detected over FFI. Missing verified bit for pollard_rho_batch_size.");
        }
        val & !(1 << 31)
    }
}
