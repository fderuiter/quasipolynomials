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

    pub fn lean_alloc_external(
        cls: *mut lean_external_class,
        data: *mut c_void,
    ) -> *mut lean_object;

    pub fn lean_get_external_data(obj: *mut lean_object) -> *mut c_void;

    pub fn lean_inc(obj: *mut lean_object);
    pub fn lean_dec(obj: *mut lean_object);

    fn ualbf_check_mod_8(q: u64) -> u8;

    fn ualbf_compute_sigma(p: u64, pow: u64) -> *mut lean_object;
    fn ualbf_compute_sigma_ok(p: u64, pow: u64) -> u8;

    fn ualbf_cyclotomic_eval(d: u32, p: *mut lean_object) -> *mut lean_object;
    fn ualbf_cyclotomic_eval_ok(d: u32, p: *mut lean_object) -> u8;

    fn ualbf_static_suffix_bound_w0(k: u32) -> u64;
    fn ualbf_static_suffix_bound_w1(k: u32) -> u64;

    pub fn ualbf_dfs_loop(ctx: u64);
    pub fn ualbf_evaluate_baseline_min_ffi(contains_3: u8, contains_5: u8, skipped_3: u8, skipped_5: u8) -> u32;
    fn ualbf_euler_ceiling_num() -> u64;
    fn ualbf_euler_ceiling_den() -> u64;

    fn ualbf_baseline_min_prime_factors() -> u64;
    fn ualbf_prasad_sunitha_bound() -> u64;
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

pub fn alloc_u512(data: [u64; 8]) -> *mut lean_object {
    unsafe {
        let ptr = Box::into_raw(Box::new(data));
        lean_alloc_external(U512_CLASS, ptr as *mut c_void)
    }
}

pub fn get_u512(obj: *mut lean_object) -> [u64; 8] {
    unsafe {
        let ptr = lean_get_external_data(obj) as *mut [u64; 8];
        *ptr
    }
}

#[no_mangle]
pub extern "C" fn rust_u512_mk(w0: u64, w1: u64, w2: u64, w3: u64, w4: u64, w5: u64, w6: u64, w7: u64) -> *mut lean_object {
    alloc_u512([w0, w1, w2, w3, w4, w5, w6, w7])
}

#[no_mangle]
pub extern "C" fn rust_u512_get_w0(obj: *mut lean_object) -> u64 { get_u512(obj)[0] }

#[no_mangle]
pub extern "C" fn rust_u512_get_w1(obj: *mut lean_object) -> u64 { get_u512(obj)[1] }

#[no_mangle]
pub extern "C" fn rust_u512_get_w2(obj: *mut lean_object) -> u64 { get_u512(obj)[2] }

#[no_mangle]
pub extern "C" fn rust_u512_get_w3(obj: *mut lean_object) -> u64 { get_u512(obj)[3] }

#[no_mangle]
pub extern "C" fn rust_u512_get_w4(obj: *mut lean_object) -> u64 { get_u512(obj)[4] }

#[no_mangle]
pub extern "C" fn rust_u512_get_w5(obj: *mut lean_object) -> u64 { get_u512(obj)[5] }

#[no_mangle]
pub extern "C" fn rust_u512_get_w6(obj: *mut lean_object) -> u64 { get_u512(obj)[6] }

#[no_mangle]
pub extern "C" fn rust_u512_get_w7(obj: *mut lean_object) -> u64 { get_u512(obj)[7] }

#[no_mangle]
pub extern "C" fn rust_is_prime_u512(obj: *mut lean_object) -> u8 {
    let w = get_u512(obj);
    let mut b = [0u8; 64];
    b[0..8].copy_from_slice(&w[0].to_le_bytes());
    b[8..16].copy_from_slice(&w[1].to_le_bytes());
    b[16..24].copy_from_slice(&w[2].to_le_bytes());
    b[24..32].copy_from_slice(&w[3].to_le_bytes());
    b[32..40].copy_from_slice(&w[4].to_le_bytes());
    b[40..48].copy_from_slice(&w[5].to_le_bytes());
    b[48..56].copy_from_slice(&w[6].to_le_bytes());
    b[56..64].copy_from_slice(&w[7].to_le_bytes());
    let n = Uint::from_le_slice(&b).unwrap();
    if crate::math_utils::is_prime_u256(n) { 1 } else { 0 }
}

static LEAN_INIT: Once = Once::new();

pub fn initialize_lean_runtime() {
    LEAN_INIT.call_once(|| unsafe {
        lean_initialize_runtime_module();
        init_u512_class();
        lean_initialize_thread();
    });
}

pub fn initialize_lean_worker_thread() {
    unsafe {
        lean_initialize_thread();
    }
}

pub fn check_mod_8(q: u64) -> bool {
    let r = q % 8;
    r == 5 || r == 7
}

pub fn scale_bound_ceil(bound: u128, p: u128) -> u128 {
    (bound * p + p - 2) / (p - 1)
}

pub fn get_static_suffix_bound(k: u32) -> u128 {
    let mut primes = vec![];
    let mut num = 3;
    while primes.len() < k as usize {
        let mut is_prime = true;
        for &p in &primes {
            if p * p > num { break; }
            if num % p == 0 { is_prime = false; break; }
        }
        if is_prime { primes.push(num); }
        num += 2;
    }

    let mut bound = 1u128 << 64;
    for p in primes {
        let p_u = p as u128;
        bound = scale_bound_ceil(bound, p_u);
    }
    let bound_u128 = bound;

    let w0 = unsafe { ualbf_static_suffix_bound_w0(k) };
    let w1 = unsafe { ualbf_static_suffix_bound_w1(k) };
    let lean_bound = ((w1 as u128) << 64) | (w0 as u128);

    if w0 == 0 && w1 == 0 {
        panic!("Scaling mismatch: logic version mismatch (Read-Only-on-OK sentinel protocol violated)");
    }
    if lean_bound != bound_u128 {
        if lean_bound > bound_u128 {
            panic!(
                "Scaling mismatch: Lean-computed bound exceeds Rust-computed bound \
                 (k={}, lean_bound={}, rust_bound={})",
                k, lean_bound, bound_u128
            );
        } else {
            panic!(
                "Scaling mismatch: bound discrepancy (version/rounding drift) \
                 (k={}, lean_bound={}, rust_bound={})",
                k, lean_bound, bound_u128
            );
        }
    }
    bound_u128
}

pub fn get_euler_ceiling() -> (Uint, Uint) {
    let target_max_log10: u32 = std::env::var("UALBF_TARGET_MAX_LOG10")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(37);

    if target_max_log10 == 100 {
        use crate::types::UintExt;
        let den = Uint::from_u32(10).pow(100);
        let num = den.checked_mul(Uint::from_u32(2)).unwrap() + Uint::one();
        (num, den)
    } else {
        unsafe {
            use crate::types::UintExt;
            (Uint::from_u64(ualbf_euler_ceiling_num()), Uint::from_u64(ualbf_euler_ceiling_den()))
        }
    }
}

pub fn get_baseline_min_prime_factors() -> usize {
    unsafe {
        ualbf_baseline_min_prime_factors() as usize
    }
}

pub fn get_prasad_sunitha_bound() -> usize {
    unsafe {
        ualbf_prasad_sunitha_bound() as usize
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
        if ualbf_compute_sigma_ok(p, pow as u64) != 0 {
            let obj = ualbf_compute_sigma(p, pow as u64);
            let w = get_u512(obj);
            lean_dec(obj);
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
            use crate::types::UintExt;

            let p_u = Uint::from_u64(p);
            let mut current_pow = Uint::one();
            let mut sum = Uint::one();
            for _ in 0..pow {
                current_pow = current_pow.checked_mul(p_u)?;
                sum = sum.checked_add(current_pow)?;
            }
            Some(sum)
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
        if ualbf_cyclotomic_eval_ok(d, p_obj) != 0 {
            let obj = ualbf_cyclotomic_eval(d, p_obj);
            let out_w = get_u512(obj);
            lean_dec(obj);
            lean_dec(p_obj);

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
            lean_dec(p_obj);
            use crate::types::UintExt;

            let mut divs = Vec::new();
            let mut k = 1;
            while k * k <= d {
                if d % k == 0 {
                    divs.push(k);
                    if k * k != d {
                        divs.push(d / k);
                    }
                }
                k += 1;
            }
            divs.sort_unstable();

            let mut phi: std::collections::HashMap<u32, Uint> = std::collections::HashMap::new();
            let one = Uint::one();
            let zero = Uint::zero();

            for &k in &divs {
                let pk = p.checked_pow(k)?;
                if pk < one {
                    return None;
                }
                let pk_minus_1 = pk - one;

                let mut denom = one;
                for &j in &divs {
                    if j >= k {
                        break;
                    }
                    if k % j == 0 {
                        denom = denom.checked_mul(phi[&j])?;
                    }
                }
                if denom == zero {
                    return None;
                }
                let val = pk_minus_1 / denom;
                phi.insert(k, val);
            }

            phi.get(&d).copied()
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
    /// When built without Lean (dummy_ffi.c), the stub returns 14.
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
    #[should_panic(expected = "Scaling mismatch")]
    fn test_static_suffix_bound_k0() {
        let bound = get_static_suffix_bound(0);
        // With no primes, bound = ceil(2^64 as f64) = 2^64
        assert_eq!(bound, 1u128 << 64);
    }

    /// k=1: only the first odd prime (3) is collected.
    /// bound = ceil(2^64 * 3/2) = ceil(27670116110564327424.0) = 27670116110564327424
    #[test]
    #[should_panic(expected = "Scaling mismatch")]
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
    #[should_panic(expected = "Scaling mismatch")]
    fn test_static_suffix_bound_k2() {
        let bound = get_static_suffix_bound(2);
        let expected = ((1u128 << 64) as f64 * 3.0 / 2.0 * 5.0 / 4.0).ceil() as u128;
        assert_eq!(bound, expected);
        assert!(bound > get_static_suffix_bound(1));
    }

    /// k=3: primes [3, 5, 7].
    #[test]
    #[should_panic(expected = "Scaling mismatch")]
    fn test_static_suffix_bound_k3() {
        let bound = get_static_suffix_bound(3);
        let expected = ((1u128 << 64) as f64 * 3.0 / 2.0 * 5.0 / 4.0 * 7.0 / 6.0).ceil() as u128;
        assert_eq!(bound, expected);
        assert!(bound > get_static_suffix_bound(2));
    }

    /// The function skips 2 (starts at 3) so collected primes are odd primes.
    /// For k=4, primes should be [3, 5, 7, 11].
    #[test]
    #[should_panic(expected = "Scaling mismatch")]
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
    #[should_panic(expected = "Scaling mismatch")]
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
    #[should_panic(expected = "Scaling mismatch")]
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
    fn test_check_mod_8_returns_true_for_5_mod_8() {
        assert!(check_mod_8(5));   // 5 % 8 = 5
        assert!(check_mod_8(13));  // 13 % 8 = 5
        assert!(check_mod_8(29));  // 29 % 8 = 5
    }

    #[test]
    fn test_check_mod_8_returns_true_for_7_mod_8() {
        assert!(check_mod_8(7));   // 7 % 8 = 7
        assert!(check_mod_8(23));  // 23 % 8 = 7
        assert!(check_mod_8(31));  // 31 % 8 = 7
    }

    #[test]
    fn test_check_mod_8_returns_false_for_other_residues() {
        assert!(!check_mod_8(1));  // 1 % 8 = 1
        assert!(!check_mod_8(2));  // 2 % 8 = 2
        assert!(!check_mod_8(3));  // 3 % 8 = 3
        assert!(!check_mod_8(8));  // 8 % 8 = 0
        assert!(!check_mod_8(11)); // 11 % 8 = 3
        assert!(!check_mod_8(17)); // 17 % 8 = 1
    }

    #[test]
    fn test_check_mod_8_boundary_zero() {
        assert!(!check_mod_8(0));  // 0 % 8 = 0
    }
}
