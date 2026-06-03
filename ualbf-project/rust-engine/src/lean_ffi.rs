use ethnum::{I256, U256};
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

    fn ualbf_euler_ceiling_num() -> u64;
    fn ualbf_euler_ceiling_den() -> u64;
}

static mut U256_CLASS: *mut lean_external_class = std::ptr::null_mut();

extern "C" fn u256_finalize(ptr: *mut c_void) {
    unsafe {
        let _ = Box::from_raw(ptr as *mut [u64; 4]);
    }
}

extern "C" fn u256_foreach(_ptr: *mut c_void, _fn: usize) {}

fn init_u256_class() {
    unsafe {
        U256_CLASS = lean_register_external_class(u256_finalize, u256_foreach);
    }
}

pub fn alloc_u256(data: [u64; 4]) -> *mut lean_object {
    unsafe {
        let ptr = Box::into_raw(Box::new(data));
        lean_alloc_external(U256_CLASS, ptr as *mut c_void)
    }
}

pub fn get_u256(obj: *mut lean_object) -> [u64; 4] {
    unsafe {
        let ptr = lean_get_external_data(obj) as *mut [u64; 4];
        *ptr
    }
}

#[no_mangle]
pub extern "C" fn rust_u256_mk(w0: u64, w1: u64, w2: u64, w3: u64) -> *mut lean_object {
    alloc_u256([w0, w1, w2, w3])
}

#[no_mangle]
pub extern "C" fn rust_u256_get_w0(obj: *mut lean_object) -> u64 {
    get_u256(obj)[0]
}

#[no_mangle]
pub extern "C" fn rust_u256_get_w1(obj: *mut lean_object) -> u64 {
    get_u256(obj)[1]
}

#[no_mangle]
pub extern "C" fn rust_u256_get_w2(obj: *mut lean_object) -> u64 {
    get_u256(obj)[2]
}

#[no_mangle]
pub extern "C" fn rust_u256_get_w3(obj: *mut lean_object) -> u64 {
    get_u256(obj)[3]
}

static LEAN_INIT: Once = Once::new();

pub fn initialize_lean_runtime() {
    LEAN_INIT.call_once(|| unsafe {
        lean_initialize_runtime_module();
        init_u256_class();
        lean_initialize_thread();
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

pub fn get_static_suffix_bound(k: u32) -> u128 {
    unsafe {
        let w0 = ualbf_static_suffix_bound_w0(k);
        let w1 = ualbf_static_suffix_bound_w1(k);
        ((w1 as u128) << 64) | (w0 as u128)
    }
}

pub fn get_euler_ceiling() -> (u64, u64) {
    unsafe {
        (ualbf_euler_ceiling_num(), ualbf_euler_ceiling_den())
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
            let w = get_u256(obj);
            lean_dec(obj);
            let mut b = [0u8; 64];
            b[0..8].copy_from_slice(&w[0].to_le_bytes());
            b[8..16].copy_from_slice(&w[1].to_le_bytes());
            b[16..24].copy_from_slice(&w[2].to_le_bytes());
            b[24..32].copy_from_slice(&w[3].to_le_bytes());
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
        b.copy_from_slice(&bytes[i*8..(i+1)*8]);
        w[i] = u64::from_le_bytes(b);
    }

    unsafe {
        let p_obj = alloc_u256([w[0], w[1], w[2], w[3]]);
        if ualbf_cyclotomic_eval_ok(d, p_obj) != 0 {
            let obj = ualbf_cyclotomic_eval(d, p_obj);
            let out_w = get_u256(obj);
            lean_dec(obj);
            lean_dec(p_obj);
            
            let mut b = [0u8; 64];
            b[0..8].copy_from_slice(&out_w[0].to_le_bytes());
            b[8..16].copy_from_slice(&out_w[1].to_le_bytes());
            b[16..24].copy_from_slice(&out_w[2].to_le_bytes());
            b[24..32].copy_from_slice(&out_w[3].to_le_bytes());
            Some(Uint::from_le_slice(&b).unwrap())
        } else {
            lean_dec(p_obj);
            None
        }
    }
}
