use crate::types::{Uint, Int, UintExt, IntExt};
use std::sync::Once;
use num_bigint::Sign;

extern "C" {
    fn lean_initialize_runtime_module();
    fn lean_initialize_thread();

    fn ualbf_check_mod_8(q: u64) -> u8;

    fn ualbf_compute_sigma_dyn(p: u64, pow: u32, out_bytes: *mut u8, out_len: *mut usize) -> u8;

    fn ualbf_mod_inverse_dyn(
        a_bytes: *const u8, a_len: usize, a_neg: u8,
        m_bytes: *const u8, m_len: usize,
        out_bytes: *mut u8, out_len: *mut usize
    ) -> u8;

    fn ualbf_cyclotomic_eval_dyn(
        d: u32,
        p_bytes: *const u8, p_len: usize,
        out_bytes: *mut u8, out_len: *mut usize
    ) -> u8;
}

static LEAN_INIT: Once = Once::new();

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

pub fn check_mod_8(q: u64) -> bool {
    unsafe { ualbf_check_mod_8(q) != 0 }
}

pub fn compute_sigma(p: u64, pow: u32) -> Uint {
    compute_sigma_checked(p, pow).unwrap_or_else(|| {
        panic!("compute_sigma overflow: σ({}^{})", p, pow)
    })
}

pub fn compute_sigma_checked(p: u64, pow: u32) -> Option<Uint> {
    let mut out_buf = vec![0u8; 1024];
    let mut out_len = out_buf.len();
    unsafe {
        if ualbf_compute_sigma_dyn(p, pow, out_buf.as_mut_ptr(), &mut out_len) != 0 {
            Some(Uint::from_bytes_le(&out_buf[..out_len]))
        } else {
            None
        }
    }
}

pub fn mod_inverse_256(a: Int, m: Int) -> Option<Int> {
    let a_bytes = a.to_bytes_le();
    let a_neg = if a_bytes.0 == Sign::Minus { 1 } else { 0 };
    let m_bytes = m.to_bytes_le();
    
    let mut out_buf = vec![0u8; 1024];
    let mut out_len = out_buf.len();

    unsafe {
        if ualbf_mod_inverse_dyn(
            a_bytes.1.as_ptr(), a_bytes.1.len(), a_neg,
            m_bytes.1.as_ptr(), m_bytes.1.len(),
            out_buf.as_mut_ptr(), &mut out_len
        ) != 0 {
            Some(Int::from_bytes_le(Sign::Plus, &out_buf[..out_len]))
        } else {
            None
        }
    }
}

pub fn cyclotomic_eval(d: u32, p: Uint) -> Option<Uint> {
    let p_bytes = p.to_bytes_le();
    let mut out_buf = vec![0u8; 1024];
    let mut out_len = out_buf.len();

    unsafe {
        if ualbf_cyclotomic_eval_dyn(d, p_bytes.as_ptr(), p_bytes.len(), out_buf.as_mut_ptr(), &mut out_len) != 0 {
            Some(Uint::from_bytes_le(&out_buf[..out_len]))
        } else {
            None
        }
    }
}
