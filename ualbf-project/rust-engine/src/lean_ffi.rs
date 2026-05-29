// lean_ffi.rs — FFI bindings to the Lean 4 compiled static library.

extern "C" {
    fn lean_initialize_runtime_module();
    fn lean_initialize_thread();

    fn ualbf_check_mod_8(q: u64) -> u8;

    fn ualbf_compute_sigma_w0(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_w1(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_w2(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_w3(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_ok(p: u64, pow: u64) -> u8;

    fn ualbf_mod_inverse_w0(
        a_w0: u64,
        a_w1: u64,
        a_w2: u64,
        a_w3: u64,
        a_neg: u64,
        m_w0: u64,
        m_w1: u64,
        m_w2: u64,
        m_w3: u64,
    ) -> u64;
    fn ualbf_mod_inverse_w1(
        a_w0: u64,
        a_w1: u64,
        a_w2: u64,
        a_w3: u64,
        a_neg: u64,
        m_w0: u64,
        m_w1: u64,
        m_w2: u64,
        m_w3: u64,
    ) -> u64;
    fn ualbf_mod_inverse_w2(
        a_w0: u64,
        a_w1: u64,
        a_w2: u64,
        a_w3: u64,
        a_neg: u64,
        m_w0: u64,
        m_w1: u64,
        m_w2: u64,
        m_w3: u64,
    ) -> u64;
    fn ualbf_mod_inverse_w3(
        a_w0: u64,
        a_w1: u64,
        a_w2: u64,
        a_w3: u64,
        a_neg: u64,
        m_w0: u64,
        m_w1: u64,
        m_w2: u64,
        m_w3: u64,
    ) -> u64;
    fn ualbf_mod_inverse_ok(
        a_w0: u64,
        a_w1: u64,
        a_w2: u64,
        a_w3: u64,
        a_neg: u64,
        m_w0: u64,
        m_w1: u64,
        m_w2: u64,
        m_w3: u64,
    ) -> u8;

    fn ualbf_cyclotomic_eval_w0(d: u64, p_w0: u64, p_w1: u64, p_w2: u64, p_w3: u64) -> u64;
    fn ualbf_cyclotomic_eval_w1(d: u64, p_w0: u64, p_w1: u64, p_w2: u64, p_w3: u64) -> u64;
    fn ualbf_cyclotomic_eval_w2(d: u64, p_w0: u64, p_w1: u64, p_w2: u64, p_w3: u64) -> u64;
    fn ualbf_cyclotomic_eval_w3(d: u64, p_w0: u64, p_w1: u64, p_w2: u64, p_w3: u64) -> u64;
    fn ualbf_cyclotomic_eval_ok(d: u64, p_w0: u64, p_w1: u64, p_w2: u64, p_w3: u64) -> u8;
}

use ethnum::{I256, U256};
use std::sync::Once;
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

pub fn compute_sigma(p: u64, pow: u32) -> U256 {
    compute_sigma_checked(p, pow).unwrap_or_else(|| {
        panic!(
            "compute_sigma overflow: σ({}^{}) does not fit in 256 bits",
            p, pow
        )
    })
}

pub fn compute_sigma_checked(p: u64, pow: u32) -> Option<U256> {
    unsafe {
        if ualbf_compute_sigma_ok(p, pow as u64) != 0 {
            let w0 = ualbf_compute_sigma_w0(p, pow as u64);
            let w1 = ualbf_compute_sigma_w1(p, pow as u64);
            let w2 = ualbf_compute_sigma_w2(p, pow as u64);
            let w3 = ualbf_compute_sigma_w3(p, pow as u64);
            Some(U256::from_words(
                ((w3 as u128) << 64) | w2 as u128,
                ((w1 as u128) << 64) | w0 as u128,
            ))
        } else {
            None
        }
    }
}

pub fn mod_inverse_256(a: I256, m: I256) -> Option<I256> {
    let a_abs = if a < I256::ZERO { -a } else { a }.as_u256();
    let (a_hi, a_lo) = a_abs.into_words();
    let a_w0 = a_lo as u64;
    let a_w1 = (a_lo >> 64) as u64;
    let a_w2 = a_hi as u64;
    let a_w3 = (a_hi >> 64) as u64;
    let a_neg: u64 = if a < I256::ZERO { 1 } else { 0 };

    let m_abs = if m < I256::ZERO { -m } else { m }.as_u256();
    let (m_hi, m_lo) = m_abs.into_words();
    let m_w0 = m_lo as u64;
    let m_w1 = (m_lo >> 64) as u64;
    let m_w2 = m_hi as u64;
    let m_w3 = (m_hi >> 64) as u64;

    unsafe {
        if ualbf_mod_inverse_ok(a_w0, a_w1, a_w2, a_w3, a_neg, m_w0, m_w1, m_w2, m_w3) != 0 {
            let w0 = ualbf_mod_inverse_w0(a_w0, a_w1, a_w2, a_w3, a_neg, m_w0, m_w1, m_w2, m_w3);
            let w1 = ualbf_mod_inverse_w1(a_w0, a_w1, a_w2, a_w3, a_neg, m_w0, m_w1, m_w2, m_w3);
            let w2 = ualbf_mod_inverse_w2(a_w0, a_w1, a_w2, a_w3, a_neg, m_w0, m_w1, m_w2, m_w3);
            let w3 = ualbf_mod_inverse_w3(a_w0, a_w1, a_w2, a_w3, a_neg, m_w0, m_w1, m_w2, m_w3);
            let res_u = U256::from_words(
                ((w3 as u128) << 64) | w2 as u128,
                ((w1 as u128) << 64) | w0 as u128,
            );
            Some(res_u.as_i256())
        } else {
            None
        }
    }
}

pub fn cyclotomic_eval_ffi(d: u32, p: U256) -> Option<U256> {
    let (p_hi, p_lo) = p.into_words();
    let p_w0 = p_lo as u64;
    let p_w1 = (p_lo >> 64) as u64;
    let p_w2 = p_hi as u64;
    let p_w3 = (p_hi >> 64) as u64;

    unsafe {
        if ualbf_cyclotomic_eval_ok(d as u64, p_w0, p_w1, p_w2, p_w3) != 0 {
            let w0 = ualbf_cyclotomic_eval_w0(d as u64, p_w0, p_w1, p_w2, p_w3);
            let w1 = ualbf_cyclotomic_eval_w1(d as u64, p_w0, p_w1, p_w2, p_w3);
            let w2 = ualbf_cyclotomic_eval_w2(d as u64, p_w0, p_w1, p_w2, p_w3);
            let w3 = ualbf_cyclotomic_eval_w3(d as u64, p_w0, p_w1, p_w2, p_w3);
            Some(U256::from_words(
                ((w3 as u128) << 64) | w2 as u128,
                ((w1 as u128) << 64) | w0 as u128,
            ))
        } else {
            None
        }
    }
}
