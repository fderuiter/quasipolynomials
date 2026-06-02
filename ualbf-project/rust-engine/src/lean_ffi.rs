use ethnum::{I256, U256};
use crate::types::{Uint, Int};
use std::sync::Once;

extern "C" {
    fn lean_initialize_runtime_module();
    fn lean_initialize_thread();

    fn ualbf_check_mod_8(q: u64) -> u8;

    fn ualbf_compute_sigma_w0(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_w1(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_w2(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_w3(p: u64, pow: u64) -> u64;
    fn ualbf_compute_sigma_ok(p: u64, pow: u64) -> u8;

    fn ualbf_cyclotomic_eval_w0(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_w1(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_w2(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_w3(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_w4(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_w5(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_w6(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_w7(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u64;
    fn ualbf_cyclotomic_eval_ok(d: u32, p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64) -> u8;

    fn ualbf_static_suffix_bound_w0(k: u32) -> u64;
    fn ualbf_static_suffix_bound_w1(k: u32) -> u64;
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

pub fn get_static_suffix_bound(k: u32) -> u128 {
    unsafe {
        let w0 = ualbf_static_suffix_bound_w0(k);
        let w1 = ualbf_static_suffix_bound_w1(k);
        ((w1 as u128) << 64) | (w0 as u128)
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
            let w0 = ualbf_compute_sigma_w0(p, pow as u64);
            let w1 = ualbf_compute_sigma_w1(p, pow as u64);
            let w2 = ualbf_compute_sigma_w2(p, pow as u64);
            let w3 = ualbf_compute_sigma_w3(p, pow as u64);
            let mut b = [0u8; 64];
            b[0..8].copy_from_slice(&w0.to_le_bytes());
            b[8..16].copy_from_slice(&w1.to_le_bytes());
            b[16..24].copy_from_slice(&w2.to_le_bytes());
            b[24..32].copy_from_slice(&w3.to_le_bytes());
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
        if ualbf_cyclotomic_eval_ok(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]) != 0 {
            let mut out = [0u64; 8];
            out[0] = ualbf_cyclotomic_eval_w0(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            out[1] = ualbf_cyclotomic_eval_w1(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            out[2] = ualbf_cyclotomic_eval_w2(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            out[3] = ualbf_cyclotomic_eval_w3(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            out[4] = ualbf_cyclotomic_eval_w4(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            out[5] = ualbf_cyclotomic_eval_w5(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            out[6] = ualbf_cyclotomic_eval_w6(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            out[7] = ualbf_cyclotomic_eval_w7(d, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
            
            let mut b = [0u8; 64];
            for i in 0..8 {
                b[i*8..(i+1)*8].copy_from_slice(&out[i].to_le_bytes());
            }
            Some(Uint::from_le_slice(&b).unwrap())
        } else {
            None
        }
    }
}
