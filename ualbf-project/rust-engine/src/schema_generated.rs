// AUTO-GENERATED from schema_manifest.json. DO NOT EDIT.

use crate::types::Uint;
use smallvec::SmallVec;
use serde::{Serialize, Deserialize};

#[derive(Clone, Debug)]
pub struct Prefix {
    pub n_l: Uint,
    pub s_l: Uint,
    pub last_idx: usize,
    pub factors: Vec<u64>,
    pub sigma_factors: Vec<Uint>,
    pub sigma_factors_u64: Vec<u64>,
    pub active_mask: Vec<u64>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct SerializedPrefix {
    pub n_l: String,
    pub s_l: String,
    pub last_idx: usize,
    pub factors: Vec<u64>,
    pub sigma_factors: Vec<String>,
    pub sigma_factors_u64: Vec<u64>,
    pub active_mask: Vec<u64>,
}

impl SerializedPrefix {
    pub fn from_prefix(p: &Prefix) -> Self {
        Self {
            n_l: p.n_l.to_string(),
            s_l: p.s_l.to_string(),
            last_idx: p.last_idx.clone(),
            factors: p.factors.clone(),
            sigma_factors: p.sigma_factors.iter().map(|x| x.to_string()).collect(),
            sigma_factors_u64: p.sigma_factors_u64.clone(),
            active_mask: p.active_mask.clone(),
        }
    }

    pub fn to_prefix(&self) -> Prefix {
        Prefix {
            n_l: Uint::from_str_radix(&self.n_l, 10).unwrap(),
            s_l: Uint::from_str_radix(&self.s_l, 10).unwrap(),
            last_idx: self.last_idx.clone(),
            factors: self.factors.clone(),
            sigma_factors: self.sigma_factors.iter().map(|x| Uint::from_str_radix(x, 10).unwrap()).collect(),
            sigma_factors_u64: self.sigma_factors_u64.clone(),
            active_mask: self.active_mask.clone(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Debug)]
pub struct PrefixTransport {
    pub n_l: [u64; 8],
    pub s_l: [u64; 8],
    pub last_idx: usize,
    pub factors: *const u64,
    pub factors_len: usize,
    pub sigma_factors: *const [u64; 8],
    pub sigma_factors_len: usize,
    pub sigma_factors_u64: *const u64,
    pub sigma_factors_u64_len: usize,
    pub active_mask: *const u64,
    pub active_mask_len: usize,
}

impl Prefix {
    pub fn to_transport(&self) -> PrefixTransport {
        PrefixTransport {
            n_l: {
                let mut w = [0u64; 8];
                let bytes = self.n_l.to_le_bytes();
                for i in 0..8 {
                    let mut b = [0u8; 8];
                    b.copy_from_slice(&bytes[i * 8..(i + 1) * 8]);
                    w[i] = u64::from_le_bytes(b);
                }
                w
            },
            s_l: {
                let mut w = [0u64; 8];
                let bytes = self.s_l.to_le_bytes();
                for i in 0..8 {
                    let mut b = [0u8; 8];
                    b.copy_from_slice(&bytes[i * 8..(i + 1) * 8]);
                    w[i] = u64::from_le_bytes(b);
                }
                w
            },
            last_idx: self.last_idx.clone(),
            factors: self.factors.as_ptr(),
            factors_len: self.factors.len(),
            sigma_factors: std::ptr::null(), // TODO: allocate arrays for FFI if needed
            sigma_factors_len: self.sigma_factors.len(),
            sigma_factors_u64: self.sigma_factors_u64.as_ptr(),
            sigma_factors_u64_len: self.sigma_factors_u64.len(),
            active_mask: self.active_mask.as_ptr(),
            active_mask_len: self.active_mask.len(),
        }
    }
}

