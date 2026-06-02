use ethnum::{I256, U256};
use smallvec::SmallVec;

pub type Uint = bnum::types::U512;
pub type Int = bnum::types::I512;
pub type Uint256 = U256;
pub type Int256 = I256;

pub trait UintExt {
    fn from_u64(v: u64) -> Self;
    fn from_u32(v: u32) -> Self;
    fn from_u128(v: u128) -> Self;
    fn from_u256(v: &ethnum::U256) -> Self;
    fn from_i256(v: &ethnum::I256) -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn as_u128(&self) -> u128;
    fn as_u64(&self) -> u64;
    fn as_u32(&self) -> u32;
    fn as_usize(&self) -> usize;
    fn as_i256(&self) -> ethnum::I256;
    fn as_u256(&self) -> ethnum::U256;
    fn as_int(&self) -> Int;
    fn as_uint(&self) -> Uint;
}

impl UintExt for Uint {
    fn from_u64(v: u64) -> Self { Self::try_from(v).unwrap() }
    fn from_u32(v: u32) -> Self { Self::try_from(v).unwrap() }
    fn from_u128(v: u128) -> Self { Self::try_from(v).unwrap() }
    fn from_u256(v: &ethnum::U256) -> Self {
        let b = v.to_le_bytes();
        let mut d = [0u8; 64];
        d[0..32].copy_from_slice(&b);
        Self::from_le_slice(&d).unwrap()
    }
    fn from_i256(v: &ethnum::I256) -> Self {
        let b = v.to_le_bytes();
        let mut d = [0u8; 64];
        d[0..32].copy_from_slice(&b);
        if v.is_negative() { for i in 32..64 { d[i] = 255; } }
        Self::from_le_slice(&d).unwrap()
    }
    fn zero() -> Self { Self::try_from(0u32).unwrap() }
    fn one() -> Self { Self::try_from(1u32).unwrap() }
    fn as_u128(&self) -> u128 { (*self).try_into().unwrap() }
    fn as_u64(&self) -> u64 { (*self).try_into().unwrap() }
    fn as_u32(&self) -> u32 { (*self).try_into().unwrap() }
    fn as_usize(&self) -> usize { (*self).try_into().unwrap() }
    fn as_i256(&self) -> ethnum::I256 {
        let bytes = self.to_le_bytes();
        let mut b = [0u8; 32];
        b.copy_from_slice(&bytes[0..32]);
        ethnum::I256::from_le_bytes(b)
    }
    fn as_u256(&self) -> ethnum::U256 {
        let bytes = self.to_le_bytes();
        let mut b = [0u8; 32];
        b.copy_from_slice(&bytes[0..32]);
        ethnum::U256::from_le_bytes(b)
    }
    fn as_int(&self) -> Int { Int::from_le_bytes(self.to_le_bytes()) }
    fn as_uint(&self) -> Uint { *self }
}

pub trait IntExt {
    fn from_u64(v: u64) -> Self;
    fn from_u32(v: u32) -> Self;
    fn from_u128(v: u128) -> Self;
    fn from_u256(v: &ethnum::U256) -> Self;
    fn from_i256(v: &ethnum::I256) -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn as_u128(&self) -> u128;
    fn as_u64(&self) -> u64;
    fn as_u32(&self) -> u32;
    fn as_usize(&self) -> usize;
    fn as_i256(&self) -> ethnum::I256;
    fn as_u256(&self) -> ethnum::U256;
    fn as_int(&self) -> Int;
    fn as_uint(&self) -> Uint;
}

impl IntExt for Int {
    fn from_u64(v: u64) -> Self { Self::try_from(v).unwrap() }
    fn from_u32(v: u32) -> Self { Self::try_from(v).unwrap() }
    fn from_u128(v: u128) -> Self { Self::try_from(v).unwrap() }
    fn from_u256(v: &ethnum::U256) -> Self {
        let b = v.to_le_bytes();
        let mut d = [0u8; 64];
        d[0..32].copy_from_slice(&b);
        Self::from_le_slice(&d).unwrap()
    }
    fn from_i256(v: &ethnum::I256) -> Self {
        let b = v.to_le_bytes();
        let mut d = [0u8; 64];
        d[0..32].copy_from_slice(&b);
        if v.is_negative() { for i in 32..64 { d[i] = 255; } }
        Self::from_le_slice(&d).unwrap()
    }
    fn zero() -> Self { Self::try_from(0u32).unwrap() }
    fn one() -> Self { Self::try_from(1u32).unwrap() }
    fn as_u128(&self) -> u128 { (*self).try_into().unwrap() }
    fn as_u64(&self) -> u64 { (*self).try_into().unwrap() }
    fn as_u32(&self) -> u32 { (*self).try_into().unwrap() }
    fn as_usize(&self) -> usize { (*self).try_into().unwrap() }
    fn as_i256(&self) -> ethnum::I256 {
        let bytes = self.to_le_bytes();
        let mut b = [0u8; 32];
        b.copy_from_slice(&bytes[0..32]);
        ethnum::I256::from_le_bytes(b)
    }
    fn as_u256(&self) -> ethnum::U256 {
        let bytes = self.to_le_bytes();
        let mut b = [0u8; 32];
        b.copy_from_slice(&bytes[0..32]);
        ethnum::U256::from_le_bytes(b)
    }
    fn as_uint(&self) -> Uint { Uint::from_le_bytes(self.to_le_bytes()) }
    fn as_int(&self) -> Int { *self }
}

#[derive(Clone, Debug)]
pub struct PrimePower {
    pub p: u64,
    pub two_e: u32,
    pub val: Uint,
    pub sigma: Uint,
    pub sigma_factors: Vec<Uint>,
    pub needs_rho: Vec<Uint>,
    pub abundance_fp: u128,
}

#[derive(Clone, Debug)]
pub struct Prefix {
    pub n_l: Uint,
    pub s_l: Uint,
    pub last_idx: usize,
    pub factors: Vec<u64>,
    pub sigma_factors: Vec<Uint>,
    pub sigma_factors_u64: Vec<u64>,
}
