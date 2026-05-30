use num_bigint::{BigInt, BigUint};
use smallvec::SmallVec;
use num_traits::{Zero, One, ToPrimitive};

pub type Uint = BigUint;
pub type Int = BigInt;
pub type Uint256 = ethnum::U256;
pub type Int256 = ethnum::I256;

pub trait UintExt: Sized {
    fn from_u64_ext(v: u64) -> Self;
    fn from_u32_ext(v: u32) -> Self;
    fn from_u128_ext(v: u128) -> Self;
    fn from_u256_ext(v: &ethnum::U256) -> Self;
    fn from_i256_ext(v: &ethnum::I256) -> Self;
    fn zero_ext() -> Self;
    fn one_ext() -> Self;
    fn as_u128(&self) -> u128;
    fn as_u64(&self) -> u64;
    fn as_u32(&self) -> u32;
    fn as_usize(&self) -> usize;
    fn as_i256(&self) -> ethnum::I256;
    fn as_u256(&self) -> ethnum::U256;
    fn as_int(&self) -> Int;
    fn as_uint(&self) -> Uint;
    fn checked_mul(&self, other: &Self) -> Option<Self>;
    fn checked_add(&self, other: &Self) -> Option<Self>;
    fn checked_pow(&self, exp: u32) -> Option<Self>;
    fn pow(&self, exp: u32) -> Self;
    fn to_le_bytes(&self) -> Vec<u8>;
}

impl UintExt for Uint {
    fn from_u64_ext(v: u64) -> Self { Self::from(v) }
    fn from_u32_ext(v: u32) -> Self { Self::from(v) }
    fn from_u128_ext(v: u128) -> Self { Self::from(v) }
    fn from_u256_ext(v: &ethnum::U256) -> Self {
        Self::from_bytes_le(&v.to_le_bytes())
    }
    fn from_i256_ext(v: &ethnum::I256) -> Self {
        Self::from_bytes_le(&v.to_le_bytes())
    }
    fn zero_ext() -> Self { <Self as Zero>::zero() }
    fn one_ext() -> Self { <Self as One>::one() }
    fn as_u128(&self) -> u128 { self.to_u128().unwrap_or(0) }
    fn as_u64(&self) -> u64 { self.to_u64().unwrap_or(0) }
    fn as_u32(&self) -> u32 { self.to_u32().unwrap_or(0) }
    fn as_usize(&self) -> usize { self.to_usize().unwrap_or(0) }
    fn as_i256(&self) -> ethnum::I256 {
        let b = self.to_bytes_le();
        let mut d = [0u8; 32];
        let len = b.len().min(32);
        d[..len].copy_from_slice(&b[..len]);
        ethnum::I256::from_le_bytes(d)
    }
    fn as_u256(&self) -> ethnum::U256 {
        let b = self.to_bytes_le();
        let mut d = [0u8; 32];
        let len = b.len().min(32);
        d[..len].copy_from_slice(&b[..len]);
        ethnum::U256::from_le_bytes(d)
    }
    fn as_int(&self) -> Int {
        BigInt::from_biguint(num_bigint::Sign::Plus, self.clone())
    }
    fn as_uint(&self) -> Uint { self.clone() }
    fn checked_mul(&self, other: &Self) -> Option<Self> { Some(self.clone() * other.clone()) }
    fn checked_add(&self, other: &Self) -> Option<Self> { Some(self.clone() + other.clone()) }
    fn checked_pow(&self, exp: u32) -> Option<Self> { Some(num_traits::pow::Pow::pow(self, exp)) }
    fn pow(&self, exp: u32) -> Self { num_traits::pow::Pow::pow(self, exp) }
    fn to_le_bytes(&self) -> Vec<u8> { self.to_bytes_le() }
}

pub trait IntExt: Sized {
    fn from_u64_ext(v: u64) -> Self;
    fn from_u32_ext(v: u32) -> Self;
    fn from_u128_ext(v: u128) -> Self;
    fn from_u256_ext(v: &ethnum::U256) -> Self;
    fn from_i256_ext(v: &ethnum::I256) -> Self;
    fn zero_ext() -> Self;
    fn one_ext() -> Self;
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
    fn from_u64_ext(v: u64) -> Self { Self::from(v) }
    fn from_u32_ext(v: u32) -> Self { Self::from(v) }
    fn from_u128_ext(v: u128) -> Self { Self::from(v) }
    fn from_u256_ext(v: &ethnum::U256) -> Self {
        Self::from_bytes_le(num_bigint::Sign::Plus, &v.to_le_bytes())
    }
    fn from_i256_ext(v: &ethnum::I256) -> Self {
        let mut val = *v;
        let sign = if v.is_negative() {
            val = -val;
            num_bigint::Sign::Minus
        } else {
            num_bigint::Sign::Plus
        };
        Self::from_bytes_le(sign, &val.to_le_bytes())
    }
    fn zero_ext() -> Self { <Self as Zero>::zero() }
    fn one_ext() -> Self { <Self as One>::one() }
    fn as_u128(&self) -> u128 { self.to_u128().unwrap_or(0) }
    fn as_u64(&self) -> u64 { self.to_u64().unwrap_or(0) }
    fn as_u32(&self) -> u32 { self.to_u32().unwrap_or(0) }
    fn as_usize(&self) -> usize { self.to_usize().unwrap_or(0) }
    fn as_i256(&self) -> ethnum::I256 {
        let (_sign, b) = self.to_bytes_le();
        let mut d = [0u8; 32];
        let len = b.len().min(32);
        d[..len].copy_from_slice(&b[..len]);
        let mut val = ethnum::I256::from_le_bytes(d);
        if self.sign() == num_bigint::Sign::Minus {
            val = -val;
        }
        val
    }
    fn as_u256(&self) -> ethnum::U256 {
        let (_sign, b) = self.to_bytes_le();
        let mut d = [0u8; 32];
        let len = b.len().min(32);
        d[..len].copy_from_slice(&b[..len]);
        ethnum::U256::from_le_bytes(d)
    }
    fn as_uint(&self) -> Uint {
        self.to_biguint().unwrap_or(Uint::zero_ext())
    }
    fn as_int(&self) -> Int { self.clone() }
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
    pub factors: SmallVec<[u64; 16]>,
    pub sigma_factors: Vec<Uint>,
}
