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

pub trait Ring: Sized {
    fn add_mod(&self, other: &Self, m: &Self) -> Self;
    fn sub_mod(&self, other: &Self, m: &Self) -> Self;
    fn mul_mod(&self, other: &Self, m: &Self) -> Self;
    fn pow_mod(&self, exp: &Self, m: &Self) -> Self;
}

pub trait Field: Ring {
    fn inv_mod(&self, m: &Self) -> Option<Self>;
}

pub trait IntegerRoots: Sized {
    fn integer_sqrt(&self) -> Self;
}

impl Ring for Uint {
    fn add_mod(&self, other: &Self, m: &Self) -> Self {
        let a = self % m;
        let b = other % m;
        if a >= m - b {
            a - (m - b)
        } else {
            a + b
        }
    }
    
    fn sub_mod(&self, other: &Self, m: &Self) -> Self {
        let a = self % m;
        let b = other % m;
        if a >= b {
            a - b
        } else {
            m - (b - a)
        }
    }

    fn mul_mod(&self, other: &Self, m: &Self) -> Self {
        let mut a = *self;
        let mut b = *other;
        if *m <= Uint::from_u128(0xFFFFFFFFFFFFFFFFu128) {
            return (a % m * (b % m)) % m;
        }
        let mut res = Uint::zero();
        a %= m;
        b %= m;
        while b > Uint::zero() {
            if b & Uint::one() == Uint::one() {
                res = res.add_mod(&a, m);
            }
            a = a.add_mod(&a, m);
            b /= Uint::from_u32(2);
        }
        res
    }

    fn pow_mod(&self, exp: &Self, m: &Self) -> Self {
        if *m <= Uint::one() {
            return Uint::zero();
        }
        let mut result = Uint::one();
        let mut base = *self % m;
        let mut e = *exp;
        while e > Uint::zero() {
            if e % Uint::from_u32(2) == Uint::one() {
                result = result.mul_mod(&base, m);
            }
            base = base.mul_mod(&base, m);
            e /= Uint::from_u32(2);
        }
        result
    }
}

impl Field for Uint {
    fn inv_mod(&self, m: &Self) -> Option<Self> {
        if *m <= Uint::one() {
            return None;
        }
        let mut t = Uint::zero();
        let mut newt = Uint::one();
        let mut r = *m;
        let mut newr = *self % m;

        while newr != Uint::zero() {
            let q = r / newr;

            let temp_t = t;
            t = newt;
            let q_newt = q.mul_mod(&newt, m);
            newt = if temp_t >= q_newt {
                temp_t - q_newt
            } else {
                m - (q_newt - temp_t)
            };

            let temp_r = r;
            r = newr;
            newr = temp_r - q * newr;
        }

        if r > Uint::one() {
            return None;
        }
        Some(t)
    }
}

impl IntegerRoots for Uint {
    fn integer_sqrt(&self) -> Self {
        if *self == Uint::zero() {
            return Uint::zero();
        }
        let mut x = *self;
        let mut y = (x + Uint::one()) / Uint::from_u32(2);
        while y < x {
            x = y;
            y = (x + *self / x) / Uint::from_u32(2);
        }
        x
    }
}

impl Ring for Int {
    fn add_mod(&self, other: &Self, m: &Self) -> Self {
        let mut a = *self % m;
        if a < Int::zero() {
            a += m;
        }
        let mut b = *other % m;
        if b < Int::zero() {
            b += m;
        }
        (a.as_uint().add_mod(&b.as_uint(), &m.as_uint())).as_int()
    }
    
    fn sub_mod(&self, other: &Self, m: &Self) -> Self {
        let mut a = *self % m;
        if a < Int::zero() {
            a += m;
        }
        let mut b = *other % m;
        if b < Int::zero() {
            b += m;
        }
        (a.as_uint().sub_mod(&b.as_uint(), &m.as_uint())).as_int()
    }

    fn mul_mod(&self, other: &Self, m: &Self) -> Self {
        let mut a = *self % m;
        if a < Int::zero() {
            a += m;
        }
        let mut b = *other % m;
        if b < Int::zero() {
            b += m;
        }
        (a.as_uint().mul_mod(&b.as_uint(), &m.as_uint())).as_int()
    }

    fn pow_mod(&self, exp: &Self, m: &Self) -> Self {
        let mut a = *self % m;
        if a < Int::zero() {
            a += m;
        }
        (a.as_uint().pow_mod(&exp.as_uint(), &m.as_uint())).as_int()
    }
}

impl Field for Int {
    fn inv_mod(&self, m: &Self) -> Option<Self> {
        let mut a = *self % m;
        if a < Int::zero() {
            a += m;
        }
        a.as_uint().inv_mod(&m.as_uint()).map(|x| x.as_int())
    }
}

impl IntegerRoots for Int {
    fn integer_sqrt(&self) -> Self {
        if *self <= Int::zero() {
            return Int::zero();
        }
        let mut x = *self;
        let mut y = (x + Int::one()) / Int::from_u32(2);
        while y < x {
            x = y;
            y = (x + *self / x) / Int::from_u32(2);
        }
        x
    }
}
