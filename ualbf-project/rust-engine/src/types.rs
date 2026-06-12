use smallvec::SmallVec;

pub type Uint = bnum::types::U512;
pub type Int = bnum::types::I512;
// No longer using ethnum types.

pub trait UintExt {
    fn from_u64(v: u64) -> Self;
    fn from_u32(v: u32) -> Self;
    fn from_u128(v: u128) -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn as_u128(&self) -> u128;
    fn as_u64(&self) -> u64;
    fn as_u32(&self) -> u32;
    fn as_usize(&self) -> usize;
    fn as_int(&self) -> Int;
    fn as_uint(&self) -> Uint;
}

impl UintExt for Uint {
    fn from_u64(v: u64) -> Self { Self::try_from(v).unwrap() }
    fn from_u32(v: u32) -> Self { Self::try_from(v).unwrap() }
    fn from_u128(v: u128) -> Self { Self::try_from(v).unwrap() }
    fn zero() -> Self { Self::try_from(0u32).unwrap() }
    fn one() -> Self { Self::try_from(1u32).unwrap() }
    fn as_u128(&self) -> u128 { (*self).try_into().unwrap() }
    fn as_u64(&self) -> u64 { (*self).try_into().unwrap() }
    fn as_u32(&self) -> u32 { (*self).try_into().unwrap() }
    fn as_usize(&self) -> usize { (*self).try_into().unwrap() }
    fn as_int(&self) -> Int { Int::from_le_bytes(self.to_le_bytes()) }
    fn as_uint(&self) -> Uint { *self }
}

pub trait IntExt {
    fn from_u64(v: u64) -> Self;
    fn from_u32(v: u32) -> Self;
    fn from_u128(v: u128) -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn as_u128(&self) -> u128;
    fn as_u64(&self) -> u64;
    fn as_u32(&self) -> u32;
    fn as_usize(&self) -> usize;
    fn as_int(&self) -> Int;
    fn as_uint(&self) -> Uint;
}

impl IntExt for Int {
    fn from_u64(v: u64) -> Self { Self::try_from(v).unwrap() }
    fn from_u32(v: u32) -> Self { Self::try_from(v).unwrap() }
    fn from_u128(v: u128) -> Self { Self::try_from(v).unwrap() }
    fn zero() -> Self { Self::try_from(0u32).unwrap() }
    fn one() -> Self { Self::try_from(1u32).unwrap() }
    fn as_u128(&self) -> u128 { (*self).try_into().unwrap() }
    fn as_u64(&self) -> u64 { (*self).try_into().unwrap() }
    fn as_u32(&self) -> u32 { (*self).try_into().unwrap() }
    fn as_usize(&self) -> usize { (*self).try_into().unwrap() }
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
    pub active_mask: Vec<u64>,
}

pub trait AlgebraicRing {
    fn add_mod(&self, other: &Self, modulus: &Self) -> Self;
    fn sub_mod(&self, other: &Self, modulus: &Self) -> Self;
    fn mul_mod(&self, other: &Self, modulus: &Self) -> Self;
    fn rem_euclid_val(&self, modulus: &Self) -> Self;
}

impl AlgebraicRing for Int {
    fn rem_euclid_val(&self, modulus: &Self) -> Self {
        let mut r = *self % *modulus;
        if r < Int::zero() {
            r += *modulus;
        }
        r
    }
    fn add_mod(&self, other: &Self, modulus: &Self) -> Self {
        (*self + *other).rem_euclid_val(modulus)
    }
    fn sub_mod(&self, other: &Self, modulus: &Self) -> Self {
        (*self - *other).rem_euclid_val(modulus)
    }
    fn mul_mod(&self, other: &Self, modulus: &Self) -> Self {
        (*self * *other).rem_euclid_val(modulus)
    }
}

impl AlgebraicRing for Uint {
    fn rem_euclid_val(&self, modulus: &Self) -> Self {
        *self % *modulus
    }
    fn add_mod(&self, other: &Self, modulus: &Self) -> Self {
        (*self + *other) % *modulus
    }
    fn sub_mod(&self, other: &Self, modulus: &Self) -> Self {
        let mut res = *self;
        if res < *other {
            res += *modulus;
        }
        (res - *other) % *modulus
    }
    fn mul_mod(&self, other: &Self, modulus: &Self) -> Self {
        (*self * *other) % *modulus
    }
}

pub trait IntegerMath {
    fn isqrt_val(&self) -> Option<Self> where Self: Sized;
    fn trial_divide(&self, limit: u32) -> (Vec<Self>, Self) where Self: Sized;
}

impl IntegerMath for Uint {
    fn isqrt_val(&self) -> Option<Self> {
        if *self == Self::zero() {
            return Some(Self::zero());
        }
        let mut x = *self;
        let mut y = (x + Self::one()) / Self::from_u32(2);
        while y < x {
            x = y;
            y = (x + *self / x) / Self::from_u32(2);
        }
        Some(x)
    }

    fn trial_divide(&self, limit: u32) -> (Vec<Self>, Self) {
        let mut remaining = *self;
        let mut factors = Vec::new();
        for &p_u32 in &[2u32, 3, 5, 7, 11, 13] {
            let p = Uint::from_u32(p_u32);
            while remaining % p == Uint::zero() {
                factors.push(p);
                remaining /= p;
            }
        }
        let mut d = Uint::from_u32(17);
        let limit_big = Uint::from_u32(limit);
        while d * d <= remaining && d < limit_big {
            while remaining % d == Uint::zero() {
                factors.push(d);
                remaining /= d;
            }
            d += Uint::from_u32(2);
            while remaining % d == Uint::zero() {
                factors.push(d);
                remaining /= d;
            }
            d += Uint::from_u32(4);
        }
        (factors, remaining)
    }
}

impl IntegerMath for Int {
    fn isqrt_val(&self) -> Option<Self> {
        if *self < Self::zero() {
            return None;
        }
        if *self == Self::zero() {
            return Some(Self::zero());
        }
        let mut x = *self;
        let mut y = (x + Self::one()) / Self::from_u32(2);
        while y < x {
            x = y;
            y = (x + *self / x) / Self::from_u32(2);
        }
        Some(x)
    }

    fn trial_divide(&self, _limit: u32) -> (Vec<Self>, Self) {
        unimplemented!()
    }
}
