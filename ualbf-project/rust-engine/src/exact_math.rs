use crate::types::Uint;

#[derive(Clone, Debug, Copy)]
pub struct U512(pub Uint, pub Uint); // (hi, lo)

impl U512 {
    pub fn mul_u256(a: Uint, b: Uint) -> Self {
        let (a_hi, a_lo) = a.into_words();
        let (b_hi, b_lo) = b.into_words();

        let a_lo = Uint::from(a_lo);
        let a_hi = Uint::from(a_hi);
        let b_lo = Uint::from(b_lo);
        let b_hi = Uint::from(b_hi);

        let lo_lo = a_lo * b_lo;
        let hi_lo = a_hi * b_lo;
        let lo_hi = a_lo * b_hi;
        let hi_hi = a_hi * b_hi;

        let (mid_sum, carry1) = hi_lo.overflowing_add(lo_hi);
        let mid_sum_shifted_lo = mid_sum << 128;
        let mid_sum_shifted_hi = mid_sum >> 128;

        let (lo, carry2) = lo_lo.overflowing_add(mid_sum_shifted_lo);

        let mut hi = hi_hi + mid_sum_shifted_hi;
        if carry1 {
            hi += Uint::ONE << 128;
        }
        if carry2 {
            hi += Uint::ONE;
        }

        Self(hi, lo)
    }

    pub fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            std::cmp::Ordering::Equal => self.1.cmp(&other.1),
            other => other,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Rational {
    pub num: Uint,
    pub den: Uint,
}

impl Rational {
    pub fn new(num: Uint, den: Uint) -> Self {
        Self { num, den }
    }
    pub fn one() -> Self {
        Self {
            num: Uint::ONE,
            den: Uint::ONE,
        }
    }
    pub fn exact_mul(&self, other: &Self) -> Self {
        Self {
            num: self.num * other.num,
            den: self.den * other.den,
        }
    }

    pub fn as_f64(&self) -> f64 {
        self.num.as_f64() / self.den.as_f64()
    }
}
