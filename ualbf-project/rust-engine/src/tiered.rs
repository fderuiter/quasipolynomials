use num_bigint::BigUint;
use std::fmt;

#[derive(Clone, Debug)]
pub enum TieredUint {
    Fast(ethnum::U256),
    Arbitrary(BigUint),
}

impl TieredUint {
    pub fn new_fast(v: ethnum::U256) -> Self {
        TieredUint::Fast(v)
    }

    pub fn new_arbitrary(v: BigUint) -> Self {
        TieredUint::Arbitrary(v)
    }

    pub fn from_u256(v: ethnum::U256) -> Self {
        TieredUint::Fast(v)
    }

    pub fn is_even(&self) -> bool {
        match self {
            TieredUint::Fast(v) => (v & ethnum::U256::ONE) == ethnum::U256::ZERO,
            TieredUint::Arbitrary(v) => num_integer::Integer::is_even(v),
        }
    }

    pub fn checked_mul(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (TieredUint::Fast(a), TieredUint::Fast(b)) => {
                if let Some(res) = a.checked_mul(*b) {
                    #[cfg(debug_assertions)]
                    {
                        let big_res = BigUint::from_bytes_le(&a.to_le_bytes()) * BigUint::from_bytes_le(&b.to_le_bytes());
                        assert_eq!(BigUint::from_bytes_le(&res.to_le_bytes()), big_res, "Precision loss detected during overlap validation!");
                    }
                    Some(TieredUint::Fast(res))
                } else {
                    Some(TieredUint::Arbitrary(BigUint::from_bytes_le(&a.to_le_bytes()) * BigUint::from_bytes_le(&b.to_le_bytes())))
                }
            }
            (TieredUint::Fast(a), TieredUint::Arbitrary(b)) => {
                Some(TieredUint::Arbitrary(BigUint::from_bytes_le(&a.to_le_bytes()) * b))
            }
            (TieredUint::Arbitrary(a), TieredUint::Fast(b)) => {
                Some(TieredUint::Arbitrary(a * BigUint::from_bytes_le(&b.to_le_bytes())))
            }
            (TieredUint::Arbitrary(a), TieredUint::Arbitrary(b)) => {
                Some(TieredUint::Arbitrary(a * b))
            }
        }
    }

    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (TieredUint::Fast(a), TieredUint::Fast(b)) => {
                if let Some(res) = a.checked_add(*b) {
                    Some(TieredUint::Fast(res))
                } else {
                    Some(TieredUint::Arbitrary(BigUint::from_bytes_le(&a.to_le_bytes()) + BigUint::from_bytes_le(&b.to_le_bytes())))
                }
            }
            (TieredUint::Fast(a), TieredUint::Arbitrary(b)) => {
                Some(TieredUint::Arbitrary(BigUint::from_bytes_le(&a.to_le_bytes()) + b))
            }
            (TieredUint::Arbitrary(a), TieredUint::Fast(b)) => {
                Some(TieredUint::Arbitrary(a + BigUint::from_bytes_le(&b.to_le_bytes())))
            }
            (TieredUint::Arbitrary(a), TieredUint::Arbitrary(b)) => {
                Some(TieredUint::Arbitrary(a + b))
            }
        }
    }
}

impl std::ops::Div for &TieredUint {
    type Output = TieredUint;
    fn div(self, rhs: Self) -> TieredUint {
        match (self, rhs) {
            (TieredUint::Fast(a), TieredUint::Fast(b)) => TieredUint::Fast(a / b),
            (TieredUint::Fast(a), TieredUint::Arbitrary(b)) => TieredUint::Arbitrary(BigUint::from_bytes_le(&a.to_le_bytes()) / b),
            (TieredUint::Arbitrary(a), TieredUint::Fast(b)) => TieredUint::Arbitrary(a / BigUint::from_bytes_le(&b.to_le_bytes())),
            (TieredUint::Arbitrary(a), TieredUint::Arbitrary(b)) => TieredUint::Arbitrary(a / b),
        }
    }
}

impl std::ops::Rem for &TieredUint {
    type Output = TieredUint;
    fn rem(self, rhs: Self) -> TieredUint {
        match (self, rhs) {
            (TieredUint::Fast(a), TieredUint::Fast(b)) => TieredUint::Fast(a % b),
            (TieredUint::Fast(a), TieredUint::Arbitrary(b)) => TieredUint::Arbitrary(BigUint::from_bytes_le(&a.to_le_bytes()) % b),
            (TieredUint::Arbitrary(a), TieredUint::Fast(b)) => TieredUint::Arbitrary(a % BigUint::from_bytes_le(&b.to_le_bytes())),
            (TieredUint::Arbitrary(a), TieredUint::Arbitrary(b)) => TieredUint::Arbitrary(a % b),
        }
    }
}

impl std::cmp::PartialEq for TieredUint {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TieredUint::Fast(a), TieredUint::Fast(b)) => a == b,
            (TieredUint::Fast(a), TieredUint::Arbitrary(b)) => &BigUint::from_bytes_le(&a.to_le_bytes()) == b,
            (TieredUint::Arbitrary(a), TieredUint::Fast(b)) => a == &BigUint::from_bytes_le(&b.to_le_bytes()),
            (TieredUint::Arbitrary(a), TieredUint::Arbitrary(b)) => a == b,
        }
    }
}

impl std::cmp::PartialOrd for TieredUint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (TieredUint::Fast(a), TieredUint::Fast(b)) => a.partial_cmp(b),
            (TieredUint::Fast(a), TieredUint::Arbitrary(b)) => BigUint::from_bytes_le(&a.to_le_bytes()).partial_cmp(b),
            (TieredUint::Arbitrary(a), TieredUint::Fast(b)) => a.partial_cmp(&BigUint::from_bytes_le(&b.to_le_bytes())),
            (TieredUint::Arbitrary(a), TieredUint::Arbitrary(b)) => a.partial_cmp(b),
        }
    }
}

impl fmt::Display for TieredUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TieredUint::Fast(v) => write!(f, "{}", v),
            TieredUint::Arbitrary(v) => write!(f, "{}", v),
        }
    }
}

impl std::cmp::PartialEq<ethnum::U256> for TieredUint {
    fn eq(&self, other: &ethnum::U256) -> bool {
        match self {
            TieredUint::Fast(v) => v == other,
            TieredUint::Arbitrary(v) => v == &BigUint::from_bytes_le(&other.to_le_bytes()),
        }
    }
}

impl std::cmp::PartialOrd<ethnum::U256> for TieredUint {
    fn partial_cmp(&self, other: &ethnum::U256) -> Option<std::cmp::Ordering> {
        match self {
            TieredUint::Fast(v) => v.partial_cmp(other),
            TieredUint::Arbitrary(v) => v.partial_cmp(&BigUint::from_bytes_le(&other.to_le_bytes())),
        }
    }
}

impl std::cmp::PartialEq<TieredUint> for ethnum::U256 {
    fn eq(&self, other: &TieredUint) -> bool {
        other == self
    }
}

impl std::cmp::PartialOrd<TieredUint> for ethnum::U256 {
    fn partial_cmp(&self, other: &TieredUint) -> Option<std::cmp::Ordering> {
        match other {
            TieredUint::Fast(v) => self.partial_cmp(v),
            TieredUint::Arbitrary(v) => BigUint::from_bytes_le(&self.to_le_bytes()).partial_cmp(v),
        }
    }
}

impl TieredUint {
    pub fn to_biguint(&self) -> BigUint {
        match self {
            TieredUint::Fast(v) => BigUint::from_bytes_le(&v.to_le_bytes()),
            TieredUint::Arbitrary(v) => v.clone(),
        }
    }
}
