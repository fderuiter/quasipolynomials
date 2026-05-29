use ethnum::{I256, U256};
use smallvec::SmallVec;

pub type Uint = U256;
pub type Int = I256;

#[derive(Clone, Debug)]
pub struct PrimePower {
    pub p: u64,
    pub two_e: u32,
    pub val: Uint,
    pub sigma: Uint,
    pub sigma_factors: Vec<Uint>,
    pub abundance_ratio: crate::exact_math::Rational, // σ(p^{2e}) / p^{2e}
}

#[derive(Clone, Debug)]
pub struct Prefix {
    pub n_l: Uint,
    pub s_l: Uint,
    pub last_idx: usize,
    /// Actual prime bases for coprimality checks in raycast.
    /// SmallVec avoids heap allocation for typical cases (≤16 factors).
    pub factors: SmallVec<[u64; 16]>,

    pub sigma_factors: Vec<Uint>,

    /// Tracks product(σ(p^{2e}) / p^{2e}) as a running fraction
    pub current_abundancy: crate::exact_math::Rational,
}
