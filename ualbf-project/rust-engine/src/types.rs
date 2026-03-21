pub type Uint = u128;
pub type Int = i128;

#[derive(Clone, Debug)]
pub struct PrimePower {
    pub p: u64,
    pub val: Uint,
    pub sigma: Uint,
    pub sigma_factors: Vec<Uint>,
    pub abundance_ratio: f64, // σ(p^{2e}) / p^{2e}
}

#[derive(Clone, Debug)]
pub struct Prefix {
    pub n_l: Uint,
    pub s_l: Uint,
    pub last_idx: usize,
    pub factors: Vec<u64>,
    pub sigma_factors: Vec<Uint>,
}
