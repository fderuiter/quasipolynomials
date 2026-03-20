use num_bigint::BigUint;

#[derive(Clone, Debug)]
pub struct PrimePower {
    pub p: u64,
    pub val: BigUint,
    pub sigma: BigUint,
}

#[derive(Clone, Debug)]
pub struct Prefix {
    pub n_l: BigUint,
    pub s_l: BigUint,
    pub last_idx: usize,
    pub factors: Vec<u64>,
}
