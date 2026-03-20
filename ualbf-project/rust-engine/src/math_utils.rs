use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{Zero, One};

pub fn mod_inverse(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    let egcd = a.extended_gcd(m);
    if egcd.gcd.is_one() {
        let mut res = egcd.x % m;
        if res < BigInt::zero() { res += m; }
        Some(res)
    } else {
        None
    }
}

pub fn compute_sigma(p: &BigUint, pow: u32) -> BigUint {
    let p_pow = p.pow(pow + 1);
    (&p_pow - BigUint::one()) / (p - BigUint::one())
}

// Emulates ECM factorization. In production, hook this to GMP/ECM via `rug` crate.
pub fn quick_factor(mut n: BigUint) -> Vec<BigUint> {
    let mut factors = Vec::new();
    let two = BigUint::from(2u32);
    let mut d = BigUint::from(3u32);
    while (&n % &two).is_zero() { n /= &two; }
    while &d * &d <= n && d < BigUint::from(100_000u32) {
        while (&n % &d).is_zero() {
            factors.push(d.clone());
            n /= &d;
        }
        d += &two;
    }
    if n > BigUint::one() { factors.push(n); }
    factors
}
