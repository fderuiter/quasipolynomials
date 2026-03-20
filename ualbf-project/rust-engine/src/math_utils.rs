use num_bigint::{BigInt, BigUint, ToBigInt};
use num_integer::Integer;
use num_traits::{Zero, One, Signed};
use std::collections::HashMap;

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

pub fn solve_crt(residues: &[BigInt], moduli: &[BigInt]) -> Option<BigInt> {
    let mut total_mod = BigInt::one();
    for m in moduli {
        total_mod *= m;
    }
    
    let mut x = BigInt::zero();
    for (r, m) in residues.iter().zip(moduli.iter()) {
        let m_i = &total_mod / m;
        if let Some(y_i) = mod_inverse(&m_i, m) {
            x = (x + r * y_i * m_i) % &total_mod;
        } else {
            return None;
        }
    }
    if x < BigInt::zero() {
        x += &total_mod;
    }
    Some(x)
}

pub fn tonelli_shanks(n: &BigInt, p: &BigInt) -> Option<BigInt> {
    let zero = BigInt::zero();
    let one = BigInt::one();
    let two = BigInt::from(2);
    
    let mut n_mod_p = n % p;
    if n_mod_p < zero { n_mod_p += p; }

    if n_mod_p.is_zero() { return Some(zero); }
    if p == &two { return Some(n_mod_p); }

    let p_minus_one = p - &one;
    let mut q = p_minus_one.clone();
    let mut s = 0u32;
    while (&q % &two).is_zero() {
        q /= &two;
        s += 1;
    }

    if n_mod_p.modpow(&(&p_minus_one / &two), p) != one {
        return None;
    }

    let mut z = BigInt::from(2);
    while z.modpow(&(&p_minus_one / &two), p) != p_minus_one {
        z += &one;
    }

    let mut m = s;
    let mut c = z.modpow(&q, p);
    let mut t = n_mod_p.modpow(&q, p);
    let mut r = n_mod_p.modpow(&((&q + &one) / &two), p);

    loop {
        if t == zero { return Some(zero); }
        if t == one { return Some(r); }

        let mut t2i = t.clone();
        let mut i = 0u32;
        while i < m {
            if t2i == one { break; }
            t2i = t2i.modpow(&two, p);
            i += 1;
        }

        if i == m { return None; }

        let mut exp = one.clone();
        for _ in 0..(m - i - 1) { exp *= &two; }
        
        let b = c.modpow(&exp, p);
        m = i;
        c = b.modpow(&two, p);
        t = (t * &c) % p;
        r = (r * b) % p;
    }
}

pub fn hensels_lift(root: &BigInt, n: &BigInt, p: &BigInt, k: u32) -> BigInt {
    let mut current_r = root.clone();
    let mut current_mod = p.clone();
    let two = BigInt::from(2);
    
    for _ in 1..k {
        current_mod *= p;
        
        let r_sqr = (&current_r * &current_r) % &current_mod;
        let diff = (&r_sqr - n) % &current_mod;
        let mut diff_pos = diff;
        if diff_pos < BigInt::zero() { diff_pos += &current_mod; }
        
        let two_r = (&two * &current_r) % &current_mod;
        
        if let Some(inv_two_r) = mod_inverse(&two_r, &current_mod) {
            let adjustment = (diff_pos * inv_two_r) % &current_mod;
            current_r = (&current_r - adjustment) % &current_mod;
            if current_r < BigInt::zero() {
                current_r += &current_mod;
            }
        } else {
            break;
        }
    }
    current_r
}

pub fn composite_tonelli_shanks(n: &BigInt, composite_m: &BigInt) -> Vec<BigInt> {
    let m_biguint = composite_m.abs().to_biguint().unwrap();
    let prime_factors = quick_factor(m_biguint);
    
    let mut prime_counts: HashMap<BigInt, u32> = HashMap::new();
    for f in prime_factors {
        let f_bi = f.to_bigint().unwrap();
        *prime_counts.entry(f_bi).or_insert(0) += 1;
    }
    
    let mut moduli = Vec::new();
    let mut prime_roots = Vec::new();

    for (p, k) in prime_counts {
        let p_pow_k = p.pow(k);
        let mut p_roots = Vec::new();
        
        if let Some(r) = tonelli_shanks(n, &p) {
            let r_lifted = hensels_lift(&r, n, &p, k);
            p_roots.push(r_lifted.clone());
            
            let mut neg_r = &p_pow_k - &r_lifted;
            neg_r %= &p_pow_k;
            if neg_r != r_lifted {
                p_roots.push(neg_r);
            }
        } else {
            return vec![]; // System has no roots
        }
        
        prime_roots.push(p_roots);
        moduli.push(p_pow_k);
    }
    
    // Cartesian product of roots across all prime powers
    let mut all_roots: Vec<BigInt> = vec![];
    let mut indices = vec![0; prime_roots.len()];
    
    if prime_roots.is_empty() { return all_roots; }

    loop {
        let current_residues: Vec<BigInt> = indices.iter().enumerate()
            .map(|(i, &idx)| prime_roots[i][idx].clone())
            .collect();
        
        if let Some(combined_root) = solve_crt(&current_residues, &moduli) {
            all_roots.push(combined_root);
        }
        
        // Increment indices
        let mut carry = true;
        for i in 0..prime_roots.len() {
            if carry {
                indices[i] += 1;
                if indices[i] >= prime_roots[i].len() {
                    indices[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry { break; } // Iterated over all combinations
    }
    
    all_roots
}
