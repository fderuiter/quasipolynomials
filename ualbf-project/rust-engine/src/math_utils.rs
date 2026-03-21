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

pub fn is_prime_biguint(n: &BigUint, k: u32) -> bool {
    let two = BigUint::from(2u32);
    let one = BigUint::one();
    let three = BigUint::from(3u32);
    
    if n <= &one { return false; }
    if n == &two || n == &three { return true; }
    if (n % &two).is_zero() { return false; }
    
    let mut d = n - &one;
    let mut r = 0;
    while (&d % &two).is_zero() {
        d /= &two;
        r += 1;
    }
    
    let bases: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    for &a_val in bases.iter().take(k as usize) {
        let a = BigUint::from(a_val);
        if &a >= n { break; }
        
        let mut x = a.modpow(&d, n);
        if x == one || x == n - &one { continue; }
        
        let mut composite = true;
        let n_minus_one = n - &one;
        for _ in 0..(r - 1) {
            x = (&x * &x) % n;
            if x == n_minus_one {
                composite = false;
                break;
            }
        }
        if composite { return false; }
    }
    true
}

fn pollards_rho(n: &BigUint, c_val: u32) -> Option<BigUint> {
    if (n % 2u32).is_zero() { return Some(BigUint::from(2u32)); }
    
    let mut x = BigUint::from(2u32);
    let mut y = BigUint::from(2u32);
    let mut d = BigUint::one();
    let c = BigUint::from(c_val);
    
    let f = |val: &BigUint, n_mod: &BigUint| -> BigUint {
        ((val * val) + &c) % n_mod
    };
    
    let mut i = 0;
    while d.is_one() {
        x = f(&x, n);
        y = f(&f(&y, n), n);
        
        let diff = if &x > &y { &x - &y } else { &y - &x };
        d = diff.gcd(n);
        
        i += 1;
        if i > 100_000 { break; } // limit iterations to avoid hang
        if d == *n { return None; }
    }
    if d.is_one() || d == *n { None } else { Some(d) }
}

// ----- u128 Fast Path Functions -----
fn add_mod_u128(a: u128, b: u128, m: u128) -> u128 {
    if a >= m - b { a - (m - b) } else { a + b }
}

fn mul_mod_u128(mut a: u128, mut b: u128, m: u128) -> u128 {
    if m <= 0xFFFFFFFFFFFFFFFF {
        return (a % m * (b % m)) % m;
    }
    let mut res = 0;
    a %= m;
    b %= m;
    while b > 0 {
        if b & 1 == 1 { res = add_mod_u128(res, a, m); }
        a = add_mod_u128(a, a, m);
        b >>= 1;
    }
    res
}

fn modpow_u128(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    if modulus <= 1 { return 0; }
    if modulus <= 0xFFFFFFFFFFFFFFFF {
        let mut result = 1;
        base %= modulus;
        while exp > 0 {
            if exp % 2 == 1 { result = (result * base) % modulus; }
            exp /= 2;
            base = (base * base) % modulus;
        }
        return result;
    }
    let mut result = 1;
    base %= modulus;
    while exp > 0 {
        if exp % 2 == 1 { result = mul_mod_u128(result, base, modulus); }
        exp /= 2;
        base = mul_mod_u128(base, base, modulus);
    }
    result
}

pub fn is_prime_u128(n: u128, k: u32) -> bool {
    if n <= 1 { return false; }
    if n == 2 || n == 3 { return true; }
    if n % 2 == 0 { return false; }
    let mut d = n - 1;
    let mut r = 0;
    while d % 2 == 0 { d /= 2; r += 1; }
    let bases: [u128; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    for &a in bases.iter().take(k as usize) {
        if a >= n { break; }
        let mut x = modpow_u128(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        let mut composite = true;
        for _ in 0..(r - 1) {
            x = mul_mod_u128(x, x, n);
            if x == n - 1 { composite = false; break; }
        }
        if composite { return false; }
    }
    true
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

fn pollards_rho_u128(n: u128, c_val: u128) -> Option<u128> {
    if n % 2 == 0 { return Some(2); }
    let mut x = 2;
    let mut y = 2;
    let mut d = 1;
    let c = c_val;
    let f = |val: u128, n_mod: u128| -> u128 {
        add_mod_u128(mul_mod_u128(val, val, n_mod), c, n_mod)
    };
    let mut i = 0;
    while d == 1 {
        x = f(x, n);
        y = f(f(y, n), n);
        let diff = if x > y { x - y } else { y - x };
        d = gcd_u128(diff, n);
        i += 1;
        if i > 150_000 { break; }
        if d == n { return None; }
    }
    if d == 1 || d == n { None } else { Some(d) }
}

pub fn quick_factor_u128(mut n: u128) -> Vec<u128> {
    let mut factors = Vec::new();
    while n % 2 == 0 { factors.push(2); n /= 2; }
    let mut queue = vec![n];
    while let Some(mut current) = queue.pop() {
        if current <= 1 { continue; }
        let mut d = 3;
        while d * d <= current && d < 100_000 {
            while current % d == 0 { factors.push(d); current /= d; }
            d += 2;
        }
        if current <= 1 { continue; }
        if is_prime_u128(current, 10) {
            factors.push(current);
        } else {
            let mut found = false;
            for c in 1..=5 {
                if let Some(divisor) = pollards_rho_u128(current, c) {
                    queue.push(divisor);
                    queue.push(current / divisor);
                    found = true;
                    break;
                }
            }
            if !found { factors.push(current); }
        }
    }
    factors.sort();
    factors
}
// ------------------------------------

pub fn quick_factor(mut n: BigUint) -> Vec<BigUint> {
    use std::convert::TryFrom;
    if let Ok(n_u128) = u128::try_from(&n) {
        return quick_factor_u128(n_u128).into_iter().map(BigUint::from).collect();
    }

    let mut factors = Vec::new();
    let two = BigUint::from(2u32);
    
    while (&n % &two).is_zero() {
        factors.push(two.clone());
        n /= &two;
    }
    
    let mut queue = vec![n];
    
    while let Some(mut current) = queue.pop() {
        if current <= BigUint::one() { continue; }
        
        let mut d = BigUint::from(3u32);
        while &d * &d <= current && d < BigUint::from(1000u32) {
            while (&current % &d).is_zero() {
                factors.push(d.clone());
                current /= &d;
            }
            d += &two;
        }
        
        if current <= BigUint::one() { continue; }
        
        if is_prime_biguint(&current, 10) {
            factors.push(current);
        } else {
            let mut found = false;
            for c in 1..=5 {
                if let Some(divisor) = pollards_rho(&current, c) {
                    queue.push(divisor.clone());
                    queue.push(current.clone() / divisor);
                    found = true;
                    break;
                }
            }
            if !found {
                factors.push(current);
            }
        }
    }
    
    factors.sort();
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

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    #[test]
    fn test_mod_inverse() {
        let a = BigInt::from(3);
        let m = BigInt::from(11);
        assert_eq!(mod_inverse(&a, &m), Some(BigInt::from(4))); // 3 * 4 = 12 = 1 mod 11
        
        let a_no_inv = BigInt::from(2);
        let m_even = BigInt::from(10);
        assert_eq!(mod_inverse(&a_no_inv, &m_even), None);
    }

    #[test]
    fn test_compute_sigma() {
        // sigma(2^2) = 1 + 2 + 4 = 7
        let p = BigUint::from(2u32);
        assert_eq!(compute_sigma(&p, 2), BigUint::from(7u32));
        
        // sigma(3^1) = 1 + 3 = 4
        let p3 = BigUint::from(3u32);
        assert_eq!(compute_sigma(&p3, 1), BigUint::from(4u32));
    }

    #[test]
    fn test_is_prime_biguint() {
        assert!(is_prime_biguint(&BigUint::from(17u32), 10));
        assert!(is_prime_biguint(&BigUint::from(997u32), 10));
        assert!(!is_prime_biguint(&BigUint::from(15u32), 10));
        assert!(!is_prime_biguint(&BigUint::from(100u32), 10));
    }

    #[test]
    fn test_quick_factor() {
        let n = BigUint::from(15u32); // 3 * 5
        let factors = quick_factor(n);
        assert_eq!(factors, vec![BigUint::from(3u32), BigUint::from(5u32)]);

        let n2 = BigUint::from(28u32); // 2 * 2 * 7
        let factors2 = quick_factor(n2);
        assert_eq!(factors2, vec![BigUint::from(2u32), BigUint::from(2u32), BigUint::from(7u32)]);
    }

    #[test]
    fn test_tonelli_shanks() {
        // x^2 = 2 mod 7. Roots are 3 and 4.
        let n = BigInt::from(2);
        let p = BigInt::from(7);
        let root = tonelli_shanks(&n, &p).unwrap();
        assert!(root == BigInt::from(3) || root == BigInt::from(4));
        
        // x^2 = 3 mod 7. No roots.
        let n_none = BigInt::from(3);
        assert_eq!(tonelli_shanks(&n_none, &p), None);
    }

    #[test]
    fn test_solve_crt() {
        // x = 2 mod 3
        // x = 3 mod 5
        // x = 2 mod 7
        // Result should be 23.
        let residues = vec![BigInt::from(2), BigInt::from(3), BigInt::from(2)];
        let moduli = vec![BigInt::from(3), BigInt::from(5), BigInt::from(7)];
        assert_eq!(solve_crt(&residues, &moduli), Some(BigInt::from(23)));
    }
}
