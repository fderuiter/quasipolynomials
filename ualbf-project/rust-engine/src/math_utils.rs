use std::collections::HashMap;
use crate::types::{Int, Uint};

pub fn mul_mod_u128(mut a: u128, mut b: u128, m: u128) -> u128 {
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

pub fn add_mod_u128(a: u128, b: u128, m: u128) -> u128 {
    debug_assert!(m > 0, "modulo must be strictly positive");
    let a = a % m;
    let b = b % m;
    if a >= m - b { a - (m - b) } else { a + b }
}

pub fn modpow_u128(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    if modulus <= 1 { return 0; }
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

pub fn pollards_rho_u128(n: u128, c_val: u128) -> Option<u128> {
    if n % 2 == 0 { return Some(2); }
    let mut x = 2;
    let mut y = 2;
    let mut d = 1;
    let f = |val: u128, n_mod: u128| -> u128 {
        add_mod_u128(mul_mod_u128(val, val, n_mod), c_val, n_mod)
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
    factors.sort_unstable();
    factors
}

pub fn extended_gcd(a: Int, b: Int) -> (Int, Int, Int) {
    let mut s = 0;
    let mut old_s = 1;
    let mut t = 1;
    let mut old_t = 0;
    let mut r = b;
    let mut old_r = a;

    while r != 0 {
        let quotient = old_r / r;
        let temp_r = r;
        r = old_r - quotient * r;
        old_r = temp_r;

        let temp_s = s;
        s = old_s - quotient * s;
        old_s = temp_s;

        let temp_t = t;
        t = old_t - quotient * t;
        old_t = temp_t;
    }
    (old_r, old_s, old_t) // gcd, x, y
}

pub fn mod_inverse(a: Int, m: Int) -> Option<Int> {
    let mut a_pos = a % m;
    if a_pos < 0 { a_pos += m; }
    let (g, x, _) = extended_gcd(a_pos, m);
    if g.abs() == 1 {
        let mut res = x % m;
        if res < 0 { res += m; }
        Some(res)
    } else {
        None
    }
}

pub fn compute_sigma(p: Uint, pow: u32) -> Uint {
    let mut sum: Uint = 1;
    let mut term: Uint = 1;
    for _ in 0..pow {
        term *= p;
        sum += term;
    }
    sum
}

pub fn solve_crt(residues: &[Int], moduli: &[Int]) -> Option<Int> {
    let mut total_mod = 1;
    for &m in moduli {
        total_mod *= m;
    }
    
    let mut x: Int = 0;
    for (&r, &m) in residues.iter().zip(moduli.iter()) {
        let m_i = total_mod / m;
        if let Some(y_i) = mod_inverse(m_i, m) {
            let mut r_pos = r % total_mod;
            if r_pos < 0 { r_pos += total_mod; }
            let mut y_i_pos = y_i % total_mod;
            if y_i_pos < 0 { y_i_pos += total_mod; }

            let term1 = mul_mod_u128(r_pos as u128, y_i_pos as u128, total_mod as u128);
            let term2 = mul_mod_u128(term1, m_i as u128, total_mod as u128) as Int;
            x = (x + term2) % total_mod;
        } else {
            return None;
        }
    }
    if x < 0 { x += total_mod; }
    Some(x)
}

pub fn tonelli_shanks(n: Int, p: Int) -> Option<Int> {
    let mut n_mod_p = n % p;
    if n_mod_p < 0 { n_mod_p += p; }

    if n_mod_p == 0 { return Some(0); }
    if p == 2 { return Some(n_mod_p); }

    let p_minus_one = p - 1;
    let mut q = p_minus_one;
    let mut s = 0u32;
    while q % 2 == 0 {
        q /= 2;
        s += 1;
    }

    if modpow_u128(n_mod_p as u128, (p_minus_one / 2) as u128, p as u128) != 1 {
        return None;
    }

    let mut z = 2;
    while modpow_u128(z as u128, (p_minus_one / 2) as u128, p as u128) != p_minus_one as u128 {
        z += 1;
    }

    let mut m = s;
    let mut c = modpow_u128(z as u128, q as u128, p as u128) as Int;
    let mut t = modpow_u128(n_mod_p as u128, q as u128, p as u128) as Int;
    let mut r = modpow_u128(n_mod_p as u128, ((q + 1) / 2) as u128, p as u128) as Int;

    loop {
        if t == 0 { return Some(0); }
        if t == 1 { return Some(r); }

        let mut t2i = t;
        let mut i = 0u32;
        while i < m {
            if t2i == 1 { break; }
            t2i = mul_mod_u128(t2i as u128, t2i as u128, p as u128) as Int;
            i += 1;
        }

        if i == m { return None; }

        let exp = 1u32 << (m - i - 1);
        let b = modpow_u128(c as u128, exp as u128, p as u128) as Int;
        
        m = i;
        c = mul_mod_u128(b as u128, b as u128, p as u128) as Int;
        t = mul_mod_u128(t as u128, c as u128, p as u128) as Int;
        r = mul_mod_u128(r as u128, b as u128, p as u128) as Int;
    }
}

pub fn hensels_lift(root: Int, n: Int, p: Int, k: u32) -> Int {
    let mut current_r = root;
    let mut current_mod = p;
    
    for _ in 1..k {
        current_mod *= p;
        
        let r_sqr = mul_mod_u128(current_r as u128, current_r as u128, current_mod as u128) as Int;
        let mut diff = (r_sqr - n) % current_mod;
        if diff < 0 { diff += current_mod; }
        
        let two_r = (2 * current_r) % current_mod;
        
        if let Some(inv_two_r) = mod_inverse(two_r, current_mod) {
            let adjustment = mul_mod_u128(diff as u128, inv_two_r as u128, current_mod as u128) as Int;
            current_r = (current_r - adjustment) % current_mod;
            if current_r < 0 { current_r += current_mod; }
        } else {
            break;
        }
    }
    current_r
}

pub fn composite_tonelli_shanks(n: Int, m_factors: &[Uint]) -> Vec<Int> {
    let mut prime_counts: HashMap<Int, u32> = HashMap::new();
    for &f in m_factors {
        *prime_counts.entry(f as Int).or_insert(0) += 1;
    }
    
    let mut moduli = Vec::new();
    let mut prime_roots = Vec::new();

    for (p, k) in prime_counts {
        let p_pow_k = p.pow(k);
        let mut p_roots = Vec::new();
        
        if let Some(r) = tonelli_shanks(n, p) {
            let r_lifted = hensels_lift(r, n, p, k);
            p_roots.push(r_lifted);
            
            let mut neg_r = p_pow_k - r_lifted;
            neg_r %= p_pow_k;
            if neg_r != r_lifted {
                p_roots.push(neg_r);
            }
        } else {
            return vec![]; // System has no roots
        }
        
        prime_roots.push(p_roots);
        moduli.push(p_pow_k);
    }
    
    let mut all_roots = vec![];
    let mut indices = vec![0; prime_roots.len()];
    
    if prime_roots.is_empty() { return all_roots; }

    loop {
        let current_residues: Vec<Int> = indices.iter().enumerate()
            .map(|(i, &idx)| prime_roots[i][idx])
            .collect();
        
        if let Some(combined_root) = solve_crt(&current_residues, &moduli) {
            all_roots.push(combined_root);
        }
        
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
        if carry { break; }
    }
    all_roots
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mod_inverse() {
        assert_eq!(mod_inverse(3, 11), Some(4));
        assert_eq!(mod_inverse(2, 10), None);
    }

    #[test]
    fn test_compute_sigma() {
        assert_eq!(compute_sigma(2, 2), 7);
        assert_eq!(compute_sigma(3, 1), 4);
    }

    #[test]
    fn test_solve_crt() {
        let residues = vec![2, 3, 2];
        let moduli = vec![3, 5, 7];
        assert_eq!(solve_crt(&residues, &moduli), Some(23));

        let residues_neg = vec![-1, -2, -5];
        assert_eq!(solve_crt(&residues_neg, &moduli), Some(23));
    }

    #[test]
    fn test_is_prime_u128() {
        assert!(is_prime_u128(17, 10));
        assert!(is_prime_u128(997, 10));
        assert!(!is_prime_u128(15, 10));
        assert!(!is_prime_u128(100, 10));
    }

    #[test]
    fn test_quick_factor_u128() {
        let factors = quick_factor_u128(15);
        assert_eq!(factors, vec![3, 5]);

        let factors2 = quick_factor_u128(28);
        assert_eq!(factors2, vec![2, 2, 7]);
    }

    #[test]
    fn test_tonelli_shanks() {
        let root = tonelli_shanks(2, 7).unwrap();
        assert!(root == 3 || root == 4);
        assert_eq!(tonelli_shanks(3, 7), None);
    }
}
