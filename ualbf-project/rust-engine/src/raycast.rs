use num_integer::Roots;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::math_utils::{mod_inverse, compute_sigma, composite_tonelli_shanks};
use crate::types::{Prefix, Uint, Int};

/// Precomputes primes whose squares yield sigma ≡ 5 or 7 mod 8
pub fn generate_illegal_valuation_primes(limit: u64) -> Vec<u64> {
    let mut illegal = Vec::new();
    for p in 3..limit {
        let mut is_prime = true;
        let mut d = 2;
        while d * d <= p {
            if p % d == 0 { is_prime = false; break; }
            d += 1;
        }
        if !is_prime { continue; }
        
        // sigma(p^2) = p^2 + p + 1. If this is 5 or 7 mod 8, p^2 is illegal.
        let sig_mod_8 = (p * p + p + 1) % 8;
        if sig_mod_8 == 5 || sig_mod_8 == 7 {
            illegal.push(p);
        }
    }
    illegal
}

pub fn phase4_exact_ray_casting(prefix: &Prefix, target_max: &Uint, illegal_primes: &[u64], pruned_count: &AtomicUsize) {
    let n_l_int = prefix.n_l as Int;
    let s_l_int = prefix.s_l as Int;
    let two: Int = 2;

    let two_n_l = (two * n_l_int) % s_l_int;
    if let Some(x_l) = mod_inverse(-two_n_l, s_l_int) {
        
        let roots = composite_tonelli_shanks(x_l, &prefix.sigma_factors);
        let max_n_int = *target_max as Int;
        let z_max = (max_n_int / n_l_int).sqrt();
        let c_max = (z_max / s_l_int) as usize;
        
        let min_n_int = 10_u128.pow(34) as Int;
        let z_min = if min_n_int > n_l_int {
            (min_n_int / n_l_int).sqrt()
        } else {
            0
        };

        for r_i in roots {
            let c_min = if z_min > r_i {
                ((z_min - r_i + s_l_int - 1) / s_l_int) as usize
            } else {
                0
            };
            
            for c in c_min..=c_max {
                let z = r_i + (c as Int) * s_l_int;
                
                let mut passed_sieve = true;
                for &p in illegal_primes {
                    let p2_bi = (p * p) as Int;
                    let r_p2 = (z % p2_bi) as u64;
                    
                    if r_p2 % p == 0 && r_p2 != 0 {
                        passed_sieve = false;
                        pruned_count.fetch_add(1, Ordering::Relaxed);
                        break;
                    }
                }
                
                if !passed_sieve { continue; }

                let mut is_coprime = true;
                for &p in &prefix.factors {
                    if z % (p as Int) == 0 {
                        is_coprime = false;
                        break;
                    }
                }
                if !is_coprime { continue; }

                let z_biguint = z as Uint;
                let n_r = z_biguint * z_biguint;
                let total_n = prefix.n_l * n_r;

                let z_factors = crate::math_utils::quick_factor_u128(z_biguint);
                let mut s_r: Uint = 1;
                let mut current_p = 0;
                let mut count: u32 = 0;
                
                for &f in &z_factors {
                    if f == current_p {
                        count += 1;
                    } else {
                        if current_p != 0 {
                            s_r *= compute_sigma(current_p as Uint, 2 * count);
                        }
                        current_p = f;
                        count = 1;
                    }
                }
                if current_p != 0 {
                    s_r *= compute_sigma(current_p as Uint, 2 * count);
                }

                if s_r * prefix.s_l == total_n * 2 + 1 {
                    println!(">>> QUASIPERFECT NUMBER FOUND: {} <<<", total_n);
                    std::process::exit(0);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_illegal_valuation_primes() {
        let illegal = generate_illegal_valuation_primes(20);
        // Expected to flag 3, 5, 11, 13, 19
        assert_eq!(illegal, vec![3, 5, 11, 13, 19]);
    }
}