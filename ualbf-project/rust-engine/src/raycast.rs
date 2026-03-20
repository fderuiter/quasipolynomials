use num_bigint::{BigInt, BigUint, ToBigUint, ToBigInt};
use num_traits::ToPrimitive;
use crate::math_utils::{mod_inverse, compute_sigma, composite_tonelli_shanks};
use crate::types::Prefix;

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

pub fn phase4_exact_ray_casting(prefix: &Prefix, target_max: &BigUint) {
    let n_l_int = prefix.n_l.to_bigint().unwrap();
    let s_l_int = prefix.s_l.to_bigint().unwrap();
    let two = BigInt::from(2);

    let two_n_l = (&two * &n_l_int) % &s_l_int;
    if let Some(x_l) = mod_inverse(&(-&two_n_l), &s_l_int) {
        
        let roots = composite_tonelli_shanks(&x_l, &s_l_int);
        let max_n_int = target_max.to_bigint().unwrap();
        let z_max = (&max_n_int / &n_l_int).sqrt();
        let c_max = (&z_max / &s_l_int).to_usize().unwrap_or(10_000_000);

        let illegal_primes = generate_illegal_valuation_primes(100);

        for r_i in roots {
            let mut valid_c = vec![true; c_max + 1];
            
            // Fast Raycast Scan with O(1) Exact Valuation Sieve
            for c in 0..=c_max {
                if !valid_c[c] { continue; }
                let z = &r_i + BigInt::from(c) * &s_l_int;
                
                // Continuous modulo filter for illegal primes
                let mut passed_sieve = true;
                for &p in &illegal_primes {
                    // Using fast integer casting where applicable
                    let p2_bi = BigInt::from(p * p);
                    let r_p2 = (&z % &p2_bi).to_u64().unwrap();
                    
                    // Filter logic: z ≡ c * p mod p^2
                    // This means p exactly divides z (valuation 1), so p^2 exactly divides z^2.
                    // This forces sigma(z^2) to have a prime factor congruent to 5 or 7 mod 8.
                    if r_p2 % p == 0 && r_p2 != 0 {
                        passed_sieve = false;
                        break;
                    }
                }
                
                if !passed_sieve { continue; }

                let z_biguint = z.to_biguint().unwrap();
                let n_r = &z_biguint * &z_biguint;
                let total_n = &prefix.n_l * &n_r;

                if compute_sigma(&z_biguint, 2) * &prefix.s_l == &total_n * 2u32 + 1u32 {
                    println!(">>> QUASIPERFECT NUMBER FOUND: {} <<<", total_n);
                    std::process::exit(0);
                }
            }
        }
    }
}
