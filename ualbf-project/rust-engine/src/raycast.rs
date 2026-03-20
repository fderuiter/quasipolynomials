use num_bigint::{BigInt, BigUint, ToBigUint, ToBigInt};
use num_traits::ToPrimitive;
use crate::math_utils::{mod_inverse, compute_sigma};
use crate::types::Prefix;

pub fn phase4_exact_ray_casting(prefix: &Prefix, target_max: &BigUint) {
    let n_l_int = prefix.n_l.to_bigint().unwrap();
    let s_l_int = prefix.s_l.to_bigint().unwrap();
    let two = BigInt::from(2);

    let two_n_l = (&two * &n_l_int) % &s_l_int;
    if let Some(x_l) = mod_inverse(&(-&two_n_l), &s_l_int) {
        
        // TODO: Replace with Tonelli-Shanks for modular roots of z^2 ≡ x_l mod s_l
        let roots: Vec<BigInt> = vec![x_l]; 

        let max_n_int = target_max.to_bigint().unwrap();
        let z_max = (&max_n_int / &n_l_int).sqrt();
        let c_max = (&z_max / &s_l_int).to_usize().unwrap_or(10_000_000);

        for r_i in roots {
            let mut valid_c = vec![true; c_max + 1];
            
            // Fast Raycast Scan
            for c in 0..=c_max {
                if valid_c[c] {
                    let z = &r_i + BigInt::from(c) * &s_l_int;
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
}
