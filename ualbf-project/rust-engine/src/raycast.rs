fn isqrt(n: Int) -> Int {
    let mut x = n;
    let mut y = (x + Int::ONE) / Int::from(2u8);
    while y < x {
        x = y;
        y = (x + n / x) / Int::from(2u8);
    }
    x
}

use crate::math_utils::{composite_tonelli_shanks, sigma_cached, SigmaCache};
use crate::types::{Int, Prefix, Uint};
use num_integer::Roots;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Precomputes primes whose squares yield sigma ≡ 5 or 7 mod 8
/// Returns tuples `(p^e, p^{e+1})` for the sieve.
/// Since we test `v_p(z) == e`, it corresponds to `v_p(N_R) == 2e`.
/// Thus the tuples track `e` such that `\sigma(p^{2e}) \equiv 5 \text{ or } 7 \pmod 8`.
pub fn generate_illegal_z_valuations(limit: u64, max_e: u32) -> Vec<(Int, Int)> {
    let mut illegal = Vec::new();
    for p in 3..limit {
        let mut is_prime = true;
        let mut d = 2;
        while d * d <= p {
            if p % d == 0 {
                is_prime = false;
                break;
            }
            d += 1;
        }
        if !is_prime {
            continue;
        }

        let p_int = Int::from(p);
        let p_mod = p % 8;
        let mut term = (p_mod * p_mod) % 8; // p^2 mod 8
        let mut sigma_mod_8 = (term + p_mod + 1) % 8; // sigma(p^2) mod 8

        for e in 1..=max_e {
            if sigma_mod_8 == 5 || sigma_mod_8 == 7 {
                illegal.push((p_int.pow(e), p_int.pow(e + 1)));
            }
            term = (term * p_mod) % 8; // p^{2e+1}
            sigma_mod_8 = (sigma_mod_8 + term) % 8;
            term = (term * p_mod) % 8; // p^{2e+2}
            sigma_mod_8 = (sigma_mod_8 + term) % 8;
        }
    }
    illegal
}

pub fn phase4_exact_ray_casting(
    prefix: &Prefix,
    target_min: &Uint,
    target_max: &Uint,
    illegal_z_valuations: &[(Int, Int)],
    pruned_count: &AtomicUsize,
    sigma_cache: &SigmaCache,
) {
    let n_l_int = prefix.n_l.as_i256();
    let s_l_int = prefix.s_l.as_i256();
    let two: i128 = 2;
    let mut a = (-two * prefix.n_l.as_i256()) % prefix.s_l.as_i256();
    if a < 0 {
        a += prefix.s_l.as_i256();
    }

    // Use the fully verified 128-bit Lean FFI
    if let Some(x_l) = crate::lean_ffi::mod_inverse_256(a, prefix.s_l.as_i256()) {
        let roots = composite_tonelli_shanks(x_l, &prefix.sigma_factors);
        let max_n_int = target_max.as_i256();
        let z_max = max_n_int / n_l_int;
        let c_max = (z_max / s_l_int).as_usize();

        let min_n_int = target_min.as_i256();
        let z_min = if min_n_int > n_l_int {
            min_n_int / n_l_int
        } else {
            ethnum::I256::ZERO
        };

        for r_i in roots {
            let c_min = if z_min > r_i {
                ((z_min - r_i + s_l_int - Int::ONE) / s_l_int).as_usize()
            } else {
                0
            };

            for c in c_min..=c_max {
                let z = r_i + Int::from(c as u64) * s_l_int;

                if z > z_max {
                    break;
                }

                if z % 2 == 0 {
                    continue;
                }

                let mut passed_sieve = true;
                for &(pe, pe1) in illegal_z_valuations {
                    let rem = z % pe1;
                    // Check if v_p(z) == e exactly.
                    // This means z is divisible by p^e (rem % pe == 0) but not p^{e+1} (rem != 0).
                    // As v_p(z) == e implies v_p(N_R) == 2e, this identifies a forbidden sigma.
                    if rem % pe == 0 && rem != 0 {
                        passed_sieve = false;
                        pruned_count.fetch_add(1, Ordering::Relaxed);
                        break;
                    }
                }

                if !passed_sieve {
                    continue;
                }

                let mut is_coprime = true;
                for &p in &prefix.factors {
                    if z % (Int::from(p)) == 0 {
                        is_coprime = false;
                        break;
                    }
                }
                if !is_coprime {
                    continue;
                }

                // ---------- Cheap pre-checks (no factoring) ----------
                let z_biguint = z.as_u256();
                let n_r = match z_biguint.checked_mul(z_biguint) {
                    Some(v) => v,
                    None => {
                        eprintln!("overflow: z*z for z={}", z);
                        continue;
                    }
                };
                let total_n = match prefix.n_l.checked_mul(n_r) {
                    Some(v) => v,
                    None => {
                        eprintln!("overflow: n_l*n_r for z={}", z);
                        continue;
                    }
                };

                // Compute required σ(z²) from QPN equation: s_l · σ(z²) = 2·n_l·z² + 1
                let two_n_plus_one = match total_n
                    .checked_mul(Uint::from(2u8))
                    .and_then(|v| v.checked_add(Uint::ONE))
                {
                    Some(v) => v,
                    None => {
                        eprintln!("overflow: 2n+1 for z={}", z);
                        continue;
                    }
                };

                // By CRT construction s_l | (2·n_l·z² + 1), so division is exact
                if two_n_plus_one % prefix.s_l != 0 {
                    // Should not happen by construction; defensive guard
                    continue;
                }
                let required_s_r = two_n_plus_one / prefix.s_l;

                // Filter 1: σ(z²) > z² always (σ includes z² + … + 1)
                if required_s_r <= n_r {
                    continue;
                }

                // Filter 2: σ(z²) < 3·z² (conservative upper bound for odd squares)
                if let Some(upper) = n_r.checked_mul(Uint::from(3u8)) {
                    if required_s_r > upper {
                        continue;
                    }
                }

                // Filter 3: σ(z²) must be odd (z is odd ⇒ z² odd ⇒ σ(z²) odd)
                if required_s_r % 2 == 0 {
                    continue;
                }

                // ---------- Factor z and verify σ(z²) == required_s_r ----------
                let z_factors = crate::math_utils::quick_factor_u256(z_biguint);
                if z_factors.is_empty() {
                    continue;
                } // factorisation failed
                let mut s_r: Uint = Uint::ONE;
                let mut current_p = 0;
                let mut count: u32 = 0;
                let mut s_r_overflowed = false;

                for &f in &z_factors {
                    if f == current_p {
                        count += 1;
                    } else {
                        if current_p != 0 {
                            match s_r.checked_mul(sigma_cached(
                                sigma_cache,
                                Uint::from(current_p),
                                2 * count,
                            )) {
                                Some(v) => s_r = v,
                                None => {
                                    eprintln!("overflow: s_r accumulation for z={}", z);
                                    s_r_overflowed = true;
                                    break;
                                }
                            }
                        }
                        current_p = f.as_u128();
                        count = 1;
                    }
                }
                if s_r_overflowed {
                    continue;
                }
                if current_p != 0 {
                    match s_r.checked_mul(sigma_cached(
                        sigma_cache,
                        Uint::from(current_p),
                        2 * count,
                    )) {
                        Some(v) => s_r = v,
                        None => {
                            eprintln!("overflow: s_r accumulation for z={}", z);
                            continue;
                        }
                    }
                }

                if s_r == required_s_r {
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
    fn test_generate_illegal_z_valuations() {
        let illegal = generate_illegal_z_valuations(20, 4);
        // e=1 flags 3, 5, 11, 13, 19 -> (p, p^2)
        // Just check that (3, 9) is in there, for example.
        assert!(illegal.contains(&(ethnum::I256::from(3), ethnum::I256::from(9))));
        assert!(illegal.contains(&(ethnum::I256::from(5), ethnum::I256::from(25))));
    }
}
