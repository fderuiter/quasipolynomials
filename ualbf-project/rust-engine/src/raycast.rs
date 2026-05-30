use num_traits::Signed;
fn isqrt_uint(n: Uint) -> Uint {
    let mut x = n.clone();
    let mut y = (x.clone() + Uint::one_ext()) / Uint::from_u32_ext(2);
    while y.clone() < x.clone() {
        x = y;
        y = (x.clone() + n.clone() / x.clone()) / Uint::from_u32_ext(2);
    }
    x
}

fn isqrt(n: Int) -> Int {
    let mut x = n.clone();
    let mut y = (x.clone() + Int::one_ext()) / Int::from_u32_ext(2);
    while y.clone() < x.clone() {
        x = y;
        y = (x.clone() + n.clone() / x.clone()) / Int::from_u32_ext(2);
    }
    x
}

use crate::math_utils::{composite_tonelli_shanks, sigma_cached, SigmaCache};
use crate::types::{Int, Prefix, Uint, UintExt, IntExt};
use num_traits::{One, Zero};
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

        let p_int = Int::from_u64_ext(p);
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
    reporter: Option<&crossbeam_channel::Sender<String>>,
) {
    let n_l_int = Int::from_u256_ext(&prefix.n_l.clone().as_u256()); // prefix is up to 10^30 usually but we use 512 bit now
    let s_l_int = Int::from_u256_ext(&prefix.s_l.clone().as_u256());
    let mut a = (Int::from_u32_ext(2) * n_l_int) % s_l_int.clone();
    if a < Int::zero_ext() {
        a += s_l_int.clone();
    }

    let x_l_opt = if a.abs() <= Int::from_u256_ext(&ethnum::U256::MAX) && s_l_int.clone() <= Int::from_u256_ext(&ethnum::U256::MAX) {
        crate::lean_ffi::mod_inverse_256(a.clone(), s_l_int.clone())
    } else {
        crate::math_utils::mod_inverse_big(a.clone(), s_l_int.clone())
    };

    if let Some(x_l) = x_l_opt {
        let roots = composite_tonelli_shanks(x_l, &prefix.sigma_factors);
        let n_l_big = prefix.n_l.clone();
        let z_max_big = if target_max.clone() > n_l_big.clone() { isqrt_uint(target_max.clone() / n_l_big.clone()) } else { Uint::zero_ext() };
        let z_min_big = if target_min.clone() > n_l_big.clone() { isqrt_uint(target_min.clone() / n_l_big.clone()) } else { Uint::zero_ext() };
        let z_max = Int::from_u256_ext(&z_max_big.as_u256());
        let z_min = Int::from_u256_ext(&z_min_big.as_u256());

        let c_max = (z_max.clone() / s_l_int.clone()).as_usize();

        for r_i in roots {
            let c_min = if z_min.clone() > r_i.clone() {
                ((z_min.clone() - r_i.clone() + s_l_int.clone() - Int::one_ext()) / s_l_int.clone()).as_usize()
            } else {
                0
            };

            for c in c_min..=c_max {
                let mut z = r_i.clone() + Int::from_u64_ext(c as u64) * s_l_int.clone();

                if z > z_max {
                    break;
                }

                if z.clone() % Int::from_u32_ext(2) == Int::zero_ext() {
                    continue;
                }

                let mut passed_sieve = true;
                for (pe, pe1) in illegal_z_valuations {
                    let rem = z.clone() % pe1.clone();
                    // Check if v_p(z) == e exactly.
                    // This means z is divisible by p^e (rem.clone() % pe.clone() == Int::zero_ext()) but not p^{e+1} (rem.clone() != Int::zero_ext()).
                    // As v_p(z) == e implies v_p(N_R) == 2e, this identifies a forbidden sigma.
                    if rem.clone() % pe.clone() == Int::zero_ext() && rem.clone() != Int::zero_ext() {
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
                    if z.clone() % Int::from_u64_ext(p) == Int::zero_ext() {
                        is_coprime = false;
                        break;
                    }
                }
                if !is_coprime {
                    continue;
                }

                // ---------- Cheap pre-checks (no factoring) ----------
                let z_biguint = z.as_u256();
                let z_tiered = Uint::from_u256_ext(&z_biguint);
                let n_l_tiered = prefix.n_l.clone();
                let s_l_tiered = prefix.s_l.clone();

                let n_r = match z_tiered.checked_mul(&z_tiered) {
                    Some(v) => v,
                    None => continue, // Will not happen since we fail over to BigUint!
                };
                let total_n = match n_l_tiered.checked_mul(&n_r) {
                    Some(v) => v,
                    None => continue,
                };

                // Compute required σ(z²) from QPN equation: s_l · σ(z²) = 2·n_l·z² + 1
                let two_n_plus_one = match total_n
                    .checked_mul(&Uint::from_u32_ext(2))
                    .and_then(|v| v.checked_add(&Uint::one_ext()))
                {
                    Some(v) => v,
                    None => continue,
                };

                // By CRT construction s_l | (2·n_l·z² + 1), so division is exact
                if &two_n_plus_one % &s_l_tiered != Uint::from_u128_ext(0 as u128) {
                    continue;
                }
                let required_s_r = &two_n_plus_one / &s_l_tiered;

                // Filter 1: σ(z²) > z² always (σ includes z² + … + 1)
                if required_s_r <= n_r {
                    continue;
                }

                // Filter 2: σ(z²) < 3·z² (conservative upper bound for odd squares)
                if let Some(upper) = n_r.checked_mul(&Uint::from_u32_ext(3)) {
                    if required_s_r > upper {
                        continue;
                    }
                }

                // Filter 3: σ(z²) must be odd (z is odd ⇒ z² odd ⇒ σ(z²) odd)
                if required_s_r.clone() % Uint::from_u32_ext(2) == Uint::zero_ext() {
                    continue;
                }

                // ---------- Factor z and verify σ(z²) == required_s_r ----------
                let z_factors = crate::math_utils::quick_factor_u256(z_tiered);
                if z_factors.is_empty() {
                    continue;
                } // factorisation failed
                let mut s_r = Uint::from_u128_ext(1 as u128);
                let mut current_p = 0;
                let mut count: u32 = 0;
                let mut s_r_overflowed = false;

                for f in z_factors {
                    if f.as_u128() == current_p {
                        count += 1;
                    } else {
                        if current_p != 0 {
                            let sig = sigma_cached(sigma_cache, Uint::from_u128_ext(current_p as u128), 2 * count);
                            match s_r.checked_mul(&sig) {
                                Some(v) => s_r = v,
                                None => {
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
                    let sig = sigma_cached(sigma_cache, Uint::from_u128_ext(current_p as u128), 2 * count);
                    match s_r.checked_mul(&sig) {
                        Some(v) => s_r = v,
                        None => {
                            continue;
                        }
                    }
                }

                if s_r == required_s_r {
                    let msg = format!(">>> QUASIPERFECT NUMBER FOUND: {} <<<", total_n);
                    println!("{}", msg);
                    if let Some(r) = reporter {
                        let _ = r.send(msg);
                    }
                    // Do not exit, continue searching the ray
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
        assert!(illegal.contains(&(Int::from_u32_ext(3), Int::from_u32_ext(9))));
        assert!(illegal.contains(&(Int::from_u32_ext(5), Int::from_u32_ext(25))));
    }
}
