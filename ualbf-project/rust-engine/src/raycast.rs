fn isqrt_uint(n: Uint) -> Uint {
    let mut x = n;
    let mut y = (x + Uint::one()) / Uint::from_u32(2);
    while y < x {
        x = y;
        y = (x + n / x) / Uint::from_u32(2);
    }
    x
}

fn isqrt(n: Int) -> Int {
    let mut x = n;
    let mut y = (x + Int::one()) / Int::from_u32(2);
    while y < x {
        x = y;
        y = (x + n / x) / Int::from_u32(2);
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

        let p_int = Int::from_u64(p);
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

/// Searches for quasiperfect numbers by enumerating residue-class progressions for z and validating
/// candidates with sieves, modular/divisibility constraints, and optional GPU-assisted pruning.
///
/// The function iterates roots and arithmetic progressions z = r + c * s_l derived from `prefix`,
/// applies an optional GPU raycast sieve for large chunks, performs CPU-side "illegal valuation"
/// sieving, enforces coprimality with `prefix.factors`, and checks various big-integer
/// divisibility and sigma-based factorization conditions. When a candidate satisfies all checks,
/// a notification message containing the found composite `n = n_l * z^2` is printed and optionally
/// sent via `reporter`. `pruned_count` is incremented for values removed by sieves.
///
/// # Parameters
/// - `prefix`: residue-class and factorization context (contains `n_l`, `s_l`, `factors`, and `sigma_factors`).
/// - `target_min`, `target_max`: inclusive bounds for the target search range; used to compute z bounds.
/// - `illegal_z_valuations`: precomputed prime-power pairs used to quickly reject z values.
/// - `pruned_count`: atomic counter incremented for values pruned by GPU or CPU sieves.
/// - `sigma_cache`: cache used for repeated sigma(p^k) lookups during sigma-based checks.
/// - `reporter`: optional channel sender to receive formatted discovery messages.
///
/// # Examples
///
/// ```no_run
/// # use std::sync::atomic::AtomicUsize;
/// # use some_crate::{Prefix, phase4_exact_ray_casting, SigmaCache};
/// // Construct a suitable `prefix`, bounds, and other arguments per your application,
/// // then call the search routine. This example is illustrative and not runnable as-is.
/// let prefix: Prefix = /* build prefix with n_l, s_l, factors, sigma_factors, ... */ unimplemented!();
/// let target_min = /* Uint lower bound */ unimplemented!();
/// let target_max = /* Uint upper bound */ unimplemented!();
/// let illegal_z_valuations = Vec::new();
/// let pruned_count = AtomicUsize::new(0);
/// let sigma_cache: SigmaCache = Default::default();
/// phase4_exact_ray_casting(&prefix, &target_min, &target_max, &illegal_z_valuations, &pruned_count, &sigma_cache, None);
/// ```
pub fn phase4_exact_ray_casting(
    prefix: &Prefix,
    target_min: &Uint,
    target_max: &Uint,
    illegal_z_valuations: &[(Int, Int)],
    pruned_count: &AtomicUsize,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<String>>,
) {
    let n_l_int = prefix.n_l.as_int();
    let s_l_int = prefix.s_l.as_int();
    let mut a = (Int::from_u32(2) * n_l_int) % s_l_int;
    if a < Int::zero() {
        a += s_l_int;
    }

    let x_l_inv_opt = crate::math_utils::mod_inverse_big(a, s_l_int);
    let x_l_opt = x_l_inv_opt.map(|x| crate::math_utils::mod_negate_big(x, s_l_int));

    if let Some(x_l) = x_l_opt {
        // Assertion: 2N_L * x_l == -1 mod S_L, or (2N_L * x_l + 1) == 0 mod S_L
        let n_l_uint = prefix.n_l;
        let x_l_uint = x_l.as_uint();
        let s_l_uint = prefix.s_l;
        let identity_check = ((Uint::from_u32(2) * n_l_uint * x_l_uint) + Uint::one()) % s_l_uint;
        assert_eq!(identity_check, Uint::zero(), "Runtime identity assertion failed: 2N_L * x_l + 1 != 0 mod S_L");

        let roots = composite_tonelli_shanks(x_l, &prefix.sigma_factors);
        let n_l_big = prefix.n_l;
        let z_max_big = if *target_max > n_l_big { isqrt_uint(*target_max / n_l_big) } else { Uint::zero() };
        let z_min_big = if *target_min > n_l_big { isqrt_uint(*target_min / n_l_big) } else { Uint::zero() };
        let z_max = z_max_big.as_int();
        let z_min = z_min_big.as_int();

        let c_max = (z_max / s_l_int).as_usize();

        for r_i in roots {
            let c_min = if z_min > r_i {
                ((z_min - r_i + s_l_int - Int::one()) / s_l_int).as_usize()
            } else {
                0
            };

            let mut c_current = c_min;
            let gpu_threshold = 100_000;
            
            while c_current <= c_max {
                let chunk_size = std::cmp::min(c_max - c_current + 1, 10_000_000); // 10M chunk size
                let c_end = c_current + chunk_size - 1;
                
                let mut valid_indices: Option<Vec<usize>> = None;
                
                if chunk_size >= gpu_threshold {
                    if let Some(gpu) = crate::gpu::get_gpu_pipeline() {
                        let mut illegal_z_valuations_u256 = Vec::with_capacity(illegal_z_valuations.len());
                        for &(pe, pe1) in illegal_z_valuations {
                            illegal_z_valuations_u256.push((pe.as_uint(), pe1.as_uint()));
                        }
                        
                        let r_i_uint = r_i.as_uint();
                        let s_l_uint = s_l_int.as_uint();
                        
                        let (gpu_valid, pruned) = gpu.raycast_sieve(
                            r_i_uint,
                            s_l_uint,
                            c_current as u64,
                            c_end as u64,
                            &illegal_z_valuations_u256
                        );
                        
                        pruned_count.fetch_add(pruned, Ordering::Relaxed);
                        valid_indices = Some(gpu_valid.into_iter().map(|c| (c_current + c as usize)).collect());
                    }
                }
                
                let mut process_c = |c: usize, count_pruned: bool| {
                    let z = r_i + Int::from_u64(c as u64) * s_l_int;

                    if z > z_max {
                        return;
                    }

                    if z % Int::from_u32(2) == Int::zero() {
                        return;
                    }

                    if count_pruned {
                        let mut passed_sieve = true;
                        for &(pe, pe1) in illegal_z_valuations {
                            let rem = z % pe1;
                            if rem % pe == Int::zero() && rem != Int::zero() {
                                passed_sieve = false;
                                pruned_count.fetch_add(1, Ordering::Relaxed);
                                break;
                            }
                        }

                        if !passed_sieve {
                            return;
                        }
                    }

                    let mut is_coprime = true;
                    for &p in &prefix.factors {
                        if z % Int::from_u64(p) == Int::zero() {
                            is_coprime = false;
                            break;
                        }
                    }
                    if !is_coprime {
                        return;
                    }

                    let z_tiered = z.as_uint();
                    let n_l_tiered = prefix.n_l;
                    let s_l_tiered = prefix.s_l;

                    let n_r = match z_tiered.checked_mul(z_tiered) {
                        Some(v) => v,
                        None => return,
                    };
                    let total_n = match n_l_tiered.checked_mul(n_r) {
                        Some(v) => v,
                        None => return,
                    };

                    let two_n_plus_one = match total_n
                        .checked_mul(Uint::from_u32(2))
                        .and_then(|v| v.checked_add(Uint::one()))
                    {
                        Some(v) => v,
                        None => return,
                    };

                    if &two_n_plus_one % &s_l_tiered != Uint::from_u128(0 as u128) {
                        return;
                    }
                    let required_s_r = &two_n_plus_one / &s_l_tiered;

                    if required_s_r <= n_r {
                        return;
                    }

                    if let Some(upper) = n_r.checked_mul(Uint::from_u32(3)) {
                        if required_s_r > upper {
                            return;
                        }
                    }

                    if required_s_r % Uint::from_u32(2) == Uint::zero() {
                        return;
                    }

                    let z_factors = crate::math_utils::quick_factor_u256(z_tiered);
                    if z_factors.is_empty() {
                        return;
                    } 
                    let mut s_r = Uint::from_u128(1 as u128);
                    let mut current_p = 0;
                    let mut count: u32 = 0;
                    let mut s_r_overflowed = false;

                    for &f in &z_factors {
                        if f.as_u128() == current_p {
                            count += 1;
                        } else {
                            if current_p != 0 {
                                let sig = sigma_cached(sigma_cache, Uint::from_u128(current_p as u128), 2 * count);
                                match s_r.checked_mul(sig) {
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
                        return;
                    }
                    if current_p != 0 {
                        let sig = sigma_cached(sigma_cache, Uint::from_u128(current_p as u128), 2 * count);
                        match s_r.checked_mul(sig) {
                            Some(v) => s_r = v,
                            None => {
                                return;
                            }
                        }
                    }

                    if s_r == required_s_r {
                        let msg = format!(">>> QUASIPERFECT NUMBER FOUND: {} <<<", total_n);
                        println!("{}", msg);
                        if let Some(r) = reporter {
                            let _ = r.send(msg);
                        }
                    }
                };
                
                if let Some(indices) = valid_indices {
                    for c in indices {
                        process_c(c, false);
                    }
                } else {
                    for c in c_current..=c_end {
                        process_c(c, true);
                    }
                }
                
                c_current = c_end + 1;
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
        assert!(illegal.contains(&(Int::from_u32(3), Int::from_u32(9))));
        assert!(illegal.contains(&(Int::from_u32(5), Int::from_u32(25))));
    }

    #[test]
    fn test_quasi_perfect_residue_class_integration() {
        let n_l = Uint::from_u32(9);
        let s_l = Uint::from_u32(13);

        let prefix = Prefix {
            n_l,
            s_l,
            last_idx: 1,
            factors: vec![3],
            sigma_factors: vec![Uint::from_u32(13)],
            sigma_factors_u64: vec![13],
            active_mask: vec![1],
        };

        let target_min = Uint::from_u32(1);
        let target_max = Uint::from_u32(100);
        let illegal_z_valuations: Vec<(Int, Int)> = vec![];
        let pruned_count = AtomicUsize::new(0);
        let sigma_cache = std::collections::HashMap::new();

        // Ensure phase4 doesn't panic when we call it, verifying the mathematical identity constraint 
        // 2N_L * x_l + 1 == 0 mod S_L holds correctly internally.
        phase4_exact_ray_casting(
            &prefix,
            &target_min,
            &target_max,
            &illegal_z_valuations,
            &pruned_count,
            &sigma_cache,
            None,
        );
    }
}
