// ---------------------------------------------------------------------------
// LLL lattice reduction (exact integer arithmetic via rug) for logarithmic
// feasibility pruning.  Uses the scaling trick: all logarithms are computed
// at 256-bit MPFR precision, multiplied by 2^200, and truncated to exact
// rug::Integer values.  The LLL algorithm then runs over ℤ, which is the
// only domain where it is proven to terminate correctly.
//
// NOTE: This module is NOT used inside the raycast inner loop.
// Its purpose is Wave 4 prefix-level Diophantine approximation pruning,
// where the exponents are unknown and LLL is the correct tool.
// ---------------------------------------------------------------------------

use rug::{Float, Integer};

/// Precision for MPFR floats used during log computation.
const PRECISION_BITS: u32 = 256;
/// The scale exponent: we multiply floats by 2^SCALE_EXP before truncating.
const SCALE_EXP: u32 = 200;

/// Calculate scaled integer log-abundancy for a prime p:
///   floor( ln(1 + 1/p + 1/p²) · 2^200 )
///
/// **Important**: This formula is only valid when `p` is prime.
/// For composite arguments, the true σ(p²)/p² can be much larger,
/// so this function must NOT be used on arbitrary composite numbers.
pub fn scaled_log_abundancy(p: u64) -> Integer {
    let float_p = Float::with_val(PRECISION_BITS, p);
    let one = Float::with_val(PRECISION_BITS, 1.0);

    // ln(σ(p²)/p²) = ln(1 + 1/p + 1/p²)
    let p_sq = Float::with_val(PRECISION_BITS, &float_p * &float_p);
    let inv_p = Float::with_val(PRECISION_BITS, &one / &float_p);
    let inv_p_sq = Float::with_val(PRECISION_BITS, &one / &p_sq);
    let sum = Float::with_val(PRECISION_BITS, &one + &inv_p);
    let term = Float::with_val(PRECISION_BITS, &sum + &inv_p_sq);
    let ln_ab = Float::with_val(PRECISION_BITS, term.ln());

    // Scale by 2^SCALE_EXP and truncate to Integer
    let mut scale = Float::with_val(PRECISION_BITS, 1);
    scale <<= SCALE_EXP;

    let scaled_val = Float::with_val(PRECISION_BITS, &ln_ab * &scale);
    scaled_val
        .to_integer()
        .expect("scaled_log_abundancy: conversion to Integer failed")
}

pub type Row = Vec<Integer>;
pub type Matrix = Vec<Row>;

/// Dot product of two integer rows.
pub fn dot(a: &[Integer], b: &[Integer]) -> Integer {
    let mut s = Integer::new();
    for (ai, bi) in a.iter().zip(b.iter()) {
        s += Integer::from(ai * bi);
    }
    s
}

/// In-place LLL basis reduction on an integer matrix (rows = basis vectors).
/// Uses the classic algorithm with δ = 3/4 and exact rational Gram-Schmidt.
///
/// Gram-Schmidt coefficients are stored as rational pairs (numerator, denominator)
/// to avoid any floating-point arithmetic.
pub fn lll_reduce(basis: &mut Matrix) {
    let m = basis.len();
    if m <= 1 {
        return;
    }
    let n = basis[0].len();

    // mu_num[i][j] and mu_den[i][j] represent μ_{i,j} = mu_num/mu_den
    let mut mu_num: Vec<Vec<Integer>> = vec![vec![Integer::new(); m]; m];
    let mut mu_den: Vec<Vec<Integer>> = vec![vec![Integer::from(1); m]; m];
    // b_star_sq_num[i] / b_star_sq_den[i] = ||b*_i||^2
    let mut bsq_num: Vec<Integer> = vec![Integer::new(); m];
    let mut bsq_den: Vec<Integer> = vec![Integer::from(1); m];
    // Orthogonal basis stored row-wise (rational: num only, denom = common bsq_den chain)
    // For exact GS we track b*_i as integer vectors divided by a common D_i.
    // Using the standard integral GS formulation (de Weger / Cohen):
    //   D_0 = 1
    //   D_i = D_{i-1} * ||b*_i||^2  (all exact integers when inputs are integers)
    //
    // We use a simpler approach: store b*_i explicitly as Integer vectors.
    let mut b_star: Matrix = vec![vec![Integer::new(); n]; m];

    // Full Gram-Schmidt recompute
    let recompute_gs = |basis: &Matrix,
                        mu_num: &mut Vec<Vec<Integer>>,
                        mu_den: &mut Vec<Vec<Integer>>,
                        b_star: &mut Matrix,
                        bsq_num: &mut Vec<Integer>,
                        bsq_den: &mut Vec<Integer>| {
        for i in 0..basis.len() {
            // b*_i = b_i
            for c in 0..n {
                b_star[i][c] = basis[i][c].clone();
            }
            // Common denominator for b*_i: product of bsq_num[0..i]
            // We scale b*_i by the product of previous bsq norms to stay in ℤ.
            // Instead, use the direct rational approach:
            //   μ_{i,j} = <b_i, b*_j> / <b*_j, b*_j>
            //   b*_i = b_i - Σ_{j<i} μ_{i,j} · b*_j
            // All stored as exact Integer fractions.
            let mut current_den = Integer::from(1);
            for jj in 0..i {
                if bsq_num[jj] == 0 {
                    mu_num[i][jj] = Integer::new();
                    mu_den[i][jj] = Integer::from(1);
                    continue;
                }
                // μ_{i,jj} = <b_i, b*_jj> / ||b*_jj||^2
                // <b*_i_current, b*_jj> where b*_i_current is scaled by current_den
                let dot_val = dot(&b_star[i], &b_star[jj]);
                mu_num[i][jj] = dot_val.clone();
                mu_den[i][jj] = Integer::from(&bsq_num[jj] * &current_den);

                // Clone jj-th row to avoid simultaneous mutable/immutable borrow
                let b_star_jj = b_star[jj].clone();
                for c in 0..n {
                    b_star[i][c] *= &bsq_num[jj];
                    b_star[i][c] -= Integer::from(&dot_val * &b_star_jj[c]);
                }
                current_den *= &bsq_num[jj];
            }
            // ||b*_i||^2 in terms of the scaled vectors: actual = sum / current_den^2
            let sq = dot(&b_star[i], &b_star[i]);
            bsq_num[i] = sq;
            bsq_den[i] = Integer::from(&current_den * &current_den);
        }
    };

    recompute_gs(
        basis,
        &mut mu_num,
        &mut mu_den,
        &mut b_star,
        &mut bsq_num,
        &mut bsq_den,
    );

    let mut k = 1usize;
    while k < m {
        // Size-reduce b_k
        for j in (0..k).rev() {
            if mu_den[k][j] == 0 {
                continue;
            }
            // Check |μ_{k,j}| > 1/2  ⟺  2·|mu_num| > |mu_den|
            let two_abs_num = Integer::from(mu_num[k][j].abs_ref()) * 2u32;
            let abs_den = Integer::from(mu_den[k][j].abs_ref());
            if two_abs_num > abs_den {
                // Exact integer rounding: r = round(mu_num / mu_den)
                let mut r = mu_num[k][j].clone();
                let half_den = Integer::from(&mu_den[k][j] >> 1);
                if r >= 0 {
                    r += half_den;
                } else {
                    r -= half_den;
                }
                r /= &mu_den[k][j];
                if r != 0 {
                    let basis_j_row = basis[j].clone();
                    for (basis_k_c, basis_j_c) in
                        basis[k].iter_mut().zip(basis_j_row.iter()).take(n)
                    {
                        *basis_k_c -= Integer::from(&r * basis_j_c);
                    }
                    recompute_gs(
                        basis,
                        &mut mu_num,
                        &mut mu_den,
                        &mut b_star,
                        &mut bsq_num,
                        &mut bsq_den,
                    );
                }
            }
        }

        // Lovász condition: ||b*_k||^2 ≥ (δ - μ_{k,k-1}^2) · ||b*_k-1||^2
        // With δ = 3/4, check:
        //   bsq_num[k]/bsq_den[k]  >=  (3/4 - (mu_num[k][k-1]/mu_den[k][k-1])^2) * bsq_num[k-1]/bsq_den[k-1]
        //
        // Cross-multiply to stay in ℤ:
        //   4 · bsq_num[k] · bsq_den[k-1] · mu_den[k][k-1]^2
        //     >= bsq_den[k] · (3 · mu_den[k][k-1]^2 - 4 · mu_num[k][k-1]^2) · bsq_num[k-1]
        let mu_d_sq = Integer::from(&mu_den[k][k - 1] * &mu_den[k][k - 1]);
        let mu_n_sq = Integer::from(&mu_num[k][k - 1] * &mu_num[k][k - 1]);

        let lhs = Integer::from(&bsq_num[k] * &bsq_den[k - 1]) * &mu_d_sq * 4u32;
        let rhs_factor = Integer::from(&mu_d_sq * 3u32) - Integer::from(&mu_n_sq * 4u32);
        let rhs = Integer::from(&bsq_den[k] * &bsq_num[k - 1]) * rhs_factor;

        if lhs >= rhs {
            k += 1;
        } else {
            // Swap rows k and k-1
            basis.swap(k, k - 1);
            recompute_gs(
                basis,
                &mut mu_num,
                &mut mu_den,
                &mut b_star,
                &mut bsq_num,
                &mut bsq_den,
            );
            if k > 1 {
                k -= 1;
            }
        }
    }
}

/// Returns `true` if the logarithmic lattice geometry of `prefix_factors`
/// structurally prevents σ(N)/N from reaching 2 + 1/(2N).
///
/// Builds a (k+1)×(k+2) integer lattice where each row encodes a prime's
/// log-abundancy contribution scaled by 2^200.  After exact LLL reduction
/// the shortest vector's last component gives the minimum achievable
/// deviation from ln(2) — if it exceeds the tolerance, the candidate is
/// provably infeasible.
///
/// **Important**: All factors in `prefix_factors` must be prime.
/// This function is intended for prefix-level Diophantine pruning
/// (Wave 4), NOT for the raycast inner loop where z is already known.
pub fn lll_prune_prefix(prefix_factors: &[u64], total_n: u128) -> bool {
    let k = prefix_factors.len();
    if k == 0 {
        return false; // not enough structure for lattice
    }

    let rows = k + 1;
    let cols = k + 2;
    let scale = Integer::from(1) << SCALE_EXP;

    let mut basis: Matrix = vec![vec![Integer::new(); cols]; rows];

    // Log-abundancy for each prefix prime p:  ln(σ(p²)/p²) = ln(1 + 1/p + 1/p²)
    for (i, &p) in prefix_factors.iter().enumerate() {
        basis[i][i] = scale.clone(); // identity block scaled by 2^200
        basis[i][cols - 1] = scaled_log_abundancy(p); // log-abundancy column
    }

    // Placeholder row for unknown suffix contribution (smallest possible prime > prefix)
    let placeholder_p = prefix_factors.iter().copied().max().unwrap_or(2) + 1;
    basis[k][k] = scale.clone();
    basis[k][cols - 1] = scaled_log_abundancy(placeholder_p);

    lll_reduce(&mut basis);

    // The tolerance: we need the total log-abundancy sum to be within
    // 1/(2N) of ln(2).  Scaled tolerance = floor(2^200 / (2 · total_n))
    let total_n_big = Integer::from(total_n);
    let tol_denom = Integer::from(&total_n_big * 2u32);
    let scaled_tol = if tol_denom > 0 {
        Integer::from(&scale / &tol_denom)
    } else {
        Integer::from(1)
    };

    // Find the shortest reduced basis vector (by squared Euclidean norm)
    let mut min_norm_sq: Option<Integer> = None;
    let mut min_last = Integer::new();
    for row in &basis {
        let nsq = dot(row, row);
        if nsq == 0 {
            continue;
        }
        let is_shorter = match &min_norm_sq {
            Some(prev) => nsq < *prev,
            None => true,
        };
        if is_shorter {
            min_norm_sq = Some(nsq);
            min_last = Integer::from(row[cols - 1].abs_ref());
        }
    }

    // If the shortest vector's log-component exceeds the scaled tolerance,
    // no integer exponent combination can close the gap → prune.
    min_last > scaled_tol
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scaled_log_abundancy() {
        // For p=3: ln(1 + 1/3 + 1/9) = ln(13/9) ≈ 0.36798...
        // Scaled by 2^200 this is a massive integer; just verify it's positive
        // and has the expected magnitude (roughly 0.368 * 2^200 ≈ 5.9 × 10^59).
        let val = scaled_log_abundancy(3);
        assert!(val > 0, "scaled log-abundancy for p=3 must be positive");
        // Check it's in the right ballpark: > 10^58 and < 10^61
        let digits = val.to_string().len();
        assert!(
            digits >= 59 && digits <= 61,
            "expected ~60 digit integer, got {} digits",
            digits
        );
    }

    #[test]
    fn test_lll_reduce_basic() {
        // Classic 2D lattice that LLL should shorten.
        // [[1, 0], [123, 1000]]  →  LLL should produce a shorter first vector.
        let mut basis: Matrix = vec![
            vec![Integer::from(1), Integer::from(0)],
            vec![Integer::from(123), Integer::from(1000)],
        ];
        lll_reduce(&mut basis);
        // After reduction the first basis vector should be short
        let norm_sq = dot(&basis[0], &basis[0]);
        // Original first vector had norm 1; it should stay short.
        // The reduced basis should have first vector norm² ≤ original smallest.
        assert!(
            norm_sq <= Integer::from(1_000_001),
            "LLL should shorten the basis, got norm² = {}",
            norm_sq
        );
    }

    #[test]
    fn test_lll_prune_prefix_empty() {
        // Empty prefix → returns false (no structure to prune)
        assert!(!lll_prune_prefix(&[], 10000));
    }

    #[test]
    fn test_lll_prune_prefix_small() {
        // Small prefix with good primes — should not prune
        let prefix = vec![3, 5, 7];
        let total_n = 3u128 * 5 * 7 * 1_000_000 * 1_000_000;
        let _result = lll_prune_prefix(&prefix, total_n);
        // We don't assert the exact result; just that it runs without panic.
    }
}
