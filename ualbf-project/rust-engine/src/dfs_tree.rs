#![allow(clippy::too_many_arguments)]

use crate::math_utils::SigmaCache;
use crate::types::{Int, Prefix, PrimePower, Uint};
use rayon::prelude::*;
use smallvec::smallvec;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;

use crate::raycast::phase4_exact_ray_casting;

/// Minimum number of distinct prime factors a QPN must have.
const MIN_PRIME_FACTORS: usize = 7;

/// The target abundance ratio for a QPN: σ(N)/N = 2 + 1/N ≈ 2.
const TARGET_ABUNDANCE: f64 = 2.0;

/// DFS depths below this threshold spawn parallel child tasks via Rayon.
/// Depths at or above this threshold use sequential push/pop recursion.
const PARALLEL_DEPTH_THRESHOLD: usize = 2;

/// Number of lock-free slots for tracking active primes (telemetry only).
const ACTIVE_PRIME_SLOTS: usize = 64;

pub struct DfsTelemetry {
    pub total_branches: usize,
    pub abundance_pruned: usize,
    pub search_space_density: f64,
}

pub fn phase2_and_4_fused(
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    sigma_cache: &SigmaCache,
) -> DfsTelemetry {
    println!("PROGRESS|PHASE|2|Fused DFS Construction & Ray-Casting");

    // Pre-compute the highest index where 3 and 5 appear in the sorted components
    // array. This turns the O(N) linear scan into an O(1) lookup inside explore_prefix.
    let max_idx_3 = components.iter().rposition(|c| c.p == 3).unwrap_or(0);
    let max_idx_5 = components.iter().rposition(|c| c.p == 5).unwrap_or(0);

    let count = AtomicUsize::new(0);
    let pruned_count = AtomicUsize::new(0);
    let abundance_pruned = AtomicUsize::new(0);
    let completed_weight_scaled = AtomicUsize::new(0);
    let total_weight_scaled: usize = components
        .iter()
        .map(|c| (10_000_000.0 / ((c.p as f64) * (c.p as f64))) as usize)
        .sum();

    // Lock-free active-primes telemetry: fixed array of AtomicU64 slots.
    // Each parallel task claims a slot on entry and clears it on exit.
    let active_primes: Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]> =
        Arc::new(std::array::from_fn(|_| AtomicU64::new(0)));

    // Top-level parallelism over components
    (0..components.len()).into_par_iter().for_each(|i| {
        let comp = &components[i];

        // Claim an active-prime slot (lock-free)
        let slot = claim_active_slot(&active_primes, comp.p);

        let mut curr = Prefix {
            n_l: comp.val,
            s_l: comp.sigma,
            last_idx: i + 1,
            factors: smallvec![comp.p],
            sigma_factors: comp.sigma_factors.clone(),
            current_abundancy: comp.abundance_ratio.clone(),
        };

        explore_prefix(
            &mut curr,
            components,
            stop_threshold,
            target_min,
            target_bound,
            illegal_valuations,
            &count,
            &pruned_count,
            &abundance_pruned,
            &completed_weight_scaled,
            total_weight_scaled,
            &active_primes,
            0,
            sigma_cache,
            max_idx_3,
            max_idx_5,
        );

        let w = (10_000_000.0 / ((comp.p as f64) * (comp.p as f64))) as usize;
        completed_weight_scaled.fetch_add(w, Ordering::Relaxed);

        // Release active-prime slot (lock-free)
        release_active_slot(&active_primes, slot);
    });

    let ap = abundance_pruned.load(Ordering::Relaxed);
    let total_branches = count.load(Ordering::Relaxed);
    let density = (total_branches as f64) / (total_weight_scaled as f64 + 1.0); // simple proxy for density
    println!(
        "DFS complete. Evaluated Branches: {} | Abundance-pruned: {}",
        total_branches, ap
    );
    DfsTelemetry {
        total_branches,
        abundance_pruned: ap,
        search_space_density: density,
    }
}

/// Claims the first available slot in the active-primes array.
/// Returns the slot index.
fn claim_active_slot(slots: &[AtomicU64; ACTIVE_PRIME_SLOTS], prime: u64) -> usize {
    for (idx, slot) in slots.iter().enumerate() {
        if slot
            .compare_exchange(0, prime, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            return idx;
        }
    }
    // Fallback: if all slots are full (shouldn't happen with 64 slots), just overwrite last
    ACTIVE_PRIME_SLOTS - 1
}

/// Releases a slot in the active-primes array.
fn release_active_slot(slots: &[AtomicU64; ACTIVE_PRIME_SLOTS], idx: usize) {
    slots[idx].store(0, Ordering::Relaxed);
}

/// Collects the currently active primes from the lock-free array (for display).
fn read_active_primes(slots: &[AtomicU64; ACTIVE_PRIME_SLOTS]) -> Vec<u64> {
    let mut primes: Vec<u64> = slots
        .iter()
        .map(|s| s.load(Ordering::Relaxed))
        .filter(|&v| v != 0)
        .collect();
    primes.sort_unstable();
    primes
}

fn explore_prefix(
    curr: &mut Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    abundance_pruned: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    max_idx_3: usize,
    max_idx_5: usize,
) {
    if curr.n_l > *target_bound {
        return;
    }

    // Telemetry Export: Sample deep prefixes for frequency analysis
    if curr.factors.len() >= 4 {
        let factors_str = curr
            .factors
            .iter()
            .map(|f| f.to_string())
            .collect::<Vec<_>>()
            .join(",");
        println!("DATA|PREFIX|{}|{}", curr.factors.len(), factors_str);
    }

    // Dynamically determine the mathematical floor based on Lean 4 UALBF-301
    // (Prasad & Sunitha: gcd(N,15)=1 ⟹ ω(N) ≥ 15)
    let dynamic_min_factors = if !curr.factors.contains(&3) && !curr.factors.contains(&5) {
        // If the search cursor has moved past the positions of 3 and 5 in the
        // sorted components array, they are permanently excluded from this branch.
        let skipped_3 = curr.last_idx > max_idx_3;
        let skipped_5 = curr.last_idx > max_idx_5;
        if skipped_3 && skipped_5 {
            15 // Enforce Prasad & Sunitha UALBF-301 Bound
        } else {
            MIN_PRIME_FACTORS
        }
    } else {
        MIN_PRIME_FACTORS
    };

    // Overflow Kill: Instantly drop if running fraction > 2.000001
    // We do exact check against 2.000001 (which is 2000001 / 1000000)
    let overflow_num = Uint::from(2000001u32);
    let overflow_den = Uint::from(1000000u32);
    let overflow_lhs = crate::exact_math::U512::mul_u256(curr.current_abundancy.num, overflow_den);
    let overflow_rhs = crate::exact_math::U512::mul_u256(curr.current_abundancy.den, overflow_num);
    if overflow_lhs.cmp(&overflow_rhs) == std::cmp::Ordering::Greater {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return;
    }

    // Unconditional Starvation Kill: Can we reach 2.0 if we add factors up to the volume constraint?

    let mut remaining_volume = *target_bound / curr.n_l;
    let mut best_remaining_num = Uint::ONE;
    let mut best_remaining_den = Uint::ONE;

    for comp in &components[curr.last_idx..] {
        if !curr.factors.contains(&comp.p) {
            if comp.val <= remaining_volume {
                remaining_volume /= comp.val;
                best_remaining_num *= comp.abundance_ratio.num;
                best_remaining_den *= comp.abundance_ratio.den;
            }
        }
    }

    let lhs = crate::exact_math::U512::mul_u256(curr.current_abundancy.num, best_remaining_num);
    let rhs_half =
        crate::exact_math::U512::mul_u256(curr.current_abundancy.den, best_remaining_den);
    // target abundance is 2.0. So we need lhs >= rhs * 2
    // We multiply rhs_half by 2
    let rhs_lo_shifted = rhs_half.1 << 1;
    let mut rhs_hi = rhs_half.0 << 1;
    if (rhs_half.1 >> 255) == Uint::ONE {
        rhs_hi += Uint::ONE;
    }
    let rhs = crate::exact_math::U512(rhs_hi, rhs_lo_shifted);

    if lhs.cmp(&rhs) == std::cmp::Ordering::Less {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return;
    }

    // Minimum prime count check (A3)
    let remaining_factors_needed = dynamic_min_factors.saturating_sub(curr.factors.len());
    if remaining_factors_needed > 0 {
        let remaining_components = components.len().saturating_sub(curr.last_idx);
        if remaining_components < remaining_factors_needed {
            return;
        }
    }

    if curr.n_l >= *stop_threshold {
        let c = count.fetch_add(1, Ordering::Relaxed) + 1;
        if c % 100_000 == 0 {
            let pr = pruned_count.load(Ordering::Relaxed);
            let comp = completed_weight_scaled.load(Ordering::Relaxed);
            let ap = abundance_pruned.load(Ordering::Relaxed);

            // Lock-free telemetry read
            let active = read_active_primes(active_primes);
            let active_count = active.len();
            let display = active
                .iter()
                .take(4)
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            let active_str = if active_count > 4 {
                format!("{}... ({} total)", display, active_count)
            } else {
                display
            };

            println!(
                "PROGRESS|UPDATE|{}|{}|{}|{}|P-Active: {} | Prefixes: {} | AbPruned: {}",
                c, total_weight_scaled, comp, pr, active_str, c, ap
            );
        }

        phase4_exact_ray_casting(
            curr,
            target_min,
            target_bound,
            illegal_valuations,
            pruned_count,
            sigma_cache,
        );
        return;
    }

    // At shallow depths, spawn parallel child tasks for work-stealing.
    // At deeper depths, use sequential push/pop to avoid allocation.
    if depth < PARALLEL_DEPTH_THRESHOLD {
        explore_prefix_parallel(
            curr,
            components,
            stop_threshold,
            target_min,
            target_bound,
            illegal_valuations,
            count,
            pruned_count,
            abundance_pruned,
            completed_weight_scaled,
            total_weight_scaled,
            active_primes,
            depth,
            sigma_cache,
            max_idx_3,
            max_idx_5,
        );
    } else {
        explore_prefix_sequential(
            curr,
            components,
            stop_threshold,
            target_min,
            target_bound,
            illegal_valuations,
            count,
            pruned_count,
            abundance_pruned,
            completed_weight_scaled,
            total_weight_scaled,
            active_primes,
            depth,
            sigma_cache,
            max_idx_3,
            max_idx_5,
        );
    }
}

/// Sequential DFS with push/pop semantics — zero allocation.
fn explore_prefix_sequential(
    curr: &mut Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    abundance_pruned: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    max_idx_3: usize,
    max_idx_5: usize,
) {
    let saved_last_idx = curr.last_idx;
    let saved_n_l = curr.n_l;
    let saved_s_l = curr.s_l;

    for i in saved_last_idx..components.len() {
        let comp = &components[i];
        if !curr.factors.contains(&comp.p) {
            if let (Some(next_n_l), Some(next_s_l)) = (
                saved_n_l.checked_mul(comp.val),
                saved_s_l.checked_mul(comp.sigma),
            ) {
                if next_n_l <= *target_bound {
                    let sigma_start_len = curr.sigma_factors.len();

                    // Push
                    curr.n_l = next_n_l;
                    curr.s_l = next_s_l;
                    curr.last_idx = i + 1;
                    curr.factors.push(comp.p);
                    curr.sigma_factors.extend_from_slice(&comp.sigma_factors);
                    let saved_abundancy = curr.current_abundancy.clone();
                    curr.current_abundancy =
                        curr.current_abundancy.exact_mul(&comp.abundance_ratio);

                    explore_prefix(
                        curr,
                        components,
                        stop_threshold,
                        target_min,
                        target_bound,
                        illegal_valuations,
                        count,
                        pruned_count,
                        abundance_pruned,
                        completed_weight_scaled,
                        total_weight_scaled,
                        active_primes,
                        depth + 1,
                        sigma_cache,
                        max_idx_3,
                        max_idx_5,
                    );

                    // Pop
                    curr.n_l = saved_n_l;
                    curr.s_l = saved_s_l;
                    curr.last_idx = saved_last_idx;
                    curr.factors.pop();
                    curr.sigma_factors.truncate(sigma_start_len);
                    curr.current_abundancy = saved_abundancy;
                }
            }
        }
    }
}

/// Parallel DFS at shallow depths — clones prefixes for each child to enable work-stealing.
fn explore_prefix_parallel(
    curr: &mut Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    abundance_pruned: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    max_idx_3: usize,
    max_idx_5: usize,
) {
    // Collect eligible children indices
    let eligible: Vec<usize> = (curr.last_idx..components.len())
        .filter(|&i| {
            let comp = &components[i];
            !curr.factors.contains(&comp.p)
                && curr
                    .n_l
                    .checked_mul(comp.val)
                    .is_some_and(|v| v <= *target_bound)
                && curr.s_l.checked_mul(comp.sigma).is_some()
        })
        .collect();

    // Spawn parallel tasks for each eligible child
    rayon::scope(|s| {
        for i in eligible {
            let comp = &components[i];
            let next_n_l = curr.n_l.checked_mul(comp.val).unwrap();
            let next_s_l = curr.s_l.checked_mul(comp.sigma).unwrap();

            let mut child = Prefix {
                n_l: next_n_l,
                s_l: next_s_l,
                last_idx: i + 1,
                factors: {
                    let mut f = curr.factors.clone();
                    f.push(comp.p);
                    f
                },
                sigma_factors: {
                    let mut sf = curr.sigma_factors.clone();
                    sf.extend_from_slice(&comp.sigma_factors);
                    sf
                },
                current_abundancy: curr.current_abundancy.exact_mul(&comp.abundance_ratio),
            };

            s.spawn(move |_| {
                explore_prefix(
                    &mut child,
                    components,
                    stop_threshold,
                    target_min,
                    target_bound,
                    illegal_valuations,
                    count,
                    pruned_count,
                    abundance_pruned,
                    completed_weight_scaled,
                    total_weight_scaled,
                    active_primes,
                    depth + 1,
                    sigma_cache,
                    max_idx_3,
                    max_idx_5,
                );
            });
        }
    });
}
