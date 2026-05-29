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
    suffix_abundance: &[[f64; 16]],
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
            current_abundancy: comp.abundance_ratio,
        };

        explore_prefix(
            &mut curr,
            components,
            stop_threshold,
            target_min,
            target_bound,
            illegal_valuations,
            suffix_abundance,
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
    suffix_abundance: &[[f64; 16]],
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

    // Unconditional Starvation Kill: Can we reach 2.0 if we add the mathematical
    // maximum possible number of allowed factors?
    let max_allowed = 15usize.saturating_sub(curr.factors.len());
    let static_best_remaining = suffix_abundance[curr.last_idx][max_allowed];

    if curr.current_abundancy * static_best_remaining < TARGET_ABUNDANCE {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return;
    }

    // Dynamically calculate the minimum factors and maximum achievable abundancy
    // based on the modular divisibility chain (Legendre-Cattaneo / Prasad-Sunitha chains).
    let (mut dynamic_min_factors, dynamic_best_achievable) = if !curr.factors.is_empty() {
        let mut factor_mask = 0u64;
        for &f in &curr.factors {
            if f < 64 {
                factor_mask |= 1 << f;
            }
        }
        
        let mut sigma_factors_u64 = smallvec::SmallVec::<[u64; 16]>::new();
        let mut sigma_factors_large = smallvec::SmallVec::<[Uint; 4]>::new();
        for sf in &curr.sigma_factors {
            if *sf <= Uint::from(u64::MAX) {
                let sf_str = sf.to_string();
                if let Ok(val) = sf_str.parse::<u64>() {
                    sigma_factors_u64.push(val);
                }
            } else {
                sigma_factors_large.push(*sf);
            }
        }

        let mut best_abundances = smallvec::SmallVec::<[f64; 32]>::new();
        let mut current_p = 0;
        let mut current_best = 1.0;

        for comp in &components[curr.last_idx..] {
            if comp.p != current_p {
                if current_p != 0 && current_best > 1.0 {
                    best_abundances.push(current_best);
                }
                current_p = comp.p;
                current_best = 1.0;
            }

            let mut illegal = false;

            // Rule B: comp.p must not be in curr.sigma_factors
            if sigma_factors_u64.contains(&comp.p) {
                illegal = true;
            } else {
                // Rule A: comp.sigma_factors must not overlap with curr.factors
                for sf in &comp.sigma_factors {
                    if *sf <= Uint::from(u64::MAX) {
                        let sf_str = sf.to_string();
                        if let Ok(sf_u64) = sf_str.parse::<u64>() {
                            if sf_u64 < 64 {
                                if (factor_mask & (1 << sf_u64)) != 0 {
                                    illegal = true;
                                    break;
                                }
                            } else if curr.factors.contains(&sf_u64) {
                                illegal = true;
                                break;
                            }
                        }
                    }
                }
            }

            if !illegal {
                if comp.abundance_ratio > current_best {
                    current_best = comp.abundance_ratio;
                }
            }
        }
        if current_p != 0 && current_best > 1.0 {
            best_abundances.push(current_best);
        }

        best_abundances.sort_unstable_by(|a, b| b.partial_cmp(a).unwrap());

        let mut max_factors_needed = 0;
        let mut accum = curr.current_abundancy;
        for &ab in &best_abundances {
            accum *= ab;
            max_factors_needed += 1;
            if accum >= TARGET_ABUNDANCE {
                break;
            }
        }

        let mut best_15 = curr.current_abundancy;
        for &ab in best_abundances.iter().take(max_allowed) {
            best_15 *= ab;
        }

        (curr.factors.len() + max_factors_needed, best_15)
    } else {
        (MIN_PRIME_FACTORS, curr.current_abundancy * static_best_remaining)
    };

    // Enforce Lean 4 UALBF-301 Bound (Prasad & Sunitha)
    let baseline_min = if !curr.factors.contains(&3) && !curr.factors.contains(&5) {
        let skipped_3 = curr.last_idx > max_idx_3;
        let skipped_5 = curr.last_idx > max_idx_5;
        if skipped_3 && skipped_5 {
            15
        } else {
            MIN_PRIME_FACTORS
        }
    } else {
        MIN_PRIME_FACTORS
    };

    // Overflow Kill: Instantly drop if running fraction > 2.000001
    if curr.current_abundancy > 2.000001 {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return;
    }

    dynamic_min_factors = dynamic_min_factors.max(baseline_min);

    // Dynamic Starvation Kill based on modular divisibility chains
    if dynamic_best_achievable < TARGET_ABUNDANCE {
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
            suffix_abundance,
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
            suffix_abundance,
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
    suffix_abundance: &[[f64; 16]],
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
                    let saved_abundancy = curr.current_abundancy;
                    curr.current_abundancy *= comp.abundance_ratio;

                    explore_prefix(
                        curr,
                        components,
                        stop_threshold,
                        target_min,
                        target_bound,
                        illegal_valuations,
                        suffix_abundance,
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
    suffix_abundance: &[[f64; 16]],
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
                current_abundancy: curr.current_abundancy * comp.abundance_ratio,
            };

            s.spawn(move |_| {
                explore_prefix(
                    &mut child,
                    components,
                    stop_threshold,
                    target_min,
                    target_bound,
                    illegal_valuations,
                    suffix_abundance,
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
