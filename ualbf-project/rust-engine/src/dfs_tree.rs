#![allow(clippy::too_many_arguments)]

use crate::types::{UintExt, IntExt};
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
pub const ACTIVE_PRIME_SLOTS: usize = 64;

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
    suffix_abundance: &[u128],
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<String>>,
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

    let lazy_cache: Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> = Arc::new(std::iter::repeat_with(std::sync::OnceLock::new).take(components.len()).collect());
    let backbone = Arc::new(crate::backbone::SearchBackbone::new(components, &lazy_cache));

    // Top-level parallelism over components
    (0..components.len()).into_par_iter().for_each(|i| {
        let comp = &components[i];

        let lazy_res = resolve_lazy_factors(comp, &lazy_cache[i]);
        if lazy_res.is_err() {
            return;
        }
        let extra_factors = lazy_res.unwrap();

        // Claim an active-prime slot (lock-free)
        let slot = claim_active_slot(&active_primes, comp.p);

        let mut curr = Prefix {
            n_l: comp.val,
            s_l: comp.sigma,
            last_idx: i + 1,
            factors: vec![comp.p],
            sigma_factors_u64: {
                let mut su = Vec::new();
                for sf in &comp.sigma_factors {
                    if *sf <= Uint::from_u128((u64::MAX) as u128) {
                        su.push(sf.as_u64());
                    }
                }
                for sf in &extra_factors {
                    if *sf <= Uint::from_u128((u64::MAX) as u128) {
                        su.push(sf.as_u64());
                    }
                }
                su
            },
            sigma_factors: {
                let mut sf = comp.sigma_factors.clone();
                sf.extend_from_slice(&extra_factors);
                sf
            },
            active_mask: backbone.compatibility_matrix[i].clone(),
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
            reporter,
            max_idx_3,
            max_idx_5,
            &lazy_cache,
            &backbone,
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


pub fn check_and_evaluate_node(
    curr: &mut Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    suffix_abundance: &[u128],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    abundance_pruned: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<String>>,
    max_idx_3: usize,
    max_idx_5: usize,
    backbone: &crate::backbone::SearchBackbone,
) -> bool {

    if curr.n_l > *target_bound {
        return false;
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
    
    // Calculate the maximum number of new prime factors we can possibly add
    // without exceeding the target_bound.
    let mut max_allowed = backbone.max_allowed_factors(curr.last_idx, curr.n_l, *target_bound);
    
    // Safety clamp (max suffix length is 127 in table)
    let max_allowed = max_allowed.min(suffix_abundance.len() - 1);
    
    let static_best_remaining = suffix_abundance[max_allowed];

    // s_l * static_best_remaining < 2 * n_l * 2^64
    let static_best_u256 = Uint::from_u128((static_best_remaining) as u128);
    let lhs = curr.s_l * static_best_u256;
    let rhs = curr.n_l << 65; // 2 * n_l * 2^64
    
    if lhs < rhs {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return false;
    }

    // Dynamically calculate the minimum factors and maximum achievable abundancy
    // based on the modular divisibility chain (Legendre-Cattaneo / Prasad-Sunitha chains).
    let (mut dynamic_min_factors, dynamic_best_achievable_fp) = if !curr.factors.is_empty() {
        let mut factor_mask = 0u64;
        for &f in &curr.factors {
            if f < 64 {
                factor_mask |= 1 << f;
            }
        }
        
        let mut best_abundances = smallvec::SmallVec::<[u128; 32]>::new();
        let mut current_p = 0;
        let mut current_best = 1u128 << 64;

        let mask = &curr.active_mask;
        let start_idx = curr.last_idx;
        let mut block_idx = start_idx / 64;
        if block_idx < mask.len() {
            let mut block = mask[block_idx] & (!0 << (start_idx % 64));
            loop {
                while block != 0 {
                    let tz = block.trailing_zeros();
                    let j = block_idx * 64 + tz as usize;
                    let comp = &components[j];
                    
                    if comp.p != current_p {
                        if current_p != 0 && current_best > (1u128 << 64) {
                            best_abundances.push(current_best);
                        }
                        current_p = comp.p;
                        current_best = 1u128 << 64;
                    }
                    if comp.abundance_fp > current_best {
                        current_best = comp.abundance_fp;
                    }
                    block &= block - 1; // clear lowest set bit
                }
                block_idx += 1;
                if block_idx >= mask.len() {
                    break;
                }
                block = mask[block_idx];
            }
        }
        if current_p != 0 && current_best > (1u128 << 64) {
            best_abundances.push(current_best);
        }

        best_abundances.sort_unstable_by(|a, b| b.cmp(a));

        let mut max_factors_needed = 0;
        // Evaluate if we can reach 2.0. We start with running abundancy = (s_l << 64)/n_l.
        let mut accum_lhs = curr.s_l;
        let mut accum_rhs = curr.n_l << 1; // 2.0
        
        for &ab in &best_abundances {
            let ab_u256 = Uint::from_u128((ab) as u128);
            accum_lhs = (accum_lhs * ab_u256 + ((Uint::one() << 64) - Uint::one())) >> 64;
            max_factors_needed += 1;
            if accum_lhs >= accum_rhs {
                break;
            }
        }

        let mut best_15: Uint = Uint::one() << 64; // Product of multipliers
        for &ab in best_abundances.iter().take(max_allowed) {
            best_15 = (best_15 * Uint::from_u128((ab) as u128) + ((Uint::one() << 64) - Uint::one())) >> 64;
        }
        
        // Final LHS = (s_l * best_15) >> 64
        let best_15_u128 = best_15.as_u128();

        (curr.factors.len() + max_factors_needed, best_15_u128)
    } else {
        (MIN_PRIME_FACTORS, static_best_remaining)
    };

    // Enforce Lean 4 UALBF-301 Bound (Prasad & Sunitha)
    let baseline_min = if !curr.factors.contains(&3) && !curr.factors.contains(&5) {
        let skipped_3 = curr.last_idx > max_idx_3;
        let skipped_5 = curr.last_idx > max_idx_5;
        if skipped_3 && skipped_5 {
            16
        } else {
            MIN_PRIME_FACTORS
        }
    } else {
        MIN_PRIME_FACTORS
    };

    // Overflow Kill: Instantly drop if running fraction > 2.000001
    // (s_l / n_l) > 2 + 1/1,000,000
    // s_l * 1,000,000 > n_l * 2,000,001
    let mul1 = Uint::from_u128((1_000_000u64) as u128);
    let mul2 = Uint::from_u128((2_000_001u64) as u128);
    if curr.s_l * mul1 > curr.n_l * mul2 {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return false;
    }

    dynamic_min_factors = dynamic_min_factors.max(baseline_min);

    // Dynamic Starvation Kill based on modular divisibility chains
    let dyn_best_u256 = Uint::from_u128((dynamic_best_achievable_fp) as u128);
    if curr.s_l * dyn_best_u256 < curr.n_l << 65 {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return false;
    }

    // Minimum prime count check (A3)
    let remaining_factors_needed = dynamic_min_factors.saturating_sub(curr.factors.len());
    if remaining_factors_needed > 0 {
        let remaining_components = components.len().saturating_sub(curr.last_idx);
        if remaining_components < remaining_factors_needed {
            return false;
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
            reporter,
        );
        return false;
    }

    // At shallow depths, spawn parallel child tasks for work-stealing.
    // At deeper depths, use sequential push/pop to avoid allocation.
    
    true
}

pub fn explore_prefix(
    curr: &mut Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    suffix_abundance: &[u128],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    abundance_pruned: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<String>>,
    max_idx_3: usize,
    max_idx_5: usize,
    lazy_cache: &Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>>,
    backbone: &crate::backbone::SearchBackbone,
) {
    if !check_and_evaluate_node(
        curr, components, stop_threshold, target_min, target_bound,
        illegal_valuations, suffix_abundance, count, pruned_count,
        abundance_pruned, completed_weight_scaled, total_weight_scaled,
        active_primes, sigma_cache, reporter, max_idx_3, max_idx_5, backbone
    ) {
        return;
    }
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
            reporter,
            max_idx_3,
            max_idx_5,
            &lazy_cache,
            &backbone,
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
            reporter,
            max_idx_3,
            max_idx_5,
            &lazy_cache,
            &backbone,
        );
    }

}

struct Frame {
    i: usize,
    saved_last_idx: usize,
    saved_n_l: Uint,
    saved_s_l: Uint,
    sigma_start_len: usize,
    saved_active_mask: Vec<u64>,
}

fn explore_prefix_sequential(
    curr: &mut Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    suffix_abundance: &[u128],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    abundance_pruned: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<String>>,
    max_idx_3: usize,
    max_idx_5: usize,
    lazy_cache: &Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>>,
    backbone: &crate::backbone::SearchBackbone,
) {
    let mut stack = Vec::with_capacity(128);
    stack.push(Frame {
        i: curr.last_idx,
        saved_last_idx: curr.last_idx,
        saved_n_l: curr.n_l,
        saved_s_l: curr.s_l,
        sigma_start_len: curr.sigma_factors.len(),
        saved_active_mask: curr.active_mask.clone(),
    });

    while let Some(mut frame) = stack.pop() {
        let mut pushed = false;
        // Efficient bitmask iteration
        let mask = &frame.saved_active_mask;
        let mut block_idx = frame.i / 64;
        let mut found_i = None;
        if block_idx < mask.len() {
            let mut block = mask[block_idx] & (!0 << (frame.i % 64));
            'search: loop {
                while block != 0 {
                    let tz = block.trailing_zeros();
                    let i = block_idx * 64 + tz as usize;
                    block &= block - 1;
                    frame.i = i + 1; // save next iteration point
                    
                    let comp = &components[i];
                    let lazy_res = resolve_lazy_factors(comp, &lazy_cache[i]);
                    if lazy_res.is_err() { continue; }
                    let extra_factors = lazy_res.unwrap();
                    
                    if let (Some(next_n_l), Some(next_s_l)) = (frame.saved_n_l.checked_mul(comp.val), frame.saved_s_l.checked_mul(comp.sigma)) {
                        if next_n_l <= *target_bound {
                            found_i = Some((i, comp, extra_factors));
                            break 'search;
                        }
                    }
                }
                block_idx += 1;
                if block_idx >= mask.len() {
                    break;
                }
                block = mask[block_idx];
            }
        }
        
        if let Some((i, comp, extra_factors)) = found_i {
            // Push state to curr
            curr.n_l = frame.saved_n_l.checked_mul(comp.val).unwrap();
            curr.s_l = frame.saved_s_l.checked_mul(comp.sigma).unwrap();
            curr.last_idx = i + 1;
            curr.factors.push(comp.p);
            curr.sigma_factors.extend_from_slice(&comp.sigma_factors);
            curr.sigma_factors.extend_from_slice(&extra_factors);
            
            let mut new_mask = frame.saved_active_mask.clone();
            let row = &backbone.compatibility_matrix[i];
            for k in 0..new_mask.len() {
                new_mask[k] &= row[k];
            }
            curr.active_mask = new_mask;
            
            let should_explore = check_and_evaluate_node(
                curr, components, stop_threshold, target_min, target_bound,
                illegal_valuations, suffix_abundance, count, pruned_count,
                abundance_pruned, completed_weight_scaled, total_weight_scaled,
                active_primes, sigma_cache, reporter, max_idx_3, max_idx_5, backbone
            );
            
            if should_explore {
                stack.push(frame);
                stack.push(Frame {
                    i: curr.last_idx,
                    saved_last_idx: curr.last_idx,
                    saved_n_l: curr.n_l,
                    saved_s_l: curr.s_l,
                    sigma_start_len: curr.sigma_factors.len(),
                    saved_active_mask: curr.active_mask.clone(),
                });
                pushed = true;
            } else {
                // Pop state from curr
                curr.n_l = frame.saved_n_l;
                curr.s_l = frame.saved_s_l;
                curr.last_idx = frame.saved_last_idx;
                curr.factors.pop();
                curr.sigma_factors.truncate(frame.sigma_start_len);
                curr.active_mask = frame.saved_active_mask.clone();
                stack.push(frame); // retry this frame
                pushed = true;
            }
        }
        
        if !pushed {
            if let Some(parent) = stack.last() {
                curr.n_l = parent.saved_n_l;
                curr.s_l = parent.saved_s_l;
                curr.last_idx = parent.saved_last_idx;
                curr.factors.pop();
                curr.sigma_factors.truncate(parent.sigma_start_len);
                curr.active_mask = parent.saved_active_mask.clone();
            }
        }
    }
}
fn explore_prefix_parallel(
    curr: &mut Prefix,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    suffix_abundance: &[u128],
    count: &AtomicUsize,
    pruned_count: &AtomicUsize,
    abundance_pruned: &AtomicUsize,
    completed_weight_scaled: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<String>>,
    max_idx_3: usize,
    max_idx_5: usize,
    lazy_cache: &Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>>,
    backbone: &crate::backbone::SearchBackbone,
) {
    // Collect eligible children indices
    let mut eligible = Vec::new();
    let mask = &curr.active_mask;
    let start_idx = curr.last_idx;
    let mut block_idx = start_idx / 64;
    if block_idx < mask.len() {
        let mut block = mask[block_idx] & (!0 << (start_idx % 64));
        loop {
            while block != 0 {
                let tz = block.trailing_zeros();
                let i = block_idx * 64 + tz as usize;
                block &= block - 1;
                let comp = &components[i];
                if curr.n_l.checked_mul(comp.val).is_some_and(|v| v <= *target_bound) {
                    eligible.push(i);
                }
            }
            block_idx += 1;
            if block_idx >= mask.len() {
                break;
            }
            block = mask[block_idx];
        }
    }

    // Spawn parallel tasks for each eligible child
    rayon::scope(|s| {
        for i in eligible {
            let comp = &components[i];
            let lazy_res = resolve_lazy_factors(comp, &lazy_cache[i]);
            if lazy_res.is_err() {
                continue;
            }
            let extra_factors = lazy_res.unwrap();

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
                sigma_factors_u64: {
                    let mut su = curr.sigma_factors_u64.clone();
                    for sf in &comp.sigma_factors {
                        if *sf <= Uint::from_u128((u64::MAX) as u128) {
                            su.push(sf.as_u64());
                        }
                    }
                    for sf in &extra_factors {
                        if *sf <= Uint::from_u128((u64::MAX) as u128) {
                            su.push(sf.as_u64());
                        }
                    }
                    su
                },
                sigma_factors: {
                    let mut sf = curr.sigma_factors.clone();
                    sf.extend_from_slice(&comp.sigma_factors);
                    sf.extend_from_slice(&extra_factors);
                    sf
                },
                active_mask: {
                    let mut new_mask = curr.active_mask.clone();
                    let row = &backbone.compatibility_matrix[i];
                    for k in 0..new_mask.len() {
                        new_mask[k] &= row[k];
                    }
                    new_mask
                },
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
                    reporter,
                    max_idx_3,
                    max_idx_5,
                    lazy_cache,
                    backbone,
                );
            });
        }
    });
}

pub fn resolve_lazy_factors(
    comp: &PrimePower,
    cache_slot: &std::sync::OnceLock<Result<Vec<Uint>, ()>>
) -> Result<Vec<Uint>, ()> {
    cache_slot.get_or_init(|| {
        if comp.needs_rho.is_empty() {
            return Ok(Vec::new());
        }
        let mut extra = Vec::new();
        for &rem in &comp.needs_rho {
            let factors = crate::math_utils::rho_factor_u256(rem);
            for &q in &factors {
                let q_mod_8 = (q % Uint::from_u128((8u32) as u128)).as_u32();
                if q_mod_8 == 5 || q_mod_8 == 7 {
                    return Err(());
                }
            }
            extra.extend(factors);
        }
        extra.sort_unstable();
        Ok(extra)
    }).clone()
}
