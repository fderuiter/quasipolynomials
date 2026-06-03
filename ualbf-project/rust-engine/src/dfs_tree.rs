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
    let mut max_allowed = 0;
    let mut temp_n = curr.n_l;
    let mut last_p = 0;
    for comp in &components[curr.last_idx..] {
        if comp.p != last_p {
            if let Some(next_n) = temp_n.checked_mul(comp.val) {
                if next_n <= *target_bound {
                    temp_n = next_n;
                    max_allowed += 1;
                    last_p = comp.p;
                    if max_allowed + curr.factors.len() >= suffix_abundance.len() - 1 {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }
    
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
        
        let sigma_factors_u64 = &curr.sigma_factors_u64;
        let mut sigma_factors_large = smallvec::SmallVec::<[Uint; 4]>::new();
        for sf in &curr.sigma_factors {
            if *sf > Uint::from_u128((u64::MAX) as u128) {
                sigma_factors_large.push(*sf);
            }
        }

        let mut best_abundances = smallvec::SmallVec::<[u128; 32]>::new();
        let mut current_p = 0;
        let mut current_best = 1u128 << 64;

        for comp in &components[curr.last_idx..] {
            if comp.p != current_p {
                if current_p != 0 && current_best > (1u128 << 64) {
                    best_abundances.push(current_best);
                }
                current_p = comp.p;
                current_best = 1u128 << 64;
            }

            let mut illegal = false;
            // Rule B: comp.p must not be in curr.sigma_factors
            if sigma_factors_u64.contains(&comp.p) {
                illegal = true;
            } else {
                // Rule A: comp.sigma_factors must not overlap with curr.factors
                for sf in &comp.sigma_factors {
                    if *sf <= Uint::from_u128((u64::MAX) as u128) {
                        let sf_u64 = sf.as_u64();
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

            // Deep Divisibility Chains: recursively check factor inclusion/exclusion ON THE NEW COMPONENT
            if !illegal {
                let mut new_factors = curr.factors.clone();
                new_factors.push(comp.p);
                let mut new_sigma_factors = curr.sigma_factors_u64.clone();
                for sf in &comp.sigma_factors {
                    if *sf <= Uint::from_u128((u64::MAX) as u128) {
                        new_sigma_factors.push(sf.as_u64());
                    }
                }
                if !crate::obstruction::verify_deep_divisibility_chain(&new_factors, &new_sigma_factors, false) {
                    illegal = true;
                }
            }

            if !illegal {
                if comp.abundance_fp > current_best {
                    current_best = comp.abundance_fp;
                }
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

    let c3 = curr.factors.contains(&3) as u8;
    let c5 = curr.factors.contains(&5) as u8;
    let s3 = (curr.last_idx > max_idx_3) as u8;
    let s5 = (curr.last_idx > max_idx_5) as u8;
    let baseline_min = unsafe { crate::lean_ffi::ualbf_evaluate_baseline_min_ffi(c3, c5, s3, s5) };

    // Overflow Kill: Instantly drop if running fraction > 2.000001
    // (s_l / n_l) > 2 + 1/1,000,000
    // s_l * 1,000,000 > n_l * 2,000,001
    let mul1 = Uint::from_u128((1_000_000u64) as u128);
    let mul2 = Uint::from_u128((2_000_001u64) as u128);
    if curr.s_l * mul1 > curr.n_l * mul2 {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return false;
    }

    dynamic_min_factors = dynamic_min_factors.max(baseline_min as usize);

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
) {
    if !check_and_evaluate_node(
        curr, components, stop_threshold, target_min, target_bound,
        illegal_valuations, suffix_abundance, count, pruned_count,
        abundance_pruned, completed_weight_scaled, total_weight_scaled,
        active_primes, sigma_cache, reporter, max_idx_3, max_idx_5
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
        );
    }

}

struct Frame {
    i: usize,
    saved_last_idx: usize,
    saved_n_l: Uint,
    saved_s_l: Uint,
    sigma_start_len: usize,
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
) {
    let mut stack = Vec::with_capacity(128);
    stack.push(Frame {
        i: curr.last_idx,
        saved_last_idx: curr.last_idx,
        saved_n_l: curr.n_l,
        saved_s_l: curr.s_l,
        sigma_start_len: curr.sigma_factors.len(),
    });

    while let Some(mut frame) = stack.pop() {
        let mut pushed = false;
        while frame.i < components.len() {
            let i = frame.i;
            frame.i += 1;
            
            let comp = &components[i];
            if curr.factors.contains(&comp.p) {
                continue;
            }
            
            let lazy_res = resolve_lazy_factors(comp, &lazy_cache[i]);
            if lazy_res.is_err() { continue; }
            let extra_factors = lazy_res.unwrap();
            
            if let (Some(next_n_l), Some(next_s_l)) = (frame.saved_n_l.checked_mul(comp.val), frame.saved_s_l.checked_mul(comp.sigma)) {
                if next_n_l <= *target_bound {
                    // Push state to curr
                    curr.n_l = next_n_l;
                    curr.s_l = next_s_l;
                    curr.last_idx = i + 1;
                    curr.factors.push(comp.p);
                    curr.sigma_factors.extend_from_slice(&comp.sigma_factors);
                    curr.sigma_factors.extend_from_slice(&extra_factors);
                    
                    let should_explore = check_and_evaluate_node(
                        curr, components, stop_threshold, target_min, target_bound,
                        illegal_valuations, suffix_abundance, count, pruned_count,
                        abundance_pruned, completed_weight_scaled, total_weight_scaled,
                        active_primes, sigma_cache, reporter, max_idx_3, max_idx_5
                    );
                    
                    if should_explore {
                        stack.push(frame);
                        stack.push(Frame {
                            i: curr.last_idx,
                            saved_last_idx: curr.last_idx,
                            saved_n_l: curr.n_l,
                            saved_s_l: curr.s_l,
                            sigma_start_len: curr.sigma_factors.len(),
                        });
                        pushed = true;
                        break;
                    }
                    
                    // Pop state from curr
                    curr.n_l = frame.saved_n_l;
                    curr.s_l = frame.saved_s_l;
                    curr.last_idx = frame.saved_last_idx;
                    curr.factors.pop();
                    curr.sigma_factors.truncate(frame.sigma_start_len);
                }
            }
        }
        
        if !pushed {
            if let Some(parent) = stack.last() {
                curr.n_l = parent.saved_n_l;
                curr.s_l = parent.saved_s_l;
                curr.last_idx = parent.saved_last_idx;
                curr.factors.pop();
                curr.sigma_factors.truncate(parent.sigma_start_len);
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

// ---- LEAN ORCHESTRATION ----

pub struct DfsContext<'a> {
    pub curr: &'a mut Prefix,
    pub components: &'a [PrimePower],
    pub stop_threshold: &'a Uint,
    pub target_min: &'a Uint,
    pub target_bound: &'a Uint,
    pub illegal_valuations: &'a [(Int, Int)],
    pub suffix_abundance: &'a [u128],
    pub count: &'a AtomicUsize,
    pub pruned_count: &'a AtomicUsize,
    pub abundance_pruned: &'a AtomicUsize,
    pub completed_weight_scaled: &'a AtomicUsize,
    pub total_weight_scaled: usize,
    pub active_primes: &'a Arc<[AtomicU64; ACTIVE_PRIME_SLOTS]>,
    pub sigma_cache: &'a SigmaCache,
    pub reporter: Option<&'a crossbeam_channel::Sender<String>>,
    pub max_idx_3: usize,
    pub max_idx_5: usize,
    pub lazy_cache: &'a Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>>,
    pub saved_states: Vec<Frame>,
    pub dyn_min_factors: u32,
    pub should_explore_memo: bool,
}

#[no_mangle]
pub extern "C" fn rust_dfs_get_components_len(ctx: u64) -> u32 {
    let dfs_ctx = unsafe { &*(ctx as *const DfsContext) };
    dfs_ctx.components.len() as u32
}

#[no_mangle]
pub extern "C" fn rust_dfs_get_curr_last_idx(ctx: u64) -> u32 {
    let dfs_ctx = unsafe { &*(ctx as *const DfsContext) };
    dfs_ctx.curr.last_idx as u32
}

#[no_mangle]
pub extern "C" fn rust_dfs_try_push(ctx: u64, i: u32) -> bool {
    let dfs_ctx = unsafe { &mut *(ctx as *mut DfsContext) };
    let i = i as usize;
    let comp = &dfs_ctx.components[i];
    if dfs_ctx.curr.factors.contains(&comp.p) {
        return false;
    }
    
    let lazy_res = resolve_lazy_factors(comp, &dfs_ctx.lazy_cache[i]);
    if lazy_res.is_err() { return false; }
    let extra_factors = lazy_res.unwrap();
    
    if let (Some(next_n_l), Some(next_s_l)) = (dfs_ctx.curr.n_l.checked_mul(comp.val), dfs_ctx.curr.s_l.checked_mul(comp.sigma)) {
        if next_n_l <= *dfs_ctx.target_bound {
            dfs_ctx.saved_states.push(Frame {
                i: i,
                saved_last_idx: dfs_ctx.curr.last_idx,
                saved_n_l: dfs_ctx.curr.n_l,
                saved_s_l: dfs_ctx.curr.s_l,
                sigma_start_len: dfs_ctx.curr.sigma_factors.len(),
            });
            dfs_ctx.curr.n_l = next_n_l;
            dfs_ctx.curr.s_l = next_s_l;
            dfs_ctx.curr.last_idx = i + 1;
            dfs_ctx.curr.factors.push(comp.p);
            dfs_ctx.curr.sigma_factors.extend_from_slice(&comp.sigma_factors);
            dfs_ctx.curr.sigma_factors.extend_from_slice(&extra_factors);
            return true;
        }
    }
    false
}

#[no_mangle]
pub extern "C" fn rust_dfs_pop(ctx: u64) {
    let dfs_ctx = unsafe { &mut *(ctx as *mut DfsContext) };
    if let Some(parent) = dfs_ctx.saved_states.pop() {
        dfs_ctx.curr.n_l = parent.saved_n_l;
        dfs_ctx.curr.s_l = parent.saved_s_l;
        dfs_ctx.curr.last_idx = parent.saved_last_idx;
        dfs_ctx.curr.factors.pop();
        dfs_ctx.curr.sigma_factors.truncate(parent.sigma_start_len);
    }
}

#[no_mangle]
pub extern "C" fn rust_dfs_get_prasad_sunitha_info(ctx: u64) -> u32 {
    let dfs_ctx = unsafe { &*(ctx as *const DfsContext) };
    let curr = &dfs_ctx.curr;
    let mut info = 0;
    if curr.factors.contains(&3) { info |= 1; }
    if curr.factors.contains(&5) { info |= 2; }
    if curr.last_idx > dfs_ctx.max_idx_3 { info |= 4; }
    if curr.last_idx > dfs_ctx.max_idx_5 { info |= 8; }
    info
}

#[no_mangle]
pub extern "C" fn rust_dfs_check_evaluate(ctx: u64, baseline_min: u32) -> bool {
    let dfs_ctx = unsafe { &mut *(ctx as *mut DfsContext) };
    
    // Unconditional Starvation Kill
    let mut max_allowed = 0;
    let mut temp_n = dfs_ctx.curr.n_l;
    let mut last_p = 0;
    for comp in &dfs_ctx.components[dfs_ctx.curr.last_idx..] {
        if comp.p != last_p {
            if let Some(next_n) = temp_n.checked_mul(comp.val) {
                if next_n <= *dfs_ctx.target_bound {
                    temp_n = next_n;
                    max_allowed += 1;
                    last_p = comp.p;
                    if max_allowed + dfs_ctx.curr.factors.len() >= dfs_ctx.suffix_abundance.len() - 1 {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }
    
    let max_allowed = max_allowed.min(dfs_ctx.suffix_abundance.len() - 1);
    let static_best_remaining = dfs_ctx.suffix_abundance[max_allowed];

    let static_best_u256 = Uint::from_u128((static_best_remaining) as u128);
    let lhs = dfs_ctx.curr.s_l * static_best_u256;
    let rhs = dfs_ctx.curr.n_l << 65; 
    
    if lhs < rhs {
        dfs_ctx.abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return false;
    }

    let (mut dynamic_min_factors, dynamic_best_achievable_fp) = if !dfs_ctx.curr.factors.is_empty() {
        let mut factor_mask = 0u64;
        for &f in &dfs_ctx.curr.factors {
            if f < 64 {
                factor_mask |= 1 << f;
            }
        }
        
        let sigma_factors_u64 = &dfs_ctx.curr.sigma_factors_u64;
        let mut sigma_factors_large = smallvec::SmallVec::<[Uint; 4]>::new();
        for sf in &dfs_ctx.curr.sigma_factors {
            if *sf > Uint::from_u128((u64::MAX) as u128) {
                sigma_factors_large.push(*sf);
            }
        }

        let mut best_abundances = smallvec::SmallVec::<[u128; 32]>::new();
        let mut current_p = 0;
        let mut current_best = 1u128 << 64;

        for comp in &dfs_ctx.components[dfs_ctx.curr.last_idx..] {
            if comp.p != current_p {
                if current_p != 0 && current_best > (1u128 << 64) {
                    best_abundances.push(current_best);
                }
                current_p = comp.p;
                current_best = 1u128 << 64;
            }

            let mut illegal = false;
            if sigma_factors_u64.contains(&comp.p) {
                illegal = true;
            } else {
                for sf in &comp.sigma_factors {
                    if *sf <= Uint::from_u128((u64::MAX) as u128) {
                        let sf_u64 = sf.as_u64();
                        if sf_u64 < 64 {
                            if (factor_mask & (1 << sf_u64)) != 0 {
                                illegal = true;
                                break;
                            }
                        } else if dfs_ctx.curr.factors.contains(&sf_u64) {
                            illegal = true;
                            break;
                        }
                    }
                }
            }

            if !illegal {
                let mut new_factors = dfs_ctx.curr.factors.clone();
                new_factors.push(comp.p);
                let mut new_sigma_factors = dfs_ctx.curr.sigma_factors_u64.clone();
                for sf in &comp.sigma_factors {
                    if *sf <= Uint::from_u128((u64::MAX) as u128) {
                        new_sigma_factors.push(sf.as_u64());
                    }
                }
                if !crate::obstruction::verify_deep_divisibility_chain(&new_factors, &new_sigma_factors, false) {
                    illegal = true;
                }
            }

            if !illegal {
                if comp.abundance_fp > current_best {
                    current_best = comp.abundance_fp;
                }
            }
        }
        if current_p != 0 && current_best > (1u128 << 64) {
            best_abundances.push(current_best);
        }

        best_abundances.sort_unstable_by(|a, b| b.cmp(a));

        let mut max_factors_needed = 0;
        let mut accum_lhs = dfs_ctx.curr.s_l;
        let mut accum_rhs = dfs_ctx.curr.n_l << 1;
        
        for &ab in &best_abundances {
            let ab_u256 = Uint::from_u128((ab) as u128);
            accum_lhs = (accum_lhs * ab_u256 + ((Uint::one() << 64) - Uint::one())) >> 64;
            max_factors_needed += 1;
            if accum_lhs >= accum_rhs {
                break;
            }
        }

        let mut best_15: Uint = Uint::one() << 64;
        for &ab in best_abundances.iter().take(max_allowed) {
            best_15 = (best_15 * Uint::from_u128((ab) as u128) + ((Uint::one() << 64) - Uint::one())) >> 64;
        }
        
        let best_15_u128 = best_15.as_u128();

        (dfs_ctx.curr.factors.len() + max_factors_needed, best_15_u128)
    } else {
        (MIN_PRIME_FACTORS, static_best_remaining)
    };

    let mul1 = Uint::from_u128((1_000_000u64) as u128);
    let mul2 = Uint::from_u128((2_000_001u64) as u128);
    if dfs_ctx.curr.s_l * mul1 > dfs_ctx.curr.n_l * mul2 {
        dfs_ctx.abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return false;
    }

    dynamic_min_factors = dynamic_min_factors.max(baseline_min as usize);

    let dyn_best_u256 = Uint::from_u128((dynamic_best_achievable_fp) as u128);
    if dfs_ctx.curr.s_l * dyn_best_u256 < dfs_ctx.curr.n_l << 65 {
        dfs_ctx.abundance_pruned.fetch_add(1, Ordering::Relaxed);
        return false;
    }

    let remaining_factors_needed = dynamic_min_factors.saturating_sub(dfs_ctx.curr.factors.len());
    if remaining_factors_needed > 0 {
        let remaining_components = dfs_ctx.components.len().saturating_sub(dfs_ctx.curr.last_idx);
        if remaining_components < remaining_factors_needed {
            return false;
        }
    }

    if dfs_ctx.curr.n_l >= *dfs_ctx.stop_threshold {
        let c = dfs_ctx.count.fetch_add(1, Ordering::Relaxed) + 1;
        if c % 100_000 == 0 {
            let pr = dfs_ctx.pruned_count.load(Ordering::Relaxed);
            let comp = dfs_ctx.completed_weight_scaled.load(Ordering::Relaxed);
            let ap = dfs_ctx.abundance_pruned.load(Ordering::Relaxed);

            let active = read_active_primes(dfs_ctx.active_primes);
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
                c, dfs_ctx.total_weight_scaled, comp, pr, active_str, c, ap
            );
        }

        phase4_exact_ray_casting(
            dfs_ctx.curr,
            dfs_ctx.target_min,
            dfs_ctx.target_bound,
            dfs_ctx.illegal_valuations,
            dfs_ctx.pruned_count,
            dfs_ctx.sigma_cache,
            dfs_ctx.reporter,
        );
        return false;
    }
    
    true
}

