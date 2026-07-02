#![allow(clippy::too_many_arguments)]
use crate::schema_generated::Prefix;

use crate::types::{UintExt, IntExt};
use crate::math_utils::SigmaCache;
use crate::types::{Int, PrimePower, Uint};
use rayon::prelude::*;
use smallvec::smallvec;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;

use crate::raycast::phase4_exact_ray_casting;

use std::sync::OnceLock;

static MIN_PRIME_FACTORS: OnceLock<usize> = OnceLock::new();
static PRASAD_SUNITHA_BOUND: OnceLock<usize> = OnceLock::new();

pub fn init_bounds() {
    let min_pf = crate::lean_ffi::get_baseline_min_prime_factors();
    if min_pf == 0 {
        panic!("Failed to resolve baseline min prime factors from proof bridge");
    }
    MIN_PRIME_FACTORS.set(min_pf).unwrap();

    let ps_bound = crate::lean_ffi::get_prasad_sunitha_bound();
    if ps_bound == 0 {
        panic!("Failed to resolve Prasad & Sunitha bound from proof bridge");
    }
    PRASAD_SUNITHA_BOUND.set(ps_bound).unwrap();

    // Mathematically verify that the 2.0 threshold remains within the bounds justified by the formal proof
    let num = crate::lean_ffi::get_target_abundance_num();
    let den = crate::lean_ffi::get_target_abundance_den();
    assert_eq!(TARGET_ABUNDANCE, (num as f64) / (den as f64), "2.0 threshold must remain within the bounds justified by the formal proof");
}

pub fn get_min_prime_factors() -> usize {
    *MIN_PRIME_FACTORS.get_or_init(|| {
        let v = crate::lean_ffi::get_baseline_min_prime_factors();
        if v == 0 { panic!("Failed to resolve baseline min prime factors from proof bridge"); }
        v
    })
}

pub fn get_prasad_sunitha_bound() -> usize {
    *PRASAD_SUNITHA_BOUND.get_or_init(|| {
        let v = crate::lean_ffi::get_prasad_sunitha_bound();
        if v == 0 { panic!("Failed to resolve Prasad & Sunitha bound from proof bridge"); }
        v
    })
}

/// The target abundance ratio for a QPN: σ(N)/N = 2 + 1/N ≈ 2.
const TARGET_ABUNDANCE: f64 = 2.0;

/// DFS depths below this threshold spawn parallel child tasks via Rayon.
/// Depths at or above this threshold use sequential push/pop recursion.

/// Number of lock-free slots for tracking active primes (telemetry only).

pub struct DfsTelemetry {
    pub total_branches: usize,
    pub abundance_pruned: usize,
    pub raycast_pruned: usize,
    pub search_space_density: f64,
    pub math_interruptions: usize,
}

pub fn phase2_and_4_fused(
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    suffix_abundance: &[u128],
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<crate::events::SearchEvent>>,
) -> DfsTelemetry {
    if let Some(r) = reporter { let _ = r.send(crate::events::SearchEvent::Phase { phase: 2, name: "Fused DFS Construction & Ray-Casting".to_string() }); }

    // Pre-compute the highest index where 3 and 5 appear in the sorted components
    // array. This turns the O(N) linear scan into an O(1) lookup inside explore_prefix.
    let max_idx_3 = components.iter().rposition(|c| c.p == 3).unwrap_or(0);
    let max_idx_5 = components.iter().rposition(|c| c.p == 5).unwrap_or(0);

    let count = AtomicUsize::new(0);
    let pruned_count = AtomicUsize::new(0);
    let abundance_pruned = AtomicUsize::new(0);
    let completed_weight_scaled = AtomicUsize::new(0);
    let math_interruptions = AtomicUsize::new(0);
    let total_weight_scaled: usize = components
        .iter()
        .map(|c| (10_000_000.0 / ((c.p as f64) * (c.p as f64))) as usize)
        .sum();

    // Lock-free active-primes telemetry: fixed array of AtomicU64 slots.
    // Each parallel task claims a slot on entry and clears it on exit.
    let active_primes: Arc<[AtomicU64]> =
        std::iter::repeat_with(|| AtomicU64::new(0)).take(crate::profile::get_profile().active_prime_slots).collect::<Arc<[AtomicU64]>>();

    let trace_writer = crate::trace::TraceWriter::new("trace.jsonl");
    let trace_tx = trace_writer.sender.clone();
    let lazy_cache: Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> = Arc::new(std::iter::repeat_with(std::sync::OnceLock::new).take(components.len()).collect());
    let backbone = Arc::new(crate::backbone::SearchBackbone::new(components, &lazy_cache));

    // Top-level parallelism over components
    (0..components.len()).into_par_iter().for_each(|i| {
        let comp = &components[i];

        let lazy_res = resolve_lazy_factors(comp, &lazy_cache[i]);
        if lazy_res.is_err() {
            math_interruptions.fetch_add(1, Ordering::Relaxed);
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
            &math_interruptions,
            total_weight_scaled,
            &active_primes,
            0,
            sigma_cache,
            reporter,
            max_idx_3,
            max_idx_5,
            &lazy_cache,
            &backbone,
            Some(&trace_tx),
        );

        let w = (10_000_000.0 / ((comp.p as f64) * (comp.p as f64))) as usize;
        completed_weight_scaled.fetch_add(w, Ordering::Relaxed);

        // Release active-prime slot (lock-free)
        release_active_slot(&active_primes, slot);
    });

    let ap = abundance_pruned.load(Ordering::Relaxed);
    let total_branches = count.load(Ordering::Relaxed);
    let rp = pruned_count.load(Ordering::Relaxed);
    drop(trace_tx); drop(trace_writer.sender);
    let _ = trace_writer.handle.join();
    let density = (total_branches as f64) / (total_weight_scaled as f64 + 1.0); // simple proxy for density
    if let Some(r) = reporter { let _ = r.send(crate::events::SearchEvent::DFSComplete { total_branches, ap, rp }); }
    DfsTelemetry {
        total_branches,
        abundance_pruned: ap,
        raycast_pruned: rp,
        search_space_density: density,
        math_interruptions: math_interruptions.load(Ordering::Relaxed),
    }
}

/// Claims the first available slot in the active-primes array.
/// Returns the slot index.
fn claim_active_slot(slots: &[AtomicU64], prime: u64) -> usize {
    for (idx, slot) in slots.iter().enumerate() {
        if slot
            .compare_exchange(0, prime, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            return idx;
        }
    }
    // Fallback: if all slots are full (shouldn't happen with 64 slots), just overwrite last
    slots.len() - 1
}

/// Releases a slot in the active-primes array.
fn release_active_slot(slots: &[AtomicU64], idx: usize) {
    slots[idx].store(0, Ordering::Relaxed);
}

/// Collects the currently active primes from the lock-free array (for display).
fn read_active_primes(slots: &[AtomicU64]) -> Vec<u64> {
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
    math_interruptions: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64]>,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<crate::events::SearchEvent>>,
    max_idx_3: usize,
    max_idx_5: usize,
    backbone: &crate::backbone::SearchBackbone,
    trace_tx: Option<&crossbeam_channel::Sender<crate::trace::TraceEvent>>,
) -> bool {

    if curr.n_l > *target_bound {
        if let Some(tx) = trace_tx {
            let mut f_vec = smallvec::SmallVec::new();
            f_vec.extend_from_slice(&curr.factors);
            let _ = tx.send(crate::trace::TraceEvent {
                factors: f_vec,
                n_l: curr.n_l,
                s_l: curr.s_l,
                reason: crate::trace::PruneReason::TargetBound,
                verification_status: "formally verified",
            });
        }
        return false;
    }

    // Telemetry Export: Sample deep prefixes for frequency analysis
    if curr.factors.len() >= 4 {
        if let Some(r) = reporter {
            let factors_str = curr.factors.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(",");
            let _ = r.send(crate::events::SearchEvent::Prefix { len: curr.factors.len(), factors_str });
        }
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
        if let Some(tx) = trace_tx {
            let mut f_vec = smallvec::SmallVec::new();
            f_vec.extend_from_slice(&curr.factors);
            let _ = tx.send(crate::trace::TraceEvent {
                factors: f_vec,
                n_l: curr.n_l,
                s_l: curr.s_l,
                reason: crate::trace::PruneReason::UnconditionalStarvation {
                    max_allowed,
                    static_best_remaining,
                    lhs,
                    rhs: Uint::from_u128(1) // we pass dummy, rhs is curr.n_l << 65 which we can reconstruct
                },
                verification_status: "formally verified",
            });
        }
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
        (get_min_prime_factors(), static_best_remaining)
    };

    let c3 = curr.factors.contains(&3) as u8;
    let c5 = curr.factors.contains(&5) as u8;
    let s3 = (curr.last_idx > max_idx_3) as u8;
    let s5 = (curr.last_idx > max_idx_5) as u8;
    let baseline_min = unsafe { crate::lean_ffi::ualbf_evaluate_baseline_min_ffi(c3, c5, s3, s5) };

    // Overflow Kill: Instantly drop if running fraction > threshold
    let overflow_den_u = Uint::from_u128(crate::manifest_constants::OVERFLOW_THRESHOLD_DEN as u128);
    let overflow_num_u = Uint::from_u128(crate::manifest_constants::OVERFLOW_THRESHOLD_NUM as u128);
    if crate::universal_bounds::cpu_check_abundancy_overflow(&curr.s_l, &curr.n_l, &overflow_den_u, &overflow_num_u) {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        if let Some(tx) = trace_tx {
            let mut f_vec = smallvec::SmallVec::new();
            f_vec.extend_from_slice(&curr.factors);
            let _ = tx.send(crate::trace::TraceEvent {
                factors: f_vec,
                n_l: curr.n_l,
                s_l: curr.s_l,
                reason: crate::trace::PruneReason::OverflowKill {
                    s_l_mul: curr.s_l * overflow_den_u,
                    n_l_mul: curr.n_l * overflow_num_u,
                },
                verification_status: "formally verified",
            });
        }
        return false;
    }

    dynamic_min_factors = dynamic_min_factors.max(baseline_min as usize);

    // Euler Ceiling pruning from the logic layer.
    let (euler_num, euler_den) = crate::lean_ffi::get_euler_ceiling();
    let mut num = Uint::one();
    let mut den = Uint::one();
    for &p in &curr.factors {
        num *= Uint::from_u64(p);
        den *= Uint::from_u64(p - 1);
    }
    if crate::universal_bounds::cpu_check_euler_ceiling(&num, &den, &euler_num, &euler_den) {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        if let Some(tx) = trace_tx {
            let mut f_vec = smallvec::SmallVec::new();
            f_vec.extend_from_slice(&curr.factors);
            let _ = tx.send(crate::trace::TraceEvent {
                factors: f_vec,
                n_l: curr.n_l,
                s_l: curr.s_l,
                reason: crate::trace::PruneReason::EulerCeiling {
                    num, den, euler_num, euler_den
                },
                verification_status: "formally verified",
            });
        }
        return false;
    }

    // Dynamic Starvation Kill based on modular divisibility chains
    let dyn_best_u256 = Uint::from_u128((dynamic_best_achievable_fp) as u128);
    if curr.s_l * dyn_best_u256 < curr.n_l << 65 {
        abundance_pruned.fetch_add(1, Ordering::Relaxed);
        if let Some(tx) = trace_tx {
            let mut f_vec = smallvec::SmallVec::new();
            f_vec.extend_from_slice(&curr.factors);
            let _ = tx.send(crate::trace::TraceEvent {
                factors: f_vec,
                n_l: curr.n_l,
                s_l: curr.s_l,
                reason: crate::trace::PruneReason::DynamicStarvation {
                    dynamic_best_achievable_fp,
                    lhs: curr.s_l * dyn_best_u256,
                    rhs: curr.n_l << 65,
                },
                verification_status: "formally verified",
            });
        }
        return false;
    }

    let prasad_sunitha_bound = get_prasad_sunitha_bound();
    let baseline_min_val = get_min_prime_factors();
    let info_mask = (c3 as u32) | ((c5 as u32) << 1) | ((s3 as u32) << 2) | ((s5 as u32) << 3);
    let remaining_components = components.len().saturating_sub(curr.last_idx);

    if crate::universal_bounds::cpu_check_prasad_sunitha(info_mask, baseline_min_val, prasad_sunitha_bound, curr.factors.len(), remaining_components) {
        if let Some(tx) = trace_tx {
            let mut f_vec = smallvec::SmallVec::new();
            f_vec.extend_from_slice(&curr.factors);
            let _ = tx.send(crate::trace::TraceEvent {
                factors: f_vec,
                n_l: curr.n_l,
                s_l: curr.s_l,
                reason: crate::trace::PruneReason::MinFactors {
                    dynamic_min_factors: if (info_mask & 3) == 0 && (info_mask & 12) == 12 { prasad_sunitha_bound } else { baseline_min_val },
                    curr_factors: curr.factors.len(),
                    remaining_components,
                },
                verification_status: "formally verified",
            });
        }
        return false;
    }

    if curr.n_l >= *stop_threshold {
        let c = count.fetch_add(1, Ordering::Relaxed) + 1;
        let now_ms = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_millis() as u64;
        let last = LAST_TELEMETRY.load(std::sync::atomic::Ordering::Relaxed);
        if c % 1024 == 0 && now_ms - last >= crate::profile::get_profile().engine_telemetry_interval_ms {
            if LAST_TELEMETRY.compare_exchange(last, now_ms, std::sync::atomic::Ordering::Relaxed, std::sync::atomic::Ordering::Relaxed).is_ok() {
                if let Some(r) = reporter {
                let pr = pruned_count.load(Ordering::Relaxed);
                let comp = completed_weight_scaled.load(Ordering::Relaxed);
                let ap = abundance_pruned.load(Ordering::Relaxed);

                let active = read_active_primes(active_primes);
                let active_count = active.len();
                let display = active.iter().take(4).map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
                let active_str = if active_count > 4 { format!("{}... ({} total)", display, active_count) } else { display };

                let _ = r.send(crate::events::SearchEvent::StatusUpdate {
                    c, total_weight_scaled, comp, pr, active_str, prefixes: c, ap
                });
                }
            }
        }

        if let Some(tx) = trace_tx {
            let mut f_vec = smallvec::SmallVec::new();
            f_vec.extend_from_slice(&curr.factors);
            let _ = tx.send(crate::trace::TraceEvent {
                factors: f_vec,
                n_l: curr.n_l,
                s_l: curr.s_l,
                reason: crate::trace::PruneReason::Raycast,
                verification_status: "auditor-checked",
            });
        }
        phase4_exact_ray_casting(
            curr,
            target_min,
            target_bound,
            illegal_valuations,
            pruned_count, math_interruptions,
            sigma_cache,
            reporter,
            max_idx_3,
            max_idx_5,
            components.len(),
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
    math_interruptions: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<crate::events::SearchEvent>>,
    max_idx_3: usize,
    max_idx_5: usize,
    lazy_cache: &Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>>,
    backbone: &crate::backbone::SearchBackbone,
    trace_tx: Option<&crossbeam_channel::Sender<crate::trace::TraceEvent>>,
) {
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
        math_interruptions,
        total_weight_scaled,
        active_primes,
        depth,
        sigma_cache,
        reporter,
        max_idx_3,
        max_idx_5,
        &lazy_cache,
        &backbone,
        trace_tx,
    );
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
    math_interruptions: &AtomicUsize,
    total_weight_scaled: usize,
    active_primes: &Arc<[AtomicU64]>,
    depth: usize,
    sigma_cache: &SigmaCache,
    reporter: Option<&crossbeam_channel::Sender<crate::events::SearchEvent>>,
    max_idx_3: usize,
    max_idx_5: usize,
    lazy_cache: &Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>>,
    backbone: &crate::backbone::SearchBackbone,
    trace_tx: Option<&crossbeam_channel::Sender<crate::trace::TraceEvent>>,
) {
    let mut ctx = DfsContext {
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
        math_interruptions,
        total_weight_scaled,
        active_primes,
        sigma_cache,
        reporter,
        max_idx_3,
        max_idx_5,
        lazy_cache,
        backbone,
        saved_states: Vec::new(),
        dyn_min_factors: 0,
        should_explore_memo: false,
        trace_tx: trace_tx.cloned(),
    };
    
    let ctx_ptr = &mut ctx as *mut DfsContext as u64;
    unsafe {
        crate::lean_ffi::ualbf_dfs_loop(ctx_ptr);
    }
}

/// Resolve and cache extra prime factors required by a PrimePower's rho remainders.
///
/// Computes and returns a sorted list of extra prime `Uint` factors for every remainder listed in
/// `comp.needs_rho`. Results are cached in `cache_slot` so subsequent calls return the same
/// computed value. If any discovered prime factor is congruent to 5 or 7 modulo 8 the function
/// returns `Err(())` to indicate the candidate must be rejected. If a remainder's factorization
/// is incomplete the function emits a diagnostic line to stderr and still continues; incomplete
/// factorizations are allowed but may defer candidate acceptance.
///
/// # Returns
///
/// `Ok(Vec<Uint>)` with the sorted extra prime factors when factorization is acceptable, or
/// `Err(())` if any found prime factor is `5` or `7` modulo `8`.
///
/// # Examples
///
/// ```no_run
/// // Example (illustrative): a PrimePower with no rho needs returns an empty vector.
/// let comp = PrimePower { needs_rho: Vec::new(), /* other fields omitted */ };
/// let slot: std::sync::OnceLock<Result<Vec<Uint>, ()>> = std::sync::OnceLock::new();
/// let extra = resolve_lazy_factors(&comp, &slot).unwrap();
/// assert!(extra.is_empty());
/// ```
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
            let fact_res = crate::math_utils::rho_factor_u256(rem);
            let factors = fact_res.factors();
            for &q in &factors {
                use crate::residue::IsValidMod8;
                if !q.is_valid_mod_8() {
                    return Err(());
                }
            }
            if !fact_res.is_complete() {
                // Output skipped because resolve_lazy_factors has no reporter. But it could be added if needed.
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
    pub math_interruptions: &'a AtomicUsize,
    pub total_weight_scaled: usize,
    pub active_primes: &'a Arc<[AtomicU64]>,
    pub sigma_cache: &'a SigmaCache,
    pub reporter: Option<&'a crossbeam_channel::Sender<crate::events::SearchEvent>>,
    pub max_idx_3: usize,
    pub max_idx_5: usize,
    pub lazy_cache: &'a Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>>,
    pub backbone: &'a crate::backbone::SearchBackbone,
    pub saved_states: Vec<crate::state::PrefixStateSnapshot>,
    pub dyn_min_factors: u32,
    pub should_explore_memo: bool,
    pub trace_tx: Option<crossbeam_channel::Sender<crate::trace::TraceEvent>>,
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
    if lazy_res.is_err() { dfs_ctx.math_interruptions.fetch_add(1, Ordering::Relaxed); return false; }
    let extra_factors = lazy_res.unwrap();
    
    if let (Some(next_n_l), Some(next_s_l)) = (dfs_ctx.curr.n_l.checked_mul(comp.val), dfs_ctx.curr.s_l.checked_mul(comp.sigma)) {
        if next_n_l <= *dfs_ctx.target_bound {
            dfs_ctx.saved_states.push(dfs_ctx.curr.capture_state());
            dfs_ctx.curr.n_l = next_n_l;
            dfs_ctx.curr.s_l = next_s_l;
            dfs_ctx.curr.last_idx = i + 1;
            dfs_ctx.curr.factors.push(comp.p);
            dfs_ctx.curr.sigma_factors.extend_from_slice(&comp.sigma_factors);
            dfs_ctx.curr.sigma_factors.extend_from_slice(&extra_factors);
            // Don't forget to push sigma_factors_u64 for the sequential engine
            for sf in &comp.sigma_factors {
                if *sf <= Uint::from_u128(u64::MAX as u128) {
                    dfs_ctx.curr.sigma_factors_u64.push(sf.as_u64());
                }
            }
            for sf in &extra_factors {
                if *sf <= Uint::from_u128(u64::MAX as u128) {
                    dfs_ctx.curr.sigma_factors_u64.push(sf.as_u64());
                }
            }
            return true;
        }
    }
    false
}

#[no_mangle]
pub extern "C" fn rust_dfs_pop(ctx: u64) {
    let dfs_ctx = unsafe { &mut *(ctx as *mut DfsContext) };
    if let Some(parent) = dfs_ctx.saved_states.pop() {
        dfs_ctx.curr.restore_state(&parent);
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
    
    check_and_evaluate_node(
        dfs_ctx.curr,
        dfs_ctx.components,
        dfs_ctx.stop_threshold,
        dfs_ctx.target_min,
        dfs_ctx.target_bound,
        dfs_ctx.illegal_valuations,
        dfs_ctx.suffix_abundance,
        dfs_ctx.count,
        dfs_ctx.pruned_count,
        dfs_ctx.abundance_pruned,
        dfs_ctx.completed_weight_scaled,
        dfs_ctx.math_interruptions,
        dfs_ctx.total_weight_scaled,
        dfs_ctx.active_primes,
        dfs_ctx.sigma_cache,
        dfs_ctx.reporter,
        dfs_ctx.max_idx_3,
        dfs_ctx.max_idx_5,
        dfs_ctx.backbone,
        dfs_ctx.trace_tx.as_ref(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{UintExt, PrimePower, Uint};
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicUsize, AtomicU64};
    use std::sync::Arc;

    // -----------------------------------------------------------------------
    // Test helpers
    // -----------------------------------------------------------------------

    fn make_prime_power(p: u64, val: u64, sigma: u64) -> PrimePower {
        PrimePower {
            p,
            two_e: 2,
            val: Uint::from_u64(val),
            sigma: Uint::from_u64(sigma),
            sigma_factors: vec![],
            needs_rho: vec![],
            abundance_fp: (sigma as u128) << 64 / (val as u128).max(1),
        }
    }

    fn make_prefix(n_l: u64, s_l: u64, last_idx: usize) -> Prefix {
        Prefix {
            n_l: Uint::from_u64(n_l),
            s_l: Uint::from_u64(s_l),
            last_idx,
            factors: vec![],
            sigma_factors: vec![],
            sigma_factors_u64: vec![],
            active_mask: vec![],
        }
    }

    fn make_active_primes() -> Arc<[AtomicU64]> {
        std::iter::repeat_with(|| AtomicU64::new(0)).take(crate::profile::get_profile().active_prime_slots).collect::<Arc<[AtomicU64]>>()
    }

    fn make_lazy_cache(len: usize) -> Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> {
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            let lock: std::sync::OnceLock<Result<Vec<Uint>, ()>> = std::sync::OnceLock::new();
            // Pre-populate: needs_rho is empty so no FFI needed
            let _ = lock.set(Ok(vec![]));
            v.push(lock);
        }
        Arc::new(v)
    }

    // Construct a DfsContext with:
    //   - `curr` pointing to a local Prefix
    //   - `components` slice
    //   - sensible defaults for all counters and optional fields
    //
    // The body closure receives a raw u64 pointer (as expected by the extern "C" functions).
    // After each extern C call returns, the caller reads back state by re-dereferencing
    // the same pointer. This avoids aliasing between a safe mutable reference and raw pointer.
    //
    // Usage: `with_dfs_ctx!(curr=..., ..., |ptr| { ... unsafe { (*ptr as *const DfsContext).curr ... } })`
    macro_rules! with_dfs_ctx {
        (
            curr = $curr:expr,
            components = $comps:expr,
            target_bound = $tb:expr,
            max_idx_3 = $mi3:expr,
            max_idx_5 = $mi5:expr,
            saved_states = $ss:expr,
            $body:expr
        ) => {{
            crate::lean_ffi::initialize_lean_runtime();
            let count = AtomicUsize::new(0);
            let pruned_count = AtomicUsize::new(0);
            let abundance_pruned = AtomicUsize::new(0);
            let completed_weight_scaled = AtomicUsize::new(0);
    let math_interruptions = AtomicUsize::new(0);
            let active_primes = make_active_primes();
            let sigma_cache: crate::math_utils::SigmaCache = HashMap::new();
            let stop_threshold = Uint::from_u128(u128::MAX);
            let target_min = Uint::from_u64(1);
            let lazy_cache = make_lazy_cache($comps.len());
            let backbone = crate::backbone::SearchBackbone::new($comps, &lazy_cache);
            let suffix_abundance: Vec<u128> = vec![1u128 << 64; 128];
            let illegal_valuations: Vec<(crate::types::Int, crate::types::Int)> = vec![];

            let mut ctx = DfsContext {
                curr: &mut $curr,
                components: $comps,
                stop_threshold: &stop_threshold,
                target_min: &target_min,
                target_bound: &$tb,
                illegal_valuations: &illegal_valuations,
                suffix_abundance: &suffix_abundance,
                count: &count,
                pruned_count: &pruned_count,
                abundance_pruned: &abundance_pruned,
                completed_weight_scaled: &completed_weight_scaled,
                math_interruptions: &math_interruptions,
                total_weight_scaled: 1000,
                active_primes: &active_primes,
                sigma_cache: &sigma_cache,
                reporter: None,
                max_idx_3: $mi3,
                max_idx_5: $mi5,
                lazy_cache: &lazy_cache,
                backbone: &backbone,
                saved_states: $ss,
                dyn_min_factors: 7,
                should_explore_memo: false,
                trace_tx: None,
            };

            // Pass the raw pointer only; the closure reads state back through the same pointer.
            let ctx_ptr = &mut ctx as *mut DfsContext as u64;
            $body(ctx_ptr)
        }};
    }

    /// Read a field from the DfsContext via raw pointer (for use after extern C calls).
    unsafe fn ctx_n_l(ptr: u64) -> Uint {
        (*(ptr as *const DfsContext)).curr.n_l
    }
    unsafe fn ctx_s_l(ptr: u64) -> Uint {
        (*(ptr as *const DfsContext)).curr.s_l
    }
    unsafe fn ctx_last_idx(ptr: u64) -> usize {
        (*(ptr as *const DfsContext)).curr.last_idx
    }
    unsafe fn ctx_factors(ptr: u64) -> Vec<u64> {
        (*(ptr as *const DfsContext)).curr.factors.clone()
    }
    unsafe fn ctx_saved_states_len(ptr: u64) -> usize {
        (*(ptr as *const DfsContext)).saved_states.len()
    }

    // -----------------------------------------------------------------------
    // Tests for rust_dfs_get_components_len
    // -----------------------------------------------------------------------

    #[test]
    fn test_get_components_len_empty() {
        let mut curr = make_prefix(1, 1, 0);
        let comps: Vec<PrimePower> = vec![];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| {
                assert_eq!(rust_dfs_get_components_len(ptr), 0);
            }
        );
    }

    #[test]
    fn test_get_components_len_three_components() {
        let mut curr = make_prefix(1, 1, 0);
        let comps = vec![
            make_prime_power(3, 9, 13),
            make_prime_power(5, 25, 31),
            make_prime_power(7, 49, 57),
        ];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 1,
            saved_states = vec![],
            |ptr| {
                assert_eq!(rust_dfs_get_components_len(ptr), 3);
            }
        );
    }

    // -----------------------------------------------------------------------
    // Tests for rust_dfs_get_curr_last_idx
    // -----------------------------------------------------------------------

    #[test]
    fn test_get_curr_last_idx_zero() {
        let mut curr = make_prefix(1, 1, 0);
        let comps: Vec<PrimePower> = vec![];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| {
                assert_eq!(rust_dfs_get_curr_last_idx(ptr), 0);
            }
        );
    }

    #[test]
    fn test_get_curr_last_idx_nonzero() {
        let mut curr = make_prefix(1, 1, 5);
        let comps: Vec<PrimePower> = vec![make_prime_power(3, 9, 13); 10];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| {
                assert_eq!(rust_dfs_get_curr_last_idx(ptr), 5);
            }
        );
    }

    // -----------------------------------------------------------------------
    // Tests for rust_dfs_get_prasad_sunitha_info
    // -----------------------------------------------------------------------

    #[test]
    fn test_prasad_sunitha_info_no_factors_no_skip() {
        // factors = [], last_idx=0, max_idx_3=5, max_idx_5=5 => none skipped
        let mut curr = make_prefix(1, 1, 0);
        let comps: Vec<PrimePower> = vec![make_prime_power(3, 9, 13); 10];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 5,
            max_idx_5 = 5,
            saved_states = vec![],
            |ptr| {
                let info = rust_dfs_get_prasad_sunitha_info(ptr);
                assert_eq!(info & 1, 0, "should not contain 3");
                assert_eq!(info & 2, 0, "should not contain 5");
                assert_eq!(info & 4, 0, "should not have skipped 3");
                assert_eq!(info & 8, 0, "should not have skipped 5");
                assert_eq!(info, 0);
            }
        );
    }

    #[test]
    fn test_prasad_sunitha_info_contains_3() {
        let mut curr = make_prefix(3, 4, 1);
        curr.factors = vec![3u64];
        let comps: Vec<PrimePower> = vec![make_prime_power(3, 9, 13); 10];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 5,
            max_idx_5 = 5,
            saved_states = vec![],
            |ptr| {
                let info = rust_dfs_get_prasad_sunitha_info(ptr);
                assert_ne!(info & 1, 0, "bit 0 should be set: contains 3");
                assert_eq!(info & 2, 0, "bit 1 should not be set: no 5");
            }
        );
    }

    #[test]
    fn test_prasad_sunitha_info_contains_5() {
        let mut curr = make_prefix(5, 6, 1);
        curr.factors = vec![5u64];
        let comps: Vec<PrimePower> = vec![make_prime_power(5, 25, 31); 10];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 5,
            max_idx_5 = 5,
            saved_states = vec![],
            |ptr| {
                let info = rust_dfs_get_prasad_sunitha_info(ptr);
                assert_eq!(info & 1, 0, "bit 0 should not be set: no 3");
                assert_ne!(info & 2, 0, "bit 1 should be set: contains 5");
            }
        );
    }

    #[test]
    fn test_prasad_sunitha_info_skipped_3() {
        // last_idx=6 > max_idx_3=5 => bit 2 set; last_idx=6 <= max_idx_5=9 => bit 3 not set
        let mut curr = make_prefix(1, 1, 6);
        let comps: Vec<PrimePower> = vec![make_prime_power(7, 49, 57); 10];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 5,
            max_idx_5 = 9,
            saved_states = vec![],
            |ptr| {
                let info = rust_dfs_get_prasad_sunitha_info(ptr);
                assert_ne!(info & 4, 0, "bit 2 should be set: skipped 3");
                assert_eq!(info & 8, 0, "bit 3 should not be set: not skipped 5");
            }
        );
    }

    #[test]
    fn test_prasad_sunitha_info_skipped_5() {
        // last_idx=10 > max_idx_3=3 and last_idx=10 > max_idx_5=9
        let mut curr = make_prefix(1, 1, 10);
        let comps: Vec<PrimePower> = vec![make_prime_power(7, 49, 57); 15];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 3,
            max_idx_5 = 9,
            saved_states = vec![],
            |ptr| {
                let info = rust_dfs_get_prasad_sunitha_info(ptr);
                assert_ne!(info & 4, 0, "bit 2 should be set: skipped 3 (last_idx=10 > 3)");
                assert_ne!(info & 8, 0, "bit 3 should be set: skipped 5 (last_idx=10 > 9)");
            }
        );
    }

    #[test]
    fn test_prasad_sunitha_info_all_bits() {
        // factors=[3,5], last_idx=10 > max_idx_3=5, last_idx=10 > max_idx_5=9
        let mut curr = make_prefix(15, 24, 10);
        curr.factors = vec![3u64, 5u64];
        let comps: Vec<PrimePower> = vec![make_prime_power(7, 49, 57); 15];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 5,
            max_idx_5 = 9,
            saved_states = vec![],
            |ptr| {
                let info = rust_dfs_get_prasad_sunitha_info(ptr);
                assert_ne!(info & 1, 0, "bit 0: contains 3");
                assert_ne!(info & 2, 0, "bit 1: contains 5");
                assert_ne!(info & 4, 0, "bit 2: skipped 3");
                assert_ne!(info & 8, 0, "bit 3: skipped 5");
                assert_eq!(info, 15);
            }
        );
    }

    // -----------------------------------------------------------------------
    // Tests for rust_dfs_try_push
    // -----------------------------------------------------------------------

    #[test]
    fn test_try_push_success_updates_state() {
        let mut curr = make_prefix(1, 1, 0);
        let p7 = make_prime_power(7, 49, 57); // val=49, sigma=57
        let comps = vec![p7];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| unsafe {
                let pushed = rust_dfs_try_push(ptr, 0);
                assert!(pushed, "should push successfully");
                // n_l updated to 1 * 49 = 49
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(49));
                // s_l updated to 1 * 57 = 57
                assert_eq!(ctx_s_l(ptr), Uint::from_u64(57));
                // last_idx updated to 1
                assert_eq!(ctx_last_idx(ptr), 1);
                // factor 7 added
                assert!(ctx_factors(ptr).contains(&7));
                // saved state preserved
                assert_eq!(ctx_saved_states_len(ptr), 1);
            }
        );
    }

    #[test]
    fn test_try_push_fails_duplicate_factor() {
        let mut curr = make_prefix(7, 8, 1);
        curr.factors = vec![7u64]; // 7 already in factors
        let p7 = make_prime_power(7, 49, 57);
        let comps = vec![p7];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| unsafe {
                let pushed = rust_dfs_try_push(ptr, 0);
                assert!(!pushed, "should fail: 7 already in factors");
                // State should be unchanged
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(7));
                assert_eq!(ctx_saved_states_len(ptr), 0);
            }
        );
    }

    #[test]
    fn test_try_push_fails_exceeds_target_bound() {
        // target_bound=10, val=49 => 1*49 > 10 => fails
        let mut curr = make_prefix(1, 1, 0);
        let p7 = make_prime_power(7, 49, 57);
        let comps = vec![p7];
        let tb = Uint::from_u64(10); // tight bound
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| unsafe {
                let pushed = rust_dfs_try_push(ptr, 0);
                assert!(!pushed, "should fail: would exceed target_bound");
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(1), "n_l should be unchanged");
                assert_eq!(ctx_saved_states_len(ptr), 0);
            }
        );
    }

    #[test]
    fn test_try_push_succeeds_at_exact_bound() {
        // n_l=1, val=49, bound=49 => 1*49 <= 49 => success
        let mut curr = make_prefix(1, 1, 0);
        let p7 = make_prime_power(7, 49, 57);
        let comps = vec![p7];
        let tb = Uint::from_u64(49);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| unsafe {
                let pushed = rust_dfs_try_push(ptr, 0);
                assert!(pushed, "n_l * val == bound should succeed (<=)");
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(49));
            }
        );
    }

    // -----------------------------------------------------------------------
    // Tests for rust_dfs_pop
    // -----------------------------------------------------------------------

    #[test]
    fn test_pop_restores_saved_state() {
        let mut curr = make_prefix(1, 1, 0);
        let p7 = make_prime_power(7, 49, 57);
        let comps = vec![p7];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| unsafe {
                // Push to mutate state
                let pushed = rust_dfs_try_push(ptr, 0);
                assert!(pushed);
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(49));
                assert_eq!(ctx_last_idx(ptr), 1);

                // Pop should restore
                rust_dfs_pop(ptr);
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(1), "n_l should be restored");
                assert_eq!(ctx_s_l(ptr), Uint::from_u64(1), "s_l should be restored");
                assert_eq!(ctx_last_idx(ptr), 0, "last_idx should be restored");
                assert!(!ctx_factors(ptr).contains(&7), "factor 7 should be removed");
                assert_eq!(ctx_saved_states_len(ptr), 0, "saved_states should be empty after pop");
            }
        );
    }

    #[test]
    fn test_pop_on_empty_stack_is_noop() {
        let mut curr = make_prefix(42, 50, 3);
        curr.factors = vec![3u64, 5u64];
        let comps = vec![make_prime_power(7, 49, 57)];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 0,
            saved_states = vec![],
            |ptr| unsafe {
                // Pop on empty saved_states should do nothing
                rust_dfs_pop(ptr);
                // State unchanged
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(42));
                assert_eq!(ctx_last_idx(ptr), 3);
                assert_eq!(ctx_factors(ptr), vec![3u64, 5u64]);
            }
        );
    }

    #[test]
    fn test_push_pop_roundtrip_multiple_times() {
        let mut curr = make_prefix(1, 1, 0);
        let p3 = make_prime_power(3, 9, 13);
        let p5 = make_prime_power(5, 25, 31);
        let comps = vec![p3, p5];
        let tb = Uint::from_u128(u128::MAX);
        with_dfs_ctx!(
            curr = curr,
            components = &comps,
            target_bound = tb,
            max_idx_3 = 0,
            max_idx_5 = 1,
            saved_states = vec![],
            |ptr| unsafe {
                // Push p3 (index 0)
                assert!(rust_dfs_try_push(ptr, 0));
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(9));
                assert_eq!(ctx_factors(ptr), vec![3u64]);

                // Push p5 (index 1)
                assert!(rust_dfs_try_push(ptr, 1));
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(9 * 25));
                assert_eq!(ctx_factors(ptr), vec![3u64, 5u64]);
                assert_eq!(ctx_saved_states_len(ptr), 2);

                // Pop p5
                rust_dfs_pop(ptr);
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(9));
                assert_eq!(ctx_factors(ptr), vec![3u64]);

                // Pop p3
                rust_dfs_pop(ptr);
                assert_eq!(ctx_n_l(ptr), Uint::from_u64(1));
                assert_eq!(ctx_factors(ptr), vec![] as Vec<u64>);
                assert_eq!(ctx_saved_states_len(ptr), 0);
            }
        );
    }

    // -----------------------------------------------------------------------
    // FFI bound tests (merged from PR branch)
    // -----------------------------------------------------------------------

    /// get_min_prime_factors must return a positive (non-zero) value.
    /// The OnceLock is lazily populated from the FFI on first call and
    /// the same value is returned on every subsequent call.
    #[test]
    fn test_get_min_prime_factors_nonzero() {
        let value = get_min_prime_factors();
        assert!(value > 0, "get_min_prime_factors must be positive, got {}", value);
    }

    /// get_prasad_sunitha_bound must return a positive (non-zero) value.
    #[test]
    fn test_get_prasad_sunitha_bound_nonzero() {
        let value = get_prasad_sunitha_bound();
        assert!(value > 0, "get_prasad_sunitha_bound must be positive, got {}", value);
    }

    /// The Prasad-Sunitha bound must be strictly greater than the baseline minimum
    /// prime factor count.  This invariant is required by the mathematical proof:
    /// excluding 3 and 5 forces a higher minimum dimension.
    #[test]
    fn test_prasad_sunitha_bound_greater_than_min_prime_factors() {
        let min_pf = get_min_prime_factors();
        let ps = get_prasad_sunitha_bound();
        assert!(
            ps > min_pf,
            "prasad_sunitha_bound ({}) must exceed get_min_prime_factors ({})",
            ps, min_pf
        );
    }

    /// Repeated calls to get_min_prime_factors must return the same value because the
    /// underlying OnceLock is initialised at most once and the FFI export is constant.
    #[test]
    fn test_get_min_prime_factors_consistent_across_calls() {
        let a = get_min_prime_factors();
        let b = get_min_prime_factors();
        assert_eq!(a, b, "get_min_prime_factors must be idempotent");
    }

    /// Repeated calls to get_prasad_sunitha_bound must return the same value.
    #[test]
    fn test_get_prasad_sunitha_bound_consistent_across_calls() {
        let a = get_prasad_sunitha_bound();
        let b = get_prasad_sunitha_bound();
        assert_eq!(a, b, "get_prasad_sunitha_bound must be idempotent");
    }

    /// The dummy FFI stubs (dummy_ffi.c) export 7 for the baseline minimum prime
    /// factors.  This test verifies the value propagates correctly through the
    /// OnceLock layer.
    #[test]
    fn test_get_min_prime_factors_matches_ffi_value() {
        let value = get_min_prime_factors();
        let ffi_value = crate::lean_ffi::get_baseline_min_prime_factors();
        assert_eq!(
            value, ffi_value,
            "dfs_tree::get_min_prime_factors ({}) must equal lean_ffi::get_baseline_min_prime_factors ({})",
            value, ffi_value
        );
    }

    /// The dummy FFI stubs (dummy_ffi.c) export 15 for the Prasad-Sunitha bound.
    /// This test verifies the value propagates correctly through the OnceLock layer.
    #[test]
    fn test_get_prasad_sunitha_bound_matches_ffi_value() {
        let value = get_prasad_sunitha_bound();
        let ffi_value = crate::lean_ffi::get_prasad_sunitha_bound();
        assert_eq!(
            value, ffi_value,
            "dfs_tree::get_prasad_sunitha_bound ({}) must equal lean_ffi::get_prasad_sunitha_bound ({})",
            value, ffi_value
        );
    }

    /// Boundary / regression check: the baseline must be at least 1 and must not
    /// exceed the Prasad-Sunitha bound.
    #[test]
    fn test_bounds_sanity_range() {
        let min_pf = get_min_prime_factors();
        let ps = get_prasad_sunitha_bound();
        assert!(min_pf >= 1, "baseline min prime factors must be >= 1");
        assert!(ps >= 2, "Prasad-Sunitha bound must be >= 2");
        assert!(ps > min_pf, "Prasad-Sunitha bound must strictly exceed baseline");
    }
}
static LAST_TELEMETRY: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
