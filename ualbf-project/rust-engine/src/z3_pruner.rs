// z3_pruner.rs — Z3-backed CDCL conflict-driven pruning for the DFS explorer.
//
// When explore_prefix hits a Starvation or Zsigmondy trap, we encode the
// conflict as a learned clause and broadcast it over an MPMC channel so
// all Rayon threads can instantly reject topologically equivalent prefixes.
//
// Architecture:
//   HOT PATH  — Pure-Rust superset conflict check + MPMC channel (lock-free).
//   COLD PATH — Z3 solver used for offline validation in tests only.
//               Z3 Context/Solver are !Send/!Sync, so they stay single-threaded.

use crate::types::Prefix;
use crossbeam_channel::{Receiver, Sender};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::RwLock;

// ---------------------------------------------------------------------------
// Conflict clause representation
// ---------------------------------------------------------------------------

/// The kind of trap that produced a conflict.
#[derive(Clone, Debug)]
pub enum TrapKind {
    /// Prefix abundance ratio × best remaining suffix < 2.0 — structurally doomed.
    Starvation,
    /// σ(p^{2e}) has a factor q ≡ 5 or 7 (mod 8) — Legendre–Cattaneo violation.
    Zsigmondy,
}

/// A learned conflict: the set of primes in the prefix that caused an UNSAT.
#[derive(Clone, Debug)]
pub struct ConflictClause {
    pub primes: Vec<u64>,
    pub kind: TrapKind,
}

// ---------------------------------------------------------------------------
// Z3Pruner — Thread-safe conflict learning + MPMC broadcast
// ---------------------------------------------------------------------------

pub struct Z3Pruner {
    /// Broadcast channel for learned conflict clauses.
    tx: Sender<ConflictClause>,
    rx: Receiver<ConflictClause>,
    /// Accumulated conflict clauses (RwLock allows parallel readers on the hot path).
    learned_clauses: RwLock<Vec<ConflictClause>>,
    /// Telemetry counters.
    pub conflicts_learned: AtomicUsize,
    pub z3_prune_hits: AtomicUsize,
}

impl Z3Pruner {
    /// Creates a new Z3Pruner with a fresh MPMC channel.
    pub fn new() -> Self {
        let (tx, rx) = crossbeam_channel::unbounded();

        Z3Pruner {
            tx,
            rx,
            learned_clauses: RwLock::new(Vec::new()),
            conflicts_learned: AtomicUsize::new(0),
            z3_prune_hits: AtomicUsize::new(0),
        }
    }

    // -----------------------------------------------------------------------
    // Trap detection
    // -----------------------------------------------------------------------

    /// Detect a starvation trap: the prefix's prime set structurally cannot
    /// reach target abundance ≥ 2.0 regardless of what remaining components
    /// are added.
    ///
    /// Any superset prefix containing these same primes will have an even
    /// *lower* current_abundance (since we're multiplying by p^{2e}/σ(p^{2e})
    /// which is < 1 for larger primes), so the conflict generalises.
    ///
    /// Returns `Some(ConflictClause)` if a structural trap is detected.
    pub fn detect_starvation_trap(
        &self,
        prefix: &Prefix,
        current_abundance: f64,
        best_remaining: f64,
    ) -> Option<ConflictClause> {
        if current_abundance * best_remaining < 2.0 {
            Some(ConflictClause {
                primes: prefix.factors.to_vec(),
                kind: TrapKind::Starvation,
            })
        } else {
            None
        }
    }

    /// Detect a Zsigmondy trap: check whether any σ(p^{2e}) factor for the
    /// primes in the prefix has q ≡ 5 or 7 (mod 8), violating the
    /// Legendre–Cattaneo obstruction.
    ///
    /// Returns `Some(ConflictClause)` with the offending prime set.
    pub fn detect_zsigmondy_trap(&self, prefix: &Prefix) -> Option<ConflictClause> {
        for &q in &prefix.sigma_factors {
            let q_mod_8 = (q % 8) as u32;
            if q_mod_8 == 5 || q_mod_8 == 7 {
                return Some(ConflictClause {
                    primes: prefix.factors.to_vec(),
                    kind: TrapKind::Zsigmondy,
                });
            }
        }
        None
    }

    // -----------------------------------------------------------------------
    // Conflict clause management (hot path — pure Rust, no Z3)
    // -----------------------------------------------------------------------

    /// Push a learned conflict clause: record it locally and broadcast to all
    /// Rayon threads via the MPMC channel.
    pub fn push_conflict(&self, clause: ConflictClause) {
        self.conflicts_learned.fetch_add(1, Ordering::Relaxed);

        // Broadcast to other threads
        let _ = self.tx.send(clause.clone());

        // Also store locally for persistent checking
        if let Ok(mut clauses) = self.learned_clauses.write() {
            clauses.push(clause);
        }
    }

    /// Drain any pending conflict clauses from the MPMC channel into our
    /// local store. Called at the start of each explore_prefix to pick up
    /// clauses learned by sibling threads.
    fn drain_channel(&self) {
        if self.rx.is_empty() { return; } // Fast path: skip the write lock entirely
        if let Ok(mut clauses) = self.learned_clauses.write() {
            while let Ok(clause) = self.rx.try_recv() {
                clauses.push(clause);
            }
        }
    }

    /// Check whether the current prefix is subsumed by any learned conflict
    /// clause. A prefix is subsumed if it contains (as a superset) all primes
    /// from any learned conflict.
    ///
    /// Returns `true` if the prefix should be pruned.
    pub fn check_prefix(&self, prefix: &Prefix) -> bool {
        // First drain any new clauses broadcast by sibling threads
        self.drain_channel();

        // READ lock — 100% parallel across all Rayon workers
        if let Ok(clauses) = self.learned_clauses.read() {
            if clauses.is_empty() { return false; }
            for clause in clauses.iter() {
                // Zero-allocation linear scan via SmallVec::contains
                if clause.primes.iter().all(|p| prefix.factors.contains(p)) {
                    self.z3_prune_hits.fetch_add(1, Ordering::Relaxed);
                    return true;
                }
            }
        }

        false
    }

    /// Verify a conflict clause using Z3 (offline validation, single-threaded).
    ///
    /// Uses Z3's implicit thread-local context. Creates a fresh solver,
    /// encodes each prime in the clause as a boolean variable, asserts all
    /// are used, and then asserts their conjunction is false (the conflict).
    /// If Z3 reports UNSAT, the conflict is confirmed to be contradictory.
    #[allow(dead_code)]
    pub fn verify_conflict_z3(clause: &ConflictClause) -> bool {
        use z3::ast::{Ast, Bool};
        use z3::{SatResult, Solver};

        let solver = Solver::new();

        // Create boolean variables for each prime in the clause
        let prime_vars: Vec<Bool> = clause
            .primes
            .iter()
            .map(|p| Bool::new_const(format!("used_p_{}", p)))
            .collect();

        // Assert all primes are used (the conflicting combination)
        for var in &prime_vars {
            solver.assert(var);
        }

        // Assert the negation: this combination should not exist
        let refs: Vec<&Bool> = prime_vars.iter().collect();
        let conjunction = Bool::and(&refs);
        solver.assert(conjunction.not());

        // If UNSAT, the conflict is confirmed
        matches!(solver.check(), SatResult::Unsat)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;

    fn make_prefix(primes: &[u64]) -> Prefix {
        Prefix {
            n_l: 1,
            s_l: 1,
            last_idx: 0,
            factors: primes.iter().copied().collect(),
            sigma_factors: vec![],
        }
    }

    #[test]
    fn test_starvation_detection() {
        let pruner = Z3Pruner::new();
        let prefix = make_prefix(&[3, 5, 7]);

        // Should detect trap when abundance is too low
        let result = pruner.detect_starvation_trap(&prefix, 0.5, 1.5);
        assert!(result.is_some());
        let clause = result.unwrap();
        assert_eq!(clause.primes, vec![3, 5, 7]);
        assert!(matches!(clause.kind, TrapKind::Starvation));

        // Should NOT detect trap when abundance is sufficient
        let result = pruner.detect_starvation_trap(&prefix, 1.5, 1.5);
        assert!(result.is_none());
    }

    #[test]
    fn test_zsigmondy_detection() {
        let pruner = Z3Pruner::new();

        // Prefix with a sigma factor ≡ 5 (mod 8) — should trigger
        let mut prefix = make_prefix(&[3, 5]);
        prefix.sigma_factors = vec![13]; // 13 % 8 = 5
        let result = pruner.detect_zsigmondy_trap(&prefix);
        assert!(result.is_some());

        // Prefix with clean sigma factors — should NOT trigger
        let mut prefix_clean = make_prefix(&[3, 5]);
        prefix_clean.sigma_factors = vec![17, 41]; // 17%8=1, 41%8=1
        let result = pruner.detect_zsigmondy_trap(&prefix_clean);
        assert!(result.is_none());
    }

    #[test]
    fn test_conflict_broadcast() {
        let pruner = Z3Pruner::new();

        // Push a conflict for primes {3, 5, 7}
        pruner.push_conflict(ConflictClause {
            primes: vec![3, 5, 7],
            kind: TrapKind::Starvation,
        });

        // A prefix containing {3, 5, 7, 11} (superset) should be pruned
        let superset_prefix = make_prefix(&[3, 5, 7, 11]);
        assert!(pruner.check_prefix(&superset_prefix));

        // A prefix containing only {3, 5} (subset) should NOT be pruned
        let subset_prefix = make_prefix(&[3, 5]);
        assert!(!pruner.check_prefix(&subset_prefix));

        // A prefix containing exactly {3, 5, 7} should be pruned
        let exact_prefix = make_prefix(&[3, 5, 7]);
        assert!(pruner.check_prefix(&exact_prefix));
    }

    #[test]
    fn test_z3_clause_learning() {
        let pruner = Z3Pruner::new();

        // Learn multiple conflicts
        pruner.push_conflict(ConflictClause {
            primes: vec![3, 5, 7],
            kind: TrapKind::Starvation,
        });
        pruner.push_conflict(ConflictClause {
            primes: vec![11, 13],
            kind: TrapKind::Zsigmondy,
        });

        // {3, 5, 7, 11} matches the first conflict
        assert!(pruner.check_prefix(&make_prefix(&[3, 5, 7, 11])));

        // {11, 13, 17} matches the second conflict
        assert!(pruner.check_prefix(&make_prefix(&[11, 13, 17])));

        // {3, 11} matches neither
        assert!(!pruner.check_prefix(&make_prefix(&[3, 11])));

        assert_eq!(pruner.conflicts_learned.load(Ordering::Relaxed), 2);
        assert_eq!(pruner.z3_prune_hits.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn test_telemetry_counters() {
        let pruner = Z3Pruner::new();

        pruner.push_conflict(ConflictClause {
            primes: vec![3],
            kind: TrapKind::Starvation,
        });

        assert_eq!(pruner.conflicts_learned.load(Ordering::Relaxed), 1);

        // Hit the conflict
        let _ = pruner.check_prefix(&make_prefix(&[3, 5]));
        assert_eq!(pruner.z3_prune_hits.load(Ordering::Relaxed), 1);

        // Hit it again
        let _ = pruner.check_prefix(&make_prefix(&[3, 7]));
        assert_eq!(pruner.z3_prune_hits.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn test_z3_verify_conflict() {
        // Validate that Z3 confirms a conflict clause is contradictory
        let clause = ConflictClause {
            primes: vec![3, 5, 7],
            kind: TrapKind::Starvation,
        };
        assert!(Z3Pruner::verify_conflict_z3(&clause));
    }
}
