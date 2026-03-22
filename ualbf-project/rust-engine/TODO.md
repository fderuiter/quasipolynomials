# Rust Engine TODO

## Correctness Bugs

- [ ] **C7 (Critical): `quick_factor_u128` silently returns composites**
  - If Pollard's rho fails after 5 `c_val` attempts, the composite remainder is pushed as a "factor". This corrupts all downstream math: Phase 1 sieve may falsely pass components, and `composite_tonelli_shanks` computes wrong roots from incorrect factorisations of `σ(N_L)`.
  - **Fix**: Either increase iteration/attempt limits, add a fallback (e.g., SQUFOF, ECM), or at minimum `panic!` / log a warning when factorisation fails so it's never silent.
  - **File**: `src/math_utils.rs:90–119`

- [ ] **C8: No overflow guards on final sigma/n multiplications**
  - In `phase4_exact_ray_casting`, `z*z`, `prefix.n_l * n_r`, `total_n * 2 + 1`, and `s_r * prefix.s_l` are all unchecked `u128` multiplications. While unlikely to overflow given the `10^37` bound, a subtle edge case could cause silent wraparound and miss a QPN.
  - **Fix**: Use `checked_mul` for the final QPN-check arithmetic, or add `debug_assert!` guards.
  - **File**: `src/raycast.rs:99–123`

## Performance

- [ ] **P1 (High): Vec cloning in DFS hot loop**
  - Every DFS node clones `factors` and `sigma_factors` Vecs. With millions of nodes, this is a massive allocation hotspot.
  - **Fix**: Use `SmallVec`, arena allocation, or a shared stack with push/pop semantics to avoid heap allocations.
  - **File**: `src/dfs_tree.rs:137–141`

- [ ] **P5 (High): Top-level-only parallelism causes load imbalance**
  - Parallelism is only at the top level (`(0..components.len()).into_par_iter()`). Small primes (3, 5, 7) have vastly deeper subtrees, causing a few threads to get stuck on massive subtrees while others finish quickly.
  - **Fix**: Use work-stealing with a depth threshold — parallelize at depth 1 or 2 as well using Rayon's `join` or scoped tasks.
  - **File**: `src/dfs_tree.rs:32`

- [ ] **P3: Full factorisation of every ray-cast candidate before QPN check**
  - `quick_factor_u128(z_biguint)` is called for every candidate `z` that passes the inner sieve, even though most will fail the final `s_r * s_l == 2n + 1` check.
  - **Fix**: Add cheaper modular pre-checks before factoring, or restructure to check the QPN equation with a fast `compute_sigma_direct(z_biguint)` that doesn't require full factorisation.
  - **File**: `src/raycast.rs:103`

- [ ] **P2: `Mutex<Vec<u64>>` contention for telemetry-only `active_primes`**
  - The `active_primes` Mutex is locked and sorted at every top-level iteration, and locked again inside DFS at every 100,000th prefix. This data is only used for display.
  - **Fix**: Use a lock-free approach (e.g., `AtomicU64` array or periodic sampling) instead of a Mutex on the hot path.
  - **File**: `src/dfs_tree.rs:29, 36–38, 53–58`

- [ ] **P6: No memoization of `compute_sigma` for small primes**
  - `compute_sigma(p, 2e)` is recomputed from scratch for every z-factor group in the ray-cast inner loop.
  - **Fix**: Precompute a lookup table for common small primes and exponents.
  - **File**: `src/raycast.rs:113, 120`

- [ ] **C4: Linear scan in `factors.contains()` in DFS inner loop**
  - `curr.factors.contains(&comp.p)` does O(k) linear scan for every candidate component at every DFS node.
  - **Fix**: Use a bitset or `HashSet<u64>` instead of `Vec<u64>` for the factors collection.
  - **File**: `src/dfs_tree.rs:134`

## Pruning Strength / Completeness

- [ ] **C2: Ray-cast z-valuation sieve limit too low**
  - `generate_illegal_z_valuations(250, 4)` only checks obstructions from primes < 250 and exponents ≤ 4. Suffix primes in `z` could have `v_p(z) >> 4`, and primes in [250, 250000] are not covered at all.
  - **Fix**: Increase the prime limit substantially (at least to match the Phase 1 sieve limit of 250,000) and consider higher exponents.
  - **File**: `src/main.rs:44`

- [ ] **C3: `suffix_abundance` pruning not tight for deep prefixes**
  - `suffix_abundance[i]` is precomputed with a fixed `k=7` multiplier (total factors needed), but deep prefixes with 3+ factors already present only need 4 more. The pruning overestimates achievable abundance and rarely prunes deep branches.
  - **Fix**: Either precompute separate suffix_abundance arrays for each depth, or compute the bound dynamically using `remaining_factors_needed` instead of a fixed 7.
  - **File**: `src/main.rs:26–41`, `src/dfs_tree.rs:88–96`
