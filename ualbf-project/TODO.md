# UALBF Project — Critical Remediation TODO

> **Status**: Active — Generated 2026-04-03  
> **Priority Legend**: 🔴 FATAL (blocks publication) · 🟡 SERIOUS (triggers desk-reject) · 🟢 HYGIENE (best practice)

---

## 1. 🔴 AI Artifacts in Source Code (`Cyclotomic.lean`)

### 1.1 Delete LLM Stream-of-Consciousness Comments

**Status**: ✅ **RESOLVED**

The file `Pure/Cyclotomic.lean` contains an internal LLM monologue at lines 1349–1367
that reads like an AI debating itself mid-proof:

```lean
-- IF q ∤ Φ_m(p) THEN q ∤ Φ_{mq}(p). Contrapositive: q | Φ_{mq}(p) → q | Φ_m... no wrong way.
-- Actually: q | Φ_{mq}(p) follows from q | Φ_m(p) by the Fermat argument:
-- We need q | Φ_{mq}(p). But maybe Φ_{mq}(p) ≡ 1 mod q.
-- Actually from cyclotomic_step_not_dvd...
-- We DON'T have q ∤ Φ_m(p); we have q | Φ_m(p). So Φ_{mq}(p) could be anything.
```

A reviewer seeing this will immediately recognize uncurated AI output and lose trust in the entire formalization.

- [x] **1.1.1** Delete the LLM chat block in `cyclotomic_eval_val_of_dvd_index`
  - File: [`Cyclotomic.lean:1349–1367`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/Cyclotomic.lean#L1349-L1367)
  - Delete all 19 comment lines starting with `-- IF q ∤ ...` through `-- ... so q must divide Φ_{mq}(p).`
  - Replace with a single clean proof sketch comment:
    ```lean
    -- q | Φ_{mq}(p): from 5h and 5g, q divides the geometric sum ∏_{d|m} Φ_{dq}(p).
    -- By 5i (cyclotomic_only_top_dvd), q ∤ Φ_{dq}(p) for d ≠ m, so q | Φ_{mq}(p).
    ```

- [x] **1.1.2** Audit `Cyclotomic.lean` for other speculative comments
  - File: [`Cyclotomic.lean:1308–1312`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/Cyclotomic.lean#L1308-L1312)
  - Lines 1308–1312 also contain hedging comments (`"Actually we need q odd for 5g"`, `"Actually for q=2, q | Φ_n(p) is rare"`)
  - Clean these into definitive, curated proof documentation

- [x] **1.1.3** Full sweep of entire `lean4-proofs/` for speculative/conversational comments
  - Search for patterns: `-- Actually`, `-- maybe`, `-- But maybe`, `-- We DON'T`, `-- not quite`, `-- no wrong way`
  - Delete or rewrite every instance into professional documentation

---

## 2. 🔴 FFI Epistemological Severance (Unverified Code Paths)

The FFI layer exports executable algorithms via `@[export]` but lacks complete
formal proofs linking those algorithms to the mathematical specifications
that the QPN theorems rely on.

### 2.1 `computeSigmaNat` ↔ `sigma` Bridge

**Status**: ✅ **RESOLVED** — `computeSigmaNat_eq_sigma` now exists in `FFI.lean:165–187`
and is fully proven (no `sorry`). The original critique assumed this theorem was missing.

- [x] **2.1.1** Audit `computeSigmaNat_eq_sigma` proof for edge cases
  - File: [`FFI.lean:165–187`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L165-L187)
  - Confirm `sum_divisors_prime_pow` matches the current Mathlib version signature
  - Run `lake build` and confirm zero `sorry` / zero warnings in this theorem

- [x] **2.1.2** Add cross-validation unit tests in `lean_ffi.rs`
  - File: [`lean_ffi.rs:169–208`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/rust-engine/src/lean_ffi.rs#L169-L208)
  - Extend `test_cross_check_sigma` with boundary cases: `(2, 0)`, `(2, 1)`, `(65521, 8)`
  - Assert `compute_sigma_checked` returns `Some(...)` for all in-range inputs

### 2.2 `modInverse_spec` Contains `sorry`

**Status**: ✅ **RESOLVED** — The unreachable `g = -1` branch was proven dead using a structural non-negativity invariant, and full algebraic reduction now proves the theorem without `sorry`.

- [x] **2.2.1** Complete the `modInverse_spec` proof (eliminate the `sorry`)
  - File: [`FFI.lean:106–136`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L106-L136)
  - The comment at line 128–136 explains the remaining gap: chain `a' ≡ a (mod m)` with Bézout to get `a * v ≡ 1 (mod m)`
  - Strategy: Use `Int.emod_emod_of_dvd`, `Int.add_mul_emod_self`, and the chain:
    1. `a' % m = a % m` (standard Int.emod identities)
    2. `a' * x ≡ g (mod m)` from `extGcd_bezout`
    3. `g ∈ {1, -1}` from the if-condition
    4. `v = ((x % m) + m) % m` → `a * v % m = 1 % m`
  - **Deliverable**: `modInverse_spec` with no `sorry`, no `axiom`, no `native_decide`

### 2.3 `toU64Lo` / `toU64Hi` Silent Truncation

**Status**: ✅ **PARTIALLY RESOLVED** — `ualbf_compute_sigma_ok` overflow guard exists
(`FFI.lean:200–202`) and the Rust side panics on overflow (`lean_ffi.rs:70–77`).

- [ ] **2.3.1** Verify the overflow guard rejects near-boundary values
  - Add a Lean `#eval` test: `ualbf_compute_sigma_ok_impl 2 127` should return `0`
  - Verify the Rust `compute_sigma_checked` correctly interprets `ok == 0` as `None`

- [ ] **2.3.2** Audit `modInverse` output path for 128-bit truncation
  - File: [`FFI.lean:216–238`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L216-L238)
  - **Decision needed**: Add a `ualbf_mod_inverse_overflow_ok` guard, or prove that for the engine's usage domain `m < 2¹²⁸` always holds

### 2.4 Paper Claims Accuracy

- [ ] **2.4.1** Update `01_introduction.tex` FFI claims
  - File: [`01_introduction.tex:33–41`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/01_introduction.tex#L33-L41)
  - Claims "formally verified arithmetic functions" — mostly true now (sigma bridge proven, Bézout proven), but `modInverse_spec` still has `sorry`
  - Either: complete the `sorry` first (2.2.1), or add a footnote

- [ ] **2.4.2** Update `04_verified_engine.tex` FFI description
  - File: [`04_verified_engine.tex:19–45`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/04_verified_engine.tex#L19-L45)
  - Mention the `_ok` overflow guards explicitly; reflect reality of bridge theorems

---

## 3. 🔴 Tautologies & Academic Padding

### 3.1 Tautological `abundancy_starvation` Theorem

The theorem in `QPN/AbundancyBound.lean:290–294` proves `X ≤ 2 ∧ Y > 2 ∧ Y < X ⟹ ⊥` by `linarith`, pushing the burden (`h_prefix_val`) into hypotheses.

- [x] **3.1.1** Choose: formally prove `h_prefix_val` **OR** acknowledge in paper
  - **Option A**: Author `abundancy_multiplicative_bipartition` proving `H(N) = H(N_L) · H(N_R)` from `Bipartition` coprimality — this partially closes the gap
  - **Option B** (recommended): Rewrite `02_math_and_formalization.tex:839–861` to explicitly state the Lean theorem proves the *logical implication*, and the runtime invariant is maintained by the Rust engine's `suffix_abundance` precomputation
  - This is standard in verified systems papers (CompCert-style trusted boundaries)

- [x] **3.1.2** Add doc-comment to `abundancy_starvation` explaining the design
  - File: [`QPN/AbundancyBound.lean:285–294`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/AbundancyBound.lean#L285-L294)
  - Explain: this is a *conditional pruning certificate*

### 3.2 "Zsigmondy Poison Trap" Padding — Delete `PoisonTrap.lean`

The `zsigmondy_poison_trap` staples 5 unused Zsigmondy hypotheses (prefixed with `_` to silence warnings) onto the standard Legendre-Cattaneo obstruction in `Obstruction.lean`.

- [ ] **3.2.1** Delete `QPN/PoisonTrap.lean`
  - File: [`QPN/PoisonTrap.lean`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/PoisonTrap.lean) (71 lines)

- [ ] **3.2.2** Remove import from `UALBF.lean`
  - File: [`UALBF.lean:17`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF.lean#L17) — delete `import UALBF.QPN.PoisonTrap`

- [ ] **3.2.3** Remove from `build.rs` C-file list
  - File: [`build.rs:38`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/rust-engine/build.rs#L38) — delete `ir_dir.join("UALBF/QPN/PoisonTrap.c"),`

- [ ] **3.2.4** Remove from `run_gui.py` theorem display
  - File: [`run_gui.py:67`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/rust-engine/run_gui.py#L67) — delete `("zsigmondy_poison_trap", ...)`

- [ ] **3.2.5** Remove from `README.md`
  - File: [`README.md:73`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/README.md#L73)

- [ ] **3.2.6** Verify no paper text references "Poison Trap" — ✅ confirmed, no matches

- [ ] **3.2.7** Run `lake build` + `cargo build --release` after deletion

---

## 4. 🟡 Proof Hygiene Violations

### 4.1 Global Linter Evasions

- [x] **4.1.1** Remove global linter evasions from `PrasadSunitha.lean:12–14`
  - Delete: `set_option linter.unusedTactic false` / `unusedVariables` / `unreachableTactic`
  - The localized `set_option` at line 197 is acceptable (scoped to one lemma)

- [x] **4.1.2** Remove global linter evasions from `RationalBounds.lean:15–17`
  - Same 3 `set_option` lines

### 4.2 Shotgun Tactic Anti-Patterns

- [x] **4.2.1** Fix `h_nodup` shotgun block (`PrasadSunitha.lean:422–428`)
  - Replace 5-alternative `first | ...` with the single correct `exact`

- [x] **4.2.2** Fix `h_sorted_le` shotgun block (`PrasadSunitha.lean:430–436`)

- [x] **4.2.3** Fix `h_perm` shotgun block (`PrasadSunitha.lean:458–462`)

- [x] **4.2.4** Fix all remaining `first |` blocks in `PrasadSunitha.lean`
  - Lines: 455, 467, 475–477, 479, 485–487, 490

- [x] **4.2.5** Fix `first |` blocks in `Cyclotomic.lean`
  - [`Cyclotomic.lean:228–230`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/Cyclotomic.lean#L228-L230), [`347–349`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/Cyclotomic.lean#L347-L349), [`354–356`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/Cyclotomic.lean#L354-L356), and throughout `Zsigmondy.lean`

### 4.3 Redundant Custom Proof

- [x] **4.3.1** Evaluate replacing `sum_range_prime_pow_mul_pred` with existing `nat_geom_sum`
  - **Status**: ✅ **RESOLVED** — Custom induction proof already replaced with one-liner delegating to Mathlib's `geom_sum_mul_of_one_le`. Thin wrapper kept (different RHS form needed by `abundancy_cross_bound`). Doc-comment added explaining rationale.

---

## 5. 🟡 TCB Expansion & Naming

### 5.1 `native_decide` on ℚ Arithmetic

- [ ] **5.1.1** Replace `native_decide` at `AbundancyBound.lean:203`
  - File: [`QPN/AbundancyBound.lean:197–203`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/AbundancyBound.lean#L197-L203)
  - This evaluates which primes are in `filter Nat.Prime (Icc 7 61)` — a finite decidable proposition
  - **Strategy A (preferred)**: Replace with `decide` (kernel-certified, may be slow but trusted)
  - **Strategy B**: Use `head_product_bound` from `RationalBounds.lean:337–342` which already verifies the product via `norm_num`

- [x] **5.1.2** Evaluate `native_decide` at `FFI.lean:56`
  - Context: proves `(b == 0) = true` after `subst hb` — trivial BEq computation
  - ✅ Replaced with `rfl` during FFI fix

### 5.2 🟡 Terrifying Nomenclature: `zsigmondy_axiom`

**Status**: ✅ **RESOLVED**

- [x] **5.2.1** Rename `zsigmondy_axiom` → `zsigmondy_theorem` in `Zsigmondy.lean`
  - File: [`Zsigmondy.lean:277`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/Zsigmondy.lean#L277)
  - This is a **fully proven lemma** — naming it "axiom" will cause reviewers to assume the proof was cheated
  - Also update the doc-comment at line 272–276 which says "Full Zsigmondy axiom"
  - Update all downstream references (e.g., `PoisonTrap.lean` uses it, but that's being deleted)

---

## 6. 🟡 Orphaned / Dead Code

### 6.1 Delete `CycloTest.lean`

- [ ] **6.1.1** Delete `Pure/CycloTest.lean`
  - File: [`CycloTest.lean`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/CycloTest.lean) (52 lines)
  - Contains two standalone lemmas (`x_sq_add_three_le_two_pow`, `composite_bound_simple`) that import raw `Mathlib` (not scoped) and are not imported by any other file
  - Move any lemmas actually used elsewhere into `Arithmetic.lean`, then delete this file

### 6.2 Verify No Dead Rust Code References Zsigmondy Traps

- [ ] **6.2.1** Confirm `dfs_tree.rs` has no `has_zsigmondy_trap` dead code
  - **Status**: ✅ Already confirmed — `dfs_tree.rs` no longer contains this function (removed in a prior conversation)

---

## 7. 🟡 Paper Corrections

### 7.1 Arithmetic Bound Consistency

- [ ] **7.1.1** Verify the `36/35` totient ratio bound is correctly stated
  - The abstract (`main.tex:48–50`) states the head-tail path gives `N/φ(N) < 2.0442` and the pure-ℚ path gives `N/φ(N) < 2.058`
  - Arithmetic check: `(20001/10000) * (36/35) = 20572.57/10000 ≈ 2.0573`, so `2.058` is slightly rounded up — acceptable
  - ✅ The bound `2.058` in the abstract is a safe rounding of `2.0573`; no correction needed
  - Verify the conclusion section also states this correctly

### 7.2 Starvation Pruning Documentation

- [ ] **7.2.1** Update Section 2.9 starvation discussion
  - File: [`02_math_and_formalization.tex:839–861`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/02_math_and_formalization.tex#L839-L861)
  - Add a sentence clarifying: the Lean theorem validates the *logical form*, while the Rust engine maintains the runtime invariant through its suffix-abundance precomputation
  - The proof sketch at lines 848–853 states `H(N) = H_{N_L} · H_{N_R}` — clarify this is the runtime invariant, not a Lean-verified chain

### 7.3 `native_decide` Reference

- [ ] **7.3.1** Update `02_math_and_formalization.tex:508` if replacing `native_decide`
  - Currently says: "via `native_decide` for the head product"
  - If replaced with `decide` or `norm_num`, update this text

### 7.4 Execution Telemetry

- [ ] **7.4.1** Verify Tables 1 & 2 reflect genuine execution data
  - File: [`05_results.tex:45–89`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/05_results.tex#L45-L89)
  - Table 1 currently shows: 346,133 branches, ~2.89s, 119,769 nodes/sec
  - Table 2 shows: 100% abundance/starvation, 0% ray-casting, 345,590 pruned
  - A `cargo run --release` is currently executing — capture the final output and update both tables with the real telemetry
  - **Critical**: The engine was modified (15-factor starvation bound, ray-cast return) — the real numbers will differ from these tables

---

## 8. 🟢 Additional Quality Improvements

### 8.1 Build Verification

- [x] **8.1.1** Run `lake build` and capture full output
  - Verify: zero `sorry` (except `modInverse_spec` if not yet completed), zero `axiom`
  - Verify: zero warnings after linter evasion removal

- [x] **8.1.2** Run `cargo test` with Lean library linked
  - Verify all FFI cross-check tests pass
  - Verify `compute_sigma_checked` returns `None` for overflow cases

### 8.2 Code Documentation

- [ ] **8.2.1** Update `README.md` to reflect PoisonTrap deletion and CycloTest deletion

- [ ] **8.2.2** Add inline documentation to `abundancy_starvation` explaining the TCB boundary

---

## Execution Order

> Suggested dependency-aware execution order:

### Phase A — Critical Fixes (blocks paper submission)
1. **1.1.1–1.1.3**: Delete LLM artifacts from Cyclotomic.lean
2. **2.2.1**: Complete `modInverse_spec` sorry
3. **3.1.1**: Resolve abundancy_starvation gap (prove or acknowledge)
4. **5.1.1**: Replace `native_decide` with `decide`/`norm_num`
5. **5.2.1**: Rename `zsigmondy_axiom` → `zsigmondy_theorem`

### Phase B — Code Cleanup (prevents desk-reject)
6. **3.2.1–3.2.7**: Delete PoisonTrap
7. **6.1.1**: Delete CycloTest.lean
8. **4.1.1–4.1.2**: Remove linter evasions
9. **4.2.1–4.2.5**: Fix shotgun tactics
10. **4.3.1**: Evaluate geom_sum replacement

### Phase C — Paper Updates (accuracy)
11. **2.4.1–2.4.2**: Update FFI claims
12. **7.2.1**: Update starvation section
13. **7.3.1**: Update native_decide references
14. **7.4.1**: Update telemetry tables from live run

### Phase D — Verification (confidence)
15. **2.1.1–2.1.2, 2.3.1–2.3.2**: FFI edge cases and tests
16. **8.1.1–8.1.2**: Full build + test suite
17. **5.1.2**: FFI.lean native_decide (low priority)

---

## Summary Statistics

| Category | Items | Blocking? |
|----------|-------|-----------|
| AI Artifacts Cleanup | 3 tasks | 🔴 Yes (credibility) |
| FFI Verification Gap | 6 tasks | 🔴 Yes (sorry) |
| Tautologies & Padding | 9 tasks | 🔴 Yes (paper accuracy) |
| Proof Hygiene | 8 tasks | 🟡 Desk-reject risk |
| TCB & Naming | 3 tasks | 🟡 Reviewer concern |
| Orphaned Code | 2 tasks | 🟡 Code quality |
| Paper Corrections | 4 tasks | 🟡 Accuracy |
| Build Verification | 4 tasks | 🟢 Best practice |
| **Total** | **39 tasks** | |
