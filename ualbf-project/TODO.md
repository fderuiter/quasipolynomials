# UALBF Project — Critical Remediation TODO

> **Status**: Active — Generated 2026-04-03  
> **Priority Legend**: 🔴 FATAL (blocks publication) · 🟡 SERIOUS (triggers desk-reject) · 🟢 HYGIENE (best practice)

---

## 1. 🔴 FFI Epistemological Severance (Unverified Code Paths)

The FFI layer exports executable algorithms via `@[export]` but lacks complete
formal proofs linking those algorithms to the mathematical specifications
that the QPN theorems rely on.

### 1.1 `computeSigmaNat` ↔ `sigma` Bridge

**Status**: ✅ **PARTIALLY RESOLVED** — `computeSigmaNat_eq_sigma` now exists in `FFI.lean:165–187`
and is fully proven (no `sorry`). The original critique assumed this theorem was missing; it has
since been authored and completed.

- [ ] **1.1.1** Audit `computeSigmaNat_eq_sigma` proof for edge cases
  - File: [`FFI.lean:165–187`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L165-L187)
  - Verify `nat_geom_sum` import from `Pure/Arithmetic.lean` handles `p = 0` and `e = 0` gracefully
  - Confirm `sum_divisors_prime_pow` (Mathlib) matches the current Mathlib version signature
  - Run `lake build` and confirm zero `sorry` / zero warnings in this theorem

- [ ] **1.1.2** Add a cross-validation unit test in `lean_ffi.rs`
  - File: [`lean_ffi.rs:169–208`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/rust-engine/src/lean_ffi.rs#L169-L208)
  - The existing `test_cross_check_sigma` tests against a pure-Rust accumulator. Extend it with:
    - `(2, 0)` → σ(2⁰) = σ(1) = 1
    - `(2, 1)` → σ(2¹) = 1 + 2 = 3
    - Boundary: `(65521, 8)` (large prime, max sieve exponent) — verify no overflow
  - Assert `compute_sigma_checked` returns `Some(...)` for all in-range inputs

### 1.2 `modInverse_spec` Contains `sorry`

**Status**: 🔴 **STILL OPEN** — `FFI.lean:124` contains `sorry`

- [ ] **1.2.1** Complete the `modInverse_spec` proof (eliminate the `sorry`)
  - File: [`FFI.lean:106–136`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L106-L136)
  - The comment at line 128–136 explains the remaining gap: need to show `a' ≡ a (mod m)` combined with Bézout gives `a * v ≡ 1 (mod m)`
  - Strategy: Use `Int.emod_emod_of_dvd`, `Int.add_mul_emod_self`, and the chain:
    1. `a' = ((a % m) + m) % m` → `a' % m = a % m` (standard Int.emod identities)
    2. `a' * x ≡ g (mod m)` from `extGcd_bezout`
    3. `g ∈ {1, -1}` from the if-condition
    4. `v = ((x % m) + m) % m` → `a * v % m = 1 % m`
  - **Deliverable**: `modInverse_spec` with no `sorry`, no `axiom`, no `native_decide`

- [ ] **1.2.2** Add Lean-level test for `modInverse` correctness
  - Create a `#eval` block in `FFI.lean` to spot-check: `modInverse 3 11 = some 4` (since 3·4 = 12 ≡ 1 mod 11)

### 1.3 `toU64Lo` / `toU64Hi` Silent Truncation

**Status**: ✅ **PARTIALLY RESOLVED** — `ualbf_compute_sigma_ok` overflow guard exists
(`FFI.lean:200–202`) and the Rust side panics on overflow (`lean_ffi.rs:70–77`).

- [ ] **1.3.1** Verify the overflow guard actually rejects near-boundary values
  - File: [`FFI.lean:200–202`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L200-L202)
  - Add a Lean `#eval` test: `ualbf_compute_sigma_ok_impl 2 127` should return `0` (σ(2¹²⁷) ≥ 2¹²⁸)
  - Verify the Rust `compute_sigma_checked` correctly interprets `ok == 0` as `None`

- [ ] **1.3.2** Audit `modInverse` output path for 128-bit truncation
  - File: [`FFI.lean:216–238`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L216-L238)
  - `modInverse` returns a value `v` where `0 ≤ v < m`. For inputs where `m` itself exceeds 2¹²⁸, the return value could be silently truncated
  - **Decision needed**: Add a `ualbf_mod_inverse_overflow_ok` guard, or prove that for the engine's usage domain `m < 2¹²⁸` always holds

- [ ] **1.3.3** Update `01_introduction.tex` FFI claims for accuracy
  - File: [`01_introduction.tex:33–41`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/01_introduction.tex#L33-L41)
  - The paper claims "formally verified arithmetic functions" are dispatched via FFI. This is now *mostly* true (sigma bridge proven, extGcd bezout proven), but `modInverse_spec` still has `sorry`
  - Either: complete the `sorry` first, or add a footnote acknowledging the partial verification

- [ ] **1.3.4** Update `04_verified_engine.tex` Section 4.1 FFI description
  - File: [`04_verified_engine.tex:19–45`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/04_verified_engine.tex#L19-L45)
  - Ensure the description matches reality: bridge theorems exist for `computeSigmaNat`, Bézout identity proven for `extGcd`, `modInverse_spec` proof deferred
  - Mention the `_ok` overflow guards explicitly

---

## 2. 🔴 Tautological `abundancy_starvation` Theorem

The `abundancy_starvation` theorem in `QPN/AbundancyBound.lean:290–294` proves the trivial
implication `X ≤ 2 ∧ Y > 2 ∧ Y < X ⟹ ⊥` by `linarith`, pushing the actual mathematical
burden (`h_prefix_val`) into hypotheses.

### 2.1 Assess the Mathematical Gap

- [ ] **2.1.1** Determine whether `h_prefix_val` can be formally proven
  - The hypothesis `h_prefix_val : abundancy_index N < N_prefix * S_max_remaining` requires proving the **sub-multiplicativity** of H(N) across the Bipartition: `H(N) = H(N_L) · H(N_R)` and `H(N_R) ≤ S_max_remaining`
  - The multiplicativity `H(N) = H(N_L) · H(N_R)` follows from the coprimality in the `Bipartition` structure + multiplicativity of σ — this is provable from existing components
  - The bound `H(N_R) ≤ S_max_remaining` depends on how `suffix_abundance` is computed in `main.rs`; this is a runtime invariant, not a Lean-provable theorem
  - **Conclusion**: The gap is fundamentally a *systems-mathematics boundary* — the Lean theorem is correct as a conditional, and the Rust engine is responsible for satisfying the preconditions

- [ ] **2.1.2** Option A: Formally prove `h_prefix_val` from sub-multiplicativity
  - File: [`QPN/AbundancyBound.lean:290–294`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/AbundancyBound.lean#L290-L294)
  - Author a new theorem `abundancy_multiplicative_bipartition` proving:
    ```lean
    theorem abundancy_multiplicative_bipartition (B : Bipartition) :
      abundancy_index B.N = abundancy_index B.N_L * abundancy_index B.N_R
    ```
  - This would partially close the gap by proving the structural decomposition

- [ ] **2.1.3** Option B: Acknowledge the assumption in the paper
  - File: [`02_math_and_formalization.tex:839–861`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/02_math_and_formalization.tex#L839-L861)
  - Rewrite the "Formal Starvation Pruning Certificate" section to explicitly state:
    - The Lean theorem proves the *logical implication* (if the bound holds, the branch is dead)
    - The *runtime invariant* (that the computed suffix abundance is a valid upper bound) is maintained by the Rust engine's precomputation logic, not by a Lean proof
  - This is the honest approach and is standard in verified systems papers (e.g., CompCert acknowledges assembly trust assumptions)

### 2.2 Documentation Fixes

- [ ] **2.2.1** Add a doc-comment to `abundancy_starvation` explaining the design
  - File: [`QPN/AbundancyBound.lean:285–294`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/AbundancyBound.lean#L285-L294)
  - Explain that this is a *conditional pruning certificate*: the Lean side proves the mathematical implication, while the Rust side is responsible for ensuring the preconditions hold via its `suffix_abundance` precomputation

---

## 3. 🟡 Academic Padding: PoisonTrap.lean

The `zsigmondy_poison_trap` in `QPN/PoisonTrap.lean` staples 5 unused
Zsigmondy hypotheses to the standard Legendre-Cattaneo Mod-8 obstruction
already proven in `Obstruction.lean`.

### 3.1 Code Cleanup

- [ ] **3.1.1** Delete `QPN/PoisonTrap.lean`
  - File: [`QPN/PoisonTrap.lean`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/PoisonTrap.lean) (71 lines)
  - The theorem `zsigmondy_poison_trap`:
    - Prefixes `_hn_odd`, `_hp_prime`, `_he_bound` with underscores (unused)
    - Discards Zsigmondy conditions `¬(q ∣ p - 1)` and `q % (2e+1) = 1` with `_`
    - Simply re-applies `legendre_cattaneo_obstruction` from `Obstruction.lean`
  - The Mod-8 obstruction is fully handled by `Obstruction.lean:20–121`
  - The Zsigmondy lemma chain (`Pure/Zsigmondy.lean`, `Pure/Cyclotomic.lean`) provides the *existence* of primitive primes, which the Phase 1 sieve already uses exhaustively

- [ ] **3.1.2** Remove import from root module `UALBF.lean`
  - File: [`UALBF.lean:17`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF.lean#L17)
  - Delete line: `import UALBF.QPN.PoisonTrap`

- [ ] **3.1.3** Remove from `build.rs` C-file list
  - File: [`build.rs:38`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/rust-engine/build.rs#L38)
  - Delete: `ir_dir.join("UALBF/QPN/PoisonTrap.c"),`

- [ ] **3.1.4** Remove from `run_gui.py` theorem display
  - File: [`run_gui.py:67`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/rust-engine/run_gui.py#L67)
  - Delete line: `("zsigmondy_poison_trap",        "QPN/PoisonTrap.lean"),`

- [ ] **3.1.5** Remove from `README.md`
  - File: [`README.md:73`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/README.md#L73)
  - Delete the `PoisonTrap.lean` entry from the file listing

### 3.2 Paper Adjustments

- [ ] **3.2.1** Verify no paper text references "Poison Trap" by name
  - Search result: **No matches** found in `paper/sections/` for "PoisonTrap" or "poison" (confirmed via grep)
  - The paper already describes the Zsigmondy obstruction chain correctly in `02_math_and_formalization.tex:814–835` using `Lemma 2.17 (Zsigmondy-Induced Parity Contradiction)` which is a separate, correctly-stated result
  - ✅ No paper changes needed for this item

- [ ] **3.2.2** Verify `02_math_and_formalization.tex` Zsigmondy section is accurate post-deletion
  - File: [`02_math_and_formalization.tex:814–835`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/02_math_and_formalization.tex#L814-L835)
  - The paper's Lemma 2.17 is architecturally different from the deleted `PoisonTrap.lean` — it correctly states the Zsigmondy-induced parity contradiction and references the Phase 1 sieve
  - Confirm that the paper references `Obstruction.lean` (not `PoisonTrap.lean`) for the mod-8 check

### 3.3 Build Verification

- [ ] **3.3.1** Run `lake build` after deletion to confirm no compilation errors
  - Working directory: `lean4-proofs/`
  - Verify no other file imports `UALBF.QPN.PoisonTrap`

- [ ] **3.3.2** Run `cargo build --release` after `build.rs` update
  - Working directory: `rust-engine/`
  - Verify the compiled library excludes `PoisonTrap.c`

---

## 4. 🟡 Proof Hygiene Violations

### 4.1 Global Linter Evasions

**Files affected:**
- [`QPN/PrasadSunitha.lean:12–14`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/PrasadSunitha.lean#L12-L14) — 3 global `set_option linter.*`
- [`Pure/RationalBounds.lean:15–17`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/Pure/RationalBounds.lean#L15-L17) — 3 global `set_option linter.*`

- [ ] **4.1.1** Remove global linter evasions from `PrasadSunitha.lean`
  - Delete lines 12–14:
    ```lean
    set_option linter.unusedTactic false
    set_option linter.unusedVariables false
    set_option linter.unreachableTactic false
    ```
  - Fix each resulting linter warning individually (see 4.2, 4.3 below)
  - **Exception**: The localized `set_option linter.unusedVariables false in` at line 197 is acceptable (scoped to a single lemma)

- [ ] **4.1.2** Remove global linter evasions from `RationalBounds.lean`
  - Delete lines 15–17 (same 3 `set_option` lines)
  - Fix each resulting linter warning individually

### 4.2 Shotgun Tactic Anti-Patterns in `PrasadSunitha.lean`

- [ ] **4.2.1** Fix `h_nodup` shotgun block (lines 422–428)
  - File: [`PrasadSunitha.lean:422–428`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/PrasadSunitha.lean#L422-L428)
  - Current: 5 alternatives via `first | ... | ... | ...`
  - Action: Hover in Lean IDE to find correct alternative, replace with single `exact`
  - Target Mathlib lemma is likely `Finset.sort_nodup (· ≤ ·) S` or `Finset.nodup_sort`

- [ ] **4.2.2** Fix `h_sorted_le` shotgun block (lines 430–436)
  - File: [`PrasadSunitha.lean:430–436`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/PrasadSunitha.lean#L430-L436)
  - Current: 5 alternatives
  - Target Mathlib lemma: `Finset.sort_sorted (· ≤ ·) S`

- [ ] **4.2.3** Fix `h_eq_elems` / `h_perm` shotgun blocks (lines 449–462)
  - File: [`PrasadSunitha.lean:449–462`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/PrasadSunitha.lean#L449-L462)
  - Also fix smaller `first |` blocks at lines 455, 467, 475–477, 479, 485–487, 490

- [ ] **4.2.4** Fix all remaining `first |` blocks in `PrasadSunitha.lean`
  - Lines: 455, 467, 475–477, 479, 485–487, 490
  - Each is a 2-alternative Mathlib API guess — determine the correct signature and use a single `exact`

### 4.3 Redundant Custom Proof: `sum_range_prime_pow_mul_pred`

- [ ] **4.3.1** Evaluate replacing `sum_range_prime_pow_mul_pred` with Mathlib lemma
  - File: [`PrasadSunitha.lean:56–77`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/PrasadSunitha.lean#L56-L77)
  - The custom 22-line induction proof proves: `(∑ k ∈ range (e+1), p^k) * (p-1) = p^(e+1) - 1`
  - **Candidate replacement**: `geom_sum_mul` from `Mathlib.Algebra.GeometricSum` or `nat_geom_sum` from `Pure/Arithmetic.lean:524`
  - **Caveat**: The custom proof works in `ℕ` (natural number subtraction), while `geom_sum_mul` works in `ℤ` or a commutative ring. May need `Nat.sub` handling.
  - **Note**: `nat_geom_sum` at `Pure/Arithmetic.lean:524` is already a custom Nat version: `(p - 1) * (∑ i ∈ range n, p^i) + 1 = p^n`. This is mathematically equivalent but has the constant on the other side.
  - **Action**: Either import `nat_geom_sum` and derive the `PrasadSunitha` form via `omega`, or keep the custom proof but add a comment referencing `nat_geom_sum` as the canonical version

- [ ] **4.3.2** If keeping the custom proof, add a doc-comment explaining why
  - Explain: Nat subtraction requires careful handling that `geom_sum_mul` (operating in ℤ) doesn't provide; the custom proof avoids an `Int.toNat` cast chain

---

## 5. 🟡 TCB Expansion: `native_decide` on ℚ Arithmetic

### 5.1 `native_decide` in `AbundancyBound.lean`

- [ ] **5.1.1** Replace `native_decide` at `AbundancyBound.lean:203` with `norm_num` or `decide`
  - File: [`QPN/AbundancyBound.lean:197–203`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/QPN/AbundancyBound.lean#L197-L203)
  - The `native_decide` evaluates a `Finset.prod` of 15 rational cube fractions
  - **Strategy A (preferred)**: Replace with `decide` (kernel-certified). May be slow (minutes), but is fully trusted
  - **Strategy B**: Unfold the `Finset.prod` into explicit `*` chains and apply `norm_num` to verify the rational equality
  - **Strategy C**: Use the existing `head_product_bound` lemma from `RationalBounds.lean:337–342` which verifies the same product via `norm_num`. Restructure the proof to use that lemma instead
  - **Note**: Strategy C is already partially implemented — `head_product_bound` exists and is used at line 210. The `native_decide` at line 203 is specifically for evaluating which primes are in `filter Nat.Prime (Icc 7 61)`. This is a `Decidable` computation, and `decide` should work (it's a finite decidable proposition)

### 5.2 `native_decide` in `FFI.lean`

- [ ] **5.2.1** Evaluate `native_decide` at `FFI.lean:56`
  - File: [`FFI.lean:55–57`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/lean4-proofs/UALBF/FFI.lean#L55-L57)
  - Context: This `native_decide` proves `(b == 0) = true` after `subst hb` establishes `b = 0`
  - This is a trivially decidable BEq computation; replacing with `simp [BEq.beq]` or `rfl` should work
  - **Risk**: Low — this is a boolean evaluation, not a rational arithmetic computation
  - **Priority**: Lower than 5.1.1 since the TCB expansion here is minimal

---

## 6. 🟢 Additional Quality Improvements

### 6.1 Paper Consistency

- [ ] **6.1.1** Audit `02_math_and_formalization.tex:508` reference to `native_decide`
  - File: [`02_math_and_formalization.tex:508`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/02_math_and_formalization.tex#L508)
  - The paper mentions `native_decide` for the head product. If replacing with `decide` or `norm_num`, update this reference

- [ ] **6.1.2** Ensure Section 2.9 starvation discussion matches actual theorem
  - File: [`02_math_and_formalization.tex:839–861`](file:///Volumes/SanDisk%20External%20SSD/Code/quasipolynomials/ualbf-project/paper/sections/02_math_and_formalization.tex#L839-L861)
  - The paper's proof sketch (lines 848–853) states `H(N) = H_{N_L} · H_{N_R}` and `H_{N_R} ≤ S_{max}` — this is exactly the `h_prefix_val` hypothesis
  - The reader may interpret this as a formally proven chain, but it's actually a runtime invariant
  - Add a sentence clarifying that the Lean theorem validates the *logical form*, while the Rust engine maintains the runtime invariant through its suffix-abundance precomputation

### 6.2 Build System

- [ ] **6.2.1** Remove `PoisonTrap.c` from `build.rs` rerun triggers
  - After deleting `PoisonTrap.lean`, the `.lake/build/ir/UALBF/QPN/PoisonTrap.c` file will no longer be generated
  - Ensure `build.rs` doesn't reference it (direct reference at line 38, covered by 3.1.3)

### 6.3 Lean Build Verification

- [ ] **6.3.1** Run `lake build` and capture full output
  - Working directory: `lean4-proofs/`
  - Verify: zero `sorry`, zero `axiom` (except `modInverse_spec` if not yet completed)
  - Verify: zero warnings after linter evasion removal
  - Document the Lean toolchain version (`lean-toolchain` file)

- [ ] **6.3.2** Run `cargo test` with Lean library linked
  - Working directory: `rust-engine/`
  - Verify all FFI cross-check tests pass
  - Verify `compute_sigma_checked` returns `None` for overflow cases

### 6.4 Code Documentation

- [ ] **6.4.1** Update `README.md` to reflect PoisonTrap deletion
  - Remove the `PoisonTrap.lean` entry from the file listing
  - Add note explaining why: the mod-8 obstruction is fully handled by `Obstruction.lean`

- [ ] **6.4.2** Add inline documentation to `abundancy_starvation` explaining the TCB boundary
  - Explain: the hypothesis `h_prefix_val` represents the Runtime–Proof interface; the Lean side proves the mathematical implication, the Rust side maintains the invariant

---

## Execution Order

> Suggested dependency-aware execution order:

1. **Phase A — Critical Fixes** (blocks paper submission)
   - 1.2.1: Complete `modInverse_spec` sorry
   - 2.1.2 or 2.1.3: Resolve abundancy_starvation gap (prove or acknowledge)
   - 5.1.1: Replace `native_decide` with `decide`/`norm_num`

2. **Phase B — Code Cleanup** (prevents desk-reject)
   - 3.1.1–3.1.5: Delete PoisonTrap
   - 4.1.1–4.1.2: Remove linter evasions
   - 4.2.1–4.2.4: Fix shotgun tactics
   - 4.3.1: Evaluate geom_sum replacement

3. **Phase C — Paper Updates** (accuracy)
   - 1.3.3–1.3.4: Update FFI claims
   - 6.1.1–6.1.2: Update starvation / native_decide references

4. **Phase D — Verification** (confidence)
   - 1.1.1–1.1.2, 1.3.1–1.3.2: FFI edge cases and tests
   - 3.3.1–3.3.2: Build verification
   - 6.3.1–6.3.2: Full build + test suite
   - 5.2.1: FFI.lean native_decide (low priority)

---

## Summary Statistics

| Category | Items | Blocking? |
|----------|-------|-----------|
| FFI Verification Gap | 8 tasks | 🔴 Yes (sorry) |
| Starvation Tautology | 4 tasks | 🔴 Yes (paper accuracy) |
| PoisonTrap Deletion | 7 tasks | 🟡 Desk-reject risk |
| Proof Hygiene | 8 tasks | 🟡 Desk-reject risk |
| TCB native_decide | 2 tasks | 🟡 Reviewer concern |
| Quality / Docs | 6 tasks | 🟢 Best practice |
| **Total** | **35 tasks** | |
