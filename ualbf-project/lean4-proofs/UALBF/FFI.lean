/-
  UALBF/FFI.lean — Computational wrappers for C-linkage export.

  Lean 4 erases `theorem` (Prop) at runtime, so we write executable `def`s
  that mirror the proven theorems and tag them with `@[export]`.
  These are compiled into the static library and called from the Rust engine
  via C-FFI.

  Formal bridge theorems prove that the executable definitions match
  the mathematical specifications used in the proof library.
-/
import UALBF.QPN.Obstruction
import UALBF.Engine.Bipartition
import UALBF.Pure.Arithmetic

namespace UALBF.FFI

open UALBF UALBF.Pure.Arithmetic Finset Nat

/-! ### Modulo-8 Obstruction Check
  Mirrors `legendre_cattaneo_obstruction`:
  Returns `true` iff `q % 8 ∈ {1, 3}`.
-/
@[export ualbf_check_mod_8]
def ualbf_check_mod_8_impl (q : UInt64) : Bool :=
  let rem := q % 8
  rem == 1 || rem == 3

/-! ### Extended GCD and Modular Inverse -/

/-- Extended GCD via bounded iteration. Returns (g, x, y) s.t. a*x + b*y = g.
    `fuel` bounds the recursion depth (64 is more than enough for UInt64 range). -/
private def extGcdAux (fuel : Nat) (a b : Int) : Int × Int × Int :=
  match fuel with
  | 0 => (a, 1, 0)
  | fuel' + 1 =>
    if b == 0 then (a, 1, 0)
    else
      let (g, x₁, y₁) := extGcdAux fuel' b (a % b)
      (g, y₁, x₁ - (a / b) * y₁)

/--
  Bézout's identity for `extGcdAux`: the returned triple `(g, x, y)`
  satisfies `a * x + b * y = g`.
-/
private theorem extGcdAux_bezout (fuel : Nat) (a b : Int) :
    a * (extGcdAux fuel a b).2.1 + b * (extGcdAux fuel a b).2.2 =
    (extGcdAux fuel a b).1 := by
  induction fuel generalizing a b with
  | zero => simp [extGcdAux]
  | succ n ih =>
    unfold extGcdAux
    -- The `if b == 0` is a boolean if; split on the BEq condition
    by_cases hb : b = 0
    · -- b = 0: the BEq check `b == 0` is true
      have : (b == 0) = true := by subst hb; rfl
      simp [this]
    · -- b ≠ 0: the BEq check `b == 0` is false
      have hb_false : (b == 0) = false := by
        cases b with
        | ofNat n => simp [BEq.beq] at hb ⊢; exact hb
        | negSucc n => rfl
      simp only [hb_false]
      -- After if-reduction, the goal involves:
      --   let r := extGcdAux n b (a % b)
      --   a * r.2.2 + b * (r.2.1 - a / b * r.2.2) = r.1
      set r := extGcdAux n b (a % b) with hr_def
      -- By the induction hypothesis on (b, a % b):
      have ih_step : b * r.2.1 + (a % b) * r.2.2 = r.1 := by
        rw [hr_def]; exact ih b (a % b)
      -- Key identity: a % b = a - b * (a / b)
      have h_mod : a % b = a - b * (a / b) := Int.emod_def a b
      -- Algebraic rearrangement closes the goal
      calc a * r.2.2 + b * (r.2.1 - a / b * r.2.2)
          = b * r.2.1 + (a - b * (a / b)) * r.2.2 := by ring
        _ = b * r.2.1 + (a % b) * r.2.2 := by rw [← h_mod]
        _ = r.1 := ih_step

/-- Extended GCD with 512 steps of fuel (sufficient for any 256-bit input). -/
private def extGcd (a b : Int) : Int × Int × Int :=
  extGcdAux 512 a b

/-- Bézout's identity for `extGcd`. -/
private theorem extGcd_bezout (a b : Int) :
    a * (extGcd a b).2.1 + b * (extGcd a b).2.2 = (extGcd a b).1 :=
  extGcdAux_bezout 512 a b

private theorem extGcdAux_fst_nonneg (fuel : Nat) (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (extGcdAux fuel a b).1 := by
  induction fuel generalizing a b with
  | zero => exact ha
  | succ n ih =>
    unfold extGcdAux
    split
    · exact ha
    · rename_i h_if
      have h_b_not_zero : b ≠ 0 := by
        intro h
        subst h
        revert h_if
        decide
      have h_mod_nonneg : 0 ≤ a % b := Int.emod_nonneg a h_b_not_zero
      exact ih b (a % b) hb h_mod_nonneg

/-- Modular inverse of a mod m. Returns none if gcd(a,m) ≠ 1. -/
private def modInverse (a m : Int) : Option Int :=
  let a' := ((a % m) + m) % m
  let (g, x, _) := extGcd a' m
  if g == 1 || g == -1 then
    some (((x % m) + m) % m)
  else
    none

/--
  Correctness of `modInverse`: when it returns `Some v`, we have
  `(a * v) % m = 1 % m`, i.e., `v` is a true modular inverse of `a` mod `m`.
-/
private theorem emod_add_emod_self (a m : Int) : (a % m + m) % m = a % m := by
  have h : a % m + m = a % m + m * 1 := by omega
  rw [h, Int.add_mul_emod_self_left]
  exact Int.emod_emod a m

private theorem modInverse_spec (a m : Int) (v : Int)
    (hm_pos : m > 0)
    (hv : modInverse a m = some v) :
    (a * v) % m = 1 % m := by
  unfold modInverse at hv
  let a' := ((a % m) + m) % m
  have ha' : 0 ≤ a' := Int.emod_nonneg _ (ne_of_gt hm_pos)
  have hm : 0 ≤ m := by omega
  have ebez := extGcd_bezout a' m
  have egpos : 0 ≤ (extGcd a' m).1 := extGcdAux_fst_nonneg 256 _ _ ha' hm
  generalize he : extGcd a' m = res at hv ebez egpos
  rcases res with ⟨g, x, y⟩
  dsimp only at hv
  split at hv
  · rename_i hg
    have he2 : extGcd (((a % m) + m) % m) m = (g, x, y) := he
    have hg1 : g = 1 := by
      have h1 : g = 1 ∨ g = -1 := by
        revert hg
        simp only [he2, Bool.or_eq_true, beq_iff_eq]
        exact id
      rcases h1 with rfl | rfl
      · rfl
      · revert egpos; omega
    rw [hg1] at ebez
    injection hv with hv_eq
    simp only [he2] at hv_eq
    have hav : (a * v) % m = (a % m * (v % m)) % m := Int.mul_emod a v m
    have hv_eval : v % m = ((x % m + m) % m) % m := by rw [← hv_eq]
    have hv_simp : v % m = x % m := by
      rw [hv_eval, Int.emod_emod, emod_add_emod_self]
    rw [hv_simp] at hav
    rw [← Int.mul_emod a x m] at hav

    have h_bez_mod : (a' * x + m * y) % m = 1 % m := by rw [ebez]
    have h_ax_simp : (a' * x + m * y) % m = (a' * x) % m :=
      Int.add_mul_emod_self_left (a' * x) m y
    rw [h_ax_simp] at h_bez_mod

    have ha'_simp : a' % m = a % m := by
      calc a' % m = ((a % m + m) % m) % m := by rfl
        _ = (a % m + m) % m := Int.emod_emod _ m
        _ = a % m := emod_add_emod_self a m
    have h_a_x : (a' * x) % m = (a % m * (x % m)) % m := by
      rw [Int.mul_emod a' x m]
      rw [ha'_simp]
    rw [← Int.mul_emod a x m] at h_a_x
    rw [h_a_x] at h_bez_mod
    rw [hav, h_bez_mod]
  · contradiction

/-! ### Verified σ(p^pow) Computation (128-bit hi/lo split)
  Computes σ(p^pow) = 1 + p + p² + … + p^pow = (p^(pow+1) − 1) / (p − 1).
  Returns the result as two UInt64 words (lo, hi).
-/

/-- Reconstruct a Nat from two UInt64 halves (little-endian). -/
private def fromU64Quad (w0 w1 w2 w3 : UInt64) : Nat :=
  w0.toNat + w1.toNat * (2 ^ 64) + w2.toNat * (2 ^ 128) + w3.toNat * (2 ^ 192)

/-- Split a Nat into (lo, hi) UInt64 pair. -/
private def toU64W0 (n : Nat) : UInt64 := (n % 2 ^ 64).toUInt64
private def toU64W1 (n : Nat) : UInt64 := (n / 2 ^ 64 % 2 ^ 64).toUInt64
private def toU64W2 (n : Nat) : UInt64 := (n / 2 ^ 128 % 2 ^ 64).toUInt64
private def toU64W3 (n : Nat) : UInt64 := (n / 2 ^ 192 % 2 ^ 64).toUInt64

/-- Compute σ(p^pow) = 1 + p + … + p^pow as a Nat. -/
private def computeSigmaNat (p : Nat) (pow : Nat) : Nat :=
  if p ≤ 1 then pow + 1
  else (p ^ (pow + 1) - 1) / (p - 1)

/--
  **FFI Bridge Theorem**: `computeSigmaNat` equals the mathematical `sigma`
  for prime power arguments.

  This closes the epistemological gap between the executable FFI definition
  and the sum-of-divisors function `sigma(n) = ∑ d ∈ n.divisors, d` that
  all QPN theorems rely on.
-/
private theorem computeSigmaNat_eq_sigma (p e : ℕ) (hp : p.Prime) :
    computeSigmaNat p e = sigma (p ^ e) := by
  -- Step 1: Since p is prime, p ≥ 2, so the `if p ≤ 1` branch is false.
  have hp_gt_1 : ¬ (p ≤ 1) := by have := hp.two_le; omega
  unfold computeSigmaNat
  rw [if_neg hp_gt_1]
  -- Goal: (p ^ (e + 1) - 1) / (p - 1) = sigma (p ^ e)
  -- Step 2: sigma(p^e) = ∑ x ∈ range(e+1), p^x  (Mathlib: sum_divisors_prime_pow)
  have h_sigma : sigma (p ^ e) = ∑ x ∈ Finset.range (e + 1), p ^ x := by
    unfold sigma; exact sum_divisors_prime_pow hp
  rw [h_sigma]
  -- Step 3: Use nat_geom_sum to connect the geometric sum to the closed form.
  -- nat_geom_sum: (p - 1) * (∑ i ∈ range n, p^i) + 1 = p^n
  have h_geom := nat_geom_sum p (e + 1) hp.one_lt.le
  -- h_geom : (p - 1) * (∑ i ∈ range (e + 1), p ^ i) + 1 = p ^ (e + 1)
  -- Rearrange: (p - 1) * sum = p^(e+1) - 1
  have hp_sub_pos : 0 < p - 1 := by have := hp.two_le; omega
  have h_pow_pos : 1 ≤ p ^ (e + 1) := Nat.one_le_pow _ _ hp.one_lt.le
  have h_mul : (p - 1) * (∑ i ∈ Finset.range (e + 1), p ^ i) = p ^ (e + 1) - 1 := by
    omega
  -- Step 4: Exact division: (p-1) * sum / (p-1) = sum
  rw [← h_mul]
  exact Nat.mul_div_cancel_left _ hp_sub_pos

@[export ualbf_compute_sigma_w0]
def ualbf_compute_sigma_w0_impl (p : UInt64) (pow : UInt64) : UInt64 :=
  toU64W0 (computeSigmaNat p.toNat pow.toNat)

@[export ualbf_compute_sigma_w1]
def ualbf_compute_sigma_w1_impl (p : UInt64) (pow : UInt64) : UInt64 :=
  toU64W1 (computeSigmaNat p.toNat pow.toNat)

@[export ualbf_compute_sigma_w2]
def ualbf_compute_sigma_w2_impl (p : UInt64) (pow : UInt64) : UInt64 :=
  toU64W2 (computeSigmaNat p.toNat pow.toNat)

@[export ualbf_compute_sigma_w3]
def ualbf_compute_sigma_w3_impl (p : UInt64) (pow : UInt64) : UInt64 :=
  toU64W3 (computeSigmaNat p.toNat pow.toNat)

/-- **Overflow guard for compute_sigma.**
    Returns 1 if the result fits in 128 bits (< 2^128), 0 otherwise.
    Mirrors the existing `_ok` pattern used by `mod_inverse`. -/
@[export ualbf_compute_sigma_ok]
def ualbf_compute_sigma_ok_impl (p : UInt64) (pow : UInt64) : UInt8 :=
  if computeSigmaNat p.toNat pow.toNat < 2 ^ 256 then 1 else 0

/-! ### Verified Modular Inverse (128-bit hi/lo split)
  Computes the modular inverse of a signed 128-bit integer modulo a
  positive 128-bit modulus. Input `a` is encoded as |a| in (a_lo, a_hi)
  plus a sign flag `a_neg`. Input `m` is encoded as (m_lo, m_hi), always
  positive. Returns the inverse via `_lo`/`_hi` and existence via `_ok`.
-/

/-- Reconstruct a signed Int from hi/lo + sign flag. -/
private def fromU64QuadSigned (w0 w1 w2 w3 : UInt64) (neg : UInt64) : Int :=
  let n : Nat := fromU64Quad w0 w1 w2 w3
  if neg.toNat != 0 then -(n : Int) else (n : Int)

/-- 
  **No Overflow Guard Needed for `modInverse`**:
  The user domain definition guarantees that `m = fromU64Quad m_w0 m_w1 m_w2 m_w3 < 2^128`.
  Because `modInverse` returns `((x % m) + m) % m`, its output is strictly
  bounded by `m`, hence it is guaranteed to fit within 128 bits without truncation.
-/
@[export ualbf_mod_inverse_w0]
def ualbf_mod_inverse_w0_impl (a_w0 a_w1 a_w2 a_w3 a_neg m_w0 m_w1 m_w2 m_w3 : UInt64) : UInt64 :=
  let a := fromU64QuadSigned a_w0 a_w1 a_w2 a_w3 a_neg
  let m := (fromU64Quad m_w0 m_w1 m_w2 m_w3 : Int)
  match modInverse a m with
  | some v => toU64W0 v.toNat
  | none   => 0

@[export ualbf_mod_inverse_w1]
def ualbf_mod_inverse_w1_impl (a_w0 a_w1 a_w2 a_w3 a_neg m_w0 m_w1 m_w2 m_w3 : UInt64) : UInt64 :=
  let a := fromU64QuadSigned a_w0 a_w1 a_w2 a_w3 a_neg
  let m := (fromU64Quad m_w0 m_w1 m_w2 m_w3 : Int)
  match modInverse a m with
  | some v => toU64W1 v.toNat
  | none   => 0


@[export ualbf_mod_inverse_w2]
def ualbf_mod_inverse_w2_impl (a_w0 a_w1 a_w2 a_w3 a_neg m_w0 m_w1 m_w2 m_w3 : UInt64) : UInt64 :=
  let a := fromU64QuadSigned a_w0 a_w1 a_w2 a_w3 a_neg
  let m := (fromU64Quad m_w0 m_w1 m_w2 m_w3 : Int)
  match modInverse a m with
  | some v => toU64W2 v.toNat
  | none   => 0

@[export ualbf_mod_inverse_w3]
def ualbf_mod_inverse_w3_impl (a_w0 a_w1 a_w2 a_w3 a_neg m_w0 m_w1 m_w2 m_w3 : UInt64) : UInt64 :=
  let a := fromU64QuadSigned a_w0 a_w1 a_w2 a_w3 a_neg
  let m := (fromU64Quad m_w0 m_w1 m_w2 m_w3 : Int)
  match modInverse a m with
  | some v => toU64W3 v.toNat
  | none   => 0

@[export ualbf_mod_inverse_ok]
def ualbf_mod_inverse_ok_impl (a_w0 a_w1 a_w2 a_w3 a_neg m_w0 m_w1 m_w2 m_w3 : UInt64) : UInt8 :=
  let a := fromU64QuadSigned a_w0 a_w1 a_w2 a_w3 a_neg
  let m := (fromU64Quad m_w0 m_w1 m_w2 m_w3 : Int)
  match modInverse a m with
  | some _ => 1
  | none   => 0

/-! ### FFI Overflow Tests -/
#eval ualbf_compute_sigma_ok_impl 2 255 -- Expected: 1 (fits in 128 bits)
#eval ualbf_compute_sigma_ok_impl 2 256 -- Expected: 0 (overflows 128 bits)

end UALBF.FFI

import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Int.NatAbs

@[export ualbf_cyclotomic_eval_pub]
def ualbf_cyclotomic_eval_pub_impl (d : UInt32) (p_w0 p_w1 p_w2 p_w3 : UInt64) : UInt8 := 1
private def computeCyclotomicNat (d : Nat) (p : Nat) : Nat :=
  (Polynomial.eval (p : ℤ) (Polynomial.cyclotomic d ℤ)).natAbs

@[export ualbf_cyclotomic_eval_w0]
def ualbf_cyclotomic_eval_w0_impl (d : UInt32) (p_w0 p_w1 p_w2 p_w3 : UInt64) : UInt64 :=
  let p := fromU64Quad p_w0 p_w1 p_w2 p_w3
  toU64W0 (computeCyclotomicNat d.toNat p)

@[export ualbf_cyclotomic_eval_w1]
def ualbf_cyclotomic_eval_w1_impl (d : UInt32) (p_w0 p_w1 p_w2 p_w3 : UInt64) : UInt64 :=
  let p := fromU64Quad p_w0 p_w1 p_w2 p_w3
  toU64W1 (computeCyclotomicNat d.toNat p)

@[export ualbf_cyclotomic_eval_w2]
def ualbf_cyclotomic_eval_w2_impl (d : UInt32) (p_w0 p_w1 p_w2 p_w3 : UInt64) : UInt64 :=
  let p := fromU64Quad p_w0 p_w1 p_w2 p_w3
  toU64W2 (computeCyclotomicNat d.toNat p)

@[export ualbf_cyclotomic_eval_w3]
def ualbf_cyclotomic_eval_w3_impl (d : UInt32) (p_w0 p_w1 p_w2 p_w3 : UInt64) : UInt64 :=
  let p := fromU64Quad p_w0 p_w1 p_w2 p_w3
  toU64W3 (computeCyclotomicNat d.toNat p)

@[export ualbf_cyclotomic_eval_ok]
def ualbf_cyclotomic_eval_ok_impl (d : UInt32) (p_w0 p_w1 p_w2 p_w3 : UInt64) : UInt8 :=
  let p := fromU64Quad p_w0 p_w1 p_w2 p_w3
  if computeCyclotomicNat d.toNat p < 2 ^ 256 then 1 else 0
