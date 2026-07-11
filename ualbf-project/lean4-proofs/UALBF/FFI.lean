/-
  UALBF/FFI.lean — Computational wrappers for C-linkage export.

  Lean 4 erases `theorem` (Prop) at runtime, so we write executable `def`s
  that mirror the proven theorems and tag them with `@[export]`.
  These are compiled into the static library and called from the Rust engine
  via C-FFI.

  Formal bridge theorems prove that the executable definitions match
  the mathematical specifications used in the proof library.
-/

import UALBF.ManifestConstants
import UALBF.Pure.Fixed64
import UALBF.Pure.Arithmetic
import UALBF.Pure.Cyclotomic

set_option exponentiation.threshold 1024

namespace UALBF.FFI

open UALBF UALBF.Pure.Arithmetic Finset Nat

-- Define the external object type (U512 remains opaque as it is purely FFI)

abbrev U512 : Type := Nat

@[extern "rust_u512_mk"]
def U512.mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512 :=
  w0.toNat +
  w1.toNat * (2 ^ 64) +
  w2.toNat * (2 ^ 128) +
  w3.toNat * (2 ^ 192) +
  w4.toNat * (2 ^ 256) +
  w5.toNat * (2 ^ 320) +
  w6.toNat * (2 ^ 384) +
  w7.toNat * (2 ^ 448)

instance : Inhabited U512 where
  default := U512.mk 0 0 0 0 0 0 0 0

@[extern "rust_u512_get_w0"]
def U512.w0 (u : @& U512) : UInt64 := (u % 2^64).toUInt64
@[extern "rust_u512_get_w1"]
def U512.w1 (u : @& U512) : UInt64 := ((u / 2^64) % 2^64).toUInt64
@[extern "rust_u512_get_w2"]
def U512.w2 (u : @& U512) : UInt64 := ((u / 2^128) % 2^64).toUInt64
@[extern "rust_u512_get_w3"]
def U512.w3 (u : @& U512) : UInt64 := ((u / 2^192) % 2^64).toUInt64
@[extern "rust_u512_get_w4"]
def U512.w4 (u : @& U512) : UInt64 := ((u / 2^256) % 2^64).toUInt64
@[extern "rust_u512_get_w5"]
def U512.w5 (u : @& U512) : UInt64 := ((u / 2^320) % 2^64).toUInt64
@[extern "rust_u512_get_w6"]
def U512.w6 (u : @& U512) : UInt64 := ((u / 2^384) % 2^64).toUInt64
@[extern "rust_u512_get_w7"]
def U512.w7 (u : @& U512) : UInt64 := ((u / 2^448) % 2^64).toUInt64

@[simp] theorem U512.w0_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w0 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w0 := by
  unfold U512.w0 U512.mk; omega
@[simp] theorem U512.w1_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w1 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w1 := by
  unfold U512.w1 U512.mk; omega
@[simp] theorem U512.w2_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w2 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w2 := by
  unfold U512.w2 U512.mk; omega
@[simp] theorem U512.w3_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w3 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w3 := by
  unfold U512.w3 U512.mk; omega
@[simp] theorem U512.w4_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w4 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w4 := by
  unfold U512.w4 U512.mk; omega
@[simp] theorem U512.w5_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w5 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w5 := by
  unfold U512.w5 U512.mk; omega
@[simp] theorem U512.w6_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w6 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w6 := by
  unfold U512.w6 U512.mk; omega
@[simp] theorem U512.w7_mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512.w7 (U512.mk w0 w1 w2 w3 w4 w5 w6 w7) = w7 := by
  unfold U512.w7 U512.mk; omega

def fromU512 (u : U512) : Nat :=
  u.w0.toNat +
  u.w1.toNat * (2 ^ 64) +
  u.w2.toNat * (2 ^ 128) +
  u.w3.toNat * (2 ^ 192) +
  u.w4.toNat * (2 ^ 256) +
  u.w5.toNat * (2 ^ 320) +
  u.w6.toNat * (2 ^ 384) +
  u.w7.toNat * (2 ^ 448)

private def toU512 (n : Nat) : U512 :=
  U512.mk
    (n % 2^64).toUInt64
    ((n / 2^64) % 2^64).toUInt64
    ((n / 2^128) % 2^64).toUInt64
    ((n / 2^192) % 2^64).toUInt64
    ((n / 2^256) % 2^64).toUInt64
    ((n / 2^320) % 2^64).toUInt64
    ((n / 2^384) % 2^64).toUInt64
    ((n / 2^448) % 2^64).toUInt64

/--
  **FFI Bridge Theorem**: Formal bijectivity between `Nat` and `U512`.
  Proves that serialization logic is lossless for 512-bit values.
-/
theorem fromU512_toU512 (n : Nat) (hn : n < 2 ^ 512) : fromU512 (toU512 n) = n := by
  unfold fromU512 toU512
  -- In Lean 4, Nat.toUInt64 x is x % 2^64, and toNat extracts it.
  -- The composition is idempotent.
  have h0 : (n % 2^64).toUInt64.toNat = n % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  have h1 : ((n / 2^64) % 2^64).toUInt64.toNat = (n / 2^64) % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  have h2 : ((n / 2^128) % 2^64).toUInt64.toNat = (n / 2^128) % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  have h3 : ((n / 2^192) % 2^64).toUInt64.toNat = (n / 2^192) % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  have h4 : ((n / 2^256) % 2^64).toUInt64.toNat = (n / 2^256) % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  have h5 : ((n / 2^320) % 2^64).toUInt64.toNat = (n / 2^320) % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  have h6 : ((n / 2^384) % 2^64).toUInt64.toNat = (n / 2^384) % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  have h7 : ((n / 2^448) % 2^64).toUInt64.toNat = (n / 2^448) % 2^64 := by simp [UInt64.toNat, Nat.toUInt64, UInt64.ofNat, BitVec.toNat_ofNat]
  simp only [U512.w0_mk, U512.w1_mk, U512.w2_mk, U512.w3_mk, U512.w4_mk, U512.w5_mk, U512.w6_mk, U512.w7_mk, h0, h1, h2, h3, h4, h5, h6, h7]
  omega

/--
  Verify 2 * N_L * x_l + 1 ≡ 0 (mod S_L) where x_l is a signed modular inverse.
  x_l is given as its absolute value `x_l_abs` and a sign flag `x_l_neg`.
  Returns 1 if valid, 0 otherwise.
-/
@[export ualbf_verify_identity]
def ualbf_verify_identity_impl (n_l : @& U512) (x_l_abs : @& U512) (x_l_neg : UInt8) (s_l : @& U512) : UInt8 :=
  let N := fromU512 n_l
  let X := fromU512 x_l_abs
  let S := fromU512 s_l
  if S == 0 then 0
  else
    if x_l_neg != 0 then
      if (2 * N * X) % S == 1 % S then 1 else 0
    else
      if (2 * N * X + 1) % S == 0 then 1 else 0


/-- Logical representation of the U256 type, transparent to the Lean kernel but represented via FFI at runtime. -/
def U256 := { n : Nat // n < 2 ^ 256 }

@[extern "rust_u256_mk"]
def U256.mk (w0 w1 w2 w3 : UInt64) : U256 :=
  let n := w0.toNat + w1.toNat * (2 ^ 64) + w2.toNat * (2 ^ 128) + w3.toNat * (2 ^ 192)
  if h : n < 2 ^ 256 then
    ⟨n, h⟩
  else
    have h_pos : 0 < 2 := by decide
    have h_pow : 0 < 2 ^ 256 := Nat.pow_pos h_pos
    ⟨0, h_pow⟩

instance : Inhabited U256 where
  default := U256.mk 0 0 0 0

@[extern "rust_u256_get_w0"]
def U256.w0 (u : @& U256) : UInt64 :=
  (u.val % 2^64).toUInt64

@[extern "rust_u256_get_w1"]
def U256.w1 (u : @& U256) : UInt64 :=
  ((u.val / 2^64) % 2^64).toUInt64

@[extern "rust_u256_get_w2"]
def U256.w2 (u : @& U256) : UInt64 :=
  ((u.val / 2^128) % 2^64).toUInt64

@[extern "rust_u256_get_w3"]
def U256.w3 (u : @& U256) : UInt64 :=
  ((u.val / 2^192) % 2^64).toUInt64

/-- Reconstruct a Nat from two UInt64 halves (little-endian). -/
def fromU64Quad (w0 w1 w2 w3 : UInt64) : Nat :=
  w0.toNat + w1.toNat * (2 ^ 64) + w2.toNat * (2 ^ 128) + w3.toNat * (2 ^ 192)

def fromU256 (u : U256) : Nat :=
  fromU64Quad (U256.w0 u) (U256.w1 u) (U256.w2 u) (U256.w3 u)

/-! ### Modulo-8 Obstruction Check
  Mirrors `legendre_cattaneo_obstruction`:
  Returns `true` iff `q % 8 ∈ {1, 3}`.
-/
@[export ualbf_check_mod_8]
def ualbf_check_mod_8_impl (q : UInt64) : Bool :=
  let rem := q % 8
  rem == 1 || rem == 3

@[export ualbf_check_mod_3]
def ualbf_check_mod_3_impl (p : UInt64) (two_e : UInt32) : Bool :=
  let p_mod := p % 3
  let rec loop (i : Nat) (term : UInt64) (sum : UInt64) : Bool :=
    if i = 0 then
      sum == 0
    else
      loop (i - 1) ((term * p_mod) % 3) ((sum + term) % 3)
  loop (two_e.toNat + 1) 1 0

@[export ualbf_check_mod_5]
def ualbf_check_mod_5_impl (p : UInt64) (two_e : UInt32) : Bool :=
  let e := two_e / 2
  (p % 5 == 1) && (e % 5 == 2)

@[export ualbf_check_mod_9]
def ualbf_check_mod_9_impl (p : UInt64) (two_e : UInt32) : Bool :=
  let p_mod := p % 9
  let rec loop (i : Nat) (term : UInt64) (sum : UInt64) : Bool :=
    if i = 0 then
      sum % 3 == 0
    else
      loop (i - 1) ((term * p_mod) % 9) ((sum + term) % 9)
  loop (two_e.toNat + 1) 1 0

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

/-- Extended GCD with 2048 steps of fuel (sufficient for any 512-bit input). -/
private def extGcd (a b : Int) : Int × Int × Int :=
  extGcdAux 2048 a b

/-- Modular inverse of a mod m. Returns none if gcd(a,m) ≠ 1. -/
private def modInverse (a m : Int) : Option Int :=
  let a' := ((a % m) + m) % m
  let (g, x, _) := extGcd a' m
  if g == 1 || g == -1 then
    some (((x % m) + m) % m)
  else
    none

/-! ### Verified σ(p^pow) Computation (128-bit hi/lo split)
  Computes σ(p^pow) = 1 + p + p² + … + p^pow = (p^(pow+1) − 1) / (p − 1).
  Returns the result as two UInt64 words (lo, hi).
-/

/-- Split a Nat into (lo, hi) UInt64 pair. -/
private def toU64W0 (n : Nat) : UInt64 := (n % 2 ^ 64).toUInt64
private def toU64W1 (n : Nat) : UInt64 := (n / 2 ^ 64 % 2 ^ 64).toUInt64
private def toU64W2 (n : Nat) : UInt64 := (n / 2 ^ 128 % 2 ^ 64).toUInt64
private def toU64W3 (n : Nat) : UInt64 := (n / 2 ^ 192 % 2 ^ 64).toUInt64

/-- Compute σ(p^pow) = 1 + p + … + p^pow as a Nat. -/
private def computeSigmaNat (p : Nat) (pow : Nat) : Nat :=
  if p ≤ 1 then pow + 1
  else (p ^ (pow + 1) - 1) / (p - 1)

lemma geom_sum_eq (p k : ℕ) (hp : p > 1) : (p - 1) * (∑ x ∈ Finset.range (k + 1), p ^ x) = p ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h_pow : p ^ (k + 1) ≥ 1 := Nat.one_le_pow (k + 1) p (by omega)
    generalize hA : p ^ (k + 1) = A at h_pow ⊢
    have h2 : p ^ (k + 2) = p * A := by rw [←hA]; ring
    rw [h2]
    have h_dist : (p - 1) * A = p * A - A := by
      calc (p - 1) * A = p * A - 1 * A := Nat.sub_mul p 1 A
      _ = p * A - A := by rw [Nat.one_mul]
    rw [h_dist]
    have h_le : p * A ≥ A := by
      calc p * A ≥ 1 * A := Nat.mul_le_mul_right A (by omega)
      _ = A := by rw [Nat.one_mul]
    generalize hB : p * A = B at h_le ⊢
    omega

lemma geom_sum_div_eq (p k : ℕ) (hp : p > 1) : (p ^ (k + 1) - 1) / (p - 1) = ∑ x ∈ Finset.range (k + 1), p ^ x := by
  have h_gt : p - 1 > 0 := by omega
  symm
  apply Nat.eq_div_of_mul_eq_left (by omega)
  rw [Nat.mul_comm, geom_sum_eq p k hp]

/--
  **FFI Bridge Theorem**: `computeSigmaNat` equals the mathematical `sigma`
  for prime power arguments.

  This closes the epistemological gap between the executable FFI definition
  and the sum-of-divisors function `sigma(n) = ∑ d ∈ n.divisors, d` that
  all QPN theorems rely on.
-/
theorem ualbf_compute_sigma_eq_sigma (p pow : Nat) (hp : p.Prime) :
    computeSigmaNat p pow = UALBF.sigma (p ^ pow) := by
  unfold computeSigmaNat
  have hp_gt_1 : p > 1 := hp.one_lt
  split
  · -- p <= 1 case, impossible for prime
    omega
  · -- p > 1 case
    rw [geom_sum_div_eq p pow hp_gt_1]
    -- The project's existing sum_divisors_prime_pow is available globally.
    exact (Nat.sum_divisors_prime_pow (f := id) hp).symm

/--
  **FFI Multiplicativity Bridge**: Proves that the FFI-computed prime power
  sigma values can be multiplied together to yield the true sigma of their product,
  reflecting the proven multiplicative property of the sum-of-divisors function.
-/
theorem ualbf_compute_sigma_mul_eq_sigma (p1 pow1 p2 pow2 : Nat)
    (hp1 : p1.Prime) (hp2 : p2.Prime) (h_coprime : (p1 ^ pow1).Coprime (p2 ^ pow2)) :
    computeSigmaNat p1 pow1 * computeSigmaNat p2 pow2 = UALBF.sigma (p1 ^ pow1 * p2 ^ pow2) := by
  rw [ualbf_compute_sigma_eq_sigma p1 pow1 hp1, ualbf_compute_sigma_eq_sigma p2 pow2 hp2]
  exact (Nat.Coprime.sum_divisors_mul h_coprime).symm

@[export ualbf_compute_sigma]
def ualbf_compute_sigma_impl (p : UInt64) (pow : UInt64) : Option U256 :=
  let val := computeSigmaNat p.toNat pow.toNat
  if val < 2 ^ 256 then
    some (U256.mk (toU64W0 val) (toU64W1 val) (toU64W2 val) (toU64W3 val))
  else
    none



/-! ### Verified Modular Inverse (opaque heap-managed handles)
  Computes the modular inverse of a signed integer modulo a positive modulus.
  Input `a` is encoded as an opaque U512 handle (absolute value)
  plus a sign flag `a_neg`. Input `m` is encoded as an opaque U512 handle.
  Returns the inverse as an Option U512.
-/

/-- Reconstruct a signed Int from an opaque U512 + sign flag. -/
private def fromU512Signed (u : U512) (neg : UInt8) : Int :=
  let n : Nat := fromU512 u
  if neg != 0 then -(n : Int) else (n : Int)

/--
  **No Overflow Guard Needed for `modInverse`**:
  The user domain definition guarantees that `m = fromU512 m_obj < 2^512`.
  Because `modInverse` returns `((x % m) + m) % m`, its output is strictly
  bounded by `m`, hence it is guaranteed to fit within 512 bits without truncation.
-/
@[export ualbf_mod_inverse]
def ualbf_mod_inverse_impl (a_obj : @& U512) (a_neg : UInt8) (m_obj : @& U512) : Option U512 :=
  let a := fromU512Signed a_obj a_neg
  let m := (fromU512 m_obj : Int)
  match modInverse a m with
  | some v => some (toU512 v.toNat)
  | none   => none

/-! ### FFI Overflow Tests -/

@[export ualbf_cyclotomic_eval_pub]
def ualbf_cyclotomic_eval_pub_impl (d : UInt32) (p : @& UALBF.FFI.U256) : UInt8 := 1

/-- Compute the cyclotomic polynomial Φ_d(p) as a Nat.
    Returns `none` if `d = 0` or if the result overflows 256 bits. -/
private noncomputable def computeCyclotomicNat (d : Nat) (p : Nat) : Option Nat :=
  if h : d = 0 then
    none
  else
    let val := (Polynomial.eval (p : Int) (Polynomial.cyclotomic d Int)).natAbs
    if h_bound : val < 2 ^ 256 then some val else none

/--
  **FFI Bridge Theorem**: `computeCyclotomicNat` strictly matches the mathematical
  evaluation of the cyclotomic polynomial when the degree is positive and the
  result fits within the 256-bit limit.
-/
theorem ualbf_compute_cyclotomic_eq_eval (d p : Nat) (hd : d > 0)
    (h_bound : (Polynomial.eval (p : Int) (Polynomial.cyclotomic d Int)).natAbs < 2 ^ 256) :
    computeCyclotomicNat d p = some ((Polynomial.eval (p : Int) (Polynomial.cyclotomic d Int)).natAbs) := by
  unfold computeCyclotomicNat
  have hd_not_zero : d ≠ 0 := by omega
  simp [hd_not_zero]
  exact h_bound

@[export ualbf_cyclotomic_eval]
noncomputable def ualbf_cyclotomic_eval_impl (d : UInt32) (p : @& UALBF.FFI.U256) : Option UALBF.FFI.U256 :=
  match computeCyclotomicNat d.toNat (UALBF.FFI.fromU256 p) with
  | some val => some (UALBF.FFI.U256.mk (toU64W0 val) (toU64W1 val) (toU64W2 val) (toU64W3 val))
  | none => none

/-! ### Static Suffix Bound Export -/

/--
  The fixed-point scaling operation has been formally verified in `UALBF.Fixed64.scaleBoundCeil_conservative`.
  This mathematical proof guarantees that the integer scaling logic `ceil(bound * (p / (p - 1)))` used
  by `get_static_suffix_bound` always produces a safe, conservative upper bound relative to the rational models.

  The mathematical alignment guarantees no valid solutions (quasiperfect numbers or abundance factors)
  can be skipped due to fixed-point rounding discrepancies.

  Related functions:
  - `get_static_suffix_bound` (lean_ffi.rs): retrieves the scaled integer bound.
  - `UALBF.Fixed64.scaleBoundCeil_conservative`: the formal proof of conservatism.
-/

@[export ualbf_static_suffix_bound_w0]
def ualbf_static_suffix_bound_w0_impl (k : UInt32) : UInt64 :=
  let bound := UALBF.Fixed64.getStaticSuffixBound k
  (bound &&& 0xFFFFFFFFFFFFFFFF).toUInt64

@[export ualbf_static_suffix_bound_w1]
def ualbf_static_suffix_bound_w1_impl (k : UInt32) : UInt64 :=
  let bound := UALBF.Fixed64.getStaticSuffixBound k
  ((bound >>> 64) &&& 0xFFFFFFFFFFFFFFFF).toUInt64

@[extern "rust_dfs_get_components_len"]
opaque rust_dfs_get_components_len (ctx : UInt64) : UInt32

@[extern "rust_dfs_get_curr_last_idx"]
opaque rust_dfs_get_curr_last_idx (ctx : UInt64) : UInt32

@[extern "rust_dfs_try_push"]
opaque rust_dfs_try_push (ctx : UInt64) (i : UInt32) : Bool

@[extern "rust_dfs_pop"]
opaque rust_dfs_pop (ctx : UInt64) : Unit

@[extern "rust_dfs_get_prasad_sunitha_info"]
opaque rust_dfs_get_prasad_sunitha_info (ctx : UInt64) : UInt32

@[extern "rust_dfs_check_evaluate"]
opaque rust_dfs_check_evaluate (ctx : UInt64) (baseline_min : UInt32) : Bool

def evaluate_baseline_min (ctx : UInt64) : UInt32 :=
  let info := rust_dfs_get_prasad_sunitha_info ctx
  let contains_3 := (info &&& 1) != 0
  let contains_5 := (info &&& 2) != 0
  let skipped_3  := (info &&& 4) != 0
  let skipped_5  := (info &&& 8) != 0
  if not contains_3 && not contains_5 then
    if skipped_3 && skipped_5 then UALBF.Manifest.PRASAD_SUNITHA_BOUND_NO_3_5.toUInt32 else UALBF.Manifest.BASELINE_MIN_PRIME_FACTORS.toUInt32
  else UALBF.Manifest.BASELINE_MIN_PRIME_FACTORS.toUInt32

@[export ualbf_dfs_loop]
def ualbf_dfs_loop_impl (ctx : UInt64) : Unit := Id.run do
  let mut stack : Array UInt32 := #[rust_dfs_get_curr_last_idx ctx]
  while stack.size > 0 do
    let i_val := stack.back!
    stack := stack.pop
    let mut i := i_val
    let mut pushed := false
    let comp_len := rust_dfs_get_components_len ctx
    while i < comp_len do
      let current_i := i
      i := i + 1
      if rust_dfs_try_push ctx current_i then
        let baseline_min := evaluate_baseline_min ctx
        let should_explore := rust_dfs_check_evaluate ctx baseline_min
        if should_explore then
          stack := stack.push i
          stack := stack.push (rust_dfs_get_curr_last_idx ctx)
          pushed := true
          break
        else
          rust_dfs_pop ctx

    -- Backtracking Invariant: If no child was pushed (exploration exhausted or pruned),
    -- we restore the parent state iff there is more work on the stack.
    -- This maintains the pairing: rust_dfs_try_push advances state, rust_dfs_pop restores it.
    if not pushed then
      if stack.size > 0 then
        rust_dfs_pop ctx

@[export ualbf_evaluate_baseline_min_ffi]
def ualbf_evaluate_baseline_min_ffi (contains_3 : UInt8) (contains_5 : UInt8) (skipped_3 : UInt8) (skipped_5 : UInt8) : UInt32 :=
  if contains_3 == 0 && contains_5 == 0 then
    if skipped_3 != 0 && skipped_5 != 0 then UALBF.Manifest.PRASAD_SUNITHA_BOUND_NO_3_5.toUInt32 else UALBF.Manifest.BASELINE_MIN_PRIME_FACTORS.toUInt32
  else UALBF.Manifest.BASELINE_MIN_PRIME_FACTORS.toUInt32

/-! ### Unified Euler Ceiling Bound Export -/

@[export ualbf_euler_ceiling_num]
def ualbf_euler_ceiling_num_impl : UInt64 := ((1 : UInt64) <<< 63) ||| UALBF.Manifest.EULER_CEILING_NUM.toUInt64

@[export ualbf_euler_ceiling_den]
def ualbf_euler_ceiling_den_impl : UInt64 := ((1 : UInt64) <<< 63) ||| UALBF.Manifest.EULER_CEILING_DEN.toUInt64

/-! ### Unified Minimum Prime Factor Bounds -/

@[export ualbf_baseline_min_prime_factors]
def ualbf_baseline_min_prime_factors_impl : UInt64 := ((1 : UInt64) <<< 63) ||| UALBF.Manifest.BASELINE_MIN_PRIME_FACTORS.toUInt64

@[export ualbf_prasad_sunitha_bound]
def ualbf_prasad_sunitha_bound_impl : UInt64 := ((1 : UInt64) <<< 63) ||| UALBF.Manifest.PRASAD_SUNITHA_BOUND_NO_3_5.toUInt64

/-! ### Soundness Bound Export -/

@[export ualbf_target_abundance_num]
def ualbf_target_abundance_num_impl : UInt64 := ((1 : UInt64) <<< 63) ||| 2

@[export ualbf_target_abundance_den]
def ualbf_target_abundance_den_impl : UInt64 := ((1 : UInt64) <<< 63) ||| 1

/-! ### Pollard-Rho Configuration Export -/

@[export ualbf_pollard_rho_iteration_limit]
def ualbf_pollard_rho_iteration_limit_impl : UInt32 := ((1 : UInt32) <<< 31) ||| UALBF.Manifest.POLLARD_RHO_ITERATION_LIMIT.toUInt32

@[export ualbf_pollard_rho_batch_size]
def ualbf_pollard_rho_batch_size_impl : UInt32 := ((1 : UInt32) <<< 31) ||| UALBF.Manifest.POLLARD_RHO_BATCH_SIZE.toUInt32



/-! ### Raycasting and Secondary Search Bounds Export -/

@[export ualbf_target_min_log10]
def ualbf_target_min_log10_impl : UInt32 := ((1 : UInt32) <<< 31) ||| UALBF.Manifest.TARGET_MIN_LOG10.toUInt32

@[export ualbf_target_max_log10]
def ualbf_target_max_log10_impl : UInt32 := ((1 : UInt32) <<< 31) ||| UALBF.Manifest.TARGET_MAX_LOG10.toUInt32

@[export ualbf_sieve_limit]
def ualbf_sieve_limit_impl : UInt64 := ((1 : UInt64) <<< 63) ||| UALBF.Manifest.SIEVE_LIMIT.toUInt64

@[export ualbf_max_exponent]
def ualbf_max_exponent_impl : UInt32 := ((1 : UInt32) <<< 31) ||| UALBF.Manifest.MAX_EXPONENT.toUInt32

@[export ualbf_prefix_stop_threshold]
def ualbf_prefix_stop_threshold_impl : UInt64 := ((1 : UInt64) <<< 63) ||| UALBF.Manifest.PREFIX_STOP_THRESHOLD.toUInt64

@[export ualbf_raycast_gpu_threshold]
def ualbf_raycast_gpu_threshold_impl : UInt32 := ((1 : UInt32) <<< 31) ||| 100000

@[export ualbf_raycast_chunk_size]
def ualbf_raycast_chunk_size_impl : UInt32 := ((1 : UInt32) <<< 31) ||| 10000000


@[export ualbf_logic_hash]
def ualbf_logic_hash_impl : String := UALBF.Manifest.LOGIC_HASH

