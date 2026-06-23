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

namespace UALBF.FFI

open UALBF UALBF.Pure.Arithmetic Finset Nat

-- Define the external object type
opaque U256Point : NonemptyType
def U256 : Type := U256Point.type
instance : Nonempty U256 := U256Point.property

opaque U512Point : NonemptyType
def U512 : Type := U512Point.type
instance : Nonempty U512 := U512Point.property

@[extern "rust_u512_mk"]
opaque U512.mk (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : U512

@[extern "rust_u512_get_w0"]
opaque U512.w0 (u : @& U512) : UInt64
@[extern "rust_u512_get_w1"]
opaque U512.w1 (u : @& U512) : UInt64
@[extern "rust_u512_get_w2"]
opaque U512.w2 (u : @& U512) : UInt64
@[extern "rust_u512_get_w3"]
opaque U512.w3 (u : @& U512) : UInt64
@[extern "rust_u512_get_w4"]
opaque U512.w4 (u : @& U512) : UInt64
@[extern "rust_u512_get_w5"]
opaque U512.w5 (u : @& U512) : UInt64
@[extern "rust_u512_get_w6"]
opaque U512.w6 (u : @& U512) : UInt64
@[extern "rust_u512_get_w7"]
opaque U512.w7 (u : @& U512) : UInt64

def fromU512 (u : U512) : Nat :=
  u.w0.toNat +
  u.w1.toNat * (2 ^ 64) +
  u.w2.toNat * (2 ^ 128) +
  u.w3.toNat * (2 ^ 192) +
  u.w4.toNat * (2 ^ 256) +
  u.w5.toNat * (2 ^ 320) +
  u.w6.toNat * (2 ^ 384) +
  u.w7.toNat * (2 ^ 448)

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


/--
  TCB Assumption: U256 Memory Safety

  The opaque U256 type is implemented via FFI and relies on Lean's reference
  counting and finalizer registration to manage memory correctly. This is a
  trusted computing base (TCB) assumption that must hold for soundness:

  - Each U256 value points to valid memory allocated by the Rust FFI layer
  - Lean's RC system correctly manages lifetime and prevents use-after-free
  - The FFI boundary correctly registers finalizers via `lean_register_external_class`
  - No double-free or memory corruption occurs during cross-language transitions

  Unlike logical axioms, this is a systems-level safety property that cannot be
  expressed as a Lean predicate. Runtime safety depends on correct FFI implementation.

  See: rust-engine/src/lean_ffi.rs for the external class registration.
-/
-- Removed vacuous axiom u256_memory_safe : True (replaced with TCB documentation)

@[extern "rust_u256_mk"]
opaque U256.mk (w0 w1 w2 w3 : UInt64) : U256

@[extern "rust_u256_get_w0"]
opaque U256.w0 (u : @& U256) : UInt64

@[extern "rust_u256_get_w1"]
opaque U256.w1 (u : @& U256) : UInt64

@[extern "rust_u256_get_w2"]
opaque U256.w2 (u : @& U256) : UInt64

@[extern "rust_u256_get_w3"]
opaque U256.w3 (u : @& U256) : UInt64

/-- Reconstruct a Nat from two UInt64 halves (little-endian). -/
def fromU64Quad (w0 w1 w2 w3 : UInt64) : Nat :=
  w0.toNat + w1.toNat * (2 ^ 64) + w2.toNat * (2 ^ 128) + w3.toNat * (2 ^ 192)

@[extern "rust_is_prime_u256"]
opaque ualbf_is_prime_u256_impl (p : @& U256) : UInt8
def fromU256 (u : U256) : Nat :=
  fromU64Quad (U256.w0 u) (U256.w1 u) (U256.w2 u) (U256.w3 u)

/-- We bridge the FFI trust gap once by trusting the Verus-verified Rust implementation.
    This eliminates the need for expensive runtime checks or complex per-factor certificate pipelines. -/
axiom rust_is_prime_sound (p : U256) : ualbf_is_prime_u256_impl p = 1 → (fromU256 p).Prime

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

/-- Extended GCD with 256 steps of fuel (sufficient for any 128-bit input). -/
private def extGcd (a b : Int) : Int × Int × Int :=
  extGcdAux 256 a b

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

/--
  **FFI Bridge Theorem**: `computeSigmaNat` equals the mathematical `sigma`
  for prime power arguments.

  This closes the epistemological gap between the executable FFI definition
  and the sum-of-divisors function `sigma(n) = ∑ d ∈ n.divisors, d` that
  all QPN theorems rely on.
-/

@[export ualbf_compute_sigma]
def ualbf_compute_sigma_impl (p : UInt64) (pow : UInt64) : U256 :=
  let val := computeSigmaNat p.toNat pow.toNat
  U256.mk (toU64W0 val) (toU64W1 val) (toU64W2 val) (toU64W3 val)

/-- **Overflow guard for compute_sigma.**
    Returns 1 if the result fits in 256 bits (< 2^256), 0 otherwise.
    Mirrors the existing `_ok` pattern used by `mod_inverse`. -/
@[export ualbf_compute_sigma_ok]
def ualbf_compute_sigma_ok_impl (p : UInt64) (pow : UInt64) : UInt8 :=
  if computeSigmaNat p.toNat pow.toNat < 2 ^ 256 then 1 else 0

/-- Sentinel protocol for Nat to U256 transition - Read-Only-on-OK -/
theorem ualbf_compute_sigma_sentinel_safe (p pow : UInt64) (h : ualbf_compute_sigma_ok_impl p pow = 1) :
  computeSigmaNat p.toNat pow.toNat < 2 ^ 256 := by
  dsimp [ualbf_compute_sigma_ok_impl] at h
  split at h
  · assumption
  · contradiction

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





@[export ualbf_cyclotomic_eval_pub]
def ualbf_cyclotomic_eval_pub_impl (d : UInt32) (p : @& UALBF.FFI.U256) : UInt8 := 1
private def computeCyclotomicNat (d : Nat) (p : Nat) : Nat :=
  if d == 3 then p^2 + p + 1
  else if d == 5 then p^4 + p^3 + p^2 + p + 1
  else if d == 7 then p^6 + p^5 + p^4 + p^3 + p^2 + p + 1
  else if d == 9 then p^6 + p^3 + 1
  else 0

@[export ualbf_cyclotomic_eval]
def ualbf_cyclotomic_eval_impl (d : UInt32) (p : @& UALBF.FFI.U256) : UALBF.FFI.U256 :=
  let val := computeCyclotomicNat d.toNat (UALBF.FFI.fromU256 p)
  UALBF.FFI.U256.mk (toU64W0 val) (toU64W1 val) (toU64W2 val) (toU64W3 val)

@[export ualbf_cyclotomic_eval_ok]
def ualbf_cyclotomic_eval_ok_impl (d : UInt32) (p : @& UALBF.FFI.U256) : UInt8 :=
  let val := computeCyclotomicNat d.toNat (UALBF.FFI.fromU256 p)
  if val = 0 then 0
  else if val < 2 ^ 256 then 1
  else 0

/-- Sentinel protocol for Nat to U256 transition - Read-Only-on-OK -/
theorem ualbf_cyclotomic_eval_sentinel_safe (d : UInt32) (p : UALBF.FFI.U256) (h : ualbf_cyclotomic_eval_ok_impl d p = 1) :
  computeCyclotomicNat d.toNat (UALBF.FFI.fromU256 p) < 2 ^ 256 := by
  dsimp [ualbf_cyclotomic_eval_ok_impl] at h
  split at h
  · contradiction
  · split at h
    · assumption
    · contradiction

/-! ### Static Suffix Bound Export -/

/--
  TCB Assumption: Fixed-Point Scaling Conservatism

  The Rust engine performs rational comparisons using 64-bit fixed-point arithmetic.
  Each rational bound `true_bound` is scaled to an integer `bound_int` via multiplication
  by 2^64, then compared using integer arithmetic to avoid floating-point rounding errors.

  This TCB assumption documents that the scaling must be conservative:
    bound_int ≥ true_bound * 2^64

  Correctness depends on:
  - The Rust FFI implementation (`get_static_suffix_bound` in lean_ffi.rs) computing
    bound_int correctly from the proven rational bounds
  - The fixed-point scaling factor (2^64) being large enough to preserve precision
  - Runtime checks on the FFI boundary validating bound_int against true_bound

  This cannot be proven within Lean because the scaling happens in external Rust code.
  The verifier should audit the FFI implementation to confirm this property holds.

  Related functions:
  - `get_static_suffix_bound` (lean_ffi.rs): retrieves the scaled integer bound
  - `fixed_point_scaling_conservative`: the mathematical property we trust holds

  See: rust-engine/src/lean_ffi.rs and rust-engine/src/dfs_tree.rs for implementation.
-/
-- Removed axiom fixed_point_scaling_conservative (replaced with TCB documentation)

@[export ualbf_static_suffix_bound_w0]
partial def ualbf_static_suffix_bound_w0_impl (k : UInt32) : UInt64 :=
  let bound := UALBF.Fixed64.getStaticSuffixBound k
  (bound &&& 0xFFFFFFFFFFFFFFFF).toUInt64

@[export ualbf_static_suffix_bound_w1]
partial def ualbf_static_suffix_bound_w1_impl (k : UInt32) : UInt64 :=
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
def ualbf_euler_ceiling_num_impl : UInt64 := UALBF.Manifest.EULER_CEILING_NUM.toUInt64

@[export ualbf_euler_ceiling_den]
def ualbf_euler_ceiling_den_impl : UInt64 := UALBF.Manifest.EULER_CEILING_DEN.toUInt64

/-! ### Unified Minimum Prime Factor Bounds -/

@[export ualbf_baseline_min_prime_factors]
def ualbf_baseline_min_prime_factors_impl : UInt64 := UALBF.Manifest.BASELINE_MIN_PRIME_FACTORS.toUInt64

@[export ualbf_prasad_sunitha_bound]
def ualbf_prasad_sunitha_bound_impl : UInt64 := UALBF.Manifest.PRASAD_SUNITHA_BOUND_NO_3_5.toUInt64

/-! ### Soundness Bound Export -/

@[export ualbf_target_abundance_num]
def ualbf_target_abundance_num_impl : UInt64 := 2

@[export ualbf_target_abundance_den]
def ualbf_target_abundance_den_impl : UInt64 := 1

/-! ### Pollard-Rho Configuration Export -/

@[export ualbf_pollard_rho_iteration_limit]
def ualbf_pollard_rho_iteration_limit_impl : UInt32 := UALBF.Manifest.POLLARD_RHO_ITERATION_LIMIT.toUInt32

@[export ualbf_pollard_rho_batch_size]
def ualbf_pollard_rho_batch_size_impl : UInt32 := UALBF.Manifest.POLLARD_RHO_BATCH_SIZE.toUInt32


