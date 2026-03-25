/-
  UALBF/FFI.lean — Computational wrappers for C-linkage export.

  Lean 4 erases `theorem` (Prop) at runtime, so we write executable `def`s
  that mirror the proven theorems and tag them with `@[export]`.
  These are compiled into the static library and called from the Rust engine
  via C-FFI.
-/
import UALBF.Obstruction
import UALBF.Bipartition

namespace UALBF.FFI

/-! ### 1. Modulo-8 Obstruction Check
  Mirrors `legendre_cattaneo_obstruction`:
  Returns true iff `q % 8 ∈ {1, 3}`.
-/
@[export ualbf_check_mod_8]
def ualbf_check_mod_8_impl (q : UInt64) : Bool :=
  let rem := q % 8
  rem == 1 || rem == 3

/-! ### 2. AMBS Suffix Target
  Mirrors `ambs_suffix_target`:
  Computes `mod_inverse(-2 * n_l, s_l)` using the extended Euclidean algorithm.
  Returns the modular inverse as UInt64, or 0 if it does not exist
  (which should never happen when n_l and s_l satisfy the coprimality invariant).
-/

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

@[export ualbf_ambs_target]
def ualbf_ambs_target_impl (n_l : UInt64) (s_l : UInt64) : UInt64 :=
  let n_l_int : Int := n_l.toNat
  let s_l_int : Int := s_l.toNat
  let neg_two_n_l := ((-2) * n_l_int) % s_l_int
  match modInverse neg_two_n_l s_l_int with
  | some v => (v % s_l_int).toNat.toUInt64
  | none   => 0

/-! ### 3. Verified compute_sigma (128-bit result via hi/lo split)
  σ(p^pow) = 1 + p + p² + … + p^pow = (p^(pow+1) - 1) / (p - 1)
  Returns the result as two UInt64 words (lo, hi).
-/

/-- Reconstruct a Nat from two UInt64 halves (little-endian). -/
private def fromU64Pair (lo hi : UInt64) : Nat :=
  lo.toNat + hi.toNat * (2 ^ 64)

/-- Split a Nat into (lo, hi) UInt64 pair. -/
private def toU64Lo (n : Nat) : UInt64 := (n % 2 ^ 64).toUInt64
private def toU64Hi (n : Nat) : UInt64 := (n / 2 ^ 64 % 2 ^ 64).toUInt64

/-- Compute σ(p^pow) = 1 + p + … + p^pow as a Nat. -/
private def computeSigmaNat (p : Nat) (pow : Nat) : Nat :=
  if p ≤ 1 then pow + 1
  else (p ^ (pow + 1) - 1) / (p - 1)

@[export ualbf_compute_sigma_lo]
def ualbf_compute_sigma_lo_impl (p : UInt64) (pow : UInt64) : UInt64 :=
  toU64Lo (computeSigmaNat p.toNat pow.toNat)

@[export ualbf_compute_sigma_hi]
def ualbf_compute_sigma_hi_impl (p : UInt64) (pow : UInt64) : UInt64 :=
  toU64Hi (computeSigmaNat p.toNat pow.toNat)

/-! ### 4. Verified mod_inverse for 128-bit values (hi/lo split)
  Modular inverse of a signed 128-bit integer mod a positive 128-bit modulus.
  Input `a` is encoded as |a| in (a_lo, a_hi) plus a sign flag a_neg.
  Input `m` is encoded as (m_lo, m_hi), always positive.
  Returns inverse via _lo/_hi and existence via _ok.
-/

/-- Reconstruct a signed Int from hi/lo + sign flag. -/
private def fromU64PairSigned (lo hi : UInt64) (neg : UInt64) : Int :=
  let n : Nat := fromU64Pair lo hi
  if neg.toNat != 0 then -(n : Int) else (n : Int)

@[export ualbf_mod_inverse_lo]
def ualbf_mod_inverse_lo_impl (a_lo a_hi a_neg m_lo m_hi : UInt64) : UInt64 :=
  let a := fromU64PairSigned a_lo a_hi a_neg
  let m := (fromU64Pair m_lo m_hi : Int)
  match modInverse a m with
  | some v => toU64Lo v.toNat
  | none   => 0

@[export ualbf_mod_inverse_hi]
def ualbf_mod_inverse_hi_impl (a_lo a_hi a_neg m_lo m_hi : UInt64) : UInt64 :=
  let a := fromU64PairSigned a_lo a_hi a_neg
  let m := (fromU64Pair m_lo m_hi : Int)
  match modInverse a m with
  | some v => toU64Hi v.toNat
  | none   => 0

@[export ualbf_mod_inverse_ok]
def ualbf_mod_inverse_ok_impl (a_lo a_hi a_neg m_lo m_hi : UInt64) : UInt8 :=
  let a := fromU64PairSigned a_lo a_hi a_neg
  let m := (fromU64Pair m_lo m_hi : Int)
  match modInverse a m with
  | some _ => 1
  | none   => 0

end UALBF.FFI
