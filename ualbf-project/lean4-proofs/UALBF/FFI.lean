/-
  UALBF/FFI.lean — Computational wrappers for C-linkage export.

  Lean 4 erases `theorem` (Prop) at runtime, so we write executable `def`s
  that mirror the proven theorems and tag them with `@[export]`.
  These are compiled into the static library `libualbf_core.a` and called
  from the Rust engine via C-FFI.
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

/-- Extended GCD: returns (g, x, y) such that a*x + b*y = g. -/
private def extGcd (a b : Int) : Int × Int × Int :=
  if b == 0 then (a, 1, 0)
  else
    let (g, x₁, y₁) := extGcd b (a % b)
    (g, y₁, x₁ - (a / b) * y₁)

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

end UALBF.FFI
