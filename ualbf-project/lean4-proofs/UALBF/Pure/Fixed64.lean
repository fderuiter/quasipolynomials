import Mathlib.Data.Nat.Basic
import UALBF.ManifestConstants

namespace UALBF.Fixed64

/-- 64.64 fixed-point arithmetic scaling function.
    Given a bound and a prime p, calculates `ceil(bound * (p / (p - 1)))`.
    This uses exact integer arithmetic matching Rust's `(bound * p + p - 2) / (p - 1)`. -/
def scaleBoundCeil (bound : Nat) (p : Nat) : Nat :=
  if p <= 1 then bound
  else (bound * p + p - 2) / (p - 1)

/-- Formal machine-checked proof that `scaleBoundCeil` operates as a conservative mathematical upper bound.
    It guarantees that `(p - 1) * scaleBoundCeil bound p >= bound * p` for all `p > 1`,
    eliminating the Fixed-Point Scaling Conservatism TCB assumption. -/
theorem scaleBoundCeil_conservative (bound p : Nat) (hp : p > 1) :
    bound * p ≤ (p - 1) * scaleBoundCeil bound p := by
  unfold scaleBoundCeil
  have hp_gt_1 : ¬(p ≤ 1) := by omega
  simp [hp_gt_1]
  let X := bound * p + p - 2
  let Y := p - 1
  have hY : Y > 0 := by omega
  let Q := X / Y
  let R := X % Y
  have _h_div : X = Y * Q + R := (Nat.div_add_mod X Y).symm
  have _h_mod_lt : R ≤ Y - 1 := by
    have := Nat.mod_lt X hY
    omega
  have _h_X_eq : X = bound * p + Y - 1 := by omega
  have h_goal_rw : (p - 1) * ((bound * p + p - 2) / (p - 1)) = Y * Q := rfl
  rw [h_goal_rw]
  omega

/-- Computes the Rust-equivalent static suffix bound using 64.64 fixed point math.
    Uses the static manifest definitions to avoid complex dynamic prime generation. -/
def getStaticSuffixBound (k : UInt32) : Nat :=
  if h : k.toNat < UALBF.Manifest.STATIC_SUFFIX_BOUNDS.size then
    UALBF.Manifest.STATIC_SUFFIX_BOUNDS[k.toNat]
  else
    UALBF.Manifest.STATIC_SUFFIX_BOUNDS.back!

end UALBF.Fixed64
