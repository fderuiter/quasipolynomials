import Mathlib.Tactic

private def extGcdAux (fuel : Nat) (a b : Int) : Int × Int × Int :=
  match fuel with
  | 0 => (a, 1, 0)
  | fuel' + 1 =>
    if b == 0 then (a, 1, 0)
    else
      let (g, x₁, y₁) := extGcdAux fuel' b (a % b)
      (g, y₁, x₁ - (a / b) * y₁)

private def extGcd (a b : Int) : Int × Int × Int :=
  extGcdAux 256 a b

private theorem extGcd_bezout (a b : Int) :
    a * (extGcd a b).2.1 + b * (extGcd a b).2.2 = (extGcd a b).1 :=
  sorry

private def modInverse (a m : Int) : Option Int :=
  let a' := ((a % m) + m) % m
  let (g, x, _) := extGcd a' m
  if g == 1 then
    some (((x % m) + m) % m)
  else
    none

private theorem modInverse_spec (a m : Int) (v : Int)
    (hm_pos : m > 0)
    (hv : modInverse a m = some v) :
    (a * v) % m = 1 % m := by
  unfold modInverse at hv
  set a' := ((a % m) + m) % m
  have h_bezout : a' * (extGcd a' m).2.1 + m * (extGcd a' m).2.2 = (extGcd a' m).1 :=
    extGcd_bezout a' m
  set g := (extGcd a' m).1
  set x := (extGcd a' m).2.1
  set y := (extGcd a' m).2.2
  split at hv
  · next h_guard =>
    injection hv with hv_eq
    sorry
  · contradiction
