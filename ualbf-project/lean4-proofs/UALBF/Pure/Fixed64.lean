import Mathlib.Data.Nat.Basic

namespace UALBF.Fixed64

/-- 64.64 fixed-point arithmetic scaling function.
    Given a bound and a prime p, calculates `ceil(bound * (p / (p - 1)))`.
    This uses exact integer arithmetic matching Rust's `(bound * p + p - 2) / (p - 1)`. -/
def scaleBoundCeil (bound : Nat) (p : Nat) : Nat :=
  if p <= 1 then bound
  else (bound * p + p - 2) / (p - 1)

/-- Naive deterministic primality check for FFI bounds computation. -/
partial def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else
    let rec loop (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d == 0 then false
      else loop (d + 2)
    loop 3

/-- Computes the Rust-equivalent static suffix bound using 64.64 fixed point math. -/
partial def getStaticSuffixBound (k : UInt32) : Nat :=
  let rec loop (primesFound : Nat) (currentNum : Nat) (bound : Nat) : Nat :=
    if primesFound >= k.toNat then bound
    else
      if isPrime currentNum then
        loop (primesFound + 1) (currentNum + 2) (scaleBoundCeil bound currentNum)
      else
        loop primesFound (currentNum + 2) bound
  loop 0 3 (1 <<< 64)

end UALBF.Fixed64
