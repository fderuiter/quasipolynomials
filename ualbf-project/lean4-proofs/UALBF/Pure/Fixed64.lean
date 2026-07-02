import Mathlib.Data.Nat.Basic

namespace UALBF.Fixed64

/-- 64.64 fixed-point arithmetic scaling function.
    Given a bound and a prime p, calculates `ceil(bound * (p / (p - 1)))`.
    This uses exact integer arithmetic matching Rust's `(bound * p + p - 2) / (p - 1)`. -/
def scaleBoundCeil (bound : Nat) (p : Nat) : Nat :=
  if p <= 1 then bound
  else (bound * p + p - 2) / (p - 1)

/-- Naive deterministic primality check for FFI bounds computation. -/
def isPrimeLoop (n d : Nat) : Bool :=
  if d * d > n then true
  else if n % d == 0 then false
  else if h : d < n then
    have : n - (d + 2) < n - d := by omega
    isPrimeLoop n (d + 2)
  else true
termination_by n - d

def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else isPrimeLoop n 3

/-- Computes the Rust-equivalent static suffix bound using 64.64 fixed point math. -/
def getStaticSuffixBound (k : UInt32) : Nat :=
  let rec loop (fuel : Nat) (primesFound : Nat) (currentNum : Nat) (bound : Nat) : Nat :=
    match fuel with
    | 0 => bound
    | fuel' + 1 =>
      if primesFound >= k.toNat then bound
      else
        if isPrime currentNum then
          loop fuel' (primesFound + 1) (currentNum + 2) (scaleBoundCeil bound currentNum)
        else
          loop fuel' primesFound (currentNum + 2) bound
  loop 100000 0 3 (1 <<< 64)

end UALBF.Fixed64
