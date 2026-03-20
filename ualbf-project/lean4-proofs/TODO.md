# AMBS Formalization TODO

To complete the full formal verification of the Algebraic-Modular Bipartition Sieve, provide Lean 4 tactic blocks (replacing the `sorry` placeholders) for the following **8** theorems and lemmas.

## Foundation (`UALBF/Basic.lean`)

- [ ] **`lemma qpn_sigma_odd`**
  - **Goal:** Prove that if `sigma n = 2n + 1`, then `sigma n` is strictly `Odd`.
  - **Strategy:** Relies on the algebraic definition of odd numbers (`2k + 1`).
  - **Definition of Done:** The `sorry` is replaced by a valid sequence of Lean tactics, rendering no warnings. The proof directly demonstrates that $2n+1$ guarantees the `Odd` property natively in Mathlib4.

- [ ] **`theorem qpn_is_odd_square`**
  - **Goal:** Prove that any Quasiperfect Number must be an odd perfect square (`Odd n ∧ ∃ m : ℕ, n = m ^ 2`).
  - **Strategy:** Uses the fact that `sigma n` is odd, which only occurs for squares or double-squares in number theory.
  - **Definition of Done:** Lean compiler accepts the proof bridging `qpn_sigma_odd` to the double-square contradiction, explicitly constructing the existential witness `m` such that `n = m^2`.

## Coprimality & Ray-Casting (`UALBF/Bipartition.lean`)

- [ ] **`lemma sigma_mul`**
  - **Goal:** Prove `sigma(N_L * N_R) = sigma(N_L) * sigma(N_R)` given `N_L.Coprime N_R`.
  - **Strategy:** Wraps Mathlib's `Nat.sum_divisors_multiplicative`.
  - **Definition of Done:** The lemma successfully applies Mathlib's built-in sum divisor multiplicativity onto our specific `QpnBipartition` structure without any axiom dependencies.

- [ ] **`theorem prefix_sigma_coprime`**
  - **Goal:** Prove the mathematical guarantee that `gcd(N_L, sigma N_L) = 1` preventing the Rust ray-caster modular inverse from ever panicking.
  - **Strategy:** Algebraic manipulation of the multiplicativity of the QPN equation `sigma N_L * sigma N_R = 2 * N_L * N_R + 1`.
  - **Definition of Done:** The `sorry` block is completely replaced by a formal algebraic contradiction showing that any common prime divisor `d > 1` would have to divide `1`, effectively proving standard coprimality.

- [ ] **`theorem ambs_suffix_target`**
  - **Goal:** Prove the AMBS modulo constraint equation `N_R * (2 * N_L) ≡ -1 (mod sigma N_L)`.
  - **Strategy:** Cast the QPN equation into the ring `ZMod (sigma N_L)` and isolate `N_R`.
  - **Definition of Done:** The equation compiles in the `ZMod (sigma p.N_L)` ring with all type coercions correctly handled, officially validating the exact target equation used in the Rust search engine.

## The Modulo-8 Obstruction (`UALBF/Obstruction.lean`)

- [ ] **`theorem legendre_cattaneo_obstruction`**
  - **Goal:** Prove `q ≡ 1 or 3 (mod 8)` for any odd prime factor of `sigma n` where `n` is a QPN.
  - **Strategy:** Quadratic reciprocity using the Legendre symbol `(-2/q) = 1` derived from `-2` being a quadratic residue in `ZMod q`.
  - **Definition of Done:** The theorem compiles perfectly by chaining `ZMod q` algebra with Mathlib's `legendreSym` properties (`legendreSym.at_two` and `legendreSym.at_neg_one`) to restrict the modulo 8 congruence classes.

## Zero-Factorization Valuation Trap (`UALBF/Valuation.lean`)

- [ ] **`lemma exact_val_sigma_dvd`**
  - **Goal:** Prove that if `p^(2e) || n`, then `sigma(p^(2e)) ∣ sigma n`.
  - **Strategy:** Coprimality between `p^(2e)` and the remainder of the factorization of `n`.
  - **Definition of Done:** The proof cleanly separates `n` into `p^(2e) * k`, proves `gcd(p^(2e), k) = 1`, and uses `sigma_mul` logic to show exact divisibility of the sigma functions.

- [ ] **`theorem rust_sieve_soundness`**
  - **Goal:** The ultimate soundness proof verifying that if `sigma(p^(2e))` yields a bad prime `q ≡ 5 or 7 (mod 8)`, then `p^(2e)` **cannot** exactly divide `N`.
  - **Strategy:** Proof by contradiction, chaining `exact_val_sigma_dvd` and `legendre_cattaneo_obstruction`.
  - **Definition of Done:** The `sorry` is closed by successfully deriving a contradiction between the given `h_bad_mod` and the Modulo-8 obstruction theorem. This permanently certifies that the Rust $\mathcal{O}(1)$ ray-cast shortcut is mathematically indistinguishable from full prime factorization.
