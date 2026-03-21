# AMBS Formalization TODO

To complete the full formal verification of the Algebraic-Modular Bipartition Sieve, provide Lean 4 tactic blocks (replacing the `sorry` placeholders) for the following **8** theorems and lemmas.

## Foundation (`UALBF/Basic.lean`)

- [x] **`lemma qpn_sigma_odd`**
  - **Goal:** Prove that if `sigma n = 2n + 1`, then `sigma n` is strictly `Odd`.
  - **Strategy:** Relies on the algebraic definition of odd numbers (`2k + 1`).
  - **Definition of Done:** The `sorry` is replaced by a valid sequence of Lean tactics, rendering no warnings. The proof directly demonstrates that $2n+1$ guarantees the `Odd` property natively in Mathlib4.

- [x] **`theorem qpn_is_odd_square`**
  - **Goal:** Prove that any Quasiperfect Number must be an odd perfect square (`Odd n ∧ ∃ m : ℕ, n = m ^ 2`).
  - **Strategy:** Uses the fact that `sigma n` is odd, which only occurs for squares or double-squares in number theory.
  - **Definition of Done:** Lean compiler accepts the proof bridging `qpn_sigma_odd` to the double-square contradiction, explicitly constructing the existential witness `m` such that `n = m^2`.

## Coprimality & Ray-Casting (`UALBF/Bipartition.lean`)

- [x] **`lemma sigma_mul`**
  - **Goal:** Prove `sigma(N_L * N_R) = sigma(N_L) * sigma(N_R)` given `N_L.Coprime N_R`.
  - **Strategy:** Wraps Mathlib's `Nat.sum_divisors_multiplicative`.
  - **Definition of Done:** The lemma successfully applies Mathlib's built-in sum divisor multiplicativity onto our specific `QpnBipartition` structure without any axiom dependencies.

- [x] **`theorem prefix_sigma_coprime`**
  - **Goal:** Prove the mathematical guarantee that `gcd(N_L, sigma N_L) = 1` preventing the Rust ray-caster modular inverse from ever panicking.
  - **Strategy:** Algebraic manipulation of the multiplicativity of the QPN equation `sigma N_L * sigma N_R = 2 * N_L * N_R + 1`.
  - **Definition of Done:** The `sorry` block is completely replaced by a formal algebraic contradiction showing that any common prime divisor `d > 1` would have to divide `1`, effectively proving standard coprimality. (Completed in previous steps)

- [x] **`theorem ambs_suffix_target`**
  - **Goal:** Prove the AMBS modulo constraint equation `N_R * (2 * N_L) ≡ -1 (mod sigma N_L)`.
  - **Strategy:** Cast the QPN equation into the ring `ZMod (sigma N_L)` and isolate `N_R`.
  - **Definition of Done:** The equation compiles in the `ZMod (sigma p.N_L)` ring with all type coercions correctly handled, officially validating the exact target equation used in the Rust search engine.

## The Modulo-8 Obstruction (`UALBF/Obstruction.lean`)

- [x] **`theorem legendre_cattaneo_obstruction`**
  - **Goal:** Prove `q ≡ 1 or 3 (mod 8)` for any odd prime factor of `sigma n` where `n` is a QPN.
  - **Breakdown:** 
    - Apply `qpn_is_odd_square` to extract that $n = m^2$. Substitute this into the strict QPN equality $2n + 1 = \sigma(n)$ to derive $2m^2 + 1 = \sigma(m^2)$.
    - Given that the target prime $q$ divides $\sigma(m^2)$, the equality collapses within the ring `ZMod q` into $2m^2 + 1 \equiv 0 \pmod q$.
    - Perform basic modular arithmetic to multiply the equation by 2, yielding $4m^2 + 2 \equiv 0 \pmod q$, which factors explicitly to $(2m)^2 \equiv -2 \pmod q$.
    - Since $(2m)^2$ is a perfect square, this immediately establishes that $-2$ is a quadratic residue in `ZMod q`.
    - Translate this property algebraically into the Mathlib Legendre symbol, evaluating `legendreSym q (-2) = 1`.
    - Apply the multiplicativity property of the Legendre symbol to decompose this into `legendreSym q (-1) * legendreSym q 2`.
    - Evaluate using standard Mathlib properties `legendreSym.at_neg_one` and `legendreSym.at_two`. The product is strictly positive if and only if the underlying algebraic congruence class of $q$ is `1` or `3` modulo 8.
  - **Definition of Done:** The theorem must compile successfully in `UALBF/Obstruction.lean` with no `sorry` warnings, formally establishing `q % 8 = 1 ∨ q % 8 = 3` using Mathlib's `legendreSym` API natively.

## Zero-Factorization Valuation Trap (`UALBF/Valuation.lean`)

- [x] **`lemma exact_val_sigma_dvd`**
  - **Goal:** Prove that if `p^(2e) || n`, then `sigma(p^(2e)) ∣ sigma n`.
  - **Strategy:** Coprimality between `p^(2e)` and the remainder of the factorization of `n`.
  - **Definition of Done:** The proof cleanly separates `n` into `p^(2e) * k`, proves `gcd(p^(2e), k) = 1`, and uses `sigma_mul` logic to show exact divisibility of the sigma functions.

- [x] **`theorem rust_sieve_soundness`**
  - **Goal:** The ultimate soundness proof verifying that if `sigma(p^(2e))` yields a bad prime `q ≡ 5 or 7 (mod 8)`, then `p^(2e)` **cannot** exactly divide `N`.
  - **Strategy:** Proof by contradiction, chaining `exact_val_sigma_dvd` and `legendre_cattaneo_obstruction`.
  - **Definition of Done:** The `sorry` is closed by successfully deriving a contradiction between the given `h_bad_mod` and the Modulo-8 obstruction theorem. This permanently certifies that the Rust $\mathcal{O}(1)$ ray-cast shortcut is mathematically indistinguishable from full prime factorization.

## Abstracted Bridging Lemmas (`UALBF/Basic.lean`)

- [x] **`lemma odd_sigma_iff_square_or_double_square`**
  - **Goal:** Prove that `Odd (sigma n)` iff `n` is a perfect square or twice a perfect square.
  - **Strategy:** Formalize the known number-theoretic property natively.
  - **Definition of Done:** Replaces `sorry` with valid Lean tactics bridging the parity of `sigma n` to its prime factorization.

- [x] **`lemma odd_sigma_iff_factorization`**
  - **Goal:** Prove `Odd (sigma n) ↔ ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p)`.
  - **Strategy:** Formalization helper bridging `sigma` parity directly to prime factorizations.
  - **Definition of Done:** Replaces `sorry` with a formal proof sequence.

- [x] **`lemma factorization_even_iff_square_or_double_square`**
  - **Goal:** Prove that if all odd prime factors have even valuation, `n` is a square or double square.
  - **Strategy:** Translate prime factorization parity conditions to the algebraic definitions of squares and double squares.
  - **Definition of Done:** Replaces `sorry` with a formalized Lean proof.
  - *Note: To maintain a clean structural hierarchy without overcomplicating the main theorem, three small localized sorrys were introduced as sub-lemmas. They must be filled to complete the proof tree:*
    - [x] **`lemma odd_even_factorization_is_square`**
      - **Goal:** Hook the odd perfect square property directly to Mathlib's `sq_iff_factorization_even`.
      - **Breakdown:** Given $m > 0$ and `∀ p ∈ m.primeFactors, Even (m.factorization p)`, we must strengthen this bounded quantifier to an unbounded one: `∀ p, Even (m.factorization p)`. Any prime $p \notin m.primeFactors$ natively evaluates to $0$ (which is even). Then, apply Mathlib's built-in `Nat.isSquare_iff_factorization_even` to extract the existential witness $k$ such that $m = k^2$.
      - **Definition of Done:** Replaces `sorry` with a sequence bridging `m.primeFactors` bounded ∀ into the unbounded Mathlib expectation, producing the existential witness `k` without compilation warnings.
      - **Addendum (Implementation):** `Nat.isSquare_iff_factorization_even` does not exist in Mathlib 4. A formal proof was constructed natively from scratch using `Nat.sq_mul_squarefree_of_pos` to factor $m = a^2 \times b$ for squarefree $b$. The even factorization premise strictly collapsed against $b$'s squarefree constraint via Mathlib's `Squarefree.natFactorization_le_one`, demonstrating definitively $b=1$ to construct the witness $m = a^2$.
    - [x] **`factorization equality helper`**
      - **Goal:** Prove `n.factorization p = u.factorization p` for odd `p` when `n = 2^e * u`.
      - **Breakdown:** Apply `Nat.factorization_mul` to split the factorization map over the product. Evaluate the resulting `Finsupp` addition at the specific odd prime $p$. Use `Nat.factorization_pow` to convert `(2^e).factorization p` into `e * 2.factorization p`. This reduces the problem to establishing that `2.factorization p = 0`.
      - **Definition of Done:** The `sorry` is resolved into explicit Mathlib evaluations bridging `Nat.factorization_mul` to isolate `u.factorization p` identically to `n.factorization p` with no syntax errors.
    - [x] **`factorization of two helper`**
      - **Goal:** Prove `(Nat.factorization 2) p = 0` for odd prime `p`.
      - **Breakdown:** Apply `Nat.Prime.factorization Nat.prime_two` to concretize the factorization of 2 into a `Finsupp.single` mapping 2 to 1 and all other inputs to 0. Since we are given $p \ne 2$, the `Finsupp.single_apply` evaluated at $p$ will strictly evaluate the false branch of the target, yielding exactly 0.
      - **Definition of Done:** Replaces the `sorry` block natively using `Finsupp.single_apply` evaluated on cleanly stated primitive inequalities without error.

- [x] **`lemma even_qpn_implies_double_square`**
  - **Goal:** Prove that if a Quasiperfect Number is even, then `n = 2m^2`.
  - **Strategy:** Uses the fact that `n` is even alongside the QPN property `sigma n = 2n + 1`.
  - **Definition of Done:** Replaces `sorry` with a valid formal proof.
  - *Note: To cleanly separate the number-theoretic Legendre obstruction from the structural parity logic, one localized sorry was introduced as a sub-lemma:*
    - [x] **`lemma square_qpn_parity_obstruction`**
      - **Goal:** Prove that if an even perfect square is a QPN, it produces a mathematical contradiction via the Legendre symbol.
      - **Breakdown:** Assume $n = m^2$ is an even QPN. $m$ is even, so $n = 4k^2 = 2^{2e} u^2$ (with $e \ge 1$ and $u$ odd). We compute $2n + 1 = 2^{2e+1} u^2 + 1$. The sum of divisors yields $\sigma(n) = (2^{2e+1}-1) \sigma(u^2)$. Since the two expressions are structurally strictly equal, $2^{2e+1}-1$ must algebraically divide $2^{2e+1} u^2 + 1$. By rewriting the target polynomial as $u^2(2^{2e+1}-1) + u^2 + 1$, mathematically $2^{2e+1}-1$ is fundamentally forced to divide exactly $u^2 + 1$. Because $e \ge 1$, the divisor evaluates cleanly to $2^{2e+1}-1 \equiv 7 \pmod 8$, inherently forcing it to lie in the equivalence class $\equiv 3 \pmod 4$. Prime factorization guarantees it must harbor at least one prime root $q \equiv 3 \pmod 4$. As $q$ inherently divides $u^2 + 1$, the modular relation $u^2 \equiv -1 \pmod q$ emerges. Mathlib's native formulation of the First Supplement to the Law of Quadratic Reciprocity strictly rejects $-1$ as a quadratic residue modulo any $q \equiv 3 \pmod 4$, permanently terminating the logic in `False` without axioms.
      - **Definition of Done:** Replaces `sorry` by natively compiling the full modular deduction chain bridging `2^{2e+1}-1 \mid u^2+1` to Mathlib's explicit quadratic non-residue theorem, returning `False`.


- [x] **`lemma qpn_not_double_square`**
  - **Goal:** Prove that a Quasiperfect Number cannot be a double square.
  - **Strategy:** Formalize the inherent contradiction in parity and abundancy limits when `n = 2m^2`.
  - **Definition of Done:** Replaces `sorry` with a valid mathematical contradiction in Lean.
