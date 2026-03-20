# UALBF Computational Engine (Rust)

A high-performance algorithmic engine for analyzing odd quasiperfect numbers and executing exact mathematical ray-casting over massive prefixes using the Unified Algebraic-Lattice Bipartition Framework (UALBF).

This tool leverages state-of-the-art computational number theory, including Legendre-Cattaneo Sieving, Pollard's Rho Factorization, Miller-Rabin Primality Testing, and the Tonelli-Shanks algorithm across composite moduli.

## 🚀 Architecture and execution flow

The execution is strictly broken into four major analytical phases:

### Phase 1: Legendre-Cattaneo Global Sieve (`src/sieve.rs`)
The engine initiates by building a space of mathematically viable "Prime Powers". By using a prime limit (e.g. 50,000) and an exponent limit, it evaluates $p^{2e}$.
Because we evaluate properties related to the sum of divisors ($\sigma$), we instantly prune factors whose $\sigma(p^{2e})$ contains prime factors congruent to 5 or 7 modulo 8. This radically drops the search space using deep algebraic invariants.

### Phase 2: Dynamic Prefix DFS Construction (`src/dfs_tree.rs`)
Using the surviving components from Phase 1, we execute a Depth-First Search to dynamically construct mathematical "Prefixes" ($n_l$). We halt recursion when our prefix combination surpasses a predefined upper bound limit target (e.g., $10^{16}$). This yields `Prefix` objects containing $n_l$ and their corresponding sigma values $s_l$.

### Phase 3: Exact Valuation Sieve & Ray-Casting Preparations (`src/main.rs`)
We take the generated Prefix objects and stream them across all available CPU cores using `rayon` for lock-free multi-threaded parallelism, initializing high-performance exact ray-casting bounds for each mathematical prefix branch.

### Phase 4: Exact Ray Casting (`src/raycast.rs`)
Here is where the dense mathematical magic happens. We evaluate a "free" prime power completion target $n_r = z^2$.
By recognizing that quasiperfect numbers satisfy $\sigma(N) = 2N + 1$, we formulate a composite congruence condition for $z^2 \pmod{s_l}$. 
- We compute the modular inverse to find the target congruence $x_l \equiv -(2n_l)^{-1} \pmod{s_l}$.
- We execute a **Composite Tonelli-Shanks** orchestrator over $s_l$:
  1. Complete factorizations of $s_l$ using **Pollard's rho**.
  2. Map roots to true primes via **Tonelli-Shanks**.
  3. Lift prime properties to prime-power constraints via **Hensel's Lemma**.
  4. Aggregate geometric root permutations across $s_l$ using the **Chinese Remainder Theorem** (`solve_crt`).
- For viable roots $z$, we implement an $O(1)$ modulo exact valuation sieve, throwing out mathematical illegal valuations instantly.
- Finally, any surviving $z$ triggers a **Miller-Rabin Primality Test** to verify mathematically unassailable quasiperfect numbers!

## 📦 Mathematics Implementation

The math utilities (`src/math_utils.rs`) are built for rigorous handling of giant integers:
- **`mod_inverse`**: Computes modular inverses using the Extended Euclidean Algorithm.
- **`compute_sigma`**: Calculates $(p^{k+1} - 1) / (p - 1)$ strictly for mathematical primes.
- **`is_prime_biguint`**: Rigorous Miller-Rabin deterministic probabilistic primality test to definitively rule out false positive composite permutations.
- **`pollards_rho` & `quick_factor`**: Robust integer factorization ensuring complete evaluation to pure prime components.
- **`tonelli_shanks` & `hensels_lift`**: The absolute cutting-edge mechanisms for lifting polynomial ring solutions modulo prime powers.

## 🛠️ Usage

To execute the computational framework natively:

```bash
# Ensure the Rust toolchain is installed
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Compile and execute the engine (automatically parallelized)
cargo run --release
```

To run test validations over the exact valuation sieves:
```bash
cargo test
```

## ⚖️ Logical Safeguards
Strictly ensures all roots derived computationally are completely validated via intrinsic structural invariant checks (Miller-Rabin verification before claiming topological discoveries) to prevent infinite loops and false positives present in classical iterative sieves.
