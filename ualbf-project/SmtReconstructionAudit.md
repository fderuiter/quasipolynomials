# Lean SMT Certificate Checker Audit Guide

## Eliminating Z3 from the Trusted Computing Base (TCB)

Historically, the verification of the `verus_proofs.rs` components relied entirely on the Z3 SMT solver. While Z3 is highly reliable, it is a complex C++ codebase that introduces a massive, unverified dependency into our Trusted Computing Base (TCB).

With the introduction of the Lean SMT Reconstruction plugin (`SmtReconstruction`), Z3's role is relegated strictly to an **untrusted oracle**. The new pipeline works as follows:

1. **Z3 Execution via Verus**: Verus invokes Z3 to find proofs of functional correctness for the Rust arithmetic, bit-vector operations, and pruning logic.
2. **SMT Proof Ingestion**: The output from Z3 (the proof logs) is parsed and ingested by the `SmtReconstruction` plugin.
3. **Lean Reconstruction**: The `SmtReconstruction` tactic translates each inference step of the Z3 proof—including resolution steps, bit-vector theory lemmas, and RNS512 arithmetic deductions—into verifiable Lean 4 terms.
4. **Kernel Verification**: The Lean 4 kernel strictly checks these terms. If any proof step is unsound or missing, the Lean compilation fails. Z3 is effectively removed from the TCB, and the verified mathematical assertions in Rust are covered entirely by the Lean kernel.

## How to Audit the Link

1. **Check the Unified Manifest**
   Run the auditor tool to generate and verify the `proof_manifest.json`:
   ```bash
   make audit
   ```
   Or explicitly run:
   ```bash
   python3 auditor.py
   python3 verify_cert.py --cert formal_certificate.json --manifest proof_manifest.json
   ```
   The `verify_cert.py` output will explicitly indicate:
   `✓ Z3 Solver has been completely eliminated from the Trusted Computing Base.`
   `✓ All SMT-verified components in verus_proofs.rs are reconstructed in Lean via SMTReconstruction.`

2. **Verify Lean Reconstruction Theorems**
   The `proof_manifest.json` tracks the `UALBF.SmtReconstruction.Certificate.z3_proofs_reconstructed` theorem alongside the pure mathematical theorems. If you open `lean4-proofs/SmtReconstruction/Certificate.lean`, you will see the root theorem verifying the entirety of the ingested `verus_proofs.rs` SMT proof logic.

3. **Check the Logic Hash**
   The cryptographic `verified_logic_hash` dynamically hashes all the trusted sources, including `verus_proofs.rs` and the `bounds_manifest.json`. Since the Verus SMT proofs are proven equivalent in Lean, the execution logic encoded in `rust-engine` operates directly under the Lean 4 proof shield. You can verify this by checking that the logic hash in the `formal_certificate.json` matches the actual output of `verification_cli hash-tcb .`.
