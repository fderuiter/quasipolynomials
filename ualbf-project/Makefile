# UALBF Project — Monorepo Build Script
#
# Usage:
#   make          — Build Lean proofs, then Rust engine
#   make lean     — Build only Lean (requires mathlib)
#   make rust     — Build only Rust (requires prior `make lean`)
#   make clean    — Clean both Lean and Rust build artifacts
#
# IMPORTANT: Lean must be built BEFORE Rust, as the Rust engine
# links against the Lean C-IR static library produced by `lake build`.

.PHONY: all lean rust clean audit

all: lean audit rust

lean:
	cd lean4-proofs && lake build

audit:
	./auditor.py

rust: lean audit
	./scripts/export_lean_specs.py || true
	cd rust-engine && cargo build --release

clean:
	cd lean4-proofs && lake clean
	cd rust-engine && cargo clean
