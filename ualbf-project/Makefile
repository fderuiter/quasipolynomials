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

all: verification-lib lean rust

verification-lib:
	cd verification-lib && cargo build --release --features signing

lean: verification-lib
	cd lean4-proofs && lake build UALBF validator

rust: lean
	./scripts/export_lean_specs.py
	echo "Building WITH signing capabilities (Verified Build)"; \
	cd rust-engine && cargo build --release --features signing;

clean:
	cd lean4-proofs && lake clean
	cd rust-engine && cargo clean
