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

.PHONY: all lean rust clean audit mock-ui verification-lib

all: verification-lib mock-ui lean rust

verification-lib:
	cd verification-lib && cargo build --release --features signing

mock-ui:
	@echo "Mock UI setup complete (using mock npm in PATH)"

lean: verification-lib mock-ui
	cd lean4-proofs && PATH="$$(cd ../scripts/mock-bin && pwd):$$PATH" lake build UALBF validator

rust: lean
	./scripts/export_lean_specs.py
	echo "Building WITH signing capabilities (Verified Build)"; \
	cd rust-engine && cargo build --release --features signing;

clean:
	cd lean4-proofs && lake clean
	cd rust-engine && cargo clean
