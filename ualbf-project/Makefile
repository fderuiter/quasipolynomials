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

all: lean rust

lean:
	cd lean4-proofs && lake build

rust: lean
	./scripts/export_lean_specs.py
	@if [ -d lean4-proofs/.lake/build/ir ] || [ -n "$$LEAN_SYSROOT" ]; then \
		echo "Building WITH signing capabilities (Verified Build)"; \
		cd rust-engine && cargo build --release --features signing; \
	else \
		echo "Building WITHOUT signing capabilities (Unverified Build)"; \
		cd rust-engine && env ALLOW_UNVERIFIED_BUILD=1 cargo build --release; \
	fi

clean:
	cd lean4-proofs && lake clean
	cd rust-engine && cargo clean
