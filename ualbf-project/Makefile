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

.PHONY: all lean rust clean audit mock-ui verification-lib check

all: verification-lib mock-ui lean rust

check:
	cargo fmt --check
	cargo clippy --workspace -- -D warnings
	python3 scripts/check_literals.py
	./scripts/check_lean_fmt.sh


verification-lib:
	cd verification-lib && cargo build --release --features signing

mock-ui:
	mkdir -p build/mock-bin
	echo '#!/usr/bin/env bash\nexit 0' > build/mock-bin/node
	echo '#!/usr/bin/env bash\nexit 0' > build/mock-bin/npx
	echo '#!/usr/bin/env bash\necho "Mocking npm command: $$@"\nmkdir -p dist build/js js\necho "module.exports = {};" > dist/index.js\necho "module.exports = {};" > build/js/index.js\necho "module.exports = {};" > js/index.js\necho "module.exports = {};" > index.js\nexit 0' > build/mock-bin/npm
	chmod +x build/mock-bin/node build/mock-bin/npx build/mock-bin/npm
	@echo "Mock UI setup complete (using mock npm in PATH)"

lean: verification-lib mock-ui
	cd lean4-proofs && PATH="$$(cd ../build/mock-bin && pwd):$$PATH" lake build UALBF validator

rust: lean
	./scripts/export_lean_specs.py
	echo "Building WITH signing capabilities (Verified Build)"; \
	cd rust-engine && cargo build --release --features signing;

clean:
	cd lean4-proofs && lake clean
	cd rust-engine && cargo clean
