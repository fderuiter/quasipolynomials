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

.PHONY: all lean rust clean audit mock-ui verification-lib check check-docs

all: verification-lib mock-ui lean rust

audit:
	python3 auditor.py

check-docs: mock-ui
	cd lean4-proofs && PATH="$$(cd ../build/mock-bin && pwd):$$PATH" lake build -Kdoc=on UALBF:docs
	RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps

check: check-docs
	cargo fmt --check
	cargo clippy --workspace -- -D warnings
	python3 scripts/check_literals.py
	./scripts/check_lean_fmt.sh
	black --check --extend-exclude '\.lake' .
	flake8 --exclude .lake,.git,__pycache__ .
	mypy --exclude '\.lake' .


verification-lib:
	cd verification-lib && cargo build --release --features signing

mock-ui:
	mkdir -p build/mock-bin
	printf '#!/usr/bin/env bash\nexit 0\n' > build/mock-bin/node
	printf '#!/usr/bin/env bash\nexit 0\n' > build/mock-bin/npx
	printf '#!/usr/bin/env bash\necho "Mocking npm command: $$@"\nmkdir -p dist build/js js\necho "module.exports = {};" > dist/index.js\necho "module.exports = {};" > build/js/index.js\necho "module.exports = {};" > js/index.js\necho "module.exports = {};" > index.js\nexit 0\n' > build/mock-bin/npm
	chmod +x build/mock-bin/node build/mock-bin/npx build/mock-bin/npm
	@echo "Mock UI setup complete (using mock npm in PATH)"

lean: verification-lib mock-ui
	cd lean4-proofs && PATH="$$(cd ../build/mock-bin && pwd):$$PATH" lake build UALBF validator

rust: lean
	./scripts/export_lean_specs.py
	python3 auditor.py
	echo "Building WITH signing capabilities (Verified Build)"; \
	cd rust-engine && cargo build --release --features signing;


clean:
	cd lean4-proofs && lake clean
	cd rust-engine && cargo clean
