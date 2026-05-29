#!/bin/bash
set -e

echo "=== UALBF Build & Verification Wrapper ==="

# Assuming /workspace is mounted to the root of the repo (where ualbf-project is)
PROJECT_DIR="/workspace/ualbf-project"

if [ ! -d "$PROJECT_DIR" ]; then
    echo "Error: Directory $PROJECT_DIR not found. Did you mount the workspace correctly?"
    echo "Usage: docker run -v \$(pwd):/workspace ualbf-env"
    exit 1
fi

cd "$PROJECT_DIR"

echo "[1/3] Resolving circular dependency (creating dummy libualbf_engine.a)..."
mkdir -p rust-engine/target/release
echo "void dummy(){}" | gcc -c -x c - -o dummy.o
ar rcs rust-engine/target/release/libualbf_engine.a dummy.o
rm dummy.o

echo "[2/3] Building Lean proofs and generating C-IR..."
cd lean4-proofs
# We use `lake build` which will succeed since the dummy library exists
lake build
cd ..

echo "[3/3] Compiling Rust engine..."
cd rust-engine
# Now cargo build will overwrite the dummy library with the real one
cargo build --release
cd ..

echo "=== Build Complete! ==="

if [ "$1" = "verify" ]; then
    echo "=== Starting Verification Process ==="
    cd "$PROJECT_DIR/rust-engine"
    # Provide a minimal search bound to prove it works in reasonable time, unless env vars are set
    export UALBF_TARGET_MIN_LOG10=${UALBF_TARGET_MIN_LOG10:-35}
    export UALBF_TARGET_MAX_LOG10=${UALBF_TARGET_MAX_LOG10:-37}
    export UALBF_SIEVE_LIMIT=${UALBF_SIEVE_LIMIT:-1000}
    cargo run --release
elif [ -n "$1" ]; then
    echo "=== Running custom command: $@ ==="
    exec "$@"
else
    echo "To run the verification suite, use the 'verify' argument or run:"
    echo "  docker run --rm -it ualbf-env verify"
fi
