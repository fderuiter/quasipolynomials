FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies required for Lean and Rust
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    libgmp-dev \
    libuv1-dev \
    python3 \
    clang \
    cmake \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# Install Rust toolchain
ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$PATH
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain 1.75.0
RUN rustup default 1.75.0

# Install Lean toolchain via elan
ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none

# Pre-install the specific Lean version used in the project
RUN elan toolchain install leanprover/lean4:v4.29.0-rc6 && elan default leanprover/lean4:v4.29.0-rc6

WORKDIR /workspace

# Copy the wrapper script
COPY build.sh /usr/local/bin/build.sh
RUN chmod +x /usr/local/bin/build.sh

ENTRYPOINT ["/usr/local/bin/build.sh"]
