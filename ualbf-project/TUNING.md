# Structured Performance Profiles — Tuning Guide

The UALBF Engine allows researchers to modify search parameters dynamically using a `profile.json` file. This prevents the need for manual code recompilation and enables easy hardware benchmarking without changing the mathematically verified bounds.

## Profile Configuration Format

The engine expects a `profile.json` file in the execution directory with the following structure:

```json
{
  "pollard_rho_batch_size": 128,
  "active_prime_slots": 64,
  "engine_telemetry_interval_ms": 1000,
  "dashboard_telemetry_interval_ms": 250
}
```

### Parameter Details

- **`pollard_rho_batch_size`**
  - **Description**: The number of polynomial iterations ($f(x) = x^2 + 1$) performed before applying the GCD step in the Pollard-rho fallback factorization logic.
  - **Tuning Strategy**: For modern processors with deep instruction pipelines, larger batch sizes (e.g., 256 or 512) increase throughput by amortizing the cost of the GCD check. For very large factors or on low-cache systems, smaller sizes (e.g., 64) might prove more responsive.

- **`active_prime_slots`**
  - **Description**: Determines the number of lock-free telemetry slots available for worker threads to report their currently processing roots.
  - **Tuning Strategy**: Set this value to be greater than or equal to the number of physical CPU cores on the execution machine. For a 128-core system, a value of `128` or `256` guarantees thread visibility without telemetry contention.

- **`engine_telemetry_interval_ms`**
  - **Description**: The minimum elapsed time (in milliseconds) before the core search loops (`sieve` and `dfs_tree`) output progress trace logs.
  - **Tuning Strategy**: Lowering this value (e.g., `100` ms) provides higher fidelity logs at a slight cost to I/O processing bandwidth. For high-throughput production runs, this value can be safely raised to `5000` or `10000` to silence logs and minimize CPU interrupts.

- **`dashboard_telemetry_interval_ms`**
  - **Description**: The update frequency for the curses GUI dashboard interface.
  - **Tuning Strategy**: Decreasing the interval leads to smoother UI frame rates (e.g., `50` ms yields 20 FPS). However, updating too frequently steals rendering cycles from the main Python thread. `250` ms is recommended for standard monitoring.

## Fallback Defaults
If the file is absent or improperly formatted, the engine applies hardcoded safe defaults:
- `pollard_rho_batch_size`: 128
- `active_prime_slots`: 64
- `engine_telemetry_interval_ms`: 1000
- `dashboard_telemetry_interval_ms`: 250
