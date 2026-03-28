#!/usr/bin/env python3
"""
UALBF Engine — Curses Dashboard (v4)

A real-time terminal GUI for monitoring the UALBF quasiperfect number search
engine.  Displays live telemetry from all engine subsystems and orchestrates
both the Lean 4 formal proof build and the Rust computational engine.

  • Phase 0  — Lean 4 Build & Proof Verification
  • Phase 1  — Legendre–Cattaneo Sieve (cyclotomic factorization)
  • Phase 2  — Fused DFS Construction & Ray-Casting
  • Lean 4 FFI bridge status (σ, mod-inverse, mod-8 checks)
  • Z3 CDCL conflict-driven pruner stats (starvation + Zsigmondy traps)
  • LLL lattice module status (standalone Wave 4 Diophantine pruning)
  • Lock-free active-primes telemetry (AtomicU64 slot array)

Usage:
    python3 run_gui.py                          # defaults: 10^35 < N < 10^37
    python3 run_gui.py --min 35 --max 40        # custom range
    python3 run_gui.py --sieve-limit 500000     # bigger sieve
    python3 run_gui.py --max-exponent 6         # higher even exponents
    python3 run_gui.py --auto-raise             # auto-increment after success
    python3 run_gui.py --skip-lean-build        # skip lake build
    python3 run_gui.py --debug                  # run without --release

Keybindings:
    q / Q   — Quit the dashboard
    r       — Raise bounds and re-run (after completion)
    l       — Toggle Lean proof status overlay
"""

import curses
import subprocess
import threading
import queue
import sys
import time
import os
import re
import argparse
import glob
from datetime import timedelta

# ═══════════════════════════════════════════════════════════════════════════════
#  Constants
# ═══════════════════════════════════════════════════════════════════════════════

REFRESH_HZ = 20          # UI refresh rate (frames per second)
LOG_THROTTLE_SEC = 5.0   # minimum interval between log file writes
MAX_LOG_LINES = 300       # scrollback buffer for the live event stream

PHASE_ICONS = {
    "0": "📐",   # Lean Build
    "1": "⚗ ",   # Sieve
    "2": "🌳",   # DFS + Ray-Cast (fused)
    "3": "⚡",   # Ray-Cast (standalone, legacy)
    "4": "🔒",   # Z3 verification
}

# Prior verified baseline — no QPN exists below this bound
VERIFIED_BASELINE = "10^35 (Hagis-Cohen, independently verified)"
VERIFIED_BASELINE_EXP = 35

# Key theorems to scan in the Lean proof files
LEAN_THEOREMS = [
    ("legendre_cattaneo_obstruction", "Obstruction.lean"),
    ("qpn_is_odd_square",            "Basic.lean"),
    ("qpn_coprime_15_omega_15",      "SpecialFactors.lean"),
    ("abundancy_le_totient_ratio",    "Abundancy.lean"),
    ("qpn_totient_bound",            "Abundancy.lean"),
    ("correction_factor_bound",      "Abundancy.lean"),
    ("sigma_prime_pow_cyclotomic",    "Cyclotomic.lean"),
    ("zsigmondy_poison_trap",        "Cyclotomic.lean"),
    ("abundancy_starvation",         "Abundancy.lean"),
]

# ═══════════════════════════════════════════════════════════════════════════════
#  ASCII Header
# ═══════════════════════════════════════════════════════════════════════════════

HEADER_ART = [
    "╔═══════════════════════════════════════════════════════════════╗",
    "║   █ █  █▀█  █   █▀▄  █▀▀   Quasiperfect Number Search      ║",
    "║   █▄█  █▀█  █▄  █▀▄  █▀    Lean4 + Rust + Z3 Engine        ║",
    "║   Established: No QPN exists below 10^35 (Hagis-Cohen)      ║",
    "╚═══════════════════════════════════════════════════════════════╝",
]

# ═══════════════════════════════════════════════════════════════════════════════
#  CLI Argument Parsing
# ═══════════════════════════════════════════════════════════════════════════════

def parse_args():
    p = argparse.ArgumentParser(
        description="UALBF Engine Dashboard — Lean4 + Rust + Z3")
    p.add_argument("--min", type=int, default=35,
                   help="Lower bound exponent (default: 35 → 10^35)")
    p.add_argument("--max", type=int, default=37,
                   help="Upper bound exponent (default: 37 → 10^37)")
    p.add_argument("--sieve-limit", type=int, default=250_000,
                   help="Prime sieve upper limit (default: 250000)")
    p.add_argument("--max-exponent", type=int, default=4,
                   help="Maximum even exponent for prime powers (default: 4)")
    p.add_argument("--prefix-stop", type=int, default=100_000_000_000,
                   help="Prefix stop threshold (default: 10^11)")
    p.add_argument("--auto-raise", action="store_true",
                   help="Auto-increment bounds and re-run after success")
    p.add_argument("--raise-step", type=int, default=2,
                   help="Exponent increment per auto-raise (default: 2)")
    p.add_argument("--skip-lean-build", action="store_true",
                   help="Skip the Lean 4 lake build phase")
    p.add_argument("--debug", action="store_true",
                   help="Run Rust engine without --release")
    return p.parse_args()

# ═══════════════════════════════════════════════════════════════════════════════
#  Helper: safe addstr (never crash on write-past-edge)
# ═══════════════════════════════════════════════════════════════════════════════

def safe_addstr(win, y, x, text, attr=0):
    """Write text to the curses window, silently clipping at the edge."""
    h, w = win.getmaxyx()
    if y < 0 or y >= h or x >= w:
        return
    max_chars = w - x - 1
    if max_chars <= 0:
        return
    try:
        win.addstr(y, x, text[:max_chars], attr)
    except curses.error:
        pass

# ═══════════════════════════════════════════════════════════════════════════════
#  Lean 4 Proof Scanner
# ═══════════════════════════════════════════════════════════════════════════════

class LeanProofStatus:
    """Scans Lean 4 source files for theorem status (sorry/axiom/verified)."""

    def __init__(self, lean_project_dir):
        self.lean_dir = os.path.join(lean_project_dir, "UALBF")
        self.theorems = {}   # name → ("verified"|"sorry"|"axiom"|"missing")
        self.sorry_count = 0
        self.axiom_count = 0
        self.build_ok = None    # None=not run, True=success, False=failed
        self.build_errors = []
        self.build_warnings = []

    def scan(self):
        """Scan all .lean files for theorem status."""
        self.sorry_count = 0
        self.axiom_count = 0
        self.theorems = {}

        for thm_name, filename in LEAN_THEOREMS:
            filepath = os.path.join(self.lean_dir, filename)
            status = self._check_theorem(filepath, thm_name)
            self.theorems[thm_name] = status
            if status == "sorry":
                self.sorry_count += 1
            elif status == "axiom":
                self.axiom_count += 1

    def _check_theorem(self, filepath, thm_name):
        if not os.path.exists(filepath):
            return "missing"
        try:
            with open(filepath, "r") as f:
                content = f.read()
        except Exception:
            return "missing"

        # Check if it's an axiom
        if re.search(rf'\baxiom\s+{re.escape(thm_name)}\b', content):
            return "axiom"

        # Find the theorem/lemma declaration
        pattern = rf'(?:theorem|lemma)\s+{re.escape(thm_name)}\b'
        match = re.search(pattern, content)
        if not match:
            return "missing"

        # Check if the proof body contains 'sorry'
        start = match.start()
        # Find the next theorem/lemma/end or EOF
        next_decl = re.search(
            r'\n(?:theorem|lemma|axiom|end|namespace)\s',
            content[start + len(thm_name):])
        if next_decl:
            body = content[start:start + len(thm_name) + next_decl.start()]
        else:
            body = content[start:]

        if re.search(r'\bsorry\b', body):
            return "sorry"
        return "verified"

    def run_lake_build(self, lean_project_dir, q: queue.Queue):
        """Run `lake build` and report progress via the queue."""
        q.put("LEAN|BUILD|START")
        try:
            proc = subprocess.Popen(
                ["lake", "build"],
                cwd=lean_project_dir,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, bufsize=1,
            )
            for line in iter(proc.stdout.readline, ''):
                line = line.strip()
                if line:
                    q.put(f"LEAN|LOG|{line}")
            proc.wait()
            if proc.returncode == 0:
                self.build_ok = True
                q.put("LEAN|BUILD|OK")
            else:
                self.build_ok = False
                self.build_errors.append(f"lake build exited with code {proc.returncode}")
                q.put(f"LEAN|BUILD|FAIL|{proc.returncode}")
        except FileNotFoundError:
            self.build_ok = False
            self.build_errors.append("'lake' command not found — is elan installed?")
            q.put("LEAN|BUILD|FAIL|lake not found")
        except Exception as e:
            self.build_ok = False
            self.build_errors.append(str(e))
            q.put(f"LEAN|BUILD|FAIL|{e}")


# ═══════════════════════════════════════════════════════════════════════════════
#  CursesGUI
# ═══════════════════════════════════════════════════════════════════════════════

class CursesGUI:
    def __init__(self, stdscr, args):
        self.stdscr = stdscr
        self.args = args
        curses.curs_set(0)
        self.stdscr.nodelay(True)
        self.stdscr.timeout(int(1000 / REFRESH_HZ))

        # ── Colors ──────────────────────────────────────────────────────
        curses.start_color()
        curses.use_default_colors()
        curses.init_pair(1, curses.COLOR_GREEN,   -1)
        curses.init_pair(2, curses.COLOR_YELLOW,  -1)
        curses.init_pair(3, curses.COLOR_CYAN,    -1)
        curses.init_pair(4, curses.COLOR_MAGENTA, -1)
        curses.init_pair(5, curses.COLOR_BLACK, curses.COLOR_CYAN)
        curses.init_pair(6, curses.COLOR_RED,     -1)
        curses.init_pair(7, curses.COLOR_WHITE,   -1)
        curses.init_pair(8, curses.COLOR_GREEN,  curses.COLOR_BLACK)
        curses.init_pair(9, curses.COLOR_CYAN,   curses.COLOR_BLACK)

        self.C_GREEN   = curses.color_pair(1)
        self.C_YELLOW  = curses.color_pair(2)
        self.C_CYAN    = curses.color_pair(3)
        self.C_MAGENTA = curses.color_pair(4)
        self.C_HEADER  = curses.color_pair(5) | curses.A_BOLD
        self.C_RED     = curses.color_pair(6)
        self.C_WHITE   = curses.color_pair(7)
        self.C_PFILL   = curses.color_pair(8)
        self.C_Z3      = curses.color_pair(9)
        self.C_LABEL   = curses.color_pair(3) | curses.A_BOLD
        self.C_BOLD    = curses.color_pair(7) | curses.A_BOLD

        self.queue = queue.Queue()
        self.log_lines = []

        # ── Bounds ──────────────────────────────────────────────────────
        self.bound_min = args.min
        self.bound_max = args.max
        self.sieve_limit = args.sieve_limit
        self.max_exponent = args.max_exponent
        self.prefix_stop = args.prefix_stop
        self.bound_history = []   # list of (min, max, result_str, elapsed)
        self.current_run = 0

        # ── Engine State ────────────────────────────────────────────────
        self.phase_num       = "0"
        self.phase_text      = "Initializing..."
        self.status_text     = "Waiting for Lean build..."
        self.eta_text        = "—"
        self.rate_text       = "—"
        self.processed_text  = "0"
        self.progress_pct    = 0.0
        self.phase_start     = time.time()
        self.global_start    = time.time()

        # Domain stats
        self.target_bound      = f"10^{self.bound_min} < N < 10^{self.bound_max}"
        self.target_bound_min  = str(self.bound_min)
        self.target_bound_max  = str(self.bound_max)
        self.verified_floor    = VERIFIED_BASELINE
        self.retained_comps    = "—"
        self.pruned_comps      = "—"
        self.qp_found          = 0

        # Z3 / CDCL stats
        self.z3_initialized    = False
        self.z3_prune_hits     = 0
        self.abundance_pruned  = 0
        self.conflicts_learned = 0
        self.ray_pruned        = 0
        self.overflow_count    = 0

        # Lean
        self.script_dir = os.path.dirname(os.path.abspath(__file__))
        self.lean_project = os.path.normpath(
            os.path.join(self.script_dir, "..", "lean4-proofs"))
        self.lean_status = LeanProofStatus(self.lean_project)
        self.lean_initialized  = False
        self.show_lean_overlay = False

        # Active primes
        self.active_primes_str = "—"
        self.active_primes_cnt = 0

        # Throughput
        self.throughput_hist   = []
        self.last_throughput_t = time.time()
        self.last_processed_n  = 0

        self.is_indeterminate  = False
        self.finished          = False
        self.running           = True
        self.awaiting_rerun    = False

        # ── Launch ──────────────────────────────────────────────────────
        threading.Thread(target=self._run_pipeline, daemon=True).start()
        self._draw_loop()

    # ═══════════════════════════════════════════════════════════════════
    #  Full pipeline: Lean build → Lean scan → Rust engine
    # ═══════════════════════════════════════════════════════════════════

    def _run_pipeline(self):
        """Orchestrate the full Lean+Rust pipeline."""
        while self.running:
            self.finished = False
            self.awaiting_rerun = False
            self.current_run += 1
            run_start = time.time()

            # Phase 0a: Lean Build
            if not self.args.skip_lean_build:
                self.queue.put("PROGRESS|PHASE|0|Lean 4 Build & Verification")
                self.lean_status.run_lake_build(self.lean_project, self.queue)
            else:
                self.lean_status.build_ok = True
                self.queue.put("LEAN|BUILD|SKIPPED")

            # Phase 0b: Scan Lean proofs
            self.lean_status.scan()
            self.queue.put(f"LEAN|SCAN|{self.lean_status.sorry_count}|{self.lean_status.axiom_count}")

            # Phase 1-4: Rust engine
            if self.lean_status.build_ok is not False:
                self._run_engine(not self.args.debug)
            else:
                self.queue.put("__ERROR__|Lean build failed — cannot launch Rust engine")

            elapsed = time.time() - run_start
            result = "✓ Complete" if self.finished else "✗ Failed/Aborted"
            self.bound_history.append(
                (self.bound_min, self.bound_max, result, elapsed))
            if self.finished:
                self.verified_floor = f"10^{self.bound_max} (this session)"

            if not self.running:
                break

            # Auto-raise or wait
            if self.args.auto_raise and self.finished:
                self.bound_min = self.bound_max
                self.bound_max += self.args.raise_step
                self.target_bound = f"10^{self.bound_min} < N < 10^{self.bound_max}"
                self._log(f"▲ Auto-raising bounds → 10^{self.bound_min} < N < 10^{self.bound_max}", "phase")
                # Reset stats for next run
                self._reset_engine_stats()
                continue
            else:
                self.awaiting_rerun = True
                # Block until user presses 'r' or 'q'
                while self.running and self.awaiting_rerun:
                    time.sleep(0.1)
                if not self.running:
                    break
                self._reset_engine_stats()

    def _reset_engine_stats(self):
        self.z3_prune_hits = 0
        self.abundance_pruned = 0
        self.conflicts_learned = 0
        self.ray_pruned = 0
        self.overflow_count = 0
        self.progress_pct = 0.0
        self.processed_text = "0"
        self.throughput_hist = []
        self.retained_comps = "—"
        self.pruned_comps = "—"
        self.target_bound = f"10^{self.bound_min} < N < 10^{self.bound_max}"

    # ═══════════════════════════════════════════════════════════════════
    #  Engine subprocess + log writer
    # ═══════════════════════════════════════════════════════════════════

    def _run_engine(self, release: bool):
        cmd = ["cargo", "run"]
        if release:
            cmd.append("--release")

        log_path = os.path.join(self.script_dir, "engine_trace.log")
        last_log_time = 0.0
        log_buffer = []

        try:
            log_file = open(log_path, "a")
            log_file.write(f"\n═══ Run #{self.current_run} — {time.ctime()} ═══\n")
            log_file.write(f"    Bounds: 10^{self.bound_min} < N < 10^{self.bound_max}\n")
            log_file.write(f"    Command: {' '.join(cmd)}\n\n")
            log_file.flush()

            env = os.environ.copy()
            env["RUST_BACKTRACE"] = "1"
            env["UALBF_TARGET_MIN_LOG10"] = str(self.bound_min)
            env["UALBF_TARGET_MAX_LOG10"] = str(self.bound_max)
            env["UALBF_SIEVE_LIMIT"] = str(self.sieve_limit)
            env["UALBF_MAX_EXPONENT"] = str(self.max_exponent)
            env["UALBF_PREFIX_STOP_THRESHOLD"] = str(self.prefix_stop)

            process = subprocess.Popen(
                cmd, cwd=self.script_dir,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, bufsize=1, env=env,
            )

            for raw_line in iter(process.stdout.readline, ''):
                if not self.running:
                    process.terminate()
                    break
                line = raw_line.strip()
                if not line:
                    continue
                self.queue.put(line)

                # ── Log throttling ──────────────────────────────────────
                now = time.time()
                is_important = (
                    line.startswith("PROGRESS|PHASE|")
                    or line.startswith("PROGRESS|DONE|")
                    or "QUASIPERFECT" in line
                    or "Error" in line
                    or "panic" in line.lower()
                    or "=== UALBF" in line
                    or "Z3 CDCL" in line
                    or "DFS complete" in line
                    or line.startswith("Retained:")
                    or line.startswith("Sieve:")
                )

                if is_important:
                    if log_buffer:
                        summary = self._summarize_buffer(log_buffer)
                        ts = time.strftime("[%H:%M:%S]")
                        log_file.write(f"{ts} [BATCH] {summary}\n")
                        log_buffer.clear()
                    ts = time.strftime("[%Y-%m-%d %H:%M:%S]")
                    log_file.write(f"{ts} {line}\n")
                    log_file.flush()
                    last_log_time = now
                elif now - last_log_time >= LOG_THROTTLE_SEC:
                    if log_buffer:
                        summary = self._summarize_buffer(log_buffer)
                        ts = time.strftime("[%H:%M:%S]")
                        log_file.write(f"{ts} [BATCH] {summary}\n")
                        log_buffer.clear()
                        log_file.flush()
                    last_log_time = now
                else:
                    log_buffer.append(line)

            process.wait()

            if log_buffer:
                summary = self._summarize_buffer(log_buffer)
                ts = time.strftime("[%H:%M:%S]")
                log_file.write(f"{ts} [BATCH] {summary}\n")

            if process.returncode == 0:
                self.queue.put("__SUCCESS_EXIT__")
                log_file.write(f"\n[{time.strftime('%H:%M:%S')}] ✓ Engine exited cleanly (code 0)\n")
            else:
                self.queue.put(f"__CRASH_EXIT__|{process.returncode}")
                log_file.write(f"\n[{time.strftime('%H:%M:%S')}] ✗ Engine CRASHED (exit code {process.returncode})\n")

            log_file.close()

        except Exception as e:
            self.queue.put(f"__ERROR__|{e}")

    @staticmethod
    def _summarize_buffer(buf):
        n = len(buf)
        updates = [l for l in buf if l.startswith("PROGRESS|UPDATE|")]
        others  = [l for l in buf if not l.startswith("PROGRESS|UPDATE|")]
        parts = []
        if updates:
            last = updates[-1]
            parts.append(f"{len(updates)} progress ticks")
            m = re.search(r'Prefixes:\s*([\d,]+)', last)
            if m: parts.append(f"prefixes={m.group(1)}")
            m = re.search(r'Z3Pruned:\s*([\d,]+)', last)
            if m: parts.append(f"z3={m.group(1)}")
        if others:
            for o in others[:3]:
                parts.append(o[:80])
            if len(others) > 3:
                parts.append(f"...+{len(others)-3} more")
        return " | ".join(parts) if parts else f"{n} lines"

    # ═══════════════════════════════════════════════════════════════════
    #  Message processing
    # ═══════════════════════════════════════════════════════════════════

    def _process_queue(self):
        while not self.queue.empty():
            try:
                line = self.queue.get_nowait()
            except queue.Empty:
                break

            # ── Lean messages ───────────────────────────────────────────
            if line.startswith("LEAN|"):
                self._parse_lean_msg(line)
                continue

            # ── Internal control messages ───────────────────────────────
            if line == "__SUCCESS_EXIT__":
                self._log("✓ Engine process exited gracefully.", "success")
                self.finished = True
                continue
            if line.startswith("__CRASH_EXIT__|"):
                code = line.split("|")[1]
                self._log(f"✗ Engine CRASHED — exit code {code}", "error")
                self.status_text = f"CRASHED (exit code {code})"
                continue
            if line.startswith("__ERROR__|"):
                msg = line.split("|", 1)[1]
                self._log(f"✗ {msg}", "error")
                continue

            # ── PROGRESS protocol ───────────────────────────────────────
            if line.startswith("PROGRESS|"):
                self._parse_progress(line)
                continue

            # ── Unstructured engine output ──────────────────────────────
            self._parse_unstructured(line)

    def _parse_lean_msg(self, line):
        parts = line.split("|")
        if len(parts) < 3:
            return
        msg_type = parts[1]
        if msg_type == "BUILD":
            sub = parts[2]
            if sub == "START":
                self.phase_num = "0"
                self.phase_text = "📐 Phase 0: Lean 4 Build"
                self.is_indeterminate = True
                self.status_text = "Running lake build..."
                self._log("📐 Starting Lean 4 build (lake build)...", "phase")
            elif sub == "OK":
                self._log("✓ Lean 4 build succeeded", "success")
                self.lean_initialized = True
            elif sub == "SKIPPED":
                self._log("⏭ Lean build skipped (--skip-lean-build)", "info")
                self.lean_initialized = True
            elif sub.startswith("FAIL"):
                reason = parts[3] if len(parts) > 3 else "unknown"
                self._log(f"✗ Lean build FAILED: {reason}", "error")
        elif msg_type == "LOG":
            text = "|".join(parts[2:])
            self.status_text = text[:120]
            # Only log interesting lines
            if "error" in text.lower() or "warning" in text.lower() or "Building" in text:
                self._log(f"  {text[:100]}", "info")
        elif msg_type == "SCAN":
            sorry_n = int(parts[2]) if len(parts) > 2 else 0
            axiom_n = int(parts[3]) if len(parts) > 3 else 0
            if sorry_n > 0:
                self._log(f"⚠ Lean scan: {sorry_n} sorry, {axiom_n} axiom(s)", "phase")
            else:
                self._log(f"✓ Lean scan: 0 sorry, {axiom_n} axiom(s)", "success")

    def _parse_progress(self, line):
        parts = line.split("|")
        if len(parts) < 4:
            return
        msg_type = parts[1]

        if msg_type == "PHASE":
            self.phase_num  = parts[2]
            phase_desc      = parts[3] if len(parts) > 3 else ""
            icon = PHASE_ICONS.get(self.phase_num, "⚙ ")
            self.phase_text = f"{icon} Phase {self.phase_num}: {phase_desc}"
            self.progress_pct   = 0.0
            self.phase_start    = time.time()
            self.eta_text       = "Calculating..."
            self.rate_text      = "—"
            self.is_indeterminate = False
            self._log(f"▶ Started Phase {self.phase_num}: {phase_desc}", "phase")

        elif msg_type == "UPDATE":
            if len(parts) >= 7:
                current_prefixes = float(parts[2])
                total_weight     = float(parts[3])
                completed_weight = float(parts[4])
                pruned           = int(parts[5])
                message          = parts[6]
                self.ray_pruned = pruned
                self.processed_text = f"{int(current_prefixes):,}"
                self._parse_update_message(message)
                elapsed = time.time() - self.phase_start
                rate = current_prefixes / elapsed if elapsed > 1 else 0
                self.rate_text = f"{rate:,.0f} nodes/s"
                now = time.time()
                if now - self.last_throughput_t >= 1.0:
                    delta_n = current_prefixes - self.last_processed_n
                    delta_t = now - self.last_throughput_t
                    inst_rate = delta_n / delta_t if delta_t > 0 else 0
                    self.throughput_hist.append(inst_rate)
                    if len(self.throughput_hist) > 60:
                        self.throughput_hist.pop(0)
                    self.last_throughput_t = now
                    self.last_processed_n = current_prefixes
                if total_weight > 0:
                    self.is_indeterminate = False
                    self.progress_pct = (completed_weight / total_weight) * 100
                    branch_rate = completed_weight / elapsed if elapsed > 1 else 0
                    if branch_rate > 0:
                        remaining = (total_weight - completed_weight) / branch_rate
                        self.eta_text = f"~{timedelta(seconds=int(remaining))} (heuristic)"
                    else:
                        self.eta_text = "Calculating..."
                else:
                    self.is_indeterminate = True
                    self.progress_pct = (elapsed * 20) % 100
                    self.eta_text = "Indeterminate"
                self.status_text = message[:120]

            elif len(parts) >= 5:
                current = float(parts[2])
                total   = float(parts[3])
                message = parts[4] if len(parts) > 4 else ""
                self.processed_text = f"{int(current):,}"
                self.status_text = message[:120]
                elapsed = time.time() - self.phase_start
                rate = current / elapsed if elapsed > 1 else 0
                self.rate_text = f"{rate:,.0f} primes/s"
                if total > 0:
                    self.is_indeterminate = False
                    self.progress_pct = (current / total) * 100
                    if rate > 0:
                        remaining = (total - current) / rate
                        self.eta_text = f"~{timedelta(seconds=int(remaining))}"
                    else:
                        self.eta_text = "Calculating..."
                else:
                    self.is_indeterminate = True
                    self.progress_pct = (elapsed * 20) % 100
                    self.eta_text = "Indeterminate"

        elif msg_type == "DONE":
            self.phase_text = "✓ Finished"
            self.status_text = parts[4] if len(parts) > 4 else "Complete"
            self.progress_pct = 100.0
            self.eta_text = "Done"
            self.rate_text = "—"
            self.is_indeterminate = False
            self.finished = True
            self._log(f"✓ {self.status_text}", "success")

    def _parse_update_message(self, msg):
        m = re.search(r'P-Active:\s*(.+?)\s*\|', msg)
        if m:
            raw = m.group(1).strip()
            self.active_primes_str = raw
            cnt = re.search(r'\((\d+)\s*total\)', raw)
            if cnt:
                self.active_primes_cnt = int(cnt.group(1))
            else:
                self.active_primes_cnt = len([x for x in raw.split(',') if x.strip().isdigit()])
        m = re.search(r'AbPruned:\s*([\d,]+)', msg)
        if m: self.abundance_pruned = int(m.group(1).replace(',', ''))
        m = re.search(r'Z3Pruned:\s*([\d,]+)', msg)
        if m: self.z3_prune_hits = int(m.group(1).replace(',', ''))
        m = re.search(r'Conflicts:\s*([\d,]+)', msg)
        if m: self.conflicts_learned = int(m.group(1).replace(',', ''))

    def _parse_unstructured(self, line):
        if "=== UALBF Engine Initializing ===" in line:
            self.lean_initialized = True
            self.status_text = "Engine initializing..."
            self._log("⚙ Engine process started", "phase")
            return

        m = re.match(r'Target Bound:\s*10\^(\d+)\s*<\s*N\s*<\s*10\^(\d+)', line)
        if m:
            self.target_bound_min = m.group(1)
            self.target_bound_max = m.group(2)
            self.target_bound = f"10^{m.group(1)} < N < 10^{m.group(2)}"
            self._log(f"🎯 {self.target_bound}", "info")
            return

        if re.match(r'Sieve:', line):
            self._log(f"⚙ {line}", "info")
            return

        if "Z3 CDCL pruner initialized" in line:
            self.z3_initialized = True
            self._log("🔒 Z3 CDCL pruner active", "phase")
            return

        m = re.match(r'Retained:\s*([\d,]+),\s*Pruned:\s*([\d,]+)', line)
        if m:
            self.retained_comps = m.group(1)
            self.pruned_comps   = m.group(2)
            self._log(f"⚗  Sieve: {self.retained_comps} retained, {self.pruned_comps} pruned", "info")
            return

        m = re.match(r'DFS complete\.\s*Abundance-pruned:\s*(\d+)\s*\|\s*Z3-pruned:\s*(\d+)\s*\|\s*Conflicts learned:\s*(\d+)', line)
        if m:
            self.abundance_pruned  = int(m.group(1))
            self.z3_prune_hits     = int(m.group(2))
            self.conflicts_learned = int(m.group(3))
            self._log(f"🌳 DFS complete: ab_pruned={m.group(1)} z3={m.group(2)} conflicts={m.group(3)}", "success")
            return

        if "QUASIPERFECT NUMBER FOUND" in line:
            self.qp_found += 1
            self._log(f"████ {line} ████", "qp")
            return

        if line.startswith("overflow:"):
            self.overflow_count += 1
            return

        self._log(line[:120], "info")

    def _log(self, text, level="info"):
        ts = time.strftime("%H:%M:%S")
        self.log_lines.append((ts, text, level))
        if len(self.log_lines) > MAX_LOG_LINES:
            self.log_lines.pop(0)

    # ═══════════════════════════════════════════════════════════════════
    #  Rendering
    # ═══════════════════════════════════════════════════════════════════

    def _draw_loop(self):
        while self.running:
            self._process_queue()
            self._render()
            try:
                c = self.stdscr.getch()
                if c == ord('q') or c == ord('Q'):
                    self.running = False
                elif c == ord('r') or c == ord('R'):
                    if self.awaiting_rerun:
                        self.bound_min = self.bound_max
                        self.bound_max += self.args.raise_step
                        self._log(f"▲ Raising bounds → 10^{self.bound_min} < N < 10^{self.bound_max}", "phase")
                        self.awaiting_rerun = False
                elif c == ord('l') or c == ord('L'):
                    self.show_lean_overlay = not self.show_lean_overlay
                elif c == curses.KEY_RESIZE:
                    self.stdscr.clear()
            except curses.error:
                pass

    def _render(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()

        if h < 24 or w < 70:
            safe_addstr(self.stdscr, 0, 0, f"Terminal too small ({w}×{h}). Need ≥70×24.", self.C_RED)
            self.stdscr.refresh()
            return

        y = 0

        # ── ASCII Header ───────────────────────────────────────────────
        for i, art_line in enumerate(HEADER_ART):
            x = max(0, (w - len(art_line)) // 2)
            safe_addstr(self.stdscr, y + i, x, art_line, self.C_CYAN | curses.A_BOLD)
        y += len(HEADER_ART) + 1

        # ── Lean Overlay ───────────────────────────────────────────────
        if self.show_lean_overlay:
            y = self._render_lean_overlay(y, w)
        else:
            # Show compact Lean status in header area
            lean_sym = "✓" if self.lean_status.build_ok else ("✗" if self.lean_status.build_ok is False else "…")
            lean_col = self.C_GREEN if self.lean_status.build_ok else (self.C_RED if self.lean_status.build_ok is False else self.C_YELLOW)
            sorry_str = f"  sorry:{self.lean_status.sorry_count} axiom:{self.lean_status.axiom_count}" if self.lean_status.theorems else ""
            safe_addstr(self.stdscr, y, 1, f"Lean [{lean_sym}]{sorry_str}  (press 'l' for details)", lean_col)
            y += 1

        # ── Main Dashboard Box ─────────────────────────────────────────
        panel_x = 1
        panel_w = w - 2
        panel_h = 14
        self._draw_box(y, panel_x, panel_w, panel_h, f"Engine Dashboard — Run #{self.current_run}", self.C_CYAN)

        row = y + 1
        self._label_value(row, panel_x + 2, "Phase      ", self.phase_text, self.C_BOLD, panel_w)
        row += 1
        status_color = self.C_RED | curses.A_BOLD if "CRASH" in self.status_text else self.C_YELLOW | curses.A_BOLD
        self._label_value(row, panel_x + 2, "Status     ", self.status_text[:panel_w - 20], status_color, panel_w)

        row += 1
        safe_addstr(self.stdscr, row, panel_x, "├" + "─" * (panel_w - 2) + "┤", self.C_CYAN)

        row += 1
        uptime = str(timedelta(seconds=int(time.time() - self.global_start)))
        self._label_value(row, panel_x + 2, "Uptime     ", uptime, self.C_WHITE, panel_w)
        row += 1
        self._label_value(row, panel_x + 2, "Processed  ", self.processed_text, self.C_WHITE, panel_w)
        row += 1
        self._label_value(row, panel_x + 2, "Throughput ", self.rate_text, self.C_WHITE, panel_w)
        row += 1
        self._label_value(row, panel_x + 2, "ETA        ", self.eta_text, self.C_YELLOW, panel_w)

        col2 = panel_x + max(38, panel_w // 2)
        stat_row = y + 4
        self._label_value(stat_row, col2, "Verified ≤", self.verified_floor, self.C_GREEN, panel_w)
        stat_row += 1
        self._label_value(stat_row, col2, "Target    ", self.target_bound, self.C_MAGENTA | curses.A_BOLD, panel_w)
        stat_row += 1
        self._label_value(stat_row, col2, "Retained  ", self.retained_comps, self.C_WHITE, panel_w)
        stat_row += 1
        self._label_value(stat_row, col2, "Sieve ✗   ", self.pruned_comps, self.C_YELLOW, panel_w)
        stat_row += 1
        qp_color = self.C_GREEN | curses.A_BOLD if self.qp_found > 0 else self.C_WHITE
        self._label_value(stat_row, col2, "QP Found  ", str(self.qp_found), qp_color, panel_w)

        row += 1
        safe_addstr(self.stdscr, row, panel_x, "├" + "─" * (panel_w - 2) + "┤", self.C_CYAN)

        row += 1
        total_pruned = self.abundance_pruned + self.z3_prune_hits + self.ray_pruned
        prune_strs = [
            f"AbundancePrune: {self.abundance_pruned:,}",
            f"Z3/CDCL: {self.z3_prune_hits:,}",
            f"Conflicts: {self.conflicts_learned:,}",
            f"RayCast✗: {self.ray_pruned:,}",
            f"Total: {total_pruned:,}",
        ]
        prune_line = "  │  ".join(prune_strs)
        safe_addstr(self.stdscr, row, panel_x + 2, prune_line[:panel_w - 4], self.C_MAGENTA)

        row += 1
        active_line = f"Active Primes ({self.active_primes_cnt}): {self.active_primes_str}"
        safe_addstr(self.stdscr, row, panel_x + 2, active_line[:panel_w - 4], self.C_CYAN)

        row += 1
        lean_sym = "✓" if self.lean_initialized else "…"
        z3_sym   = "✓" if self.z3_initialized   else "…"
        lean_col = self.C_GREEN if self.lean_initialized else self.C_YELLOW
        z3_col   = self.C_GREEN if self.z3_initialized   else self.C_YELLOW
        safe_addstr(self.stdscr, row, panel_x + 2, f"Lean FFI [{lean_sym}]", lean_col)
        safe_addstr(self.stdscr, row, panel_x + 18, f"Z3 CDCL [{z3_sym}]", z3_col)
        safe_addstr(self.stdscr, row, panel_x + 33, "LLL ≡ rug/MPFR [W4]", self.C_CYAN)

        # ── Progress Bar ───────────────────────────────────────────────
        y_bar = y + panel_h
        bar_w = panel_w - 12
        if bar_w > 10:
            if self.is_indeterminate:
                pos = int((self.progress_pct / 100.0) * max(1, bar_w - 6))
                bar = "─" * pos + "▓▓▓▓" + "─" * max(0, bar_w - 4 - pos)
                bar_color = self.C_YELLOW
                pct_str = " ···  "
            else:
                filled = int((self.progress_pct / 100.0) * bar_w)
                bar = "█" * filled + "░" * (bar_w - filled)
                bar_color = self.C_GREEN
                pct_str = f" {self.progress_pct:5.1f}%"
            safe_addstr(self.stdscr, y_bar, panel_x + 1, f" [{bar}]{pct_str}", bar_color)

        # ── Sparkline ──────────────────────────────────────────────────
        y_bar += 1
        if self.throughput_hist and bar_w > 10:
            spark_chars = " ▁▂▃▄▅▆▇█"
            hist = self.throughput_hist[-(panel_w - 20):]
            if hist:
                max_val = max(hist) if max(hist) > 0 else 1
                spark = "".join(spark_chars[int((v / max_val) * (len(spark_chars) - 1))] for v in hist)
                safe_addstr(self.stdscr, y_bar, panel_x + 2, "Throughput: ", self.C_LABEL)
                safe_addstr(self.stdscr, y_bar, panel_x + 14, spark[:panel_w - 16], self.C_GREEN)
            y_bar += 1

        # ── Bound History (if any previous runs) ──────────────────────
        if self.bound_history:
            y_bar += 1
            safe_addstr(self.stdscr, y_bar, panel_x + 2, "─── Bound History ───", self.C_MAGENTA | curses.A_BOLD)
            y_bar += 1
            for bmin, bmax, result, elapsed in self.bound_history[-3:]:
                elapsed_str = str(timedelta(seconds=int(elapsed)))
                entry = f"  10^{bmin}..10^{bmax}: {result} ({elapsed_str})"
                color = self.C_GREEN if "✓" in result else self.C_RED
                safe_addstr(self.stdscr, y_bar, panel_x + 2, entry[:panel_w - 4], color)
                y_bar += 1

        # ── Log Panel ──────────────────────────────────────────────────
        log_y = y_bar + 1
        log_x = 1
        log_w = w - 2
        log_h = h - log_y - 1
        if log_h < 3:
            log_h = 3

        self._draw_box(log_y, log_x, log_w, log_h, "Event Stream", self.C_MAGENTA)

        max_visible = log_h - 2
        visible = self.log_lines[-max_visible:] if max_visible > 0 else []
        for i, (ts, text, level) in enumerate(visible):
            color = self.C_WHITE
            if level == "error":   color = self.C_RED | curses.A_BOLD
            elif level == "success": color = self.C_GREEN
            elif level == "phase":   color = self.C_CYAN | curses.A_BOLD
            elif level == "qp":      color = self.C_GREEN | curses.A_BOLD
            entry = f"[{ts}] {text}"
            safe_addstr(self.stdscr, log_y + 1 + i, log_x + 1, entry[:log_w - 3], color)

        # ── Footer ─────────────────────────────────────────────────────
        footer_y = h - 1
        if self.awaiting_rerun:
            footer = " Search complete. Press 'r' to raise bounds & re-run, 'q' to quit. "
        elif self.finished:
            footer = " Search complete. Press 'q' to exit. "
        else:
            footer = " q=Quit  l=Lean  r=Raise "
        safe_addstr(self.stdscr, footer_y, 0, footer, self.C_HEADER)
        ts_str = time.strftime(" %H:%M:%S ")
        safe_addstr(self.stdscr, footer_y, max(0, w - len(ts_str) - 1), ts_str, self.C_HEADER)

        self.stdscr.refresh()

    def _render_lean_overlay(self, y, w):
        """Render the Lean proof status overlay panel."""
        panel_x = 1
        panel_w = w - 2
        panel_h = len(LEAN_THEOREMS) + 4
        self._draw_box(y, panel_x, panel_w, panel_h, "Lean 4 Proof Status (press 'l' to close)", self.C_MAGENTA)

        row = y + 1
        build_sym = {"✓": self.C_GREEN, "✗": self.C_RED, "…": self.C_YELLOW}
        bs = "✓" if self.lean_status.build_ok else ("✗" if self.lean_status.build_ok is False else "…")
        self._label_value(row, panel_x + 2, "lake build", bs, build_sym.get(bs, self.C_WHITE), panel_w)
        row += 1
        safe_addstr(self.stdscr, row, panel_x, "├" + "─" * (panel_w - 2) + "┤", self.C_MAGENTA)
        row += 1

        for thm_name, filename in LEAN_THEOREMS:
            status = self.lean_status.theorems.get(thm_name, "—")
            if status == "verified":
                sym, col = "✓ verified", self.C_GREEN
            elif status == "sorry":
                sym, col = "⚠ sorry", self.C_YELLOW | curses.A_BOLD
            elif status == "axiom":
                sym, col = "△ axiom", self.C_CYAN
            elif status == "missing":
                sym, col = "✗ missing", self.C_RED
            else:
                sym, col = "— unknown", self.C_WHITE
            label = f"{thm_name:<35s}"
            safe_addstr(self.stdscr, row, panel_x + 2, label, self.C_LABEL)
            safe_addstr(self.stdscr, row, panel_x + 38, sym, col)
            safe_addstr(self.stdscr, row, panel_x + 52, filename, self.C_WHITE)
            row += 1

        return y + panel_h

    # ═══════════════════════════════════════════════════════════════════
    #  Drawing helpers
    # ═══════════════════════════════════════════════════════════════════

    def _draw_box(self, y, x, w, h, title, color):
        safe_addstr(self.stdscr, y, x, "╭" + "─" * (w - 2) + "╮", color)
        for i in range(1, h - 1):
            safe_addstr(self.stdscr, y + i, x, "│", color)
            safe_addstr(self.stdscr, y + i, x + w - 1, "│", color)
        safe_addstr(self.stdscr, y + h - 1, x, "╰" + "─" * (w - 2) + "╯", color)
        safe_addstr(self.stdscr, y, x + 2, f" {title} ", color | curses.A_BOLD)

    def _label_value(self, y, x, label, value, value_color, panel_w):
        safe_addstr(self.stdscr, y, x, f"{label}: ", self.C_LABEL)
        safe_addstr(self.stdscr, y, x + len(label) + 2, str(value)[:panel_w - len(label) - 6], value_color)


# ═══════════════════════════════════════════════════════════════════════════════
#  Entry point
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    args = parse_args()
    curses.wrapper(lambda stdscr: CursesGUI(stdscr, args))
