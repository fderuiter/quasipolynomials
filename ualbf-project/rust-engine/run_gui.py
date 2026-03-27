#!/usr/bin/env python3
"""
UALBF Engine — Curses Dashboard (v3)

A real-time terminal GUI for monitoring the UALBF quasiperfect number search
engine.  Displays live telemetry from all engine subsystems:

  • Phase 1  — Legendre–Cattaneo Sieve (cyclotomic factorization)
  • Phase 2  — Fused DFS Construction & Ray-Casting
  • Lean 4 FFI bridge status (σ, mod-inverse, mod-8 checks)
  • Z3 CDCL conflict-driven pruner stats (starvation + Zsigmondy traps)
  • LLL lattice module status (standalone Wave 4 Diophantine pruning)
  • Lock-free active-primes telemetry (AtomicU64 slot array)

The log file (engine_trace.log) is throttled to one summary line every
5 seconds to keep file sizes manageable during long runs.

Usage:
    python3 run_gui.py            # from the rust-engine/ directory
    python3 run_gui.py --release  # (default, same as above)
    python3 run_gui.py --debug    # run without --release

Keybindings:
    q / Q   — Quit the dashboard
"""

import curses
import subprocess
import threading
import queue
import sys
import time
import os
import re
from datetime import timedelta

# ═══════════════════════════════════════════════════════════════════════════════
#  Constants
# ═══════════════════════════════════════════════════════════════════════════════

REFRESH_HZ = 20          # UI refresh rate (frames per second)
LOG_THROTTLE_SEC = 5.0   # minimum interval between log file writes
MAX_LOG_LINES = 300       # scrollback buffer for the live event stream

PHASE_ICONS = {
    "1": "⚗ ",   # Sieve
    "2": "🌳",   # DFS + Ray-Cast (fused)
    "3": "⚡",   # Ray-Cast (standalone, legacy)
    "4": "🔒",   # Z3 verification
}

# ═══════════════════════════════════════════════════════════════════════════════
#  ASCII Header
# ═══════════════════════════════════════════════════════════════════════════════

HEADER_ART = [
    "╔═══════════════════════════════════════════════════════════════╗",
    "║   █ █  █▀█  █   █▀▄  █▀▀   Quasiperfect Number Search      ║",
    "║   █▄█  █▀█  █▄  █▀▄  █▀    Lean4 + Rust + Z3 Engine        ║",
    "╚═══════════════════════════════════════════════════════════════╝",
]

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
#  CursesGUI
# ═══════════════════════════════════════════════════════════════════════════════

class CursesGUI:
    def __init__(self, stdscr):
        self.stdscr = stdscr
        curses.curs_set(0)
        self.stdscr.nodelay(True)
        self.stdscr.timeout(int(1000 / REFRESH_HZ))

        # ── Colors ──────────────────────────────────────────────────────
        curses.start_color()
        curses.use_default_colors()
        curses.init_pair(1, curses.COLOR_GREEN,   -1)  # success / QP found
        curses.init_pair(2, curses.COLOR_YELLOW,  -1)  # warnings / ETA
        curses.init_pair(3, curses.COLOR_CYAN,    -1)  # labels / boxes
        curses.init_pair(4, curses.COLOR_MAGENTA, -1)  # domain stats
        curses.init_pair(5, curses.COLOR_BLACK, curses.COLOR_CYAN)  # header bar
        curses.init_pair(6, curses.COLOR_RED,     -1)  # errors
        curses.init_pair(7, curses.COLOR_WHITE,   -1)  # body text
        curses.init_pair(8, curses.COLOR_GREEN,  curses.COLOR_BLACK)  # progress fill
        curses.init_pair(9, curses.COLOR_CYAN,   curses.COLOR_BLACK)  # Z3 stats

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

        # ── State ───────────────────────────────────────────────────────
        self.phase_num       = "0"
        self.phase_text      = "Initializing..."
        self.status_text     = "Waiting for engine process..."
        self.eta_text        = "—"
        self.rate_text       = "—"
        self.processed_text  = "0"
        self.progress_pct    = 0.0
        self.phase_start     = time.time()
        self.global_start    = time.time()

        # Domain stats
        self.target_bound      = "—"
        self.target_bound_min  = "—"
        self.target_bound_max  = "—"
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

        # Lean FFI
        self.lean_initialized  = False

        # Active primes
        self.active_primes_str = "—"
        self.active_primes_cnt = 0

        # Throughput history for sparkline
        self.throughput_hist   = []
        self.last_throughput_t = time.time()
        self.last_processed_n  = 0

        self.is_indeterminate  = False
        self.finished          = False
        self.running           = True

        # ── Launch ──────────────────────────────────────────────────────
        use_release = "--debug" not in sys.argv
        threading.Thread(target=self._run_engine, args=(use_release,), daemon=True).start()
        self._draw_loop()

    # ═══════════════════════════════════════════════════════════════════
    #  Engine subprocess + log writer
    # ═══════════════════════════════════════════════════════════════════

    def _run_engine(self, release: bool):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        cmd = ["cargo", "run"]
        if release:
            cmd.append("--release")

        log_path = os.path.join(script_dir, "engine_trace.log")
        last_log_time = 0.0
        log_buffer = []

        try:
            log_file = open(log_path, "w")
            log_file.write(f"═══ UALBF Engine Trace — Started {time.ctime()} ═══\n")
            log_file.write(f"    Command: {' '.join(cmd)}\n\n")
            log_file.flush()

            env = os.environ.copy()
            env["RUST_BACKTRACE"] = "1"

            process = subprocess.Popen(
                cmd, cwd=script_dir,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, bufsize=1, env=env,
            )

            for raw_line in iter(process.stdout.readline, ''):
                if not raw_line:
                    continue
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
                )

                if is_important:
                    # Flush buffer first
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
                    # Write buffered summary
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

            # Flush remaining buffer
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
        """Summarize a batch of buffered lines into a compact log entry."""
        n = len(buf)
        # Count update lines
        updates = [l for l in buf if l.startswith("PROGRESS|UPDATE|")]
        others  = [l for l in buf if not l.startswith("PROGRESS|UPDATE|")]

        parts = []
        if updates:
            # Extract last update's key stats
            last = updates[-1]
            parts.append(f"{len(updates)} progress ticks")
            # Try to pull stats from the message portion
            m = re.search(r'Prefixes:\s*([\d,]+)', last)
            if m:
                parts.append(f"prefixes={m.group(1)}")
            m = re.search(r'Z3Pruned:\s*([\d,]+)', last)
            if m:
                parts.append(f"z3={m.group(1)}")
            m = re.search(r'Conflicts:\s*([\d,]+)', last)
            if m:
                parts.append(f"conflicts={m.group(1)}")
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
        """Drain all pending messages and update state."""
        while not self.queue.empty():
            try:
                line = self.queue.get_nowait()
            except queue.Empty:
                break

            # ── Internal control messages ───────────────────────────────
            if line == "__SUCCESS_EXIT__":
                self._log("✓ Engine process exited gracefully.", "success")
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
                # Full fused update: PROGRESS|UPDATE|count|total_w|comp_w|pruned|message
                current_prefixes = float(parts[2])
                total_weight     = float(parts[3])
                completed_weight = float(parts[4])
                pruned           = int(parts[5])
                message          = parts[6]

                self.ray_pruned = pruned
                self.processed_text = f"{int(current_prefixes):,}"

                # Parse the structured message for Z3 stats & active primes
                self._parse_update_message(message)

                # Throughput
                elapsed = time.time() - self.phase_start
                rate = current_prefixes / elapsed if elapsed > 1 else 0
                self.rate_text = f"{rate:,.0f} nodes/s"

                # Record throughput for sparkline
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

                # Progress & ETA (weighted)
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
                # Phase-1 sieve update: PROGRESS|UPDATE|current|total|msg
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
        """Extract stats from the structured message portion of a DFS UPDATE."""
        # P-Active: 3, 5, 7... (12 total) | Prefixes: 1,200,000 | AbPruned: 500 | Z3Pruned: 42 | Conflicts: 8
        m = re.search(r'P-Active:\s*(.+?)\s*\|', msg)
        if m:
            raw = m.group(1).strip()
            self.active_primes_str = raw
            # Try to extract count
            cnt = re.search(r'\((\d+)\s*total\)', raw)
            if cnt:
                self.active_primes_cnt = int(cnt.group(1))
            else:
                # Count comma-separated primes
                self.active_primes_cnt = len([x for x in raw.split(',') if x.strip().isdigit()])

        m = re.search(r'AbPruned:\s*([\d,]+)', msg)
        if m:
            self.abundance_pruned = int(m.group(1).replace(',', ''))

        m = re.search(r'Z3Pruned:\s*([\d,]+)', msg)
        if m:
            self.z3_prune_hits = int(m.group(1).replace(',', ''))

        m = re.search(r'Conflicts:\s*([\d,]+)', msg)
        if m:
            self.conflicts_learned = int(m.group(1).replace(',', ''))

    def _parse_unstructured(self, line):
        """Parse free-form engine output for stats and flags."""
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
            return  # suppress noisy overflow warnings from raycast

        # Fallback: just log it
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

        # ── Main Dashboard Box ─────────────────────────────────────────
        panel_x = 1
        panel_w = w - 2
        panel_h = 14
        self._draw_box(y, panel_x, panel_w, panel_h, "Engine Dashboard", self.C_CYAN)

        # Row 1: Phase & Status
        row = y + 1
        self._label_value(row, panel_x + 2, "Phase      ", self.phase_text, self.C_BOLD, panel_w)
        row += 1
        status_color = self.C_RED | curses.A_BOLD if "CRASH" in self.status_text else self.C_YELLOW | curses.A_BOLD
        self._label_value(row, panel_x + 2, "Status     ", self.status_text[:panel_w - 20], status_color, panel_w)

        # Separator
        row += 1
        safe_addstr(self.stdscr, row, panel_x, "├" + "─" * (panel_w - 2) + "┤", self.C_CYAN)

        # ── Left column: Performance ───────────────────────────────────
        row += 1
        uptime = str(timedelta(seconds=int(time.time() - self.global_start)))
        self._label_value(row, panel_x + 2, "Uptime     ", uptime, self.C_WHITE, panel_w)
        row += 1
        self._label_value(row, panel_x + 2, "Processed  ", self.processed_text, self.C_WHITE, panel_w)
        row += 1
        self._label_value(row, panel_x + 2, "Throughput ", self.rate_text, self.C_WHITE, panel_w)
        row += 1
        self._label_value(row, panel_x + 2, "ETA        ", self.eta_text, self.C_YELLOW, panel_w)

        # ── Right column: Domain & Pruning Stats ───────────────────────
        col2 = panel_x + max(38, panel_w // 2)
        stat_row = y + 4
        self._label_value(stat_row, col2, "Target    ", self.target_bound, self.C_MAGENTA | curses.A_BOLD, panel_w)
        stat_row += 1
        self._label_value(stat_row, col2, "Retained  ", self.retained_comps, self.C_WHITE, panel_w)
        stat_row += 1
        self._label_value(stat_row, col2, "Sieve ✗   ", self.pruned_comps, self.C_YELLOW, panel_w)
        stat_row += 1
        qp_color = self.C_GREEN | curses.A_BOLD if self.qp_found > 0 else self.C_WHITE
        self._label_value(stat_row, col2, "QP Found  ", str(self.qp_found), qp_color, panel_w)

        # ── Separator ──────────────────────────────────────────────────
        row += 1
        safe_addstr(self.stdscr, row, panel_x, "├" + "─" * (panel_w - 2) + "┤", self.C_CYAN)

        # ── Pruning Intelligence Row ───────────────────────────────────
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

        # ── Active Primes Row ──────────────────────────────────────────
        row += 1
        active_line = f"Active Primes ({self.active_primes_cnt}): {self.active_primes_str}"
        safe_addstr(self.stdscr, row, panel_x + 2, active_line[:panel_w - 4], self.C_CYAN)

        # ── Subsystem Status ───────────────────────────────────────────
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

        # ── Sparkline (throughput history) ──────────────────────────────
        y_bar += 1
        if self.throughput_hist and bar_w > 10:
            spark_chars = " ▁▂▃▄▅▆▇█"
            # Fit to available width
            hist = self.throughput_hist[-(panel_w - 20):]
            if hist:
                max_val = max(hist) if max(hist) > 0 else 1
                spark = ""
                for v in hist:
                    idx = int((v / max_val) * (len(spark_chars) - 1))
                    spark += spark_chars[idx]
                safe_addstr(self.stdscr, y_bar, panel_x + 2, "Throughput: ", self.C_LABEL)
                safe_addstr(self.stdscr, y_bar, panel_x + 14, spark[:panel_w - 16], self.C_GREEN)
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
            if level == "error":
                color = self.C_RED | curses.A_BOLD
            elif level == "success":
                color = self.C_GREEN
            elif level == "phase":
                color = self.C_CYAN | curses.A_BOLD
            elif level == "qp":
                color = self.C_GREEN | curses.A_BOLD
            elif level == "info":
                color = self.C_WHITE

            entry = f"[{ts}] {text}"
            safe_addstr(self.stdscr, log_y + 1 + i, log_x + 1, entry[:log_w - 3], color)

        # ── Footer ─────────────────────────────────────────────────────
        footer_y = h - 1
        if self.finished:
            footer = " Search complete. Press 'q' to exit. "
        else:
            footer = " q=Quit "
        safe_addstr(self.stdscr, footer_y, 0, footer, self.C_HEADER)
        # Right-justified timestamp
        ts_str = time.strftime(" %H:%M:%S ")
        safe_addstr(self.stdscr, footer_y, max(0, w - len(ts_str) - 1), ts_str, self.C_HEADER)

        self.stdscr.refresh()

    # ═══════════════════════════════════════════════════════════════════
    #  Drawing helpers
    # ═══════════════════════════════════════════════════════════════════

    def _draw_box(self, y, x, w, h, title, color):
        """Render a Unicode box with an inline title."""
        safe_addstr(self.stdscr, y, x, "╭" + "─" * (w - 2) + "╮", color)
        for i in range(1, h - 1):
            safe_addstr(self.stdscr, y + i, x, "│", color)
            safe_addstr(self.stdscr, y + i, x + w - 1, "│", color)
        safe_addstr(self.stdscr, y + h - 1, x, "╰" + "─" * (w - 2) + "╯", color)
        safe_addstr(self.stdscr, y, x + 2, f" {title} ", color | curses.A_BOLD)

    def _label_value(self, y, x, label, value, value_color, panel_w):
        """Render a 'Label : Value' pair."""
        safe_addstr(self.stdscr, y, x, f"{label}: ", self.C_LABEL)
        safe_addstr(self.stdscr, y, x + len(label) + 2, str(value)[:panel_w - len(label) - 6], value_color)


# ═══════════════════════════════════════════════════════════════════════════════
#  Entry point
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    curses.wrapper(CursesGUI)
