import curses
import subprocess
import threading
import queue
import sys
import time
import os
from datetime import timedelta

class CursesGUI:
    def __init__(self, stdscr):
        self.stdscr = stdscr
        curses.curs_set(0) # Hide cursor
        self.stdscr.nodelay(1)
        
        curses.start_color()
        curses.use_default_colors()
        
        # Color pairs
        # 1: Green, 2: Yellow, 3: Cyan, 4: Magenta
        # 5: Cyan bg for header, 6: Red, 7: Default/White
        curses.init_pair(1, curses.COLOR_GREEN, -1)
        curses.init_pair(2, curses.COLOR_YELLOW, -1)
        curses.init_pair(3, curses.COLOR_CYAN, -1)
        curses.init_pair(4, curses.COLOR_MAGENTA, -1)
        curses.init_pair(5, curses.COLOR_BLACK, curses.COLOR_CYAN)
        curses.init_pair(6, curses.COLOR_RED, -1)
        # Attempt to use white or default for text
        curses.init_pair(7, curses.COLOR_WHITE, -1) 
        
        self.queue = queue.Queue()
        self.log_lines = []
        
        # State variables
        self.phase_text = "Initializing..."
        self.status_text = "Waiting for engine to start..."
        self.eta_text = "--"
        self.rate_text = "--"
        self.processed_text = "0"
        self.progress_pct = 0.0
        self.phase_start_time = time.time()
        self.global_start_time = time.time()
        
        # Extracted Stats
        self.target_bound = "--"
        self.retained_components = "--"
        self.pruned_components = "--"
        self.quasiperfect_found = 0
        
        self.is_indeterminate = False
        self.running = True
        
        threading.Thread(target=self.run_engine, daemon=True).start()
        self.draw_loop()
        
    def run_engine(self):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        cmd = ["cargo", "run", "--release"]
        log_file_path = os.path.join(script_dir, "engine_trace.log")
        try:
            with open(log_file_path, "w") as f:
                f.write(f"=== UALBF Engine Trace Log: Run Started at {time.ctime()} ===\n")
            
            process = subprocess.Popen(cmd, cwd=script_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
            for line in iter(process.stdout.readline, ''):
                if line:
                    self.queue.put(line.strip())
                    with open(log_file_path, "a") as f:
                        f.write(line)
            process.wait()
            if process.returncode == 0:
                self.queue.put("SUCCESS_EXIT")
                with open(log_file_path, "a") as f:
                    f.write("\n[System] SUCCESS_EXIT\n")
            else:
                self.queue.put(f"PROGRESS|DONE|4|1|Engine Crashed! Exit code {process.returncode}")
                with open(log_file_path, "a") as f:
                    f.write(f"\n[System] CRASH: Exit code {process.returncode}\n")
        except Exception as e:
            self.queue.put(f"Error starting engine: {e}")
            
    def draw_loop(self):
        while self.running:
            # Process incoming queue messages
            while not self.queue.empty():
                line = self.queue.get()
                if line.startswith("PROGRESS|"):
                    parts = line.split("|")
                    if len(parts) >= 4:
                        msg_type = parts[1]
                        if msg_type == "PHASE":
                            self.phase_text = f"Phase {parts[2]}: {parts[3]}"
                            self.progress_pct = 0.0
                            self.phase_start_time = time.time()
                            self.eta_text = "Calculating..."
                            self.rate_text = "0 items/s"
                            self.log_lines.append(f"[*] Started {parts[3]}")
                        elif msg_type == "UPDATE":
                            current = float(parts[2])
                            total = float(parts[3])
                            self.status_text = parts[4] if len(parts) > 4 else ""
                            self.processed_text = f"{int(current):,}"
                            
                            elapsed = time.time() - self.phase_start_time
                            rate = current / elapsed if elapsed > 0 else 0
                            self.rate_text = f"{rate:,.1f} nodes/sec"
                            
                            if total > 0:
                                self.is_indeterminate = False
                                self.progress_pct = (current / total) * 100
                                if elapsed > 1.0 and current > 0:
                                    remaining = (total - current) / rate
                                    self.eta_text = str(timedelta(seconds=int(remaining)))
                            else:
                                self.is_indeterminate = True
                                sw_pct = (elapsed * 20) % 100 
                                self.progress_pct = sw_pct
                                self.eta_text = "Indeterminate (Unbounded Search)"
                        elif msg_type == "DONE":
                            self.phase_text = "Finished!"
                            self.status_text = parts[4] if len(parts) > 4 else "Complete"
                            self.progress_pct = 100.0
                            self.eta_text = "Done"
                            self.rate_text = "--"
                            self.is_indeterminate = False
                            self.log_lines.append(f"[*] Execution Complete. Press 'q' to exit.")
                elif line == "SUCCESS_EXIT":
                    self.log_lines.append(f"[*] Engine OS Process Exited Gracefully.")
                else:
                    # Parse custom engine logs for stats
                    if "Target Bound:" in line:
                        self.target_bound = line.split("Target Bound:")[-1].strip()
                    elif "Retained:" in line and "Pruned:" in line:
                        try:
                            # E.g., Retained: 25, Pruned: 400
                            parts = line.split(",")
                            self.retained_components = parts[0].split(":")[1].strip()
                            self.pruned_components = parts[1].split(":")[1].strip()
                        except: pass
                    elif "QUASIPERFECT NUMBER FOUND" in line:
                        self.quasiperfect_found += 1
                        
                    timestamp = time.strftime("%H:%M:%S")
                    self.log_lines.append(f"[{timestamp}] {line[:120]}")
                    if len(self.log_lines) > 200:
                        self.log_lines.pop(0)

            # Rendering
            self.stdscr.erase()
            height, width = self.stdscr.getmaxyx()
            
            if height < 20 or width < 60:
                self.stdscr.addstr(0, 0, f"Terminal must be at least 60x20. (Current: {width}x{height})", curses.color_pair(6))
                self.stdscr.refresh()
                time.sleep(0.1)
                continue
                
            # Header
            header_str = " UALBF Computational Engine "
            self.stdscr.attron(curses.color_pair(5) | curses.A_BOLD)
            self.stdscr.addstr(0, max(0, (width - len(header_str)) // 2), header_str)
            self.stdscr.attroff(curses.color_pair(5) | curses.A_BOLD)
            
            # --- Status & Statistics Panel ---
            panel_y = 2
            panel_x = 2
            panel_w = width - 4
            panel_h = 12
            
            # Box drawing wrapper
            def draw_box(y, x, w, h, title, color_pair):
                self.stdscr.addstr(y, x, "╭" + "─" * (w - 2) + "╮", color_pair)
                for i in range(1, h - 1):
                    self.stdscr.addstr(y + i, x, "│", color_pair)
                    self.stdscr.addstr(y + i, x + w - 1, "│", color_pair)
                self.stdscr.addstr(y + h - 1, x, "╰" + "─" * (w - 2) + "╯", color_pair)
                self.stdscr.addstr(y, x + 2, f" {title} ", color_pair | curses.A_BOLD)
                
            draw_box(panel_y, panel_x, panel_w, panel_h, "Engine Dashboard", curses.color_pair(3))
            
            # Phase and Status (Top secton)
            self.stdscr.addstr(panel_y + 1, panel_x + 2, "Current Task : ", curses.color_pair(3) | curses.A_BOLD)
            self.stdscr.addstr(panel_y + 1, panel_x + 17, f"{self.phase_text}", curses.color_pair(7))
            
            self.stdscr.addstr(panel_y + 2, panel_x + 2, "Status       : ", curses.color_pair(3) | curses.A_BOLD)
            self.stdscr.addstr(panel_y + 2, panel_x + 17, f"{self.status_text[:panel_w-20]}", curses.color_pair(2) | curses.A_BOLD)
            
            # Separator
            self.stdscr.addstr(panel_y + 3, panel_x, "├" + "─" * (panel_w - 2) + "┤", curses.color_pair(3))
            
            # Left Sub-Column (Performance)
            global_elapsed = str(timedelta(seconds=int(time.time() - self.global_start_time)))
            self.stdscr.addstr(panel_y + 4, panel_x + 2, "Uptime       :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 4, panel_x + 17, f"{global_elapsed}", curses.color_pair(7))
            
            self.stdscr.addstr(panel_y + 5, panel_x + 2, "Processed    :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 5, panel_x + 17, f"{self.processed_text}", curses.color_pair(7))
            
            self.stdscr.addstr(panel_y + 6, panel_x + 2, "Throughput   :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 6, panel_x + 17, f"{self.rate_text}", curses.color_pair(7))
            
            self.stdscr.addstr(panel_y + 7, panel_x + 2, "ETA          :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 7, panel_x + 17, f"{self.eta_text}", curses.color_pair(2))
            
            # Right Sub-Column (Domain Stats)
            col_x = panel_x + max(40, panel_w // 2)
            
            self.stdscr.addstr(panel_y + 4, col_x, "Target Bound :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 4, col_x + 15, f"{self.target_bound}", curses.color_pair(4) | curses.A_BOLD)
            
            self.stdscr.addstr(panel_y + 5, col_x, "Retained     :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 5, col_x + 15, f"{self.retained_components}", curses.color_pair(7))
            
            self.stdscr.addstr(panel_y + 6, col_x, "Pruned       :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 6, col_x + 15, f"{self.pruned_components}", curses.color_pair(2))
            
            qp_found_text_color = curses.color_pair(1) | curses.A_BOLD if self.quasiperfect_found > 0 else curses.color_pair(7)
            self.stdscr.addstr(panel_y + 7, col_x, "QP Found     :", curses.color_pair(3))
            self.stdscr.addstr(panel_y + 7, col_x + 15, f"{self.quasiperfect_found}", qp_found_text_color)
            
            # Separator
            self.stdscr.addstr(panel_y + 8, panel_x, "├" + "─" * (panel_w - 2) + "┤", curses.color_pair(3))
            
            # Progress Bar
            bar_width = panel_w - 14
            if bar_width > 10:
                if self.is_indeterminate:
                    pos = int((self.progress_pct / 100.0) * (bar_width - 8))
                    bar = "─" * pos + "[████]" + "─" * (bar_width - 6 - pos)
                    color = curses.color_pair(2)
                else:
                    filled = int((self.progress_pct / 100.0) * bar_width)
                    empty = bar_width - filled
                    bar = "█" * filled + "▒" * empty
                    color = curses.color_pair(1)
                
                pct_str = f" {self.progress_pct:5.1f}%" if not self.is_indeterminate else " Active "
                self.stdscr.addstr(panel_y + 9, panel_x + 2, f"[{bar}]{pct_str}", color)
                
            # --- Logs Panel ---
            log_y = panel_y + panel_h
            log_x = 2
            log_w = width - 4
            log_h = height - log_y - 1
            
            if log_h > 3:
                draw_box(log_y, log_x, log_w, log_h, "Live Event Stream", curses.color_pair(4))
                
                max_log_lines = log_h - 2
                visible_logs = self.log_lines[-max_log_lines:] if max_log_lines > 0 else []
                # Simple color coding for logs
                for idx, log in enumerate(visible_logs):
                    # Prevent writing off-screen by truncating strictly
                    safe_log = log[:log_w-4]
                    if "QUASIPERFECT NUMBER FOUND" in log:
                        self.stdscr.addstr(log_y + 1 + idx, log_x + 2, safe_log, curses.color_pair(1) | curses.A_BOLD)
                    elif "Error" in log or "Crashed" in log:
                        self.stdscr.addstr(log_y + 1 + idx, log_x + 2, safe_log, curses.color_pair(6) | curses.A_BOLD)
                    elif "Started" in log or "Complete" in log or "SUCCESS_EXIT" in log:
                        self.stdscr.addstr(log_y + 1 + idx, log_x + 2, safe_log, curses.color_pair(3))
                    else:
                        self.stdscr.addstr(log_y + 1 + idx, log_x + 2, safe_log, curses.color_pair(7))
                
            self.stdscr.refresh()
            
            # Loop delay and input
            try:
                c = self.stdscr.getch()
                if c == ord('q') or c == ord('Q'):
                    self.running = False
            except:
                pass
                
            time.sleep(0.05)

if __name__ == "__main__":
    curses.wrapper(CursesGUI)
