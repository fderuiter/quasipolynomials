import curses
import subprocess
import threading
import queue
import sys
import time
from datetime import timedelta

class CursesGUI:
    def __init__(self, stdscr):
        self.stdscr = stdscr
        curses.curs_set(0) # Hide cursor
        self.stdscr.nodelay(1)
        
        curses.start_color()
        curses.use_default_colors()
        curses.init_pair(1, curses.COLOR_GREEN, -1)
        curses.init_pair(2, curses.COLOR_YELLOW, -1)
        curses.init_pair(3, curses.COLOR_CYAN, -1)
        curses.init_pair(4, curses.COLOR_MAGENTA, -1)
        curses.init_pair(5, curses.COLOR_BLACK, curses.COLOR_CYAN)
        
        self.queue = queue.Queue()
        self.log_lines = []
        
        self.phase_text = "Initializing..."
        self.status_text = "Waiting for engine to start..."
        self.eta_text = "--"
        self.rate_text = "--"
        self.processed_text = "0"
        self.progress_pct = 0.0
        self.phase_start_time = time.time()
        self.global_start_time = time.time()
        
        self.is_indeterminate = False
        
        self.running = True
        threading.Thread(target=self.run_engine, daemon=True).start()
        
        self.draw_loop()
        
    def run_engine(self):
        import os
        script_dir = os.path.dirname(os.path.abspath(__file__))
        cmd = ["cargo", "run", "--release"]
        try:
            process = subprocess.Popen(cmd, cwd=script_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
            for line in iter(process.stdout.readline, ''):
                if line:
                    self.queue.put(line.strip())
            process.wait()
            self.queue.put("PROGRESS|DONE|4|1|Engine Run Finished.")
        except Exception as e:
            self.queue.put(f"Error starting engine: {e}")
            
    def draw_loop(self):
        while self.running:
            # Process queue
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
                                # Smooth sweeping bar based on time
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
                else:
                    timestamp = time.strftime("%H:%M:%S")
                    self.log_lines.append(f"[{timestamp}] {line[:120]}")
                    if len(self.log_lines) > 100:
                        self.log_lines.pop(0)

            # Draw Interface
            self.stdscr.erase()
            height, width = self.stdscr.getmaxyx()
            
            if height < 15 or width < 50:
                self.stdscr.addstr(0, 0, "Terminal too small!")
                self.stdscr.refresh()
                time.sleep(0.1)
                continue
                
            # Draw Header Box
            header_str = " UALBF Computational Engine Tracker "
            self.stdscr.addstr(0, max(0, (width - len(header_str)) // 2), header_str, curses.color_pair(5) | curses.A_BOLD)
            
            # Draw Execution Panel
            panel_y = 1
            panel_x = 2
            panel_w = width - 4
            panel_h = 10
            
            # Top Border
            self.stdscr.addstr(panel_y, panel_x, "┌" + "─" * (panel_w - 2) + "┐")
            self.stdscr.addstr(panel_y, panel_x + 2, " Execution Metrics ", curses.color_pair(3) | curses.A_BOLD)
            
            # Middle Borders
            for i in range(1, panel_h - 1):
                self.stdscr.addstr(panel_y + i, panel_x, "│")
                self.stdscr.addstr(panel_y + i, panel_x + panel_w - 1, "│")
                
            # Bottom Border
            self.stdscr.addstr(panel_y + panel_h - 1, panel_x, "└" + "─" * (panel_w - 2) + "┘")
            
            # Content
            self.stdscr.addstr(panel_y + 1, panel_x + 2, f"Current Task : ", curses.color_pair(3) | curses.A_BOLD)
            self.stdscr.addstr(panel_y + 1, panel_x + 17, f"{self.phase_text}")
            
            self.stdscr.addstr(panel_y + 2, panel_x + 2, f"Status       : ", curses.color_pair(3) | curses.A_BOLD)
            self.stdscr.addstr(panel_y + 2, panel_x + 17, f"{self.status_text}", curses.color_pair(2))
            
            # Metrics
            global_elapsed = str(timedelta(seconds=int(time.time() - self.global_start_time)))
            self.stdscr.addstr(panel_y + 4, panel_x + 2, f"Uptime       : {global_elapsed}")
            self.stdscr.addstr(panel_y + 5, panel_x + 2, f"Processed    : {self.processed_text}")
            self.stdscr.addstr(panel_y + 6, panel_x + 2, f"Throughput   : {self.rate_text}")
            self.stdscr.addstr(panel_y + 7, panel_x + 2, f"ETA          : {self.eta_text}")
            
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
                self.stdscr.addstr(panel_y + 8, panel_x + 2, f"[{bar}]{pct_str}", color)
                
            # Logs Panel
            log_y = 12
            log_x = 2
            log_w = width - 4
            log_h = height - 13
            
            if log_h > 0:
                self.stdscr.addstr(log_y, log_x, "┌" + "─" * (log_w - 2) + "┐")
                self.stdscr.addstr(log_y, log_x + 2, " Live Engine Logs ", curses.color_pair(3) | curses.A_BOLD)
                for i in range(1, log_h - 1):
                    self.stdscr.addstr(log_y + i, log_x, "│")
                    self.stdscr.addstr(log_y + i, log_x + log_w - 1, "│")
                self.stdscr.addstr(log_y + log_h - 1, log_x, "└" + "─" * (log_w - 2) + "┘")
                
                max_log_lines = log_h - 2
                visible_logs = self.log_lines[-max_log_lines:] if max_log_lines > 0 else []
                for idx, log in enumerate(visible_logs):
                    self.stdscr.addstr(log_y + 1 + idx, log_x + 2, log[:log_w-4])
                
            self.stdscr.refresh()
            
            # Check for input
            try:
                c = self.stdscr.getch()
                if c == ord('q') or c == ord('Q'):
                    self.running = False
            except:
                pass
                
            time.sleep(0.05)

if __name__ == "__main__":
    curses.wrapper(CursesGUI)
