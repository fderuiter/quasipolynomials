import curses
import subprocess
import threading
import queue
import sys
import time

class CursesGUI:
    def __init__(self, stdscr):
        self.stdscr = stdscr
        curses.curs_set(0) # Hide cursor
        self.stdscr.nodelay(1)
        
        curses.start_color()
        curses.init_pair(1, curses.COLOR_GREEN, curses.COLOR_BLACK)
        curses.init_pair(2, curses.COLOR_YELLOW, curses.COLOR_BLACK)
        curses.init_pair(3, curses.COLOR_CYAN, curses.COLOR_BLACK)
        
        self.queue = queue.Queue()
        self.log_lines = []
        
        self.phase_text = "Initializing..."
        self.status_text = "Waiting for engine to start..."
        self.progress_pct = 0.0
        
        self.running = True
        threading.Thread(target=self.run_engine, daemon=True).start()
        
        self.draw_loop()
        
    def run_engine(self):
        import os
        script_dir = os.path.dirname(os.path.abspath(__file__))
        cmd = ["cargo", "run", "--release"]
        try:
            process = subprocess.Popen(cmd, cwd=script_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
            for line in process.stdout:
                self.queue.put(line.strip())
            process.wait()
            self.queue.put("PROGRESS|DONE|1|1|Engine Run Finished.")
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
                            self.log_lines.append(f"--- Started {parts[3]} ---")
                        elif msg_type == "UPDATE":
                            current = float(parts[2])
                            total = float(parts[3])
                            self.status_text = parts[4] if len(parts) > 4 else ""
                            if total > 0:
                                self.progress_pct = (current / total) * 100
                            else:
                                self.progress_pct = (current % 1000) / 10 # Indeterminate sweeping bar
                        elif msg_type == "DONE":
                            self.phase_text = "Finished!"
                            self.status_text = parts[4] if len(parts) > 4 else "Complete"
                            self.progress_pct = 100.0
                            self.log_lines.append("Execution Complete. Press 'q' to exit.")
                else:
                    self.log_lines.append(line)
                    if len(self.log_lines) > 50:
                        self.log_lines.pop(0)

            # Draw Interface
            self.stdscr.erase()
            height, width = self.stdscr.getmaxyx()
            
            # Title
            title = "UALBF Computational Engine Tracker"
            self.stdscr.addstr(1, max(0, (width - len(title)) // 2), title, curses.color_pair(3) | curses.A_BOLD)
            
            # Phase & Status
            self.stdscr.addstr(4, 5, f"Current Task: {self.phase_text}", curses.color_pair(2))
            self.stdscr.addstr(5, 5, f"Status: {self.status_text}")
            
            # Progress Bar
            bar_width = width - 14
            if bar_width > 10:
                filled = int((self.progress_pct / 100.0) * bar_width)
                empty = bar_width - filled
                bar = "[" + "#" * filled + "-" * empty + "]"
                self.stdscr.addstr(7, 5, f"{self.progress_pct:5.1f}% {bar}", curses.color_pair(1))
            
            # Logs
            self.stdscr.addstr(10, 5, "--- Engine Logs ---", curses.color_pair(3))
            
            max_log_lines = height - 13
            visible_logs = self.log_lines[-max_log_lines:] if max_log_lines > 0 else []
            for idx, log in enumerate(visible_logs):
                self.stdscr.addstr(12 + idx, 5, log[:width-10])
                
            self.stdscr.refresh()
            
            # Check for input
            try:
                c = self.stdscr.getch()
                if c == ord('q'):
                    self.running = False
            except:
                pass
                
            time.sleep(0.05)

if __name__ == "__main__":
    curses.wrapper(CursesGUI)
