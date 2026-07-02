#!/usr/bin/env python3
import sys
import re

FILES_TO_CHECK = [
    "src/dfs_tree.rs",
    "src/raycast.rs"
]

FORBIDDEN_PATTERNS = [
    r"TARGET_ABUNDANCE\s*:\s*f64",
    r"gpu_threshold\s*=\s*\d+",
    r"chunk_size\s*=\s*std::cmp::min\([^,]+,\s*\d+\)",
    r"<<\s*65",
]

def main():
    failed = False
    for filepath in FILES_TO_CHECK:
        try:
            with open(filepath, "r") as f:
                content = f.read()
                for pattern in FORBIDDEN_PATTERNS:
                    if re.search(pattern, content):
                        print(f"ERROR: Found forbidden hardcoded literal matching '{pattern}' in {filepath}", file=sys.stderr)
                        failed = True
        except Exception as e:
            print(f"Failed to read {filepath}: {e}", file=sys.stderr)
            failed = True

    if failed:
        sys.exit(1)
    else:
        print("Literal check passed.")
        sys.exit(0)

if __name__ == "__main__":
    main()
