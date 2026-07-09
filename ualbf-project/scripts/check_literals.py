#!/usr/bin/env python3
import sys
import re
import os
import json

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

def strip_comments(content):
    # Remove block comments
    content = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
    # Remove line comments
    content = re.sub(r'--.*', '', content)
    return content

def main():
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    lean_dir = os.path.join(repo_root, "lean4-proofs", "UALBF")
    lean_files = []
    for root, _, files in os.walk(lean_dir):
        for file in files:
            if file.endswith(".lean") and file not in ["ManifestConstants.lean", "FFI.lean"]:
                lean_files.append(os.path.join(root, file))
                
    manifest_path = os.path.join(repo_root, "bounds_manifest.json")
    with open(manifest_path, "r") as f:
        manifest = json.load(f)
        
    bounds = set()
    def extract_bounds(d):
        for v in d.values():
            if isinstance(v, dict):
                extract_bounds(v)
            elif isinstance(v, int) and not isinstance(v, bool):
                bounds.add(str(v))
    extract_bounds(manifest)
    
    ignored_bounds = {"0", "4", "7", "128"}
    bounds = bounds - ignored_bounds
    
    failed = False
    for filepath in FILES_TO_CHECK:
        full_path = os.path.join(repo_root, "rust-engine", filepath)
        try:
            with open(full_path, "r") as f:
                content = f.read()
                for pattern in FORBIDDEN_PATTERNS:
                    if re.search(pattern, content):
                        print(f"ERROR: Found forbidden hardcoded literal matching '{pattern}' in {filepath}", file=sys.stderr)
                        failed = True
        except Exception as e:
            print(f"Failed to read {filepath}: {e}", file=sys.stderr)
            failed = True
            
    for filepath in lean_files:
        try:
            with open(filepath, "r") as f:
                content = f.read()
                content = strip_comments(content)
                lines = content.split('\n')
                for line_idx, code_line in enumerate(lines):
                    for b in bounds:
                        if b == "15" and re.search(r'(gcd\s*15|∣\s*15|\|\s*15|Coprime\s*15|coprime\s*to\s*15|P14)', code_line):
                            continue
                        if b == "43" and re.search(r'(\{|\[|/|P14)', code_line):
                            continue
                        if b == "10000" and "/" in code_line:
                            continue
                        if re.search(r"\b" + b + r"\b", code_line):
                            print(f"ERROR: Found forbidden literal '{b}' from manifest in {filepath}:{line_idx+1}: {code_line.strip()}", file=sys.stderr)
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
