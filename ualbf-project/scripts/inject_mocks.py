#!/usr/bin/env python3
import os
import subprocess
import re

def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_dir = os.path.join(script_dir, "..", "lean4-proofs")
    os.chdir(project_dir)

    pw_dir = os.path.join(".lake", "packages", "proofwidgets")
    
    if not os.path.exists(pw_dir):
        print("Resolving dependencies to locate ProofWidgets...")
        try:
            # First try resolve-deps to just fetch without full update
            res = subprocess.run(["lake", "resolve-deps"], capture_output=True, text=True)
            if res.returncode != 0:
                subprocess.run(["lake", "update"], capture_output=True, text=True)
        except FileNotFoundError:
            print("lake command not found, skipping resolution.")
            return

    if not os.path.exists(pw_dir):
        print("ProofWidgets directory not found after resolution. Nothing to mock.")
        return

    print("Extracting JS targets from ProofWidgets lakefile.lean...")
    lakefile_path = os.path.join(pw_dir, "lakefile.lean")
    
    js_files = set()
    if os.path.exists(lakefile_path):
        with open(lakefile_path, "r", encoding="utf-8") as f:
            content = f.read()
            # Extract any string literal ending in .js
            matches = re.findall(r'"([^"]+\.js)"', content)
            for m in matches:
                js_files.add(os.path.basename(m))
    
    # Fallbacks in case dynamic building is used
    common_mocks = ["index.js", "insertBtn.js", "interactiveCheckBtn.js", "widget.js", "exprPresentation.js"]
    for m in common_mocks:
        js_files.add(m)

    js_dir = os.path.join(pw_dir, ".lake", "build", "js")
    os.makedirs(js_dir, exist_ok=True)

    for js_file in js_files:
        filepath = os.path.join(js_dir, js_file)
        print(f"Mocking JS bundle: {js_file}")
        with open(filepath, "w", encoding="utf-8") as f:
            f.write("export default {};\n")
        
        # Create trace file
        tracepath = filepath + ".trace"
        with open(tracepath, "w", encoding="utf-8") as f:
            f.write("0\n")

    # Mock the trace for the aggregate target if needed by Lake
    build_dir = os.path.join(pw_dir, ".lake", "build")
    with open(os.path.join(build_dir, "widgetJsAll.trace"), "w", encoding="utf-8") as f:
        f.write("0\n")
    with open(os.path.join(build_dir, ".nobuild"), "w", encoding="utf-8") as f:
        f.write("0\n")

    print("Mock bundle injection complete.")

if __name__ == "__main__":
    main()
