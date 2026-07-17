#!/usr/bin/env python3
import json
import os
import re
import sys

def get_nested_value(d, path):
    keys = path.split('.')
    for k in keys:
        if k in d:
            d = d[k]
        else:
            return None
    return d

def main():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    manifest_path = os.path.join(base_dir, "metadata_manifest.json")
    
    if not os.path.exists(manifest_path):
        print(f"Error: {manifest_path} not found.")
        sys.exit(1)
        
    with open(manifest_path, "r", encoding="utf-8") as f:
        manifest = json.load(f)
        
    errors = 0
    
    # 1. Check code references
    for doc in manifest.get("documents", []):
        doc_file = os.path.join(base_dir, doc["file"])
        if not os.path.exists(doc_file):
            print(f"Error: Document {doc['file']} not found.")
            errors += 1
            continue
            
        with open(doc_file, "r", encoding="utf-8") as df:
            doc_content = df.read()
            
        for ref in doc.get("code_references", []):
            marker = ref["marker"]
            target = ref["target"]
            
            # verify marker is in doc
            if marker not in doc_content:
                # Let's find line number if it's there, but it's not.
                # Actually, the acceptance criteria says:
                # "The build fails with explicit file and line coordinates when a document reference points to a missing or renamed code construct."
                # This means the marker IS in the document, but the code construct (target) is missing!
                pass # marker could be missing if someone removed it, but the main check is the target file
            
            # verify target file exists
            target_path = os.path.join(base_dir, target)
            if not os.path.exists(target_path):
                # find line coordinates in doc
                with open(doc_file, "r", encoding="utf-8") as df_lines:
                    for line_no, line in enumerate(df_lines, 1):
                        if marker in line:
                            print(f"Error in {doc['file']}:{line_no}: Referenced code construct '{target}' is missing or renamed.")
                            errors += 1
                if marker not in doc_content:
                    print(f"Error in {doc['file']}: Marker '{marker}' not found, but it was supposed to point to '{target}'.")
                    errors += 1
            else:
                # verify marker is in doc
                if marker not in doc_content:
                    print(f"Error in {doc['file']}: Marker '{marker}' not found in document.")
                    errors += 1

    # 2. Check hardcoded metrics
    for metric in manifest.get("hardcoded_metrics", []):
        doc_file = os.path.join(base_dir, metric["file"])
        if not os.path.exists(doc_file):
            print(f"Error: Document {metric['file']} not found.")
            errors += 1
            continue
            
        with open(doc_file, "r", encoding="utf-8") as df_lines:
            lines = df_lines.readlines()
            
        for check in metric.get("checks", []):
            regex = re.compile(check["regex"])
            source_file = os.path.join(base_dir, check["source"])
            
            if not os.path.exists(source_file):
                print(f"Error: Source manifest {check['source']} not found.")
                errors += 1
                continue
                
            with open(source_file, "r", encoding="utf-8") as sf:
                source_data = json.load(sf)
                
            expected_val = str(get_nested_value(source_data, check["json_path"]))
            
            for line_no, line in enumerate(lines, 1):
                m = regex.search(line)
                if m:
                    actual_val = m.group(1)
                    if actual_val != expected_val:
                        print(f"Error in {metric['file']}:{line_no}: Hardcoded metric '{actual_val}' conflicts with manifest value '{expected_val}'.")
                        errors += 1
                        
    if errors > 0:
        sys.exit(1)
    print("Metadata Verification Hub: All checks passed.")

if __name__ == "__main__":
    main()
