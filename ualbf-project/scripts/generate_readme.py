#!/usr/bin/env python3
import json
import os
import hashlib
import sys

def get_superscript(n):
    sup = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
    return str(n).translate(sup)

def main():
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    workspace_root = os.path.dirname(repo_root) # /app
    
    manifest_path = os.path.join(repo_root, "bounds_manifest.json")
    with open(manifest_path, "r", encoding="utf-8") as f:
        manifest = json.load(f)
        
    template_path = os.path.join(workspace_root, "README.template.md")
    output_path = os.path.join(workspace_root, "README.md")
    
    with open(template_path, "r", encoding="utf-8") as f:
        template = f.read()
        
    prasad_sunitha = manifest["omega_bounds"]["prasad_sunitha"]["proof_bound"]
    target_max_log10 = manifest["search_bounds"]["target_max_log10"]["value"]
    target_max_log10_sup = get_superscript(target_max_log10)
    target_min_log10 = manifest["search_bounds"]["target_min_log10"]["value"]
    target_min_log10_sup = get_superscript(target_min_log10)
    euler_num = manifest["euler_ceiling"]["num"]
    euler_den = manifest["euler_ceiling"]["den"]
    euler_val = euler_num / euler_den
    
    content = template.replace("{{prasad_sunitha_bound}}", str(prasad_sunitha))
    content = content.replace("{{target_max_log10}}", str(target_max_log10))
    content = content.replace("{{target_max_log10_sup}}", str(target_max_log10_sup))
    content = content.replace("{{target_min_log10}}", str(target_min_log10))
    content = content.replace("{{target_min_log10_sup}}", str(target_min_log10_sup))
    content = content.replace("{{euler_ceiling}}", str(euler_val))
    
    if os.path.exists(output_path):
        with open(output_path, "r", encoding="utf-8") as f:
            old_content = f.read()
            
        sig_marker = "<!-- GENERATED_HASH: "
        if sig_marker in old_content:
            parts = old_content.split(sig_marker)
            body = parts[0]
            old_sig = parts[1].split(" -->")[0].strip()
            actual_sig = hashlib.sha256(body.encode('utf-8')).hexdigest()
            if actual_sig != old_sig:
                print("ERROR: README.md was manually edited! Please edit README.template.md or bounds_manifest.json instead.", file=sys.stderr)
                sys.exit(1)
                
    body = content
    new_sig = hashlib.sha256(body.encode('utf-8')).hexdigest()
    final_content = f"{body}<!-- GENERATED_HASH: {new_sig} -->\n"
    
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(final_content)
        
if __name__ == "__main__":
    main()
