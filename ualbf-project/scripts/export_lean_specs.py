#!/usr/bin/env python3
import os
import json

def generate_rust_types(schema, repo_root):
    # We will generate a file src/schema_generated.rs in rust-engine
    rust_path = os.path.join(repo_root, "rust-engine", "src", "schema_generated.rs")
    
    with open(rust_path, "w") as f:
        f.write("// AUTO-GENERATED from schema_manifest.json. DO NOT EDIT.\n\n")
        f.write("use crate::types::Uint;\n")
        f.write("use smallvec::SmallVec;\n")
        f.write("use serde::{Serialize, Deserialize};\n\n")
        
        for struct_name, struct_def in schema.items():
            fields = struct_def["fields"]
            
            # 1. Rust Struct (e.g. Prefix)
            f.write("#[derive(Clone, Debug)]\n")
            if struct_name == "SearchState":
                rust_name = "Prefix" # In Rust, it's called Prefix
            else:
                rust_name = struct_name
                
            f.write(f"pub struct {rust_name} {{\n")
            for field in fields:
                f.write(f"    pub {field['name']}: {field['rust_type']},\n")
            f.write("}\n\n")
            
            # 2. Serialized Rust Struct (e.g. SerializedPrefix)
            ser_name = f"Serialized{rust_name}"
            f.write("#[derive(Serialize, Deserialize, Debug)]\n")
            f.write(f"pub struct {ser_name} {{\n")
            for field in fields:
                f.write(f"    pub {field['name']}: {field.get('rust_ser_type', field['rust_type'])},\n")
            f.write("}\n\n")
            
            # 3. Conversion methods
            f.write(f"impl {ser_name} {{\n")
            f.write(f"    pub fn from_{rust_name.lower()}(p: &{rust_name}) -> Self {{\n")
            f.write(f"        Self {{\n")
            for field in fields:
                conv = field.get('rust_ser_convert', 'v.clone()').replace('v', f"p.{field['name']}")
                f.write(f"            {field['name']}: {conv},\n")
            f.write(f"        }}\n")
            f.write(f"    }}\n\n")
            
            f.write(f"    pub fn to_{rust_name.lower()}(&self) -> {rust_name} {{\n")
            f.write(f"        {rust_name} {{\n")
            for field in fields:
                conv = field.get('rust_deser_convert', 'v.clone()').replace('v', f"self.{field['name']}")
                f.write(f"            {field['name']}: {conv},\n")
            f.write(f"        }}\n")
            f.write(f"    }}\n")
            f.write(f"}}\n\n")


def generate_lean_types(schema, repo_root):
    lean_path = os.path.join(repo_root, "lean4-proofs", "UALBF", "Engine", "SearchState.lean")
    with open(lean_path, "w") as f:
        f.write("-- AUTO-GENERATED from schema_manifest.json. DO NOT EDIT.\n\n")
        f.write("import Mathlib.Data.Nat.Basic\n")
        f.write("import Lean.Data.Json\n\n")
        f.write("namespace UALBF.Engine\n\n")
        
        for struct_name, struct_def in schema.items():
            fields = struct_def["fields"]
            f.write(f"structure {struct_name} where\n")
            for field in fields:
                f.write(f"  {field['name']} : {field['lean_type']}\n")
            f.write(f"deriving Inhabited, Repr, FromJson, ToJson\n\n")
            
        f.write("end UALBF.Engine\n")

def generate_verus_specs(bounds, repo_root):
    export_path = os.path.join(repo_root, "rust-engine", "src", "lean_export.rs")
    with open(export_path, "w") as f:
        tot_num = bounds["euler_ceiling"]["num"]
        tot_den = bounds["euler_ceiling"]["den"]
        baseline = bounds["omega_bounds"]["baseline"]["proof_bound"]
        ps_bound = bounds["omega_bounds"]["prasad_sunitha"]["proof_bound"]
        
        f.write(f"""// AUTO-GENERATED from bounds_manifest.json. DO NOT EDIT.

use vstd::prelude::*;

verus! {{
    pub spec fn lean_qpn_totient_bound_num() -> nat {{ {tot_num} }}
    pub spec fn lean_qpn_totient_bound_den() -> nat {{ {tot_den} }}
    
    pub spec fn lean_baseline_min_prime_factors() -> nat {{ {baseline} }}
    
    pub spec fn lean_prasad_sunitha_bound() -> nat {{ {ps_bound} }}
}}
""")

def main():
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    # 1. Load schema manifest
    schema_path = os.path.join(repo_root, "schema_manifest.json")
    if os.path.exists(schema_path):
        with open(schema_path, "r") as f:
            schema = json.load(f)
        generate_rust_types(schema, repo_root)
        generate_lean_types(schema, repo_root)
        print(f"Schema generated from {schema_path}")
    else:
        print(f"Warning: {schema_path} not found.")

    # 2. Load bounds manifest
    bounds_path = os.path.join(repo_root, "bounds_manifest.json")
    if os.path.exists(bounds_path):
        with open(bounds_path, "r") as f:
            bounds = json.load(f)
        generate_verus_specs(bounds, repo_root)
        print(f"Verus specs generated from {bounds_path}")
    else:
        print(f"Warning: {bounds_path} not found.")

if __name__ == "__main__":
    main()
