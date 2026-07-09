#!/usr/bin/env python3
import os
import json
import re

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

            # 4. Transport Rust Struct
            has_transport = any("ffi_transport_type" in field for field in fields)
            if has_transport:
                transport_name = f"{rust_name}Transport"
                f.write("#[repr(C)]\n")
                f.write("#[derive(Clone, Debug)]\n")
                f.write(f"pub struct {transport_name} {{\n")
                for field in fields:
                    if "ffi_transport_type" in field:
                        ffi_t = field["ffi_transport_type"]
                        if ffi_t == "U512":
                            f.write(f"    pub {field['name']}: [u64; 8],\n")
                        elif ffi_t == "Array U512":
                            f.write(f"    pub {field['name']}: *const [u64; 8],\n")
                            f.write(f"    pub {field['name']}_len: usize,\n")
                        else:
                            f.write(f"    pub {field['name']}: {ffi_t},\n")
                    else:
                        rust_t = field["rust_type"]
                        if "Vec<" in rust_t:
                            inner = rust_t.replace("Vec<", "").replace(">", "")
                            f.write(f"    pub {field['name']}: *const {inner},\n")
                            f.write(f"    pub {field['name']}_len: usize,\n")
                        else:
                            f.write(f"    pub {field['name']}: {rust_t},\n")
                f.write("}\n\n")

                # Conversion utilities
                f.write(f"impl {rust_name} {{\n")
                f.write(f"    pub fn to_transport(&self) -> {transport_name} {{\n")
                f.write(f"        {transport_name} {{\n")
                for field in fields:
                    if "ffi_transport_type" in field:
                        ffi_t = field["ffi_transport_type"]
                        if ffi_t == "U512":
                            f.write(f"            {field['name']}: {{\n")
                            f.write(f"                let bytes = self.{field['name']}.to_le_bytes();\n")
                            f.write(f"                crate::lean_ffi::bytes_to_words::<64, 8>(&bytes)\n")
                            f.write(f"            }},\n")
                        elif ffi_t == "Array U512":
                            f.write(f"            {field['name']}: std::ptr::null(), // TODO: allocate arrays for FFI if needed\n")
                            f.write(f"            {field['name']}_len: self.{field['name']}.len(),\n")
                    else:
                        rust_t = field["rust_type"]
                        if "Vec<" in rust_t:
                            f.write(f"            {field['name']}: self.{field['name']}.as_ptr(),\n")
                            f.write(f"            {field['name']}_len: self.{field['name']}.len(),\n")
                        else:
                            f.write(f"            {field['name']}: self.{field['name']}.clone(),\n")
                f.write(f"        }}\n")
                f.write(f"    }}\n")
                f.write(f"}}\n\n")


def generate_lean_types(schema, repo_root):
    lean_path = os.path.join(repo_root, "lean4-proofs", "UALBF", "Engine", "SearchState.lean")
    with open(lean_path, "w") as f:
        f.write("-- AUTO-GENERATED from schema_manifest.json. DO NOT EDIT.\n\n")
        f.write("import Mathlib.Data.Nat.Basic\n")
        f.write("import Lean.Data.Json\n")
        f.write("import UALBF.FFI\n\n")
        f.write("namespace UALBF.Engine\n\n")
        
        for struct_name, struct_def in schema.items():
            fields = struct_def["fields"]
            f.write(f"structure {struct_name} where\n")
            for field in fields:
                f.write(f"  {field['name']} : {field['lean_type']}\n")
            f.write(f"deriving Inhabited, Repr, Lean.FromJson, Lean.ToJson\n\n")

            has_transport = any("ffi_transport_type" in field for field in fields)
            if has_transport:
                transport_name = f"{struct_name}Transport"
                f.write(f"structure {transport_name} where\n")
                for field in fields:
                    if "ffi_transport_type" in field:
                        ffi_t = field["ffi_transport_type"]
                        if ffi_t == "U512":
                            f.write(f"  {field['name']} : UALBF.FFI.U512\n")
                        elif ffi_t == "Array U512":
                            f.write(f"  {field['name']} : Array UALBF.FFI.U512\n")
                    else:
                        f.write(f"  {field['name']} : {field['lean_type']}\n")
                f.write(f"deriving Inhabited\n\n")

                f.write(f"def {transport_name}.toNative (t : {transport_name}) : {struct_name} := {{\n")
                for field in fields:
                    if "ffi_transport_type" in field:
                        ffi_t = field["ffi_transport_type"]
                        if ffi_t == "U512":
                            f.write(f"  {field['name']} := UALBF.FFI.fromU512 t.{field['name']},\n")
                        elif ffi_t == "Array U512":
                            f.write(f"  {field['name']} := t.{field['name']}.map UALBF.FFI.fromU512,\n")
                    else:
                        f.write(f"  {field['name']} := t.{field['name']},\n")
                f.write("}\n\n")
            
        f.write("end UALBF.Engine\n")

def generate_verus_specs(bounds, repo_root, bounds_hash):
    export_path = os.path.join(repo_root, "rust-engine", "src", "lean_export.rs")
    with open(export_path, "w") as f:
        tot_num = bounds["euler_ceiling"]["num"]
        tot_den = bounds["euler_ceiling"]["den"]
        baseline = bounds["omega_bounds"]["baseline"]["proof_bound"]
        ps_bound = bounds["omega_bounds"]["prasad_sunitha"]["proof_bound"]
        
        f.write(f"""// AUTO-GENERATED from bounds_manifest.json. DO NOT EDIT.

pub const EXPORTED_BOUNDS_MANIFEST_HASH: &str = "{bounds_hash}";

use vstd::prelude::*;

verus! {{
    pub spec fn lean_qpn_totient_bound_num() -> nat {{ {tot_num} }}
    pub spec fn lean_qpn_totient_bound_den() -> nat {{ {tot_den} }}
    
    pub spec fn lean_baseline_min_prime_factors() -> nat {{ {baseline} }}
    
    pub spec fn lean_prasad_sunitha_bound() -> nat {{ {ps_bound} }}
}}
""")


def map_type(t):
    t = t.strip()
    if t == "UInt8": return "u8"
    if t == "UInt32": return "u32"
    if t == "UInt64": return "u64"
    if t == "Bool": return "u8"
    if "U512" in t or "U256" in t: return "*mut crate::lean_ffi::lean_object"
    if t == "Unit": return "()"
    return "UNKNOWN"

def generate_ffi(repo_root):
    lean_ffi_path = os.path.join(repo_root, "lean4-proofs", "UALBF", "FFI.lean")
    out_path = os.path.join(repo_root, "rust-engine", "src", "ffi_generated.rs")
    
    with open(lean_ffi_path, "r") as f:
        content = f.read()

    exports = re.findall(r'@\[export\s+(\w+)\]\n(?:private\s+|partial\s+)?def\s+\w+\s*(.*?)\s*:\s*([a-zA-Z0-9_\. ]+?)(?:\s*:=|\n)', content, re.DOTALL)
    externs = re.findall(r'@\[extern\s+"([^"]+)"\]\n(?:opaque|def)\s+(\S+)\s+(.*?)\n', content)

    out = []
    out.append("// AUTO-GENERATED from Lean metadata. DO NOT EDIT.\n")
    out.append("extern \"C\" {")
    for name, args_str, ret_type in exports:
        args = []
        if args_str.strip():
            for match in re.finditer(r'\(([^:]+):\s*([^)]+)\)', args_str):
                names = match.group(1).split()
                t = match.group(2)
                rt = map_type(t)
                for n in names:
                    args.append(f"{n}: {rt}")
        ret = map_type(ret_type)
        ret_str = f" -> {ret}" if ret != "()" else ""
        out.append(f"    pub fn {name}({', '.join(args)}){ret_str};")
    out.append("}\n")
    
    for name, lean_name, sig in externs:
        if name.startswith("rust_u512_get_w"):
            idx = name[-1]
            out.append(f"#[no_mangle]\npub extern \"C\" fn {name}(obj: *mut crate::lean_ffi::lean_object) -> u64 {{ crate::lean_ffi::get_u512(obj)[{idx}] }}\n")
        elif name.startswith("rust_u256_get_w"):
            idx = name[-1]
            out.append(f"#[no_mangle]\npub extern \"C\" fn {name}(obj: *mut crate::lean_ffi::lean_object) -> u64 {{ crate::lean_ffi::get_u512(obj)[{idx}] }}\n")
        elif name.startswith("rust_is_prime_u256"):
            out.append(f"""#[no_mangle]
pub extern "C" fn {name}(obj: *mut crate::lean_ffi::lean_object) -> u8 {{
    let w = crate::lean_ffi::get_u512(obj);
    let mut w4 = [0u64; 4];
    w4.copy_from_slice(&w[0..4]);
    let b64 = crate::lean_ffi::words_to_bytes::<4, 64>(&w4);
    let n = crate::types::Uint::from_le_slice(&b64).unwrap();
    if crate::math_utils::verified_is_prime(n) {{ 1 }} else {{ 0 }}
}}
""")

    with open(out_path, "w") as f:
        f.write("\n".join(out))
    print(f"FFI bindings generated to {out_path}")

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
        import hashlib
        with open(bounds_path, "r") as f:
            bounds_content = f.read()
            bounds = json.loads(bounds_content)
            bounds_hash = hashlib.sha256(bounds_content.encode('utf-8')).hexdigest()
        generate_verus_specs(bounds, repo_root, bounds_hash)
        print(f"Verus specs generated from {bounds_path}")
        generate_ffi(repo_root)
    else:
        print(f"Warning: {bounds_path} not found.")

if __name__ == "__main__":
    main()
