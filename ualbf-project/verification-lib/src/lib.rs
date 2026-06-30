pub use ed25519_dalek;
pub use hex;
pub use sha2;

#[macro_export]
macro_rules! define_tcb {
    ( $( $file:expr ),* $(,)? ) => {
        pub const TCB_FILES: &[&str] = &[ $( $file ),* ];
        
        #[macro_export]
        macro_rules! compute_tcb_hash_at_compile_time {
            () => {
                {
                    use $crate::sha2::{Digest, Sha256};
                    let mut logic_hasher = Sha256::new();
                    $(
                        logic_hasher.update(include_bytes!($file));
                    )*
                    $crate::hex::encode(logic_hasher.finalize())
                }
            }
        }
    }
}

define_tcb!(
    "dfs_tree.rs",
    "sieve.rs",
    "verus_proofs.rs",
    "manifest_constants.rs",
    "lean_ffi.rs",
    "dummy_ffi.c",
    "../../lean4-proofs/UALBF/QPN/AbundancyBound.lean",
    "../build.rs"
);

pub fn compute_verified_logic_hash_runtime(repo_root: &std::path::Path) -> std::io::Result<String> {
    use sha2::{Digest, Sha256};
    let mut logic_hasher = Sha256::new();
    let base_dir = repo_root.join("rust-engine/src");
    
    for file in TCB_FILES {
        let path = base_dir.join(file);
        let path = path.canonicalize().unwrap_or(path);
        let content = std::fs::read(&path)?;
        logic_hasher.update(&content);
    }
    Ok(hex::encode(logic_hasher.finalize()))
}

pub fn format_payload(
    manifest_hash: &str,
    verified_logic_hash: &str,
    total_branches_searched: usize,
    target_min_log10: u32,
    target_max_log10: u32,
    trace_hash: &str,
    factorization_depth: u32,
) -> String {
    let mut map = std::collections::BTreeMap::new();
    map.insert("manifest_hash", serde_json::Value::String(manifest_hash.to_string()));
    map.insert("verified_logic_hash", serde_json::Value::String(verified_logic_hash.to_string()));
    map.insert("total_branches_searched", serde_json::Value::Number(serde_json::Number::from(total_branches_searched)));
    map.insert("target_min_log10", serde_json::Value::Number(serde_json::Number::from(target_min_log10)));
    map.insert("target_max_log10", serde_json::Value::Number(serde_json::Number::from(target_max_log10)));
    map.insert("trace_hash", serde_json::Value::String(trace_hash.to_string()));
    map.insert("factorization_depth", serde_json::Value::Number(serde_json::Number::from(factorization_depth)));
    
    serde_json::to_string(&map).unwrap()
}

pub fn verify_signature(
    public_key_hex: &str,
    signature_hex: &str,
    payload: &str,
) -> Result<bool, String> {
    use ed25519_dalek::{Verifier, VerifyingKey, Signature};
    
    let pub_bytes = hex::decode(public_key_hex).map_err(|e| e.to_string())?;
    let sig_bytes = hex::decode(signature_hex).map_err(|e| e.to_string())?;
    
    let public_key = VerifyingKey::from_bytes(pub_bytes.as_slice().try_into().map_err(|_| "Invalid key length")?).map_err(|e| e.to_string())?;
    let signature = Signature::from_bytes(sig_bytes.as_slice().try_into().map_err(|_| "Invalid sig length")?);
    
    Ok(public_key.verify(payload.as_bytes(), &signature).is_ok())
}
