#[cfg(feature = "signing")]
pub use ed25519_dalek;
#[cfg(feature = "signing")]
pub use hex;
#[cfg(feature = "signing")]
pub use sha2;

#[macro_export]
macro_rules! define_tcb {
    ( $( $file:expr ),* $(,)? ) => {
        pub const TCB_FILES: &[&str] = &[ $( $file ),* ];
        
        #[macro_export]
        #[cfg(feature = "signing")]
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

        #[macro_export]
        #[cfg(not(feature = "signing"))]
        macro_rules! compute_tcb_hash_at_compile_time {
            () => {
                "unverified_logic_hash".to_string()
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
    "../build.rs",
    "gpu.rs",
    "kernel.metal",
    "../../bounds_manifest.json"
);

#[cfg(feature = "signing")]
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
    sampling_rate: Option<f64>,
    deterministic_seed: Option<u64>,
) -> String {
    let mut map = std::collections::BTreeMap::new();
    map.insert("manifest_hash", serde_json::Value::String(manifest_hash.to_string()));
    map.insert("verified_logic_hash", serde_json::Value::String(verified_logic_hash.to_string()));
    map.insert("total_branches_searched", serde_json::Value::Number(serde_json::Number::from(total_branches_searched)));
    map.insert("target_min_log10", serde_json::Value::Number(serde_json::Number::from(target_min_log10)));
    map.insert("target_max_log10", serde_json::Value::Number(serde_json::Number::from(target_max_log10)));
    map.insert("trace_hash", serde_json::Value::String(trace_hash.to_string()));
    map.insert("factorization_depth", serde_json::Value::Number(serde_json::Number::from(factorization_depth)));
    
    if let Some(rate) = sampling_rate {
        map.insert("sampling_rate", serde_json::Value::Number(serde_json::Number::from_f64(rate).unwrap()));
    }
    if let Some(seed) = deterministic_seed {
        map.insert("deterministic_seed", serde_json::Value::Number(serde_json::Number::from(seed)));
    }
    
    serde_json::to_string(&map).unwrap()
}

#[cfg(feature = "signing")]
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

#[cfg(feature = "python")]
use pyo3::prelude::*;

#[cfg(feature = "python")]
#[pyfunction]
pub fn validate_certificate(cert_json_str: &str) -> PyResult<String> {
    use pyo3::exceptions::{PyValueError, PyException};
    
    // Parse the JSON string
    let cert: serde_json::Value = serde_json::from_str(cert_json_str)
        .map_err(|e| PyValueError::new_err(format!("Failed to parse certificate JSON: {}", e)))?;
        
    let obj = cert.as_object()
        .ok_or_else(|| PyValueError::new_err("Certificate is not a JSON object"))?;
        
    let telemetry = obj.get("telemetry")
        .and_then(|t| t.as_object())
        .ok_or_else(|| PyValueError::new_err("Missing or invalid 'telemetry' object"))?;
        
    // Extract signed fields
    let manifest_hash = obj.get("manifest_hash").and_then(|v| v.as_str()).unwrap_or("");
    let verified_logic_hash = obj.get("verified_logic_hash").and_then(|v| v.as_str()).unwrap_or("");
    let public_key = obj.get("public_key").and_then(|v| v.as_str()).unwrap_or("");
    let signature = obj.get("signature").and_then(|v| v.as_str()).unwrap_or("");
    
    let total_branches_searched = telemetry.get("total_branches_searched").and_then(|v| v.as_u64()).unwrap_or(0) as usize;
    let target_min_log10 = telemetry.get("target_min_log10").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
    let target_max_log10 = telemetry.get("target_max_log10").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
    let trace_hash = telemetry.get("trace_hash").and_then(|v| v.as_str()).unwrap_or("");
    let factorization_depth = telemetry.get("factorization_depth").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
    
    let (sampling_rate, deterministic_seed) = if let Some(profile) = telemetry.get("verification_profile").and_then(|v| v.as_object()) {
        (
            profile.get("sampling_rate").and_then(|v| v.as_f64()),
            profile.get("deterministic_seed").and_then(|v| v.as_u64()),
        )
    } else {
        (None, None)
    };
    
    // Reconstruct payload
    let payload = format_payload(
        manifest_hash,
        verified_logic_hash,
        total_branches_searched,
        target_min_log10,
        target_max_log10,
        trace_hash,
        factorization_depth,
        sampling_rate,
        deterministic_seed
    );
    
    // Verify signature
    let is_valid = verify_signature(public_key, signature, &payload)
        .map_err(|e| PyException::new_err(format!("Signature verification error: {}", e)))?;
        
    if !is_valid {
        return Err(PyException::new_err("Invalid cryptographic signature"));
    }
    
    // Check mandatory fields to prevent empty strings being valid
    if manifest_hash.is_empty() { return Err(PyValueError::new_err("Missing manifest_hash")); }
    if public_key.is_empty() { return Err(PyValueError::new_err("Missing public_key")); }
    if signature.is_empty() { return Err(PyValueError::new_err("Missing signature")); }
    
    // Return the unmodified JSON so Python can use it
    Ok(cert_json_str.to_string())
}

#[cfg(feature = "python")]
#[pyfunction]
pub fn hash_tcb(repo_root: &str) -> PyResult<String> {
    use pyo3::exceptions::PyException;
    let path = std::path::Path::new(repo_root);
    compute_verified_logic_hash_runtime(path)
        .map_err(|e| PyException::new_err(format!("Failed to hash TCB: {}", e)))
}

#[cfg(feature = "python")]
#[pymodule]
fn verification_lib(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(validate_certificate, m)?)?;
    m.add_function(wrap_pyfunction!(hash_tcb, m)?)?;
    Ok(())
}


#[cfg(feature = "signing")]
#[no_mangle]
pub extern "C" fn verify_certificate(
    cert_json_ptr: *const std::ffi::c_char,
    pub_key_ptr: *const std::ffi::c_char,
    is_valid_out: *mut bool,
    out_manifest_hash_buf: *mut std::ffi::c_char,
    out_manifest_hash_len: usize,
) -> *mut std::ffi::c_void {
    use std::ffi::{CStr, CString};
    
    unsafe { *is_valid_out = false; }
    
    let mut write_error = |err: &str| {
        unsafe {
            if !out_manifest_hash_buf.is_null() && out_manifest_hash_len > 0 {
                let bytes = err.as_bytes();
                let copy_len = std::cmp::min(bytes.len(), out_manifest_hash_len - 1);
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), out_manifest_hash_buf as *mut u8, copy_len);
                *out_manifest_hash_buf.add(copy_len) = 0;
            }
        }
    };
    
    if cert_json_ptr.is_null() || pub_key_ptr.is_null() {
        return std::ptr::null_mut();
    }
    
    let cert_json_str = unsafe { CStr::from_ptr(cert_json_ptr) }.to_string_lossy();
    let expected_pub_key = unsafe { CStr::from_ptr(pub_key_ptr) }.to_string_lossy();
    
    let cert: serde_json::Value = match serde_json::from_str(&cert_json_str) {
        Ok(c) => c,
        Err(_) => {
            write_error("Failed to parse JSON");
            return std::ptr::null_mut();
        }
    };
    
    let obj = match cert.as_object() {
        Some(o) => o,
        None => {
            write_error("Certificate is not a JSON object");
            return std::ptr::null_mut();
        }
    };
    
    let telemetry = match obj.get("telemetry").and_then(|t| t.as_object()) {
        Some(t) => t,
        None => {
            write_error("Missing or invalid telemetry object");
            return std::ptr::null_mut();
        }
    };
    
    let manifest_hash = obj.get("manifest_hash").and_then(|v| v.as_str()).unwrap_or("");
    let verified_logic_hash = obj.get("verified_logic_hash").and_then(|v| v.as_str()).unwrap_or("");
    let public_key = obj.get("public_key").and_then(|v| v.as_str()).unwrap_or("");
    let signature = obj.get("signature").and_then(|v| v.as_str()).unwrap_or("");
    
    if public_key != expected_pub_key {
        write_error("Certificate public key does not match trusted signer key!");
        return std::ptr::null_mut();
    }
    
    let total_branches_searched = telemetry.get("total_branches_searched").and_then(|v| v.as_u64()).unwrap_or(0) as usize;
    let target_min_log10 = telemetry.get("target_min_log10").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
    let target_max_log10 = telemetry.get("target_max_log10").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
    let trace_hash = telemetry.get("trace_hash").and_then(|v| v.as_str()).unwrap_or("");
    let factorization_depth = telemetry.get("factorization_depth").and_then(|v| v.as_u64()).unwrap_or(0) as u32;
    
    let payload = format_payload(
        manifest_hash,
        verified_logic_hash,
        total_branches_searched,
        target_min_log10,
        target_max_log10,
        trace_hash,
        factorization_depth,
        None,
        None
    );
    
    let is_valid = verify_signature(public_key, signature, &payload).unwrap_or(false);
    
    if !is_valid || manifest_hash.is_empty() || signature.is_empty() {
        write_error("Invalid cryptographic signature!");
        return std::ptr::null_mut();
    }
    
    unsafe {
        *is_valid_out = true;
    }
    write_error(manifest_hash);
    
    Box::into_raw(Box::new(cert)) as *mut std::ffi::c_void
}

#[cfg(feature = "signing")]
#[no_mangle]
pub extern "C" fn free_certificate(cert_ptr: *mut std::ffi::c_void) {
    if !cert_ptr.is_null() {
        unsafe {
            let _ = Box::from_raw(cert_ptr as *mut serde_json::Value);
        }
    }
}
