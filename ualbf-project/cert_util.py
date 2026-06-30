import json
import os

class CertificateError(Exception):
    """Base class for certificate-related errors."""
    pass

class CertificateJSONError(CertificateError):
    """Raised when a certificate file cannot be parsed as valid JSON."""
    pass

class CertificateValidationError(CertificateError):
    """Raised when a certificate is missing mandatory fields or fails structural validation."""
    pass

MANDATORY_CRYPTO_FIELDS = [
    "manifest_hash",
    "verified_logic_hash",
    "public_key",
    "signature",
]

MANDATORY_TELEMETRY_FIELDS = [
    "target_min_log10",
    "target_max_log10",
    "total_branches_searched",
    "phase2_execution_time_ms",
]

def load_and_validate_cert(cert_path):
    """
    Loads and validates an exhaustion certificate from the given path.
    Enforces strict presence of all mandatory cryptographic and telemetry fields.
    """
    if not os.path.exists(cert_path):
        raise CertificateValidationError(f"Certificate file not found: {cert_path}")
    
    try:
        with open(cert_path, "r") as f:
            cert = json.load(f)
    except json.JSONDecodeError as e:
        raise CertificateJSONError(f"Failed to decode certificate JSON: {e}")
        
    for field in MANDATORY_CRYPTO_FIELDS:
        if field not in cert:
            raise CertificateValidationError(f"Missing mandatory cryptographic field: '{field}'")
            
    if "telemetry" not in cert:
        raise CertificateValidationError("Missing 'telemetry' object in certificate")
        
    tel = cert["telemetry"]
    if not isinstance(tel, dict):
        raise CertificateValidationError("'telemetry' must be a JSON object")
        
    for field in MANDATORY_TELEMETRY_FIELDS:
        if field not in tel:
            raise CertificateValidationError(f"Missing mandatory telemetry field: '{field}'")
            
    return cert
