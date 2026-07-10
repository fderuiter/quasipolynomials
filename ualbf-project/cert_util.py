import json
import os

try:
    import verification_lib
except ImportError:
    # Give a helpful message if the library hasn't been built
    raise ImportError(
        "Native verification_lib not found. Please build the verification-lib extension (e.g. `maturin develop`)."
    )


class CertificateError(Exception):
    """Base class for certificate-related errors."""

    pass


class CertificateJSONError(CertificateError):
    """Raised when a certificate file cannot be parsed as valid JSON."""

    pass


class CertificateValidationError(CertificateError):
    """Raised when a certificate is missing mandatory fields or fails structural validation."""

    pass


def load_and_validate_cert(cert_path):
    """
    Loads and validates an exhaustion certificate from the given path.
    Delegates to the shared Rust native library to ensure 100% schema parity
    and correct cryptographic logic.
    """
    if not os.path.exists(cert_path):
        raise CertificateValidationError(f"Certificate file not found: {cert_path}")

    with open(cert_path, "r") as f:
        cert_str = f.read()

    try:
        # The native library validates the signature and structure
        validated_str = verification_lib.validate_certificate(cert_str)
        cert = json.loads(validated_str)
    except Exception as e:
        raise CertificateValidationError(f"Validation failed: {e}")

    return cert
