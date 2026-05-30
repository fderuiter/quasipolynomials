#include <stdint.h>
#include <stddef.h>

void lean_initialize_runtime_module() {}
void lean_initialize_thread() {}

uint8_t ualbf_check_mod_8(uint64_t q) { return 1; }

// Dynamic FFI with byte arrays
uint8_t ualbf_compute_sigma_dyn(uint64_t p, uint32_t pow, uint8_t* out_bytes, size_t* out_len) {
    if (*out_len > 0) {
        out_bytes[0] = 0;
        *out_len = 1;
    }
    return 1;
}

uint8_t ualbf_mod_inverse_dyn(
    const uint8_t* a_bytes, size_t a_len, uint8_t a_neg,
    const uint8_t* m_bytes, size_t m_len,
    uint8_t* out_bytes, size_t* out_len
) {
    if (*out_len > 0) {
        out_bytes[0] = 0;
        *out_len = 1;
    }
    return 1;
}

uint8_t ualbf_cyclotomic_eval_dyn(
    uint32_t d, 
    const uint8_t* p_bytes, size_t p_len,
    uint8_t* out_bytes, size_t* out_len
) {
    if (*out_len > 0) {
        out_bytes[0] = 0;
        *out_len = 1;
    }
    return 1;
}
