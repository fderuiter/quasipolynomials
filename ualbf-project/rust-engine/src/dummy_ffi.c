#include <stdint.h>
#include <stdbool.h>

void lean_initialize_runtime_module() {}
void lean_initialize() {}
void initialize_Ualbf_C_Main() {}
void lean_initialize_thread() {}

void* lean_register_external_class(void* finalize, void* foreach) { return 0; }
void* lean_alloc_external(void* cls, void* data) { return 0; }
void* lean_get_external_data(void* obj) { return 0; }
void lean_inc(void* obj) {}
void lean_dec(void* obj) {}

uint8_t ualbf_check_mod_8(uint64_t q) { uint64_t r = q % 8; return (r == 5 || r == 7) ? 1 : 0; }

void* ualbf_compute_sigma(uint64_t p, uint64_t pow) { return 0; }
uint8_t ualbf_compute_sigma_ok(uint64_t p, uint64_t pow) { return 0; }

void* ualbf_cyclotomic_eval(uint32_t d, void* p) { return 0; }
uint8_t ualbf_cyclotomic_eval_ok(uint32_t d, void* p) { return 0; }

/**
 * Compute the static suffix bound w0 for the given k.
 *
 * @param k Input parameter that defines the bound.
 * @returns The static suffix bound w0 for k; in this implementation always returns 0.
 */
uint64_t ualbf_static_suffix_bound_w0(uint32_t k) { return 0; }
/**
 * Compute the static suffix bound w1 for a given k.
 *
 * @param k Parameter index used to determine the bound.
 * @returns The static suffix bound w1 for `k`; in this stub implementation this function always returns 0.
 */
uint64_t ualbf_static_suffix_bound_w1(uint32_t k) { return 0; }
/**
 * Compute the numerator of the Euler ceiling for the given k.
 *
 * @param k Index parameter for which the Euler ceiling numerator is requested.
 * @returns The numerator of the Euler ceiling for k (currently a placeholder value `0`).
 */
uint64_t ualbf_euler_ceiling_num(uint32_t k) { return 0; }
/**
 * Retrieve the denominator of the Euler ceiling for the given index k.
 *
 * @param k Index for which to obtain the denominator.
 * @returns The denominator value for k (always 1).
 */
uint64_t ualbf_euler_ceiling_den(uint32_t k) { return 1; }

