#include <stdint.h>
#include <stdbool.h>

void lean_initialize_runtime_module() {}
void lean_initialize() {}
void initialize_Ualbf_C_Main() {}
void lean_initialize_thread() {}

void* lean_register_external_class(void* finalize, void* foreach) { return 0; }
void* rs_lean_alloc_external(void* cls, void* data) { return 0; }
void* rs_lean_get_external_data(void* obj) { return 0; }
void rs_lean_inc(void* obj) {}
void rs_lean_dec(void* obj) {}


void* initialize_ualbf_UALBF(uint8_t builtin) { return 0; }

uint8_t ualbf_check_mod_8(uint64_t q) { uint64_t r = q % 8; return (r == 1 || r == 3) ? 1 : 0; }

uint8_t ualbf_check_mod_3(uint64_t p, uint32_t two_e) {
    uint64_t p_mod = p % 3;
    uint64_t sum = 0;
    uint64_t term = 1;
    for (uint32_t i = 0; i <= two_e; i++) {
        sum = (sum + term) % 3;
        term = (term * p_mod) % 3;
    }
    return sum == 0 ? 1 : 0;
}

uint8_t ualbf_check_mod_5(uint64_t p, uint32_t two_e) {
    uint32_t e = two_e / 2;
    return (p % 5 == 1 && e % 5 == 2) ? 1 : 0;
}

uint8_t ualbf_check_mod_9(uint64_t p, uint32_t two_e) {
    uint64_t p_mod = p % 9;
    uint64_t sum = 0;
    uint64_t term = 1;
    for (uint32_t i = 0; i <= two_e; i++) {
        sum = (sum + term) % 9;
        term = (term * p_mod) % 9;
    }
    return (sum % 3 == 0) ? 1 : 0;
}

void* ualbf_compute_sigma(uint64_t p, uint64_t pow) { return (void*)1; }
void* ualbf_cyclotomic_eval(uint32_t d, void* p) { return (void*)1; }
void* ualbf_mod_inverse(void* a_obj, uint8_t a_neg, void* m_obj) { return (void*)1; }
uint8_t ualbf_verify_identity(void* n_l, void* x_l_abs, uint8_t x_l_neg, void* s_l) { return 1; }
uint8_t ualbf_verify_no_roots(void* n_obj, void* p_obj) { return 1; }

uint64_t ualbf_static_suffix_bound_w0(uint32_t k) { return 0; }
uint64_t ualbf_static_suffix_bound_w1(uint32_t k) { return 0; }

#ifndef PRASAD_SUNITHA_BOUND_NO_3_5
#define PRASAD_SUNITHA_BOUND_NO_3_5 15
#endif
#ifndef BASELINE_MIN_PRIME_FACTORS
#define BASELINE_MIN_PRIME_FACTORS 7
#endif
#ifndef EULER_CEILING_NUM
#define EULER_CEILING_NUM 20442
#endif
#ifndef EULER_CEILING_DEN
#define EULER_CEILING_DEN 10000
#endif

uint64_t ualbf_euler_ceiling_num() { return (1ULL << 63) | EULER_CEILING_NUM; }
uint64_t ualbf_euler_ceiling_den() { return (1ULL << 63) | EULER_CEILING_DEN; }
uint64_t ualbf_baseline_min_prime_factors() { return (1ULL << 63) | BASELINE_MIN_PRIME_FACTORS; }
uint64_t ualbf_prasad_sunitha_bound() { return (1ULL << 63) | PRASAD_SUNITHA_BOUND_NO_3_5; }

uint64_t ualbf_target_abundance_num() { return (1ULL << 63) | 2; }
uint64_t ualbf_target_abundance_den() { return (1ULL << 63) | 1; }

uint32_t ualbf_pollard_rho_iteration_limit() { return (1U << 31) | 1000; }
uint32_t ualbf_pollard_rho_batch_size() { return (1U << 31) | 64; }

void ualbf_dfs_loop(uint64_t ctx) { (void)ctx; }
uint32_t ualbf_evaluate_baseline_min_ffi(uint8_t contains_3, uint8_t contains_5, uint8_t skipped_3, uint8_t skipped_5) {
    if (!contains_3 && !contains_5 && skipped_3 && skipped_5) return PRASAD_SUNITHA_BOUND_NO_3_5;
    return BASELINE_MIN_PRIME_FACTORS;
}

uint32_t ualbf_target_min_log10() { return (1U << 31) | 43; }
uint32_t ualbf_target_max_log10() { return (1U << 31) | 45; }
uint64_t ualbf_sieve_limit() { return (1ULL << 63) | 250000; }
uint32_t ualbf_max_exponent() { return (1U << 31) | 4; }
uint64_t ualbf_prefix_stop_threshold() { return (1ULL << 63) | 100000000000ULL; }
uint32_t ualbf_raycast_gpu_threshold() { return (1U << 31) | 100000; }
uint32_t ualbf_raycast_chunk_size() { return (1U << 31) | 10000000; }
