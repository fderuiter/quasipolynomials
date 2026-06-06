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

uint64_t ualbf_static_suffix_bound_w0(uint32_t k) { return 0; }
uint64_t ualbf_static_suffix_bound_w1(uint32_t k) { return 0; }

uint64_t ualbf_euler_ceiling_num() { return 20442; }
uint64_t ualbf_euler_ceiling_den() { return 10000; }

uint64_t ualbf_baseline_min_prime_factors() { return 7; }
uint64_t ualbf_prasad_sunitha_bound() { return 14; }
