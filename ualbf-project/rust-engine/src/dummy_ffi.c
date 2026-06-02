#include <stdint.h>
#include <stdbool.h>

bool ualbf_cyclotomic_eval_ok = false;
uint64_t ualbf_cyclotomic_eval_w0(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }
uint64_t ualbf_cyclotomic_eval_w1(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }
uint64_t ualbf_cyclotomic_eval_w2(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }
uint64_t ualbf_cyclotomic_eval_w3(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }
uint64_t ualbf_cyclotomic_eval_w4(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }
uint64_t ualbf_cyclotomic_eval_w5(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }
uint64_t ualbf_cyclotomic_eval_w6(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }
uint64_t ualbf_cyclotomic_eval_w7(uint32_t d, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t p4, uint64_t p5, uint64_t p6, uint64_t p7) { return 0; }

bool ualbf_compute_sigma_ok = false;
uint64_t ualbf_compute_sigma_w0(uint64_t p, uint64_t a) { return 0; }
uint64_t ualbf_compute_sigma_w1(uint64_t p, uint64_t a) { return 0; }
uint64_t ualbf_compute_sigma_w2(uint64_t p, uint64_t a) { return 0; }
uint64_t ualbf_compute_sigma_w3(uint64_t p, uint64_t a) { return 0; }

uint64_t ualbf_static_suffix_bound_w0(uint32_t k) { return 0; }
uint64_t ualbf_static_suffix_bound_w1(uint32_t k) { return 0; }

void lean_initialize_runtime_module() {}
void lean_initialize() {}
void initialize_Ualbf_C_Main() {}
void lean_initialize_thread() {}
uint8_t ualbf_check_mod_8(uint64_t q) { uint64_t r = q % 8; return (r == 5 || r == 7) ? 1 : 0; }
