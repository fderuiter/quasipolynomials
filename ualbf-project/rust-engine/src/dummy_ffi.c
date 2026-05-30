#include <stdint.h>
#include <stdbool.h>

bool ualbf_cyclotomic_eval_ok = false;
uint64_t ualbf_cyclotomic_eval_w0 = 0;
uint64_t ualbf_cyclotomic_eval_w1 = 0;
uint64_t ualbf_cyclotomic_eval_w2 = 0;
uint64_t ualbf_cyclotomic_eval_w3 = 0;
void ualbf_cyclotomic_eval(uint32_t d, uint64_t p_w0, uint64_t p_w1, uint64_t p_w2, uint64_t p_w3) {}

bool ualbf_compute_sigma_ok = false;
uint64_t ualbf_compute_sigma_w0 = 0;
uint64_t ualbf_compute_sigma_w1 = 0;
uint64_t ualbf_compute_sigma_w2 = 0;
uint64_t ualbf_compute_sigma_w3 = 0;
void ualbf_compute_sigma(uint64_t p, uint32_t a) {}

bool ualbf_mod_inverse_ok = false;
uint64_t ualbf_mod_inverse_w0 = 0;
uint64_t ualbf_mod_inverse_w1 = 0;
uint64_t ualbf_mod_inverse_w2 = 0;
uint64_t ualbf_mod_inverse_w3 = 0;
void ualbf_mod_inverse_256(uint64_t a_w0, uint64_t a_w1, uint64_t a_w2, uint64_t a_w3, uint64_t m_w0, uint64_t m_w1, uint64_t m_w2, uint64_t m_w3) {}

void lean_initialize_runtime_module() {}
void lean_initialize() {}
void initialize_Ualbf_C_Main() {}
void lean_initialize_thread() {}
