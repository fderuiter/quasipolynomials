import re

with open("/app/ualbf-project/rust-engine/src/dummy_ffi.c", "r") as f:
    content = f.read()

content = re.sub(r'uint64_t ualbf_euler_ceiling_num = (.*?);', r'uint64_t ualbf_euler_ceiling_num() { return \1; }', content)
content = re.sub(r'uint64_t ualbf_euler_ceiling_den = (.*?);', r'uint64_t ualbf_euler_ceiling_den() { return \1; }', content)
content = re.sub(r'uint64_t ualbf_baseline_min_prime_factors = (.*?);', r'uint64_t ualbf_baseline_min_prime_factors() { return \1; }', content)
content = re.sub(r'uint64_t ualbf_prasad_sunitha_bound = (.*?);', r'uint64_t ualbf_prasad_sunitha_bound() { return \1; }', content)

content = re.sub(r'uint64_t ualbf_target_abundance_num = (.*?);', r'uint64_t ualbf_target_abundance_num() { return \1; }', content)
content = re.sub(r'uint64_t ualbf_target_abundance_den = (.*?);', r'uint64_t ualbf_target_abundance_den() { return \1; }', content)

content = re.sub(r'uint32_t ualbf_pollard_rho_iteration_limit = (.*?);', r'uint32_t ualbf_pollard_rho_iteration_limit() { return \1; }', content)
content = re.sub(r'uint32_t ualbf_pollard_rho_batch_size = (.*?);', r'uint32_t ualbf_pollard_rho_batch_size() { return \1; }', content)

content = re.sub(r'uint32_t ualbf_target_min_log10 = (.*?);', r'uint32_t ualbf_target_min_log10() { return \1; }', content)
content = re.sub(r'uint32_t ualbf_target_max_log10 = (.*?);', r'uint32_t ualbf_target_max_log10() { return \1; }', content)
content = re.sub(r'uint64_t ualbf_sieve_limit = (.*?);', r'uint64_t ualbf_sieve_limit() { return \1; }', content)
content = re.sub(r'uint32_t ualbf_max_exponent = (.*?);', r'uint32_t ualbf_max_exponent() { return \1; }', content)
content = re.sub(r'uint64_t ualbf_prefix_stop_threshold = (.*?);', r'uint64_t ualbf_prefix_stop_threshold() { return \1; }', content)
content = re.sub(r'uint32_t ualbf_raycast_gpu_threshold = (.*?);', r'uint32_t ualbf_raycast_gpu_threshold() { return \1; }', content)
content = re.sub(r'uint32_t ualbf_raycast_chunk_size = (.*?);', r'uint32_t ualbf_raycast_chunk_size() { return \1; }', content)

content += '\nconst char* lean_string_cstr(void* str) { return "dummy_hash"; }\n'
content += 'void* ualbf_logic_hash() { return (void*)1; }\n'

with open("/app/ualbf-project/rust-engine/src/dummy_ffi.c", "w") as f:
    f.write(content)
