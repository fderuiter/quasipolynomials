use ualbf_macros::universal_pruning_bounds;

universal_pruning_bounds!();

#[cfg(test)]
mod differential_tests {
    use super::*;
    use crate::types::{Uint, UintExt};
    use proptest::prelude::*;
    use std::fs::File;
    use std::io::Write;
    use std::process::Command;
    use std::sync::Once;
    use tempfile::TempDir;

    #[repr(C)]
    #[derive(Debug, Clone, Copy)]
    struct RNS512 {
        w: [u64; 8],
    }

    fn uint_to_rns(u: &Uint) -> RNS512 {
        let mut w = [0u64; 8];
        for i in 0..8 {
            w[i] = ((u >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
        }
        RNS512 { w }
    }

    fn get_library() -> (TempDir, libloading::Library) {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let cpp_path = temp_dir.path().join("metal_logic.cpp");
        let so_path = temp_dir.path().join("libmetal_logic.so");

        let mut f = File::create(&cpp_path).expect("Failed to create cpp file");
        
        let wrapper = format!(r#"
#include <cstdint>

struct RNS512 {{
    uint64_t w[8];
}};

inline uint64_t mulhi(uint64_t a, uint64_t b) {{
    return (uint64_t)(((unsigned __int128)a * (unsigned __int128)b) >> 64);
}}

inline int cmp(RNS512 a, RNS512 b) {{
    for (int i = 7; i >= 0; i--) {{
        if (a.w[i] > b.w[i]) return 1;
        if (a.w[i] < b.w[i]) return -1;
    }}
    return 0;
}}

{}

extern "C" {{
    bool ffi_check_abundancy_overflow(const RNS512* s_l, const RNS512* n_l, uint64_t target_num, uint64_t target_den) {{
        return ualbf_check_abundancy_overflow(*s_l, *n_l, target_num, target_den);
    }}

    bool ffi_check_euler_ceiling(const RNS512* num, const RNS512* den, uint64_t euler_num, uint64_t euler_den) {{
        return ualbf_check_euler_ceiling(*num, *den, euler_num, euler_den);
    }}

    bool ffi_check_prasad_sunitha(uint32_t info_mask, uint32_t baseline_min, uint32_t prasad_sunitha_bound, uint32_t curr_factors_len, uint32_t remaining_components) {{
        return ualbf_check_prasad_sunitha(info_mask, baseline_min, prasad_sunitha_bound, curr_factors_len, remaining_components);
    }}
}}
"#, METAL_PRUNING_LOGIC);

        f.write_all(wrapper.as_bytes()).expect("Failed to write to file");

        let status = Command::new("clang++")
            .arg("-shared")
            .arg("-fPIC")
            .arg("-O2")
            .arg("-x")
            .arg("c++")
            .arg("-o")
            .arg(&so_path)
            .arg(&cpp_path)
            .status()
            .expect("Failed to run clang++");
        
        if !status.success() {
            let status2 = Command::new("g++")
                .arg("-shared")
                .arg("-fPIC")
                .arg("-O2")
                .arg("-x")
                .arg("c++")
                .arg("-o")
                .arg(&so_path)
                .arg(&cpp_path)
                .status()
                .expect("Failed to run g++ fallback");
            assert!(status2.success(), "Failed to compile C++ logic");
        }

        let lib = unsafe { libloading::Library::new(so_path).expect("Failed to load library") };
        (temp_dir, lib)
    }

    static LIB: std::sync::OnceLock<(TempDir, libloading::Library)> = std::sync::OnceLock::new();

    fn get_lib() -> &'static libloading::Library {
        &LIB.get_or_init(|| get_library()).1
    }

    prop_compose! {
        fn arbitrary_rns512()(w0 in any::<u64>(), w1 in any::<u64>(), w2 in any::<u64>(), w3 in any::<u64>(), w4 in any::<u64>(), w5 in any::<u64>(), w6 in any::<u64>(), w7 in 0u64..=0u64) -> Uint {
            let mut u = Uint::zero();
            u |= Uint::from_u64(w0);
            u |= Uint::from_u64(w1) << 64;
            u |= Uint::from_u64(w2) << 128;
            u |= Uint::from_u64(w3) << 192;
            u |= Uint::from_u64(w4) << 256;
            u |= Uint::from_u64(w5) << 320;
            u |= Uint::from_u64(w6) << 384;
            u |= Uint::from_u64(w7) << 448;
            u
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(10000))]

        #[test]
        fn test_differential_abundancy_overflow(
            s_l in arbitrary_rns512(),
            n_l in arbitrary_rns512(),
            target_num in any::<u64>(),
            target_den in any::<u64>()
        ) {
            let rns_s_l = uint_to_rns(&s_l);
            let rns_n_l = uint_to_rns(&n_l);
            
            let ffi_res = unsafe {
                let func: libloading::Symbol<unsafe extern "C" fn(*const RNS512, *const RNS512, u64, u64) -> bool> = get_lib().get(b"ffi_check_abundancy_overflow\0").expect("Failed to find symbol");
                func(&rns_s_l, &rns_n_l, target_num, target_den)
            };
            let cpu_res = cpu_check_abundancy_overflow(&s_l, &n_l, target_num, target_den);
            prop_assert_eq!(cpu_res, ffi_res, "Divergence found! s_l={}, n_l={}, target_num={}, target_den={}", s_l, n_l, target_num, target_den);
        }

        #[test]
        fn test_differential_euler_ceiling(
            num in arbitrary_rns512(),
            den in arbitrary_rns512(),
            euler_num in any::<u64>(),
            euler_den in any::<u64>()
        ) {
            let rns_num = uint_to_rns(&num);
            let rns_den = uint_to_rns(&den);
            
            let ffi_res = unsafe {
                let func: libloading::Symbol<unsafe extern "C" fn(*const RNS512, *const RNS512, u64, u64) -> bool> = get_lib().get(b"ffi_check_euler_ceiling\0").expect("Failed to find symbol");
                func(&rns_num, &rns_den, euler_num, euler_den)
            };
            
            let enum_u = Uint::from_u64(euler_num);
            let eden_u = Uint::from_u64(euler_den);
            let cpu_res = cpu_check_euler_ceiling(&num, &den, &enum_u, &eden_u);
            prop_assert_eq!(cpu_res, ffi_res, "Divergence found! num={}, den={}, euler_num={}, euler_den={}", num, den, euler_num, euler_den);
        }

        #[test]
        fn test_differential_prasad_sunitha(
            info_mask in any::<u32>(),
            baseline_min in 0..=(u32::MAX as usize),
            prasad_sunitha_bound in 0..=(u32::MAX as usize),
            curr_factors_len in 0..=(u32::MAX as usize),
            remaining_components in 0..=(u32::MAX as usize)
        ) {
            let ffi_res = unsafe {
                let func: libloading::Symbol<unsafe extern "C" fn(u32, u32, u32, u32, u32) -> bool> = get_lib().get(b"ffi_check_prasad_sunitha\0").expect("Failed to find symbol");
                func(info_mask, baseline_min as u32, prasad_sunitha_bound as u32, curr_factors_len as u32, remaining_components as u32)
            };
            let cpu_res = cpu_check_prasad_sunitha(info_mask, baseline_min, prasad_sunitha_bound, curr_factors_len, remaining_components);
            prop_assert_eq!(cpu_res, ffi_res, "Divergence found! info_mask={}, baseline_min={}, prasad_bound={}, curr_factors_len={}, rem={}", info_mask, baseline_min, prasad_sunitha_bound, curr_factors_len, remaining_components);
        }
    }
}
