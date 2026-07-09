extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn, ReturnType, PatType, PatIdent, Pat};

#[proc_macro_attribute]
pub fn lean_ffi_export(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let block = &input_fn.block;
    
    let mut args = Vec::new();
    let mut arg_wrappers = Vec::new();
    let mut arg_vars = Vec::new();

    for arg in &input_fn.sig.inputs {
        if let syn::FnArg::Typed(PatType { pat, ty, .. }) = arg {
            if let Pat::Ident(PatIdent { ident, .. }) = &**pat {
                args.push(quote! { #ident: *mut crate::lean_ffi::lean_object });
                arg_wrappers.push(quote! {
                    let #ident = crate::lean_ffi::LeanObjectWrapper::new(#ident);
                });
                arg_vars.push(quote! {
                    let #ident: #ty = crate::lean_ffi::FromLean::from_lean(#ident.as_ptr());
                });
            }
        }
    }

    let output = match &input_fn.sig.output {
        ReturnType::Default => {
            quote! {
                #[no_mangle]
                pub extern "C" fn #fn_name(#(#args),*) {
                    #(#arg_wrappers)*
                    #(#arg_vars)*
                    #block
                }
            }
        },
        ReturnType::Type(_, ty) => {
            quote! {
                #[no_mangle]
                pub extern "C" fn #fn_name(#(#args),*) -> *mut crate::lean_ffi::lean_object {
                    #(#arg_wrappers)*
                    #(#arg_vars)*
                    let result: #ty = #block;
                    crate::lean_ffi::ToLean::to_lean(&result).into_raw()
                }
            }
        }
    };

    output.into()
}

#[proc_macro]
pub fn universal_pruning_bounds(_input: TokenStream) -> TokenStream {
    // Generate the Metal code for the bounds
    let metal_code = r#"
inline RNS512 ualbf_mul_u64(RNS512 a, uint64_t b) {
    RNS512 res;
    uint64_t carry = 0;
    for(int i=0; i<8; i++) {
        uint64_t lo = a.w[i] * b;
        uint64_t hi = mulhi(a.w[i], b);
        uint64_t sum1 = lo + carry;
        uint64_t c1 = (sum1 < carry) ? 1 : 0;
        res.w[i] = sum1;
        carry = hi + c1;
    }
    return res;
}

inline bool ualbf_check_abundancy_overflow(RNS512 s_l, RNS512 n_l, uint64_t target_num, uint64_t target_den) {
    RNS512 lhs = ualbf_mul_u64(s_l, target_den);
    RNS512 rhs = ualbf_mul_u64(n_l, target_num);
    return cmp(lhs, rhs) > 0;
}

inline bool ualbf_check_euler_ceiling(RNS512 num, RNS512 den, uint64_t euler_num, uint64_t euler_den) {
    RNS512 lhs = ualbf_mul_u64(num, euler_den);
    RNS512 rhs = ualbf_mul_u64(den, euler_num);
    return cmp(lhs, rhs) > 0;
}

inline bool ualbf_check_prasad_sunitha(uint32_t info_mask, uint32_t baseline_min, uint32_t prasad_sunitha_bound, uint32_t curr_factors_len, uint32_t remaining_components) {
    uint32_t dynamic_min = baseline_min;
    if ((info_mask & 3) == 0 && (info_mask & 12) == 12) {
        dynamic_min = prasad_sunitha_bound;
    }
    uint32_t remaining_needed = 0;
    if (dynamic_min > curr_factors_len) {
        remaining_needed = dynamic_min - curr_factors_len;
    }
    if (remaining_needed > 0) {
        if (remaining_components < remaining_needed) {
            return true; // Prune!
        }
    }
    return false;
}
"#;

    // Generate the identical Rust code
    let rust_code = quote! {
        use crate::types::UintExt;
        pub const METAL_ABUNDANCY_CALL_SITE: &str = "if (ualbf_check_abundancy_overflow(s_l, prefix_data.n_l, prefix_data.overflow_num, prefix_data.overflow_den)) return;";
        pub const METAL_PRUNING_LOGIC: &str = #metal_code;

        #[macro_export]
        macro_rules! shared_abundancy_call_site {
            ($s_l:expr, $n_l:expr, $num:expr, $den:expr) => {
                crate::universal_bounds::cpu_check_abundancy_overflow($s_l, $n_l, $num, $den)
            }
        }
        pub use shared_abundancy_call_site;

        pub fn cpu_check_abundancy_overflow(s_l: &crate::types::Uint, n_l: &crate::types::Uint, target_num: u64, target_den: u64) -> bool {
            let num = crate::types::Uint::from_u64(target_num);
            let den = crate::types::Uint::from_u64(target_den);
            s_l * den > n_l * num
        }

        pub fn cpu_check_euler_ceiling(num: &crate::types::Uint, den: &crate::types::Uint, euler_num: &crate::types::Uint, euler_den: &crate::types::Uint) -> bool {
            let enum_u = euler_num;
            let eden_u = euler_den;
            num * eden_u > den * enum_u
        }
        
        pub fn cpu_check_prasad_sunitha(info_mask: u32, baseline_min: usize, prasad_sunitha_bound: usize, curr_factors_len: usize, remaining_components: usize) -> bool {
            let mut dynamic_min = baseline_min;
            if (info_mask & 3) == 0 && (info_mask & 12) == 12 {
                dynamic_min = prasad_sunitha_bound;
            }
            let remaining_needed = dynamic_min.saturating_sub(curr_factors_len);
            if remaining_needed > 0 {
                if remaining_components < remaining_needed {
                    return true;
                }
            }
            false
        }
    };

    rust_code.into()
}
