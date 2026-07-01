extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn, ReturnType, Type, FnArg, PatType, PatIdent, Pat};

#[proc_macro_attribute]
pub fn lean_ffi_export(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let block = &input_fn.block;
    
    let mut args = Vec::new();
    let mut arg_wrappers = Vec::new();
    let mut arg_vars = Vec::new();

    for arg in &input_fn.sig.inputs {
        if let FnArg::Typed(PatType { pat, ty, .. }) = arg {
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
