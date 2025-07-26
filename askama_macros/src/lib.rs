#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(elided_lifetimes_in_paths)]
#![deny(unreachable_pub)]
#![doc = include_str!("../README.md")]

mod filter_fn;
mod helpers;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote_spanned;
use syn::{ItemFn, parse_macro_input};

use crate::filter_fn::filter_fn_impl;

struct CompileError {
    span: Span,
    msg: &'static str,
}
impl CompileError {
    pub(crate) fn new(span: Span, msg: &'static str) -> Self {
        Self { span, msg }
    }
}

askama_derive::make_derive_template! {
    #[proc_macro_derive(Template, attributes(template))]
    pub fn derive_template() {
        extern crate askama;
    }
}

#[proc_macro_attribute]
pub fn filter_fn(_args: TokenStream, item: TokenStream) -> TokenStream {
    let ffn = parse_macro_input!(item as ItemFn);
    match filter_fn_impl(ffn) {
        Ok(tt) => tt.into(),
        Err(err) => {
            let msg = err.msg;
            quote_spanned!(err.span => askama::helpers::core::compile_error!(#msg);).into()
        }
    }
}
