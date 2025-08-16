fn main() {
    println!("cargo::rerun-if-changed=build.rs");

    #[cfg(all(feature = "external-sources", feature = "nightly-spans"))]
    {
        const CODE: &str = r#"
#![feature(proc_macro_def_site, proc_macro_expand)]

extern crate proc_macro;

use proc_macro::{Span, TokenStream};

fn main() {
    if false {
        let _: TokenStream = TokenStream::new().expand_expr().unwrap();
        let _: Span = Span::def_site();
    }
}"#;

        if let Ok(ac) = autocfg::AutoCfg::new()
            && ac.probe_raw(CODE).is_ok()
        {
            println!("cargo::rustc-cfg=USE_NIGHTLY_SPANS");
        }
    }
}
