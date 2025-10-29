#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(elided_lifetimes_in_paths)]
#![deny(unreachable_pub)]
#![doc = include_str!("../README.md")]

askama_derive::make_derive_template! {
    #[proc_macro_derive(Template, attributes(template))]
    pub fn derive_template() {
        extern crate askama;
    }
}

askama_derive::make_filter_fn! {
    #[proc_macro_attribute]
    pub fn filter_fn() {
        extern crate askama;
    }
}
