#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![deny(elided_lifetimes_in_paths)]
#![deny(unreachable_pub)]

askama_derive::make_derive_template! {
    #[proc_macro_derive(Template, attributes(template))]
    pub fn derive_template() {
        extern crate askama;
    }
}
