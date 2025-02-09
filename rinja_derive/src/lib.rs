#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![no_std]
#![doc = include_str!("../README.md")]

#[cfg(not(docsrs))]
compile_error!(
    "\
    New versions of `rinja` will be released under the name `askama`. \
    Please update your dependencies from e.g. `rinja_derive = \"0.3.5\"` to \
    `askama_derive = \"0.13.0\"`.\n\
    Useful information can be found in our upgrade guide \
    <https://askama.readthedocs.io/en/v0.13.0/upgrading.html>, \
    and in our blog post <https://blog.guillaume-gomez.fr/articles/2025-03-19+Askama+and+Rinja+merge>.\
    "
);
