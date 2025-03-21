# askama_escape: HTML escaping, extracted from [Askama](https://askama.readthedocs.io/)

[![Crates.io](https://img.shields.io/crates/v/askama_escape?logo=rust&style=flat-square&logoColor=white "Crates.io")](https://crates.io/crates/askama)
[![GitHub Workflow Status](https://img.shields.io/github/actions/workflow/status/askama-rs/askama/rust.yml?branch=master&logo=github&style=flat-square&logoColor=white "GitHub Workflow Status")](https://github.com/askama-rs/askama/actions/workflows/rust.yml)
[![docs.rs](https://img.shields.io/docsrs/askama_escape?logo=docsdotrs&style=flat-square&logoColor=white "docs.rs")](https://docs.rs/askama_escape/)

Useful if you don't need a template engine, but if you need to escape a text for HTML or XML.

This implementation escapes `'"'`, `'&'`, `'\'',` `'<'` and `'>'`.

### Example

```rust
use askama_escape::{escape, escape_html, escape_html_char, Html};

assert_eq!(
    escape("<script>alert('Hello & bye!')</script>", Html).to_string(),
    "&#60;script&#62;alert(&#39;Hello &#38; bye!&#39;)&#60;/script&#62;",
);

let mut dest = String::new();
escape_html(&mut dest, "<script>alert('Hello & bye!')</script>").unwrap();
assert_eq!(
    dest,
    "&#60;script&#62;alert(&#39;Hello &#38; bye!&#39;)&#60;/script&#62;",
);

let mut dest = String::new();
escape_html_char(&mut dest, '&').unwrap();
assert_eq!(dest, "&#38;");
```
