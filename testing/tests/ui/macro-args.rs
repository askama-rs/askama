// This test ensures that the proc-macro fails if two arguments are not separated.

use askama::Template;

#[derive(Template)]
#[template(
    source = r###"{{e!{ r#""#r"  \ "}}}"###,
    ext = "html"
)]
struct Example;

fn main() {}
