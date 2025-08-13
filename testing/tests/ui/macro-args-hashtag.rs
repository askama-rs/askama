// This test ensure that we have the right error if a `#` character isn't prepended by
// a whitespace character.

use askama::Template;

#[derive(Template)]
#[template(
    source = r###"{{z!{'r#}}}"###,
    ext = "html"
)]
struct Example;

fn main() {}
