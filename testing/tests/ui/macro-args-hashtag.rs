// This test ensures that we have the right error if a `#` character isn't prepended by
// a whitespace character and also that lifetimes are correctly handled.

use askama::Template;

#[derive(Template)]
#[template(
    source = r###"{{z!{'r#}}}"###,
    ext = "html"
)]
struct Example;

#[derive(Template)]
#[template(
    source = r###"{{z!{'r# y}}}"###,
    ext = "html"
)]
struct Example2;

#[derive(Template)]
#[template(
    source = r###"{{z!{'break}}}"###,
    ext = "html"
)]
struct Example3;

#[derive(Template)]
#[template(
    source = r###"{{z!{'r#self}}}"###,
    ext = "html"
)]
struct Example4;

fn main() {}
