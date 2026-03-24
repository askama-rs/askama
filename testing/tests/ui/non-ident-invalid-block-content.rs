use askama::Template;

// This test ensures that in case the "tag" in the block is not an ident, we don't end up in a
// "you should never encounter this error" case.
// Regression test for <https://github.com/askama-rs/askama/issues/713>.
#[derive(Template)]
#[template(source = r#"{% {} %}"#, ext = "txt")]
struct Foo;

fn main() {}
