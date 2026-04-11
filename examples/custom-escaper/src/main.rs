use std::fmt;

use askama::Template;
use askama::filters::Escaper;

#[derive(Template)]
#[template(source = "name: {{name}}", ext = "upper")]
struct Foo {
    name: &'static str,
}

#[derive(Clone, Copy)]
struct Upper;

impl Escaper for Upper {
    fn write_escaped_str<W: fmt::Write>(&self, mut dest: W, string: &str) -> fmt::Result {
        dest.write_str(string.to_uppercase().as_str())
    }

    fn write_escaped_char<W: fmt::Write>(&self, mut dest: W, c: char) -> fmt::Result {
        for upper in c.to_uppercase() {
            dest.write_char(upper)?;
        }
        Ok(())
    }
}

fn main() {
    let rendered = Foo {
        name: "George Name",
    }
    .render()
    .unwrap();
    assert_eq!(&rendered, "name: GEORGE NAME");
    println!("{rendered}");
}
