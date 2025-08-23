use askama::Template;

#[derive(Template)]
#[template(
    source = r##"bla
{% extends "base.html" %}
"##,
    ext = "txt",
    print = "ast"
)]
pub struct X;

fn main() {}
