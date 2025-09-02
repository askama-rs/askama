use askama::Template;

#[derive(Template)]
#[template(
    source = r##"bla
{% extends "base.html" %}
"##,
    ext = "txt",
)]
pub struct X;

fn main() {}
