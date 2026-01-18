// This test ensures that we don't emit a warning when `foo` is used in `extend-duplicated.html`.
// However we're supposed to have two warnings:
// 1. In `extend-duplicated.html` since `content` block is called twice.
// 2. In the current file since `foo` block is called twice.

use askama::Template;

#[derive(Template)]
#[template(source = r#"{% extends "extend-duplicated.html" %}
{% block foo %}blob{% endblock %}
{% block foo %}blob{% endblock %}
"#, ext = "txt")]
struct Foo {
    title: &'static str,
}

fn main() {}
