use askama::Template;

// Check if the block call is duplicated in the current template.
#[derive(Template)]
#[template(
    source = r##"{% extends "base.html" %}

{% block content %}{% endblock %}
{% block content %}{% endblock %}
"##,
    ext = "txt",
)]
struct X {
    title: &'static str,
}

// Check if the block call is called in the extended template and in the current one.
#[derive(Template)]
#[template(
    source = r##"{% extends "child.html" %}

{% block content %}another{% endblock %}
"##,
    ext = "txt",
)]
struct X2 {
    title: &'static str,
}

fn main() {}
