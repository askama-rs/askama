use askama::Template;

#[derive(Template)]
#[template(
    ext = "txt",
    source = "{% if show %}{% block list %}{{ s }}{% endblock %}{% endif %}",
    block = "list"
)]
struct InIf<'a> {
    show: bool,
    s: &'a str,
}

#[derive(Template)]
#[template(
    ext = "txt",
    source = "{% match n %}{% when Some(n) %}{% block one %}{{ n }}{% endblock %}{% else %}{% endmatch %}",
    blocks = ["one"]
)]
struct InMatch {
    n: Option<u32>,
}

#[derive(Template)]
#[template(
    ext = "txt",
    source = "{% for i in items %}{% block item %}{{ i }}{% endblock %}{% endfor %}",
    blocks = ["item"]
)]
struct InFor {
    items: Vec<u32>,
}

fn main() {
}
