use askama::Template;

#[derive(Template)]
#[template(
    ext = "txt",
    source = "{% for i in items %}{% block item %}{{ i }}{% endblock %}{% endfor %}",
    blocks = ["item"]
)]
struct InFor {
    items: Vec<u32>,
}

#[derive(Template)]
#[template(
    ext = "txt",
    source = "{% for i in items %}{% if *i > 1 %}{% block item %}{{ i }}{% endblock %}{% endif %}{% endfor %}",
    block = "item"
)]
struct InIfInFor {
    items: Vec<u32>,
}

fn main() {
}
