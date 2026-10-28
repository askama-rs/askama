use askama::Template;

#[derive(Template)]
#[template(ext = "txt", source = "äöü {{ a.b.c!( hello ) }}")]
struct UnexpectedToken;

#[derive(Template)]
#[template(ext = "txt", source = "äöü {% block meta %}then{% else %}else{% endblock meta %}")]
struct UnexpectedElse;

fn main() {}
