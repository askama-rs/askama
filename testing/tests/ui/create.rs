use askama::Template;

#[derive(Template)]
#[template(source = "{% create x = 'a' %}", ext = "html")]
struct Create1;

fn main() {}
