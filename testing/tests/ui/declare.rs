use askama::Template;

#[derive(Template)]
#[template(source = "{% decl x = 'a' %}", ext = "html")]
struct Declare1;

#[derive(Template)]
#[template(source = "{% declare x = 'a' %}", ext = "html")]
struct Declare2;

fn main() {}
