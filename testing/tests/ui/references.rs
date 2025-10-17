use askama::Template;

#[derive(Template)]
#[template(source = "{{J::<&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&e>()}}", ext = "html")]
struct X;

fn main() {}
