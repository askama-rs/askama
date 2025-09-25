use askama::Template;

#[derive(Template)]
#[template(source = r#"{{ e!(0o08) }}"#, ext = "html")]
struct A;

#[derive(Template)]
#[template(source = r#"{{ e!(0b3) }}"#, ext = "html")]
struct B;
