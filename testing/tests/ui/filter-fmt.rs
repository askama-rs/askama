use askama::Template;

#[derive(Template)]
#[template(source = r#"{{ "{}" | fmt(12) }}"#, ext = "txt")]
pub struct ShouldBeFormat;

#[derive(Template)]
#[template(source = r#"{{ 12 | fmt(12) }}"#, ext = "txt")]
pub struct WrongFmt;

#[derive(Template)]
#[template(source = r#"{{ 12 | format("{}") }}"#, ext = "txt")]
pub struct ShouldBeFmt;

#[derive(Template)]
#[template(source = r#"{{ 12 | format() }}"#, ext = "txt")]
pub struct WrongFormat;

fn main() {}
