use askama::Template;

#[derive(Template)]
#[template(source = r#"{{ text | truncate }}"#, ext = "html")]
struct NoArgument<'a> {
    text: &'a str,
}

#[derive(Template)]
#[template(source = r#"{{ text | truncate(length) }}"#, ext = "html")]
struct WrongArgumentType<'a> {
    text: &'a str,
    length: f32,
}

#[derive(Template)]
#[template(source = r#"{{ text | truncate(length, extra) }}"#, ext = "html")]
struct TooManyArguments<'a> {
    text: &'a str,
    length: usize,
    extra: bool,
}

fn main() {}
