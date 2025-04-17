use askama::Template;

#[derive(Template)]
#[template(
    source = r#"I have {{ count }} butterfl{{ count | pluralize(pl = "ies", "y") }}."#,
    ext = "txt"
)]
struct PositionalAfterNamed {
    count: usize,
}

#[derive(Template)]
#[template(
    source = r#"I have {{ count }} butterfl{{ count | pluralize(pl = "y", pl = "ies") }}."#,
    ext = "txt"
)]
struct NamedRepeated {
    count: usize,
}

#[derive(Template)]
#[template(
    source = r#"I have {{ count }} butterfl{{ count | pluralize("y", sg = "ies") }}."#,
    ext = "txt"
)]
struct NamedButAlreadyPositional {
    count: usize,
}

#[derive(Template)]
#[template(
    source = r#"I have {{ count }} butterfl{{ count | pluralize("y", plural = "ies") }}."#,
    ext = "txt"
)]
struct NoSuchNamedArgument {
    count: usize,
}

#[derive(Template)]
#[template(
    source = r#"Scream: {{ message | uppercase(case = "upper") }}"#,
    ext = "txt"
)]
struct NamedArgumentButNoArgumentExpected<'a> {
    message: &'a str,
}

fn main() {}
