use askama::Template;

// Truncated conditional expressions

#[derive(Template)]
#[template(ext = "html", source = "{{ 1 + 2 if }}")]
struct StopAfterIf;

#[derive(Template)]
#[template(ext = "html", source = "{{ 1 + 2 if 🦀 }}")]
struct OtherTokenAfterIf;

#[derive(Template)]
#[template(ext = "html", source = "{{ 1 + 2 if 3 + }}")]
struct EndInBinaryStateInCondition;

#[derive(Template)]
#[template(ext = "html", source = "{{ 1 + 2 if 3 + 4 }}")]
struct ElseIsNotOptional; // actually valid in Jinja, defaults to `else 0`

#[derive(Template)]
#[template(ext = "html", source = "{{ 1 + 2 if 3 + 4 else }}")]
struct StopAfterElse;

#[derive(Template)]
#[template(ext = "html", source = "{{ 1 + 2 if 3 + 4 else 🦀 }}")]
struct OtherTokenAfterElse;

// Raw identifiers and strings are not keywords

#[derive(Template)]
#[template(ext = "html", source = "{{ then r#if condition else otherwise }}")]
struct RawIf;

#[derive(Template)]
#[template(ext = "html", source = "{{ then if condition r#else otherwise }}")]
struct RawElse;

#[derive(Template)]
#[template(ext = "html", source = r#"{{ then "if" condition else otherwise }}"#)]
struct StringIf;

#[derive(Template)]
#[template(ext = "html", source = r#"{{ then if condition "else" otherwise }}"#)]
struct StringElse;

fn main() {}
