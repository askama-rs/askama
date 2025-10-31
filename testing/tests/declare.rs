use askama::Template;

// This test ensures that the `decl` keyword works as expected.
#[test]
fn decl() {
    #[derive(Template)]
    #[template(
        source = r#"{%- decl x -%}
{%- if y -%}
    {%- let x = String::new() %}
{%- else -%}
    {%- let x = format!("blob") %}
{%- endif -%}
{{ x }}"#,
        ext = "html"
    )]
    struct A {
        y: bool,
    }

    assert_eq!(A { y: false }.render().unwrap(), "blob");
    assert_eq!(A { y: true }.render().unwrap(), "");
}

// Same as `decl` except with the `declare` keyword.
#[test]
fn declare() {
    #[derive(Template)]
    #[template(
        source = r#"{%- declare x -%}
{%- if y -%}
    {%- let x = String::new() %}
{%- else -%}
    {%- let x = format!("blob") %}
{%- endif -%}
{{ x }}"#,
        ext = "html"
    )]
    struct A {
        y: bool,
    }

    assert_eq!(A { y: false }.render().unwrap(), "blob");
    assert_eq!(A { y: true }.render().unwrap(), "");
}
