use askama::Template;

// This test ensures that rust macro calls in `let`/`set` statements are not prepended with `&`.
#[test]
fn let_macro() {
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

// Ensures that variables name can start with `_`.
#[test]
fn underscore_ident1() {
    #[derive(Template)]
    #[template(source = r#"{% let _x = 7 %}{{ _x }}"#, ext = "html")]
    struct X;

    assert_eq!(X.render().unwrap(), "7")
}

// Ensures that variables can be named `_`.
#[allow(irrefutable_let_patterns)] // part of the test
#[allow(clippy::redundant_pattern_matching)] // We want to test if `Some(_)` is recognized.
#[test]
fn underscore_ident2() {
    #[derive(Template)]
    #[template(
        source = r#"{% if let Some(_) = Some(12) %}hey{% endif %}
{% if let [_] = [12] %}hoy{% endif %}
{% match [12] %}
{%- when [_] %}matched
{%- endmatch -%}
{%- let _ = 2 -%}
{%- let [_] = [2] -%}
"#,
        ext = "html"
    )]
    struct X;

    assert_eq!(X.render().unwrap(), "hey\nhoy\nmatched");
}

#[test]
fn let_block() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- set navigation %}{{b}}: c{% endset -%}
{{ navigation -}}
"#,
        ext = "txt"
    )]
    struct Foo {
        b: u32,
    }

    assert_eq!(Foo { b: 0 }.render().unwrap(), "0: c");
}
