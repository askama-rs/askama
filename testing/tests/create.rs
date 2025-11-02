use askama::Template;

// This test ensures that rust macro calls in `let`/`set` statements are not prepended with `&`.
#[test]
fn create() {
    #[derive(Template)]
    #[template(
        source = r#"{%- create x -%}
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
