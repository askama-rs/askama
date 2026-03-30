use askama::Template;

#[derive(Template)]
#[template(
    source = r#"
        {%- macro test(title: Option<u32> = None) -%}{% endmacro -%}
        {%- let y = 12 -%}
        {% call test(y) %}{% endcall -%}
        {% call test(x) %}{% endcall -%}
        {{ test(y) }}
        {{ test(x) }}
    "#,
    ext = "txt",
)]
struct F {
    x: u32,
}

#[derive(Template)]
#[template(
    source = r#"
        {%- macro test(title: Option<u32> = None) -%}{% endmacro -%}
        {%- let y = 12 -%}
        {{ test(y) }}
        {{ test(x) }}
    "#,
    ext = "txt",
)]
struct G {
    x: u32,
}

fn main() {}
