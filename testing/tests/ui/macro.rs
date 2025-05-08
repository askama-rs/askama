use askama::Template;

#[derive(Template)]
#[template(source = "{%- macro thrice(param) -%}
{{ param }}
{%- endmacro -%}

{%- call thrice(2, 3) -%}{%- endcall -%}", ext = "html")]
struct InvalidNumberOfArgs;

#[derive(Template)]
#[template(source = "{%- macro thrice(param, param2) -%}
{{ param }} {{ param2 }}
{%- endmacro -%}

{%- call thrice() -%}{%- endcall -%}", ext = "html")]
struct InvalidNumberOfArgs2;

#[derive(Template)]
#[template(source = "{%- macro thrice() -%}
{%- endmacro -%}

{%- call thrice(1, 2) -%}{%- endcall -%}", ext = "html")]
struct InvalidNumberOfArgs3;

#[derive(Template)]
#[template(source = "{% macro thrice( %}{% endmacro %}", ext = "html")]
struct NoClosingParen1;

#[derive(Template)]
#[template(source = "{% macro thrice(a, b, c %}{% endmacro %}", ext = "html")]
struct NoClosingParen2;

#[derive(Template)]
#[template(source = "{% macro thrice(a, b, c= %}{% endmacro %}", ext = "html")]
struct NoClosingParen3;

#[derive(Template)]
#[template(source = "{% macro thrice(a, b, c = %}{% endmacro %}", ext = "html")]
struct NoClosingParen4;

#[derive(askama::Template)]
#[template(
    source = r#"
        {% macro example(name, value, current, label="", id="") %}
        {% endmacro %}
        {% call example(name="name", value="") %}{% endcall %}
    "#,
    ext = "txt"
)]
struct WrongNumberOfParams;

#[derive(askama::Template)]
#[template(
    source = r#"
        {% macro example(name, value, arg=12) %}
        {% endmacro %}
        {% call example(0, name="name", value="") %}{% endcall %}
    "#,
    ext = "txt"
)]
struct DuplicatedArg;

fn main() {
}
