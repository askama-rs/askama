use askama::Template;

#[derive(Template)]
#[template(
    source = r#"
    {% macro test() %}
        {{- caller("a", "b") -}}
    {%- endmacro -%}
    {%- call(a,b,c) test() -%}
        {{- a -}}
    {%- endcall -%}
    "#,
    ext = "txt"
)]
struct InvalidNumberArguments {
}

#[derive(Template)]
#[template(
    source = r#"
    {% macro test() %}
        {{- caller("a", "b") -}}
    {%- endmacro -%}
    {%- call(a) test() -%}
        {{- a -}}
    {%- endcall -%}
    "#,
    ext = "txt"
)]
struct InvalidNumberArguments1 {
}

#[derive(Template)]
#[template(
    source = r#"
    {% macro test() %}
        {{- caller("a") -}}
    {%- endmacro -%}
    {%- call(a test() -%}
        {{- a -}}
    {%- endcall -%}
    "#,
    ext = "txt"
)]
struct NoClosingParen {
}

#[derive(Template)]
#[template(
    source = r#"
    {% macro test() %}
        {{- caller("a") -}}
    {%- endmacro -%}
    {%- call(a) test() -%}
        {{- caller(a) -}}
    {%- endcall -%}
    "#,
    ext = "txt"
)]
struct CallerInCaller {
}

#[derive(Template)]
#[template(
    source = r#"
    {% macro test2() %}
        {{ caller("bb") }}
    {% endmacro %}
    {% macro test() %}
        {{ caller("a") }}
    {%- endmacro -%}
    {%- call(a) test() -%}
        {% call(b) test2() %}
            {{ caller("b") }}
        {% endcall %}
        {{- a -}}
    {%- endcall -%}
    "#,
    ext = "txt"
)]
struct CallerInCaller1 {
}

#[derive(Template)]
#[template(
    source = r#"{{caller()}}"#,
    ext = "txt"
)]
struct JustCaller{
}

#[derive(Template)]
#[template(
    source = r#"
    {% macro test() %}
        {{ caller("a", one = "b") }}
    {%- endmacro -%}
    {%- call(two, one) test() -%}
        {{- two -}} {{- one -}}
    {%- endcall -%}
    "#,
    ext = "txt"
)]
struct NamedArguments {
}

fn main() {}

