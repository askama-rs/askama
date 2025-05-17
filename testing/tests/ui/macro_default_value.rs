use askama::Template;

#[derive(Template)]
#[template(source = "{%- macro thrice(param1, param2=0) -%}
{{ param1 }} {{ param2 }}
{%- endmacro -%}
{%- call thrice() -%}{%- endcall -%}", ext = "html")]
struct InvalidDefault1;

#[derive(Template)]
#[template(source = "{%- macro thrice(param1, param2=0) -%}
{{ param1 }} {{ param2 }}
{%- endmacro -%}
{%- call thrice(1, 2, 3) -%}{%- endcall -%}", ext = "html")]
struct InvalidDefault2;

fn main() {
}
