use askama::Template;

#[derive(Template)]
#[template(source = "
{%- let x: u32 : u64 = 12 -%}
", ext = "html")]
struct T1;

#[derive(Template)]
#[template(source = "
{%- let x: u32 : u64 %}12{% endlet -%}
", ext = "html")]
struct T2;

#[derive(Template)]
#[template(source = "
{%- let x: = -%}
", ext = "html")]
struct T3;

#[derive(Template)]
#[template(source = "
{%- let x: u8 = -%}
", ext = "html")]
struct T4;

#[derive(Template)]
#[template(source = "
{%- let x: -%}
", ext = "html")]
struct T5;

#[derive(Template)]
#[template(source = "
{%- let x: u32
", ext = "html")]
struct T6;

#[derive(Template)]
#[template(source = "
{%- let x
", ext = "html")]
struct T7;

#[derive(Template)]
#[template(source = "
{%- let x = 12
", ext = "html")]
struct T8;

fn main() {}
