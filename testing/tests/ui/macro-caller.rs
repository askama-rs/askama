use askama::Template;

#[derive(Template)]
#[template(source = "{%- macro caller() -%}{%- endmacro -%}", ext = "html")]
struct MacroSuper;

fn main() {
}
