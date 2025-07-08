use askama::Template;

// Calling into a macro that expects content (`caller`) using
// the call-expr syntax should fail

#[derive(Template)]
#[template(
    source = r#"
{% macro testmacro() %}
    {{caller()}}
{% endmacro %}
{{ testmacro() }}
    "#,
    ext = "txt"
)]
struct MacroCallerWithCallExpr;

fn main() {}
