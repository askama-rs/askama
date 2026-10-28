use askama::Template;

#[derive(Template)]
#[template(
    source = "
        {% macro one(x) %}{% call one(x) %}{% endcall %}{% endmacro %}
        {% call one(1) %}{% endcall %}
    ",
    ext = "html"
)]
struct Direct;

#[derive(Template)]
#[template(
    source = "
        {% macro one(x) %}{% call two %}{% endcall %}{% endmacro %}
        {% macro two %}{% call three %}{% endcall %}{% endmacro %}
        {% macro three %}{% call four %}{% endcall %}{% endmacro %}
        {% macro four %}{% call five %}{% endcall %}{% endmacro %}
        {% macro five %}{% call one(1) %}{% endcall %}{% endmacro %}
        {% call one(1) %}{% endcall %}
    ",
    ext = "html"
)]
struct Indirect;

#[derive(Template)]
#[template(
    source = r#"
        {% import "macro-recursion-1.html" as next %}
        {% macro some_macro(x) %}
            {% call next::some_macro(x) %}{% endcall %}
        {% endmacro %}
        {% call some_macro(1) %}{% endcall %}
    "#,
    ext = "html"
)]
struct AcrossImports;

#[derive(Template)]
#[template(
    source = "
        {% macro one(n: u32) %}{% call(x) one(n) %}{{ x }}{% endcall %}{% endmacro %}
        {% call(x) one(1) %}{{ x }}{% endcall %}
    ",
    ext = "html"
)]
struct CallerArgs;

#[derive(Template)]
#[template(
    source = "
        {% macro one(n: u32) %}{{ caller() }}{{ one(n) }}{% endmacro %}
        {% call one(1) %}{% endcall %}
    ",
    ext = "html"
)]
struct NoCallerBody;

fn main() {
}
