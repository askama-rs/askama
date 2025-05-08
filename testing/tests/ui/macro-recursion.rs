use askama::Template;

#[derive(Template)]
#[template(
    source = "
        {% macro one %}{% call one %}{% endcall %}{% endmacro %}
        {% call one %}{% endcall %}
    ",
    ext = "html"
)]
struct Direct;

#[derive(Template)]
#[template(
    source = "
        {% macro one %}{% call two %}{% endcall %}{% endmacro %}
        {% macro two %}{% call three %}{% endcall %}{% endmacro %}
        {% macro three %}{% call four %}{% endcall %}{% endmacro %}
        {% macro four %}{% call five %}{% endcall %}{% endmacro %}
        {% macro five %}{% call one %}{% endcall %}{% endmacro %}
        {% call one %}{% endcall %}
    ",
    ext = "html"
)]
struct Indirect;

#[derive(Template)]
#[template(
    source = r#"
        {% import "macro-recursion-1.html" as next %}
        {% macro some_macro %}
            {% call next::some_macro %}{% endcall %}
        {% endmacro %}
        {% call some_macro %}{% endcall %}
    "#,
    ext = "html"
)]
struct AcrossImports;

fn main() {
}
