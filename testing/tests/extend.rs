use askama::Template;

#[test]
fn test_macro_in_block_inheritance() {
    #[derive(Template)]
    #[template(
        source = r#"{% extends "extend_and_import.html" %}
{%- import "macro.html" as m2 -%}

{%- macro another(param) -%}

--> {{ param }}

{%- endmacro -%}

{% block header -%}
{% call m1::twice(1) %}{% endcall %}
{% call m2::twice(2) %}{% endcall %}
{% call another(3) %}{% endcall %}
{%- endblock -%}
"#,
        ext = "txt"
    )]
    struct A;

    assert_eq!(A.render().unwrap(), "\n\n1 1\n2 2\n--> 3");
}

// This test ensures that comments are allowed before `extends` block.
#[test]
fn test_comment_before_extend() {
    #[derive(Template)]
    #[template(source = r##"{# comment #}{% extends "base.html" %}"##, ext = "txt")]
    pub struct X {
        title: &'static str,
    }
}
