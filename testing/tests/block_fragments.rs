use askama::Template;

/// Tests a simple base-inherited template with block fragment rendering.
#[test]
fn test_fragment_simple() {
    #[derive(Template)]
    #[template(path = "fragment-simple.html", block = "body")]
    struct FragmentSimple<'a> {
        name: &'a str,
    }

    let simple = FragmentSimple { name: "world" };

    assert_eq!(simple.render().unwrap(), "\n<p>Hello world!</p>\n");
}

/// Tests a case where a block fragment rendering calls the parent.
/// Single inheritance only.
#[test]
fn test_fragment_super() {
    #[derive(Template)]
    #[template(path = "fragment-super.html", block = "body")]
    struct FragmentSuper<'a> {
        name: &'a str,
    }

    let sup = FragmentSuper { name: "world" };

    assert_eq!(
        sup.render().unwrap(),
        "\n<p>Hello world!</p>\n\n<p>Parent body content</p>\n\n"
    );
}

/// Tests rendering a block fragment inside of a block.
#[test]
fn test_fragment_nested_block() {
    #[derive(Template)]
    #[template(path = "fragment-nested-block.html", block = "nested")]
    struct FragmentNestedBlock;

    let nested_block = FragmentNestedBlock {};

    assert_eq!(
        nested_block.render().unwrap(),
        "\n<p>I should be here.</p>\n"
    );
}

/// Tests rendering a block fragment with multiple inheritance.
/// The middle parent adds square brackets around the base.
#[test]
fn test_fragment_nested_super() {
    #[derive(Template)]
    #[template(path = "fragment-nested-super.html", block = "body")]
    struct FragmentNestedSuper<'a> {
        name: &'a str,
    }

    let nested_sup = FragmentNestedSuper { name: "world" };

    assert_eq!(
        nested_sup.render().unwrap(),
        "\n<p>Hello world!</p>\n\n[\n<p>Parent body content</p>\n]\n\n"
    );
}

/// Tests a case where an expression is defined outside of a block fragment
/// Ideally, the struct isn't required to define that field.
#[test]
fn test_fragment_unused_expression() {
    #[derive(Template)]
    #[template(path = "fragment-unused-expr.html", block = "body")]
    struct FragmentUnusedExpr<'a> {
        required: &'a str,
    }

    let unused_expr = FragmentUnusedExpr {
        required: "Required",
    };

    assert_eq!(unused_expr.render().unwrap(), "\n<p>Required</p>\n");
}

#[test]
fn test_specific_block() {
    #[derive(Template)]
    #[template(path = "blocks.txt", block = "index")]
    struct RenderInPlace<'a> {
        s1: Section<'a>,
    }

    #[derive(Template)]
    #[template(path = "blocks.txt", block = "section")]
    struct Section<'a> {
        values: &'a [&'a str],
    }

    let s1 = Section {
        values: &["a", "b", "c"],
    };
    assert_eq!(s1.render().unwrap(), "[abc]");
    let t = RenderInPlace { s1 };
    assert_eq!(t.render().unwrap(), "\nSection: [abc]\n");
}

#[test]
fn test_render_only_block() {
    #[derive(Template)]
    #[template(
        source = r#"{% block empty %}
{% endblock %}

{% if let Some(var) = var %}
{{ var }}
{% endif %}"#,
        block = "empty",
        ext = "txt"
    )]
    struct Empty {}

    assert_eq!(Empty {}.render().unwrap(), "\n");
}

#[test]
fn test_fragment_include() {
    #[derive(Template)]
    #[template(
        source = r#"{% extends "fragment-base.html" %}

{% block body %}
{% include "included.html" %}
{% endblock %}

{% block other_body %}
<p>Don't render me.</p>
{% endblock %}"#,
        block = "body",
        ext = "html"
    )]
    struct FragmentInclude<'a> {
        s: &'a str,
    }

    let fragment_include = FragmentInclude { s: "world" };
    assert_eq!(fragment_include.render().unwrap(), "\nINCLUDED: world\n");
}

// This test ensures that parent variables are inherited in the block.
// This is a regression test for <https://github.com/askama-rs/askama/issues/246>.
#[test]
fn test_variable_inheritance_in_block() {
    #[derive(Template)]
    #[template(
        source = r#"{% extends "base-decl.txt" %}
{%- block extended -%}
--> {{ variable }}
{% include "use-var.txt" -%}
{% endblock %}"#,
        ext = "txt"
    )]
    struct Y;

    assert_eq!(Y.render().unwrap(), "--> 42\n42");
}

// A block nested in an `if` or `match` renders on its own when its branch is taken.
// See <https://github.com/askama-rs/askama/issues/81>.
#[test]
fn test_fragment_nested_in_if_and_match() {
    #[derive(Template)]
    #[template(
        source = "<ul>{% if show %}<b>{{ s }}</b>{% block list %}<li>{{ s }}</li>{% endblock %}{% endif %}</ul>",
        blocks = ["list"],
        ext = "html"
    )]
    struct InIf<'a> {
        show: bool,
        s: &'a str,
    }

    let t = InIf { show: true, s: "x" };
    assert_eq!(t.render().unwrap(), "<ul><b>x</b><li>x</li></ul>");
    assert_eq!(t.as_list().render().unwrap(), "<li>x</li>");
    assert_eq!(
        InIf {
            show: false,
            s: "x"
        }
        .as_list()
        .render()
        .unwrap(),
        ""
    );

    #[derive(Template)]
    #[template(
        source = "{% if let Some(n) = opt %}{{ n }}[{% block val %}{{ n }}{% endblock %}]{% else %}none{% endif %}",
        blocks = ["val"],
        ext = "txt"
    )]
    struct IfLet {
        opt: Option<u32>,
    }

    assert_eq!(IfLet { opt: Some(3) }.render().unwrap(), "3[3]");
    assert_eq!(IfLet { opt: Some(3) }.as_val().render().unwrap(), "3");
    assert_eq!(IfLet { opt: None }.as_val().render().unwrap(), "");

    #[derive(Template)]
    #[template(
        source = "{% match opt %}{% when Some(n) %}{% if *n > 1 %}{% block big %}big {{ n }}{% endblock %}{% endif %}{% when None %}nil{% endmatch %}",
        blocks = ["big"],
        ext = "txt"
    )]
    struct InMatch {
        opt: Option<u32>,
    }

    assert_eq!(InMatch { opt: Some(3) }.as_big().render().unwrap(), "big 3");
    assert_eq!(InMatch { opt: Some(1) }.as_big().render().unwrap(), "");
    assert_eq!(InMatch { opt: None }.as_big().render().unwrap(), "");

    #[derive(Template)]
    #[template(
        source = "{% block outer %}<div>{% if a %}{% block inner %}in{% endblock %}{% endif %}</div>{% endblock %}",
        blocks = ["outer", "inner"],
        ext = "html"
    )]
    struct InOuter {
        a: bool,
    }

    assert_eq!(
        InOuter { a: true }.as_outer().render().unwrap(),
        "<div>in</div>"
    );
    assert_eq!(InOuter { a: true }.as_inner().render().unwrap(), "in");
    assert_eq!(InOuter { a: false }.as_inner().render().unwrap(), "");
}
