use askama::Template;

#[test]
fn test_include() {
    #[derive(Template)]
    #[template(path = "include.html")]
    struct IncludeTemplate<'a> {
        strs: &'a [&'a str],
    }

    let strs = vec!["foo", "bar"];
    let s = IncludeTemplate { strs: &strs };
    assert_eq!(s.render().unwrap(), "\n  INCLUDED: foo\n  INCLUDED: bar");
}

#[test]
fn test_include_with_nested_paths() {
    #[derive(Template)]
    #[template(path = "leaf-templates/includer.html")]
    struct LeafTemplate;

    assert!(LeafTemplate.render().is_ok());
}

#[test]
fn test_include_extends() {
    #[derive(Template)]
    #[template(path = "include-extends.html")]
    struct IncludeExtendsTemplate<'a> {
        name: &'a str,
    }

    let template = IncludeExtendsTemplate { name: "Alice" };

    assert_eq!(
        template.render().unwrap(),
        "<div>\n    \
         <h1>Welcome</h1>\n    \
         <div>\n    \
         <p>Below me is the header</p>\n    \
         foo\n    \
         <p>Above me is the header</p>\n\
         </div>\n\
         Hello, Alice!\n\
         </div>"
    );
}

#[test]
fn test_include_macro() {
    #[derive(Template)]
    #[template(path = "include-macro.html")]
    struct IncludeMacroTemplate<'a> {
        name: &'a str,
        name2: &'a str,
    }

    let template = IncludeMacroTemplate {
        name: "Alice",
        name2: "Bob",
    };

    assert_eq!(template.render().unwrap(), "Hello, Alice!\nHowdy, Bob!");
}

// Check that if an `extends` has an `include` calling a `block`, then this `block` being the
// first called, the following ones will be ignored.
//
// So in this test:
// 1. `block_in_include_extended.html` extends `block_in_include_base.html`.
// 2. `block_in_include_base.html` defines a block called `block_in_base` and includes
//    `block_in_include_partial.html`.
// 3. `block_in_include_partial.html` uses the block `block_in_base`.
// 4. Back to `block_in_include_extended.html`: it uses the block `block_in_base`. However, this
//    block was already called, so this second call is ignored.
//
// Related issue is <https://github.com/askama-rs/askama/issues/272>.
#[test]
fn block_in_include() {
    #[derive(Template)]
    #[template(path = "block_in_include_extended.html")]
    struct TmplExtended;

    #[derive(Template)]
    #[template(path = "block_in_include_base.html", block = "block_in_base")]
    struct TmplBlockInBase;

    #[derive(Template)]
    #[template(path = "block_in_include_partial.html", block = "block_in_partial")]
    struct TmplBlockInPartial;

    assert_eq!(
        TmplExtended.render().unwrap(),
        "block_in_base: from extended!\nblock_in_partial: from partial!\n"
    );
    assert_eq!(
        TmplBlockInBase.render().unwrap(),
        "block_in_base: from base!\n"
    );
    assert_eq!(
        TmplBlockInPartial.render().unwrap(),
        "block_in_partial: from partial!\n"
    );
}

#[test]
fn test_nested_includes() {
    #[derive(Template)]
    #[template(path = "include-nested.html")]
    struct IncludeTemplate<'a> {
        strs: &'a [&'a str],
    }

    let strs = vec!["foo", "bar"];
    let s = IncludeTemplate { strs: &strs };
    assert_eq!(
        s.render().unwrap(),
        "\n  NESTED: INCLUDED: foo\n  NESTED: INCLUDED: bar"
    );
}

#[test]
fn test_include_block() {
    // Only `value` and `length` are rendered, so the struct needs no `title`.
    #[derive(Template)]
    #[template(
        source = r#"{% include "include-block-page.html" block value %}
{%- include "include-block-page.html" block length %}"#,
        ext = "html"
    )]
    struct Partial<'a> {
        value: &'a str,
        length: usize,
    }

    let partial = Partial {
        value: "some value",
        length: 10,
    };
    assert_eq!(
        partial.render().unwrap(),
        "\n<p>Value: some value</p>\n<p>Length: 10</p>"
    );
}

#[test]
fn test_include_block_ws() {
    #[derive(Template)]
    #[template(
        source = r#"<b> {%- include "include-block-page.html" block title -%} </b>"#,
        ext = "html"
    )]
    struct Title<'a> {
        title: &'a str,
    }

    assert_eq!(Title { title: "Home" }.render().unwrap(), "<b>Home</b>");
}

#[test]
fn test_include_block_sees_locals() {
    #[derive(Template)]
    #[template(
        source = r#"{% for name in names %}{% include "fragment-simple.html" block body %}{% endfor %}"#,
        ext = "html"
    )]
    struct Loop<'a> {
        names: &'a [&'a str],
    }

    let names = ["a", "b"];
    assert_eq!(
        Loop { names: &names }.render().unwrap(),
        "\n<p>Hello a!</p>\n\n<p>Hello b!</p>\n"
    );
}

#[test]
fn test_include_nested_block() {
    #[derive(Template)]
    #[template(
        source = r#"{% include "fragment-nested-block.html" block nested %}"#,
        ext = "html"
    )]
    struct Nested;

    #[derive(Template)]
    #[template(
        source = r#"{% include "fragment-nested-block.html" block body %}"#,
        ext = "html"
    )]
    struct Outer;

    assert_eq!(Nested.render().unwrap(), "\n<p>I should be here.</p>\n");
    assert_eq!(
        Outer.render().unwrap(),
        "\n<p>Don't render me!</p>\n\n<p>I should be here.</p>\n\n"
    );
}

#[test]
fn test_include_block_super() {
    #[derive(Template)]
    #[template(
        source = r#"{% include "fragment-super.html" block body %}"#,
        ext = "html"
    )]
    struct Super<'a> {
        name: &'a str,
    }

    #[derive(Template)]
    #[template(
        source = r#"{% include "fragment-nested-super.html" block body %}"#,
        ext = "html"
    )]
    struct NestedSuper<'a> {
        name: &'a str,
    }

    #[derive(Template)]
    #[template(
        source = r#"{% include "fragment-simple.html" block body %}"#,
        ext = "html"
    )]
    struct Overridden<'a> {
        name: &'a str,
    }

    // A block the child template does not override comes from its parent.
    #[derive(Template)]
    #[template(
        source = r#"{% include "include-block-child.html" block body %}"#,
        ext = "html"
    )]
    struct FromParent;

    assert_eq!(
        Super { name: "world" }.render().unwrap(),
        "\n<p>Hello world!</p>\n\n<p>Parent body content</p>\n\n"
    );
    assert_eq!(
        NestedSuper { name: "world" }.render().unwrap(),
        "\n<p>Hello world!</p>\n\n[\n<p>Parent body content</p>\n]\n\n"
    );
    assert_eq!(
        Overridden { name: "world" }.render().unwrap(),
        "\n<p>Hello world!</p>\n"
    );
    assert_eq!(
        FromParent.render().unwrap(),
        "\n<p>Parent body content</p>\n"
    );
}

#[test]
fn test_include_block_in_block_fragment() {
    // The `oob` block is rendered on its own and includes a block of another template.
    #[derive(Template)]
    #[template(
        source = r#"{{ skipped }}{% block oob %}[{% include "fragment-simple.html" block body %}]{% endblock %}"#,
        ext = "html",
        blocks = ["oob"]
    )]
    struct Page<'a> {
        skipped: &'a str,
        name: &'a str,
    }

    let page = Page {
        skipped: "skipped",
        name: "world",
    };
    assert_eq!(page.as_oob().render().unwrap(), "[\n<p>Hello world!</p>\n]");
    assert_eq!(page.render().unwrap(), "skipped[\n<p>Hello world!</p>\n]");
}

#[test]
fn test_include_block_outside_block_fragment() {
    // Outside the `oob` fragment, the included block must stay discarded too.
    #[derive(Template)]
    #[template(
        source = r#"{% include "fragment-simple.html" block body %}{% block oob %}x{% endblock %}"#,
        ext = "html",
        blocks = ["oob"]
    )]
    struct Page<'a> {
        name: &'a str,
    }

    assert_eq!(Page { name: "world" }.as_oob().render().unwrap(), "x");
}

// Like a block fragment, an included block can sit inside an `if` or `match`.
#[test]
fn test_include_block_in_if_and_match() {
    #[derive(Template)]
    #[template(
        source = r#"[{% include "include-block-nested.html" block list %}]"#,
        ext = "html"
    )]
    struct InIf<'a> {
        show: bool,
        s: &'a str,
    }

    assert_eq!(InIf { show: true, s: "x" }.render().unwrap(), "[x]");
    assert_eq!(
        InIf {
            show: false,
            s: "x"
        }
        .render()
        .unwrap(),
        "[]"
    );

    // The child overrides a block that its parent places inside the `if`.
    #[derive(Template)]
    #[template(
        source = r#"[{% include "include-block-nested-child.html" block list %}]"#,
        ext = "html"
    )]
    struct InParentIf {
        show: bool,
    }

    assert_eq!(InParentIf { show: true }.render().unwrap(), "[overridden]");
    assert_eq!(InParentIf { show: false }.render().unwrap(), "[]");

    // The child nests the block in one that only its parent places inside the `if`.
    #[derive(Template)]
    #[template(
        source = r#"[{% include "include-block-nested-inner.html" block item %}]"#,
        ext = "html"
    )]
    struct InBlockInParentIf<'a> {
        show: bool,
        s: &'a str,
    }

    let t = InBlockInParentIf { show: true, s: "x" };
    assert_eq!(t.render().unwrap(), "[x]");
    let t = InBlockInParentIf {
        show: false,
        s: "x",
    };
    assert_eq!(t.render().unwrap(), "[]");

    #[derive(Template)]
    #[template(
        source = r#"[{% include "include-block-match.html" block val %}]"#,
        ext = "txt"
    )]
    struct InMatch {
        opt: Option<u32>,
    }

    assert_eq!(InMatch { opt: Some(3) }.render().unwrap(), "[3]");
    assert_eq!(InMatch { opt: None }.render().unwrap(), "[]");
}

#[test]
fn test_include_block_in_child_template() {
    // Like any top-level content of a child template, the first include renders nothing.
    #[derive(Template)]
    #[template(
        source = r#"{% extends "fragment-base.html" %}
{%- include "include-block-page.html" block title %}
{%- block body %}<h1>{% include "include-block-page.html" block title %}</h1>{% endblock %}"#,
        ext = "html"
    )]
    struct Child<'a> {
        title: &'a str,
    }

    assert_eq!(
        Child { title: "Home" }.render().unwrap(),
        "<html>\n<head></head>\n<body>\n<h1>Home</h1>\n\n</body>\n</html>"
    );
}
