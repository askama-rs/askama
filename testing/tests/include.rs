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
