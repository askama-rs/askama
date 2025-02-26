use askama::Template;

#[test]
fn test_macro() {
    #[derive(Template)]
    #[template(path = "macro.html")]
    struct MacroTemplate<'a> {
        s: &'a str,
    }

    let t = MacroTemplate { s: "foo" };
    assert_eq!(t.render().unwrap(), "12foo foo foo34foo foo5");
}

#[test]
fn test_macro_no_args() {
    #[derive(Template)]
    #[template(path = "macro-no-args.html")]
    struct MacroNoArgsTemplate;

    let t = MacroNoArgsTemplate;
    assert_eq!(t.render().unwrap(), "11the best thing111we've ever done11");
}

#[test]
fn test_import() {
    #[derive(Template)]
    #[template(path = "import.html")]
    struct ImportTemplate<'a> {
        s: &'a str,
    }

    let t = ImportTemplate { s: "foo" };
    assert_eq!(t.render().unwrap(), "foo foo foo");
}

#[test]
fn test_nested() {
    #[derive(Template)]
    #[template(path = "deep-nested-macro.html")]
    struct NestedTemplate;

    let t = NestedTemplate;
    assert_eq!(t.render().unwrap(), "foo");
}

#[test]
fn test_deep_import() {
    #[derive(Template)]
    #[template(path = "deep-import-parent.html")]
    struct DeepImportTemplate;

    let t = DeepImportTemplate;
    assert_eq!(t.render().unwrap(), "foo");
}

#[test]
fn test_short_circuit() {
    #[derive(Template)]
    #[template(path = "macro-short-circuit.html")]
    struct ShortCircuitTemplate {}

    let t = ShortCircuitTemplate {};
    assert_eq!(t.render().unwrap(), "truetruetruefalsetruetrue");
}

#[test]
fn test_nested_macro_with_args() {
    #[derive(Template)]
    #[template(path = "nested-macro-args.html")]
    struct NestedMacroArgsTemplate {}

    let t = NestedMacroArgsTemplate {};
    assert_eq!(t.render().unwrap(), "first second");
}

#[test]
fn str_cmp() {
    #[derive(Template)]
    #[template(path = "macro-import-str-cmp.html")]
    struct StrCmpTemplate;

    let t = StrCmpTemplate;
    assert_eq!(t.render().unwrap(), "AfooBotherCneitherD");
}

#[test]
fn test_macro_self_arg() {
    #[derive(Template)]
    #[template(path = "macro-self-arg.html")]
    struct MacroSelfArgTemplate<'a> {
        s: &'a str,
    }

    let t = MacroSelfArgTemplate { s: "foo" };
    assert_eq!(t.render().unwrap(), "foo");
}

#[test]
// We check that it's always the correct values passed to the
// expected argument.
fn test_named_argument() {
    #[derive(Template)]
    #[template(
        source = "{%- macro thrice(param1, param2) -%}
{{ param1 }} {{ param2 }}
{% endmacro -%}

{%- call thrice(param1=2, param2=3) -%}
{%- call thrice(param2=3, param1=2) -%}
{%- call thrice(3, param2=2) -%}
",
        ext = "html"
    )]
    struct MacroNamedArg;

    assert_eq!(
        MacroNamedArg.render().unwrap(),
        "\
2 3
2 3
3 2
"
    );
}

#[test]
fn test_only_named_argument() {
    #[derive(Template)]
    #[template(
        source = r#"{% macro button(label) %}
{{- label -}}
{% endmacro %}

{%- call button(label="hi") -%}
"#,
        ext = "html"
    )]
    struct OnlyNamedArgument;

    assert_eq!(OnlyNamedArgument.render().unwrap(), "hi");
}

// Check for trailing commas.
#[test]
fn test_trailing_comma() {
    #[derive(Template)]
    #[template(
        source = r#"{% macro button(label , ) %}
{{- label -}}
{% endmacro %}
{%- macro button2(label ,) %}
{% endmacro %}
{%- macro button3(label,) %}
{% endmacro %}
{%- macro button4(label, ) %}
{% endmacro %}
{%- macro button5(label ) %}
{% endmacro %}

{%- call button(label="hi" , ) -%}
{%- call button(label="hi" ,) -%}
{%- call button(label="hi",) -%}
{%- call button(label="hi", ) -%}
{%- call button(label="hi" ) -%}
"#,
        ext = "html"
    )]
    struct TrailingComma;

    assert_eq!(TrailingComma.render().unwrap(), "hihihihihi");
}

#[test]
fn test_default_value() {
    #[derive(Template)]
    #[template(
        source = "{%- macro thrice(param1=0, param2=1) -%}
{{ param1 }} {{ param2 }}
{% endmacro -%}

{%- call thrice() -%}
{%- call thrice(param1=4) -%}
{%- call thrice(param2=4) -%}
{%- call thrice(param2=4, param1=5) -%}
{%- call thrice(4) -%}
",
        ext = "html"
    )]
    struct MacroDefaultValue;

    assert_eq!(
        MacroDefaultValue.render().unwrap(),
        "0 1\n4 1\n0 4\n5 4\n4 1\n"
    );
}

// This test ensures that the mix of named argument and default value generates
// the expected result.
#[test]
fn test_default_value2() {
    #[derive(Template)]
    #[template(
        source = "{%- macro thrice(param1=0, param2=1, param3=2) -%}
{{ param1 }} {{ param2 }} {{ param3 }}
{% endmacro -%}

{%- call thrice(4, param3=5) -%}
",
        ext = "html"
    )]
    struct MacroDefaultValue2;

    assert_eq!(MacroDefaultValue2.render().unwrap(), "4 1 5\n");
}

// This test ensures that we can use the macro arguments as default value.
#[test]
fn test_default_value3() {
    #[derive(Template)]
    #[template(
        source = "{%- macro thrice(a=1, b=a + 1, c=a + b + 2) -%}
{{ a }} {{ b }} {{ c }}
{% endmacro -%}

{%- call thrice() -%}
{%- call thrice(b=6) -%}
{%- call thrice(c=3) -%}
{%- call thrice(a=3) -%}
",
        ext = "html"
    )]
    struct MacroDefaultValue3;

    assert_eq!(
        MacroDefaultValue3.render().unwrap(),
        "1 2 5\n1 6 9\n1 2 3\n3 4 9\n"
    );
}

// This test ensures that we can use declared variables as default value for
// macro arguments.
#[test]
fn test_default_value4() {
    #[derive(Template)]
    #[template(
        source = "{% let x = 12 %}
{%- macro thrice(a=x, b=y) -%}
{{ a }} {{ b }}
{% endmacro -%}

{%- let y = 4 -%}
{%- call thrice() -%}
{%- call thrice(1) -%}
{%- call thrice(b=1) -%}
",
        ext = "html"
    )]
    struct MacroDefaultValue4;

    assert_eq!(MacroDefaultValue4.render().unwrap(), "12 4\n1 4\n12 1\n");
}

// This test ensures that we can macro arguments take precedence over declared
// variables when a macro argument default value is using a variable.
#[test]
fn test_default_value5() {
    #[derive(Template)]
    #[template(
        source = "{% let a = 12 %}
{%- macro thrice(a=3, b=a) -%}
{{ a }} {{ b }}
{% endmacro -%}

{%- call thrice() -%}
{%- call thrice(1) -%}
{%- call thrice(1, 2) -%}
",
        ext = "html"
    )]
    struct MacroDefaultValue5;

    assert_eq!(MacroDefaultValue5.render().unwrap(), "3 3\n1 1\n1 2\n");
}

// This test ensures...
// * macro arguments can be named as rust keywords (e.g. "type", "as", "ref", etc.).
// * the keyword is escaped at definition.
// * the keyword is escaped at invocation.
#[test]
fn test_rust_keywords_as_args() {
    #[derive(Template)]
    #[template(
        source = "
{%- macro input(type) -%}
{{ type }}
{% endmacro -%}

{%- call input(1) -%}
{%- call input(type=1) -%}
",
        ext = "html"
    )]
    struct MacroRustKwArgs;

    // primarily checking for compilation
    assert_eq!(MacroRustKwArgs.render().unwrap(), "1\n1\n");
}

// This test ensures...
// * macro arguments can be named as rust keywords (e.g. "type", "as", "ref", etc.).
// * the argument has a default value.
// * the keyword is escaped at definition.
// * the keyword is escaped at invocation.
#[test]
fn test_rust_keywords_as_args_with_default() {
    #[derive(Template)]
    #[template(
        source = "
{%- macro input(type=1) -%}
{{ type }}
{% endmacro -%}

{%- call input() -%}
{%- call input(1) -%}
{%- call input(type=1) -%}
",
        ext = "html"
    )]
    struct MacroRustKwArgsDefault;

    // primarily checking for compilation
    assert_eq!(MacroRustKwArgsDefault.render().unwrap(), "1\n1\n1\n");
}

// This test ensures...
// * macro arguments can be named as rust keywords (e.g. "type", "as", "ref", etc.).
// * a non-literal expression is given as default
// * the keyword is escaped at definition.
// * the keyword is escaped at invocation.
#[test]
fn test_rust_keywords_as_args_with_default_expr() {
    #[derive(Template)]
    #[template(
        source = "
{%- macro input(type=1+2) -%}
{{ type }}
{% endmacro -%}

{%- call input() -%}
{%- call input(1) -%}
{%- call input(type=1) -%}
",
        ext = "html"
    )]
    struct MacroRustKwArgsDefaultExpr;

    // primarily checking for compilation
    assert_eq!(MacroRustKwArgsDefaultExpr.render().unwrap(), "3\n1\n1\n");
}
