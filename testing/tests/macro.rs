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
fn test_include_in_macro_block() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro test_macro() -%}
    {%- include "foo.html" -%}
{%- endmacro -%}
{%- call test_macro() %}{%- endcall -%}
        "#,
        ext = "txt"
    )]
    struct IncludeInMacroBlock;
    let x = IncludeInMacroBlock {};
    assert_eq!(x.render().unwrap(), "foo.html");
}

#[test]
fn test_macro_caller_context_is_declaration_site() {
    #[derive(Template)]
    #[template(
        ext = "html",
        source = r#"
{%- import "macro-with-caller.html" as parentscope -%}
{%- call parentscope::outer() -%}
    {%- call parentscope::intermediate() -%}{%- endcall -%}
{%- endcall -%}
    "#
    )]
    struct CallsiteContextIsDeclarationSiteTemplate {}

    let t = CallsiteContextIsDeclarationSiteTemplate {};
    assert_eq!(t.render().unwrap(), "<div>intermediatecontent</div>");
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

{%- call thrice(param1=2, param2=3) -%}{%- endcall -%}
{%- call thrice(param2=3, param1=2) -%}{%- endcall -%}
{%- call thrice(3, param2=2) -%}{%- endcall -%}
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

{%- call button(label="hi") -%}{%- endcall -%}
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

{%- call button(label="hi" , ) -%}{%- endcall -%}
{%- call button(label="hi" ,) -%}{%- endcall -%}
{%- call button(label="hi",) -%}{%- endcall -%}
{%- call button(label="hi", ) -%}{%- endcall -%}
{%- call button(label="hi" ) -%}{%- endcall -%}
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

{%- call thrice() -%}{%- endcall -%}
{%- call thrice(param1=4) -%}{%- endcall -%}
{%- call thrice(param2=4) -%}{%- endcall -%}
{%- call thrice(param2=4, param1=5) -%}{%- endcall -%}
{%- call thrice(4) -%}{%- endcall -%}
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

{%- call thrice(4, param3=5) -%}{%- endcall -%}
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

{%- call thrice() -%}{%- endcall -%}
{%- call thrice(b=6) -%}{%- endcall -%}
{%- call thrice(c=3) -%}{%- endcall -%}
{%- call thrice(a=3) -%}{%- endcall -%}
",
        ext = "html"
    )]
    struct MacroDefaultValue3;

    assert_eq!(
        MacroDefaultValue3.render().unwrap(),
        "1 2 5\n1 6 9\n1 2 3\n3 4 9\n"
    );
}

// This test a caller expression with expressions in the arguments.
#[test]
fn test_caller_expr() {
    #[derive(Template)]
    #[template(
        source = "{%- macro thrice(a, b, c) -%}
{{caller(a+10,b - 10,a+b+c)}}
{% endmacro -%}
{%- call(a,b,c) thrice(10,11,13) -%}{{a}} {{b}} {{c + 1}}{%- endcall -%}
",
        ext = "html"
    )]
    struct MacroCallerExpr;
    assert_eq!(MacroCallerExpr.render().unwrap(), "20 1 35\n");
}

#[test]
fn test_caller_in_macro_call_before_caller() {
    #[derive(Template)]
    #[template(
        source = r#"
            {%- macro test2() -%}
                a
                {{- caller() -}}
            {%- endmacro -%}
            {%- macro test() -%}
               {%- call test2() -%}b{%- endcall -%}
               {{- caller() -}}
            {%- endmacro -%}
            {%- call test() -%}{%- call test2() -%}b{%- endcall -%}{%- endcall -%}
        "#,
        ext = "txt"
    )]
    struct CallerWithMacro;
    assert_eq!(CallerWithMacro.render().unwrap(), "abab");
}

#[test]
fn test_caller_in_caller() {
    #[derive(Template)]
    #[template(
        source = r#"
        {%- macro test2() -%}
            {{ caller("bb") }}
        {%- endmacro -%}
        {%- macro test() -%}
            {{ caller("a") }}
            {%- call(b) test2() -%}
                five: {{ b }}
            {%~ endcall -%}
        {%- endmacro -%}
        {%- macro test3() -%}
            {{ caller("cc") }}
        {%- endmacro -%}
        {%- macro test4() -%}
            {{ caller("dd") }}
        {%- endmacro -%}
        {%- call(a) test() -%}
            {%- call(b) test2() -%}
                one: {{ b }}
            {%~ endcall -%}
            {%- call(b) test3() -%}
                two: {{ b }}
                {%~ call(b) test4() -%}
                    three: {{ b }}
                {%~ endcall -%}
            {%- endcall -%}
            four: {{ a }}
        {%~ endcall -%}
        "#,
        ext = "txt"
    )]
    struct CallerInCaller;
    assert_eq!(
        CallerInCaller.render().unwrap(),
        "one: bb\ntwo: cc\nthree: dd\nfour: a\nfive: bb\n"
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
{%- call thrice() -%}{%- endcall -%}
{%- call thrice(1) -%}{%- endcall -%}
{%- call thrice(b=1) -%}{%- endcall -%}
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

{%- call thrice() -%}{%- endcall -%}
{%- call thrice(1) -%}{%- endcall -%}
{%- call thrice(1, 2) -%}{%- endcall -%}
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

{%- call input(1) -%}{%- endcall -%}
{%- call input(type=1) -%}{%- endcall -%}
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

{%- call input() -%}{%- endcall -%}
{%- call input(1) -%}{%- endcall -%}
{%- call input(type=1) -%}{%- endcall -%}
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

{%- call input() -%}{%- endcall -%}
{%- call input(1) -%}{%- endcall -%}
{%- call input(type=1) -%}{%- endcall -%}
",
        ext = "html"
    )]
    struct MacroRustKwArgsDefaultExpr;

    // primarily checking for compilation
    assert_eq!(MacroRustKwArgsDefaultExpr.render().unwrap(), "3\n1\n1\n");
}

// This test ensures that default values can be paths with generics.
#[test]
fn test_macro_default_value_generics() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro test(title = Option::<String>::None, b = Option::<u32>::Some(0)) -%}
    {%- if let Some(title) = title -%}
        Title: {{title}}
    {%- endif -%}
    {%- if let Some(b) = b -%}---> {{b}}{% endif -%}
{%- endmacro -%}

{% call test(b = Option::<u32>::Some(3)) %}{% endcall -%}
"#,
        ext = "html"
    )]
    struct Example;

    assert_eq!(Example.render().unwrap(), "---> 3");
}

#[test]
fn test_expr_macro_call_same_ctx() {
    #[derive(Template)]
    #[template(
        source = "
{%- macro samescope(optarg=1+2) -%}
{{ optarg }}
{% endmacro -%}

{{- samescope() -}}
{{- samescope(1) -}}
",
        ext = "html"
    )]
    struct ExprMacroCall;

    // primarily checking for compilation
    assert_eq!(ExprMacroCall.render().unwrap(), "3\n1\n");
}

#[test]
fn test_expr_macro_call_imported() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- import "macro.html" as otherscope -%}
{{- otherscope::twice("xxx") -}}
"#,
        ext = "html"
    )]
    struct ExprMacroCall;

    // primarily checking for compilation
    assert_eq!(ExprMacroCall.render().unwrap(), "xxx xxx");
}

#[test]
fn test_expr_macro_call_imported_nested() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- import "nested-macro.html" as otherscope -%}
{{- otherscope::parent() -}}
"#,
        ext = "html"
    )]
    struct ExprMacroCall;

    // primarily checking for compilation
    assert_eq!(ExprMacroCall.render().unwrap(), "foo");
}

#[test]
fn test_expr_macro_call_imported_nested2() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- import "nested-macro-callexpr.html" as otherscope -%}
{% let child1 = "Test: Macros scoped by file" %}
{{- otherscope::parent() -}}
"#,
        ext = "html"
    )]
    struct ExprMacroCall;

    // primarily checking for compilation
    assert_eq!(ExprMacroCall.render().unwrap(), "foo");
}

#[test]
fn test_expr_macro_call_importchain_nested() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- import "macro-import-callexpr.html" as otherscope -%}
{{- otherscope::intermediate() -}}
"#,
        ext = "html"
    )]
    struct ExprMacroCall;

    // primarily checking for compilation
    assert_eq!(ExprMacroCall.render().unwrap(), "foo");
}

#[test]
fn test_expr_macro_call_named_arguments() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro testmacro(arg0 = "-", arg1 = 5) -%}
    {{ arg0 }} | {{ arg1 }};
{%- endmacro -%}
{{- testmacro() }}
{{- testmacro("a") }}
{{- testmacro("b", 1337) }}
{{- testmacro("c", arg1 = 1338) }}
{{- testmacro(arg0 = "d", arg1 = 1339) -}}
"#,
        ext = "html"
    )]
    struct ExprMacroCall;

    // primarily checking for compilation
    assert_eq!(
        ExprMacroCall.render().unwrap(),
        "- | 5;a | 5;b | 1337;c | 1338;d | 1339;"
    );
}

#[test]
fn test_macro_caller_is_defined_check() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro testmacro() -%}
    {%- if caller is defined -%}
        {{- caller() -}}
    {%- else -%}
        no caller defined
    {%- endif -%}
{%- endmacro -%}
{{- testmacro() -}}
{%- call testmacro() -%}|this time with caller{%- endcall -%}
"#,
        ext = "html"
    )]
    struct ExprMacroCall;

    // primarily checking for compilation
    assert_eq!(
        ExprMacroCall.render().unwrap(),
        "no caller defined|this time with caller"
    );
}

// This test ensures that raw lifetimes are correctly handled.
#[test]
fn test_macro_raw_lifetime() {
    macro_rules! test {
        ('r#ignore_me) => {
            "ok"
        };
    }

    #[derive(Template)]
    #[template(source = r##"{{ test!('r#ignore_me) }}"##, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "ok");
}

// Because of how we generated "resolved variables", we had it in two parts:
// first the `(__askama_item` and then `index0)` (with the `.` generated in the
// middle). Of course, doing that in two passes went horribly wrong as you cannot
// generate `Ident` from that.
#[test]
fn test_loop_variable_in_macro_call() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro w(lol) -%}
y: {{ lol -}}
{% endmacro -%}

{%- for x in &[0] -%}
{%- call w(loop.index) %}{% endcall -%}
{% endfor %}"#,
        ext = "txt"
    )]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "y: 1");
}
