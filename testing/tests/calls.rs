use askama::Template;

#[test]
fn test_one_func() {
    #[derive(Template)]
    #[template(source = "{{ b(value) }}", ext = "txt")]
    struct OneFunction {
        value: u32,
    }

    impl OneFunction {
        fn b(&self, x: &u32) -> u32 {
            self.value + x
        }
    }

    let t = OneFunction { value: 10 };
    assert_eq!(t.render().unwrap(), "20");
}

#[test]
fn test_one_func_self() {
    #[derive(Template)]
    #[template(source = "{{ self.func(value) }}", ext = "txt")]
    struct OneFunctionSelf {
        value: i32,
    }

    impl OneFunctionSelf {
        fn func(&self, i: &i32) -> i32 {
            2 * i
        }
    }

    let t = OneFunctionSelf { value: 123 };
    assert_eq!(t.render().unwrap(), "246");
}

#[test]
fn test_one_func_index() {
    #[derive(Template)]
    #[template(source = "{{ func[index](value) }}", ext = "txt")]
    struct OneFunctionIndex<'a> {
        func: &'a [fn(&i32) -> i32],
        value: i32,
        index: usize,
    }

    let t = OneFunctionIndex {
        func: &[|_| panic!(), |&i| 2 * i, |_| panic!(), |_| panic!()],
        value: 123,
        index: 1,
    };
    assert_eq!(t.render().unwrap(), "246");
}

#[test]
fn test_one_func_binop() {
    struct AddToGetAFunction;

    impl std::ops::Add<usize> for &AddToGetAFunction {
        type Output = fn(&i32) -> i32;

        fn add(self, rhs: usize) -> Self::Output {
            assert_eq!(rhs, 1);
            |&i| 2 * i
        }
    }

    #[derive(Template)]
    #[template(source = "{{ (func + index)(value) }}", ext = "txt")]
    struct OneFunctionBinop<'a> {
        func: &'a AddToGetAFunction,
        value: i32,
        index: usize,
    }

    let t = OneFunctionBinop {
        func: &AddToGetAFunction,
        value: 123,
        index: 1,
    };
    assert_eq!(t.render().unwrap(), "246");
}

mod test_double_attr_arg {
    use askama::Template;

    fn double_attr_arg_helper(x: u32) -> u32 {
        x * x + x
    }

    #[derive(askama::Template)]
    #[template(
        source = "{{ self::double_attr_arg_helper(self.x.0 + 2) }}",
        ext = "txt"
    )]
    struct DoubleAttrArg {
        x: (u32,),
    }

    #[test]
    fn test_double_attr_arg() {
        let t = DoubleAttrArg { x: (10,) };
        assert_eq!(t.render().unwrap(), "156");
    }
}

// This test ensures that whitespace characters are removed when `endcall` ends
// with `-%}`.
#[test]
fn test_caller() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro test() -%}
{{- caller() -}}
{%- endmacro -%}
{%- call() test() %}
nested
{% endcall -%}
"#,
        ext = "html"
    )]
    struct CallerEmpty;
    assert_eq!(CallerEmpty.render().unwrap(), "\nnested\n");
}

// This test ensures that whitespace characters are NOT removed when `endcall` ends
// with `%}`.
#[test]
fn test_caller2() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro test() -%}
{{- caller() -}}
{%- endmacro -%}
{%- call() test() %}
nested
{% endcall %}
"#,
        ext = "html"
    )]
    struct CallerEmpty;
    assert_eq!(CallerEmpty.render().unwrap(), "\nnested\n\n");
}

#[test]
fn test_nested_caller_aliasing1() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro inner() -%}
    inner before|{{- caller(1) -}}|inner after
{%- endmacro -%}
{%- macro outer() -%}
    outer before|
    {%- set caller_ = caller -%}
    {%- call(c) inner() -%}
        {{c}}
        {{- caller_(3, 4) -}}
    {%- endcall -%}
    |outer after
{%- endmacro -%}
{%- call(a, b) outer() -%}
    content{{a}}-{{b}}
{%- endcall -%}
"#,
        ext = "html"
    )]
    struct NestedCallerAliasing;
    assert_eq!(
        NestedCallerAliasing.render().unwrap(),
        "outer before|inner before|1content3-4|inner after|outer after"
    );
}

#[test]
fn test_nested_caller_aliasing2() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro layer0() -%}A{{ caller() }}a{%- endmacro -%}
{%- macro layer1() -%}B
    {%- set caller_layer1 = caller -%}
    {%- call layer0() -%}{{ caller_layer1() }}{%- endcall -%}
b{%- endmacro -%}
{%- macro layer2() -%}C
    {%- set caller_layer2 = caller -%}
    {%- call layer1() -%}{{ caller_layer2() }}{%- endcall -%}
c{%- endmacro -%}

{%- call layer2() -%}_CONTENT_{%- endcall -%}
"#,
        ext = "html"
    )]
    struct NestedCallerAliasing;
    assert_eq!(NestedCallerAliasing.render().unwrap(), "CBA_CONTENT_abc");
}

#[test]
fn test_caller_struct() {
    struct TestInput<'a> {
        a: &'a str,
        b: &'a str,
    }
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro test(a) -%}
{{- caller(a) -}}
{%- endmacro -%}
{%- call(value) test(a) -%}
a: {{value.a}}
b: {{value.b}}
{%- endcall -%}
"#,
        ext = "txt"
    )]
    struct Tmpl<'a> {
        a: TestInput<'a>,
    }
    let x = Tmpl {
        a: TestInput { a: "one", b: "two" },
    };
    assert_eq!(x.render().unwrap(), "a: one\nb: two");
}

#[test]
fn test_include_in_call_block() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro test_macro() -%}
    {{caller()}}
{%- endmacro -%}
{%- call test_macro() %}
    {%- include "foo.html" -%}
{%- endcall -%}
        "#,
        ext = "txt"
    )]
    struct IncludeInCallBlock;
    let x = IncludeInCallBlock {};
    assert_eq!(x.render().unwrap(), "foo.html");
}

#[test]
fn test_include_in_call_block_in_macro() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro macro1() -%}
    {{caller()}}
{%- endmacro -%}
{%- macro macro2() -%}
    {%- call macro1() -%}
        {%- include "foo.html" -%}
    {%- endcall -%}
{%- endmacro -%}
{%- call macro2() %}{%- endcall -%}
        "#,
        ext = "txt"
    )]
    struct IncludeInCallBlock;
    let x = IncludeInCallBlock {};
    assert_eq!(x.render().unwrap(), "foo.html");
}

#[test]
fn test_caller_args() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro test() -%}
{{~ caller("test") ~}}
{{~ caller(1) ~}}
{%- endmacro -%}
{%- call(value) test() -%}
nested {{value}}  
{%- endcall -%}
"#,
        ext = "html"
    )]
    struct CallerEmpty {}
    let x = CallerEmpty {};
    assert_eq!(x.render().unwrap(), "nested test\nnested 1");
}

// Ensures that fields are not moved when calling a jinja macro.
#[test]
fn test_do_not_move_fields() {
    #[derive(Template)]
    #[template(
        source = "
{%- macro package_navigation(title, show) -%}
{%- if show -%}
{{title}}
{%- else -%}
no show
{%- endif -%}
{%- endmacro -%}

{%- call package_navigation(title=title, show=true) -%}{%- endcall -%}
",
        ext = "html"
    )]
    struct DoNotMoveFields {
        title: String,
    }

    let x = DoNotMoveFields {
        title: "a".to_string(),
    };
    assert_eq!(x.render().unwrap(), "a");
}

#[test]
fn test_closure_field() {
    #[derive(Template)]
    #[template(source = "{{ (func)(value) }}", ext = "txt")]
    struct ClosureField {
        func: fn(&i32) -> i32,
        value: i32,
    }

    let t = ClosureField {
        func: |&i| 2 * i,
        value: 123,
    };
    assert_eq!(t.render().unwrap(), "246");
}

mod test_not_method {
    use askama::Template;

    fn single() -> &'static str {
        "a"
    }

    mod sub_mod {
        pub fn sub_fn(v: i32) -> i32 {
            v * 2
        }
    }

    #[derive(Template)]
    #[template(
        source = "
    {{- self::single() -}}
    {{- sub_mod::sub_fn(3) -}}
    ",
        ext = "txt"
    )]
    struct NotMethod;

    #[test]
    fn test_not_method() {
        assert_eq!(NotMethod.render().unwrap(), "a6");
    }
}

mod test_deref_method_arg {
    use askama::Template;

    #[derive(Template)]
    #[template(
        source = "
    {{- bar(x) -}}
    {{- bar(&*x) -}}
    {{- foo(*x) -}}
    {{- foo(*&*x) -}}
    {# #} {{+ extra_fn::bar(x) -}}
    {{- extra_fn::bar(&*x) -}}
    {{- extra_fn::foo(*x) -}}
    {{- extra_fn::foo(*&*x) -}}
    ",
        ext = "txt"
    )]
    struct DerefMethodArg {
        x: u32,
    }

    mod extra_fn {
        pub fn bar(x: &u32) -> u32 {
            *x + 4
        }
        pub fn foo(x: u32) -> u32 {
            x + 5
        }
    }

    impl DerefMethodArg {
        fn bar(&self, x: &u32) -> u32 {
            *x + 1
        }
        fn foo(&self, x: u32) -> u32 {
            x
        }
    }

    // This test ensures that the `*`/`&` operators are correctly placed on method/function arguments.
    #[test]
    fn test_deref_method_arg() {
        let x = DerefMethodArg { x: 2 };
        assert_eq!(x.render().unwrap(), "3322 6677");
    }
}

mod sub_test {
    use std::borrow::Borrow;

    use askama::Template;

    pub fn bar(x: &String) -> String {
        format!("bar: {x}")
    }

    // This test ensures that temporary variables behind references (like one generated
    // from `.borrow()`) still work.
    //
    // Regression test for <https://github.com/askama-rs/askama/issues/683>.
    #[test]
    fn test_borrow() {
        #[derive(Template)]
        #[template(
            source = r#"
{{- crate::sub_test::bar(b.to_string().borrow()) -}}
"#,
            ext = "txt"
        )]
        struct Foo {
            b: u32,
        }

        assert_eq!(Foo { b: 0 }.render().unwrap(), "bar: 0");
    }
}

// This test ensures that temporary variables behind references (like one generated
// from `.borrow()`) still work.
//
// Regression test for <https://github.com/askama-rs/askama/issues/661>.
#[test]
fn test_temporary_refs() {
    #[derive(Template)]
    #[template(
        ext = "html",
        source = r#"{{ Some("x".to_string().as_str()).unwrap() }}"#
    )]
    struct Tpl;

    assert_eq!(Tpl.render().unwrap(), "x");
}
