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

{%- call package_navigation(title=title, show=true) -%}
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
