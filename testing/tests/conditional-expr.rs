use askama::Template;

#[test]
fn test_associativity() {
    // Here we test the associativity of conditional expressions.
    // `a if b else c if d else e` is the same as `a if b else (c if d else e)` in Python,
    // so we want to parse it right-to-left, too.

    #[derive(Template)]
    #[template(
        source = r#"
            {{-
                "a" if a else
                "b" if b else
                "c" if c else
                "d" if d else
                "-"
            -}}
        "#,
        ext = "html"
    )]
    struct Abcd<'a> {
        a: bool,
        b: &'a bool,
        c: &'a &'a bool,
        d: &'a &'a &'a bool,
    }

    for a in [false, true] {
        for b in [&false, &true] {
            for c in [&&false, &&true] {
                for d in [&&&false, &&&true] {
                    let expected = match (a, b, c, d) {
                        (true, _, _, _) => "a",
                        (_, true, _, _) => "b",
                        (_, _, true, _) => "c",
                        (_, _, _, true) => "d",
                        _ => "-",
                    };
                    let actual = Abcd { a, b, c, d }.to_string();
                    assert_eq!(actual, expected, "a={a} b={b} c={c} d={d}");
                }
            }
        }
    }
}

#[test]
fn test_associativity_reversed() {
    // This test makes sure explicit grouping works.

    #[derive(Template)]
    #[template(
        source = r#"
            {{-
                (
                    (
                        (
                            "-" if !d else "d"
                        ) if !c else "c"
                    ) if !b else "b"
                ) if !a else "a"
            -}}
        "#,
        ext = "html"
    )]
    struct Abcd<'a> {
        a: bool,
        b: &'a bool,
        c: &'a &'a bool,
        d: &'a &'a &'a bool,
    }

    for a in [false, true] {
        for b in [&false, &true] {
            for c in [&&false, &&true] {
                for d in [&&&false, &&&true] {
                    let expected = match (a, b, c, d) {
                        (true, _, _, _) => "a",
                        (_, true, _, _) => "b",
                        (_, _, true, _) => "c",
                        (_, _, _, true) => "d",
                        _ => "-",
                    };
                    let actual = Abcd { a, b, c, d }.to_string();
                    assert_eq!(actual, expected, "a={a} b={b} c={c} d={d}");
                }
            }
        }
    }
}

#[test]
fn test_associativity_infix() {
    // Being a ternary operator, a conditional-expression can be the condition of a
    // conditional-expression without the need for explicit grouping.

    #[derive(Template)]
    #[template(
        source = r#"{{- "a" if then if cond else otherwise else "b" -}}"#,
        ext = "html"
    )]
    struct ThenOtherwise<'a> {
        cond: bool,
        then: &'a bool,
        otherwise: &'a &'a bool,
    }

    for cond in [false, true] {
        for then in [&false, &true] {
            for otherwise in [&&false, &&true] {
                let expected = if if cond { *then } else { **otherwise } {
                    "a"
                } else {
                    "b"
                };
                let actual = ThenOtherwise {
                    cond,
                    then,
                    otherwise,
                }
                .to_string();
                assert_eq!(
                    actual, expected,
                    "cond={cond} then={then} otherwise={otherwise}"
                );
            }
        }
    }
}

// Conditional expressions are just expressions, so you should be able to use them in all
// places that expect an expression.

#[test]
fn test_call_argument() {
    #[derive(Template)]
    #[template(
        source = r#"{{- method(then if cond else otherwise) -}}"#,
        ext = "html"
    )]
    struct AsArgument {
        cond: bool,
        then: i32,
        otherwise: i32,
    }

    impl AsArgument {
        fn method(&self, value: &i32) -> i32 {
            *value
        }
    }

    assert_eq!(
        AsArgument {
            cond: true,
            then: 1,
            otherwise: -1
        }
        .to_string(),
        "1"
    );
    assert_eq!(
        AsArgument {
            cond: false,
            then: 1,
            otherwise: -1
        }
        .to_string(),
        "-1"
    );
}

#[test]
fn test_filter_argument() {
    #[derive(Template)]
    #[template(
        source = r#"{{- input | add(then if cond else otherwise) -}}"#,
        ext = "html"
    )]
    struct AsFilterArgument {
        input: i32,
        cond: bool,
        then: i32,
        otherwise: i32,
    }

    mod filters {
        pub(crate) fn add(input: &i32, _: &dyn askama::Values, arg: &i32) -> askama::Result<i32> {
            Ok(*input + *arg)
        }
    }

    assert_eq!(
        AsFilterArgument {
            input: 10,
            cond: true,
            then: 1,
            otherwise: -1
        }
        .to_string(),
        "11"
    );
    assert_eq!(
        AsFilterArgument {
            input: 10,
            cond: false,
            then: 1,
            otherwise: -1
        }
        .to_string(),
        "9"
    );

    for input in -10..10 {
        for cond in [false, true] {
            for then in -10..10 {
                for otherwise in -10..10 {
                    let expected = if cond {
                        input + then
                    } else {
                        input + otherwise
                    };
                    let actual = AsFilterArgument {
                        input,
                        cond,
                        then,
                        otherwise,
                    };
                    assert_eq!(expected.to_string(), actual.to_string());
                }
            }
        }
    }
}

#[test]
fn test_if_condition() {
    #[derive(Template)]
    #[template(
        source = r#"
            {%- if then if cond else otherwise -%}
                a
            {%- else -%}
                b
            {%- endif -%}
        "#,
        ext = "html"
    )]
    struct AsIfCondition {
        cond: bool,
        then: bool,
        otherwise: bool,
    }

    for cond in [false, true] {
        for then in [false, true] {
            for otherwise in [false, true] {
                let expected = if if cond { then } else { otherwise } {
                    "a"
                } else {
                    "b"
                };
                let actual = AsIfCondition {
                    cond,
                    then,
                    otherwise,
                }
                .to_string();
                assert_eq!(
                    actual, expected,
                    "cond={cond} then={then} otherwise={otherwise}"
                );
            }
        }
    }
}
