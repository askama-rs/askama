use std::cell::Cell;

use winnow::{LocatingSlice, Parser};

use crate::expr::BinOp;
use crate::node::{Extends, Include, Let, Lit, Raw, Whitespace, Ws};
use crate::{
    Ast, Expr, Filter, InnerSyntax, InputStream, LetValueOrBlock, Level, Node, Num, PathComponent,
    PathOrIdentifier, Span, State, StrLit, Syntax, SyntaxBuilder, Target,
};

fn as_path<'a>(path: &[(&'a str, Span)]) -> Vec<PathComponent<'a>> {
    path.iter()
        .map(|&(name, span)| PathComponent {
            name,
            span,
            generics: None,
        })
        .collect::<Vec<_>>()
}

#[test]
fn test_ws_splitter() {
    #[track_caller]
    fn check_ws_split(s: &str, &(lws, val, rws): &(&str, &str, &str)) {
        let s = Lit::split_ws_parts(s, Span::no_span());
        assert_eq!(s.lws, lws);
        assert_eq!(s.val, val);
        assert_eq!(s.rws, rws);
    }

    check_ws_split("", &("", "", ""));
    check_ws_split("a", &("", "a", ""));
    check_ws_split("\ta", &("\t", "a", ""));
    check_ws_split("b\n", &("", "b", "\n"));
    check_ws_split(" \t\r\n", &(" \t\r\n", "", ""));
}

#[test]
fn test_lit_spans() {
    #[track_caller]
    fn check(src: &str, lit: &Lit<'_>) {
        let (lws, val, rws) = lit.spans();
        assert_eq!(lws.as_infix_of(src), Some(lit.lws));
        assert_eq!(val.as_infix_of(src), Some(lit.val));
        assert_eq!(rws.as_infix_of(src), Some(lit.rws));
    }

    let syntax = Syntax::default();
    let src = " \n a b \t{% raw %}\t x y \n{% endraw %}";
    let ast = Ast::from_str(src, None, &syntax).unwrap();
    let [lit, raw] = ast.nodes() else {
        panic!("unexpected nodes: {:?}", ast.nodes());
    };
    let (Node::Lit(lit), Node::Raw(raw)) = (&**lit, &**raw) else {
        panic!("unexpected nodes: {:?}", ast.nodes());
    };
    assert_eq!((lit.lws, lit.val, lit.rws), (" \n ", "a b", " \t"));
    assert_eq!(
        (raw.lit.lws, raw.lit.val, raw.lit.rws),
        ("\t ", "x y", " \n")
    );
    check(src, lit);
    check(src, &raw.lit);
}

#[test]
#[should_panic]
fn test_invalid_block() {
    let syntax = Syntax::default();
    Ast::from_str("{% extend \"blah\" %}", None, &syntax).unwrap();
}

fn int_lit<'a>(i: &'a str, span: Span) -> Box<Expr<'a>> {
    Box::new(Expr::NumLit {
        num_with_suffix: i,
        num: Num::Int(i, None),
        span,
    })
}

fn bin_op<'a>(op: &'a str, lhs: Box<Expr<'a>>, rhs: Box<Expr<'a>>, span: Span) -> Box<Expr<'a>> {
    Box::new(Expr::BinOp {
        inner: crate::expr::BinOp { op, lhs, rhs },
        span,
    })
}

fn call<'a>(path: Box<Expr<'a>>, args: Vec<Box<Expr<'a>>>, span: Span) -> Box<Expr<'a>> {
    Box::new(Expr::Call {
        call: crate::expr::Call {
            path,
            generics: None,
            args,
        },
        span,
    })
}

#[test]
fn test_parse_filter() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ strvar|e }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("e", Span::new(10..11)),
                    arguments: vec![Box::new(Expr::Var {
                        name: "strvar",
                        span: Span::new(3..9)
                    })],
                },
                span: Span::new(9..12)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ 2|abs }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("abs", Span::new(5..8)),
                    arguments: vec![int_lit("2", Span::new(3..4))],
                },
                span: Span::new(4..9)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ -2|abs }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("abs", Span::new(6..9)),
                    arguments: vec![Box::new(Expr::Unary {
                        operator: "-",
                        expr: int_lit("2", Span::new(4..5)),
                        span: Span::new(3..4)
                    })],
                },
                span: Span::new(5..10)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1 - 2)|abs }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("abs", Span::new(11..14)),
                    arguments: vec![Box::new(Expr::Group {
                        elem: bin_op(
                            "-",
                            int_lit("1", Span::new(4..5)),
                            int_lit("2", Span::new(8..9)),
                            Span::new(6..7),
                        ),
                        span: Span::new(3..10)
                    })],
                },
                span: Span::new(10..15)
            }),
        ))],
    );
}

#[test]
fn test_parse_numbers() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ 2 }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            int_lit("2", Span::new(3..4))
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ 2.5 }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::NumLit {
                num_with_suffix: "2.5",
                num: Num::Float("2.5", None),
                span: Span::new(3..6)
            })
        ))],
    );
}

#[test]
fn test_parse_var() {
    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str("{{ foo }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Var {
                name: "foo",
                span: Span::new(3..6)
            })
        ))]
    );
    assert_eq!(
        Ast::from_str("{{ foo_bar }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Var {
                name: "foo_bar",
                span: Span::new(3..10)
            })
        ))],
    );

    assert_eq!(
        Ast::from_str("{{ none }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Var {
                name: "none",
                span: Span::new(3..7)
            })
        ))]
    );
}

#[test]
fn test_parse_const() {
    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str("{{ FOO }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Path {
                components: as_path(&[("FOO", Span::new(3..6))]),
                span: Span::new(3..6)
            })
        ))]
    );
    assert_eq!(
        Ast::from_str("{{ FOO_BAR }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Path {
                components: as_path(&[("FOO_BAR", Span::new(3..10))]),
                span: Span::new(3..10)
            })
        ))],
    );

    assert_eq!(
        Ast::from_str("{{ NONE }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Path {
                components: as_path(&[("NONE", Span::new(3..7))]),
                span: Span::new(3..7)
            })
        ))]
    );
}

#[test]
fn test_parse_path() {
    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str("{{ None }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Path {
                components: as_path(&[("None", Span::new(3..7))]),
                span: Span::new(3..7)
            }),
        ))]
    );
    assert_eq!(
        Ast::from_str("{{ Some(123) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Path {
                    components: as_path(&[("Some", Span::new(3..7))]),
                    span: Span::new(3..7)
                }),
                vec![int_lit("123", Span::new(8..11))],
                Span::new(7..8),
            ),
        ))],
    );

    assert_eq!(
        Ast::from_str("{{ Ok(123) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Path {
                    components: as_path(&[("Ok", Span::new(3..5))]),
                    span: Span::new(3..5)
                }),
                vec![int_lit("123", Span::new(6..9))],
                Span::new(5..6),
            ),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ Err(123) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Path {
                    components: as_path(&[("Err", Span::new(3..6))]),
                    span: Span::new(3..6)
                }),
                vec![int_lit("123", Span::new(7..10))],
                Span::new(6..7),
            ),
        ))],
    );
}

#[test]
fn test_parse_var_call() {
    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str("{{ function(\"123\", 3) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Var {
                    name: "function",
                    span: Span::new(3..11)
                }),
                vec![
                    Box::new(Expr::StrLit {
                        inner: StrLit {
                            content: "123",
                            prefix: None,
                            contains_null: false,
                            contains_unicode_character: false,
                            contains_unicode_escape: false,
                            contains_high_ascii: false,
                        },
                        span: Span::new(12..17)
                    }),
                    int_lit("3", Span::new(19..20))
                ],
                Span::new(11..12),
            ),
        ))],
    );
}

#[test]
fn test_parse_path_call() {
    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str("{{ Option::None }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Path {
                components: as_path(&[("Option", Span::new(3..9)), ("None", Span::new(11..15))]),
                span: Span::new(3..15)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ Option::Some(123) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Path {
                    components: as_path(&[
                        ("Option", Span::new(3..9)),
                        ("Some", Span::new(11..15))
                    ]),
                    span: Span::new(3..15)
                }),
                vec![int_lit("123", Span::new(16..19))],
                Span::new(15..16),
            )
        ))],
    );

    assert_eq!(
        Ast::from_str("{{ self::function(\"123\", 3) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Path {
                    components: as_path(&[
                        ("self", Span::new(3..7)),
                        ("function", Span::new(9..17))
                    ]),
                    span: Span::new(3..17)
                }),
                vec![
                    Box::new(Expr::StrLit {
                        inner: StrLit {
                            content: "123",
                            prefix: None,
                            contains_null: false,
                            contains_unicode_character: false,
                            contains_unicode_escape: false,
                            contains_high_ascii: false,
                        },
                        span: Span::new(18..23)
                    }),
                    int_lit("3", Span::new(25..26))
                ],
                Span::new(17..18),
            )
        ))],
    );
}

#[test]
fn test_parse_root_path() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ std::string::String::new() }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Path {
                    components: as_path(&[
                        ("std", Span::new(3..6)),
                        ("string", Span::new(8..14)),
                        ("String", Span::new(16..22)),
                        ("new", Span::new(24..27))
                    ]),
                    span: Span::new(3..27)
                }),
                vec![],
                Span::new(27..28),
            ),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ ::std::string::String::new() }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Path {
                    components: as_path(&[
                        ("", Span::new(3..3)),
                        ("std", Span::new(5..8)),
                        ("string", Span::new(10..16)),
                        ("String", Span::new(18..24)),
                        ("new", Span::new(26..29))
                    ]),
                    span: Span::new(3..29)
                }),
                vec![],
                Span::new(29..30),
            ),
        ))],
    );
}

#[test]
fn test_rust_macro() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ vec!(1, 2, 3) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("vec", Span::new(3..6))],
                arguments: "1, 2, 3",
                span: Span::new(6..7)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ alloc::vec!(1, 2, 3) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("alloc", Span::new(3..8)), ("vec", Span::new(10..13))],
                arguments: "1, 2, 3",
                span: Span::new(13..14)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{a!()}}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("a", Span::new(2..3))],
                arguments: "",
                span: Span::new(3..4)
            })
        ))]
    );
    assert_eq!(
        Ast::from_str("{{a !()}}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("a", Span::new(2..3))],
                arguments: "",
                span: Span::new(4..5)
            })
        ))]
    );
    assert_eq!(
        Ast::from_str("{{a! ()}}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("a", Span::new(2..3))],
                arguments: "",
                span: Span::new(3..4)
            })
        ))]
    );
    assert_eq!(
        Ast::from_str("{{a ! ()}}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("a", Span::new(2..3))],
                arguments: "",
                span: Span::new(4..5)
            })
        ))]
    );
    assert_eq!(
        Ast::from_str("{{A!()}}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("A", Span::new(2..3))],
                arguments: "",
                span: Span::new(3..4)
            })
        ))]
    );
    assert_eq!(
        &*Ast::from_str("{{a.b.c!( hello )}}", None, &syntax)
            .unwrap_err()
            .to_string(),
        "the token `!` was not expected at this point in the expression\n\
        failed to parse template source near offset 7",
    );
}

#[test]
fn change_delimiters_parse_filter() {
    let syntax = Syntax(InnerSyntax {
        expr_start: "{=",
        expr_end: "=}",
        ..InnerSyntax::default()
    });
    Ast::from_str("{= strvar|e =}", None, &syntax).unwrap();
}

#[test]
fn unicode_delimiters_in_syntax() {
    let syntax = Syntax(InnerSyntax {
        expr_start: "🖎", // U+1F58E == b"\xf0\x9f\x96\x8e"
        expr_end: "✍",   // U+270D = b'\xe2\x9c\x8d'
        ..InnerSyntax::default()
    });
    assert_eq!(
        Ast::from_str("Here comes the expression: 🖎 e ✍.", None, &syntax)
            .unwrap()
            .nodes(),
        [
            Box::new(Node::Lit(Lit {
                lws: "",
                val: "Here comes the expression:",
                rws: " ",
                span: Span::new(0..27),
            })),
            Box::new(Node::Expr(
                Ws(None, None),
                Box::new(Expr::Var {
                    name: "e",
                    span: Span::new(32..33)
                })
            )),
            Box::new(Node::Lit(Lit {
                lws: "",
                val: ".",
                rws: "",
                span: Span::new(37..38),
            })),
        ],
    );
}

#[test]
fn test_precedence() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ a + b == c }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "==",
                bin_op(
                    "+",
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    Box::new(Expr::Var {
                        name: "b",
                        span: Span::new(7..8)
                    }),
                    Span::new(5..6)
                ),
                Box::new(Expr::Var {
                    name: "c",
                    span: Span::new(12..13)
                }),
                Span::new(9..11)
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a + b * c - d / e }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "-",
                bin_op(
                    "+",
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    bin_op(
                        "*",
                        Box::new(Expr::Var {
                            name: "b",
                            span: Span::new(7..8)
                        }),
                        Box::new(Expr::Var {
                            name: "c",
                            span: Span::new(11..12)
                        }),
                        Span::new(9..10)
                    ),
                    Span::new(5..6)
                ),
                bin_op(
                    "/",
                    Box::new(Expr::Var {
                        name: "d",
                        span: Span::new(15..16)
                    }),
                    Box::new(Expr::Var {
                        name: "e",
                        span: Span::new(19..20)
                    }),
                    Span::new(17..18)
                ),
                Span::new(13..14),
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a * (b + c) / -d }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "/",
                bin_op(
                    "*",
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    Box::new(Expr::Group {
                        elem: bin_op(
                            "+",
                            Box::new(Expr::Var {
                                name: "b",
                                span: Span::new(8..9)
                            }),
                            Box::new(Expr::Var {
                                name: "c",
                                span: Span::new(12..13)
                            }),
                            Span::new(10..11)
                        ),
                        span: Span::new(7..14)
                    }),
                    Span::new(5..6)
                ),
                Box::new(Expr::Unary {
                    operator: "-",
                    expr: Box::new(Expr::Var {
                        name: "d",
                        span: Span::new(18..19)
                    }),
                    span: Span::new(17..18)
                }),
                Span::new(15..16)
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a || b && c || d && e }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "||",
                bin_op(
                    "||",
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    bin_op(
                        "&&",
                        Box::new(Expr::Var {
                            name: "b",
                            span: Span::new(8..9)
                        }),
                        Box::new(Expr::Var {
                            name: "c",
                            span: Span::new(13..14)
                        }),
                        Span::new(10..12)
                    ),
                    Span::new(5..7),
                ),
                bin_op(
                    "&&",
                    Box::new(Expr::Var {
                        name: "d",
                        span: Span::new(18..19)
                    }),
                    Box::new(Expr::Var {
                        name: "e",
                        span: Span::new(23..24)
                    }),
                    Span::new(20..22)
                ),
                Span::new(15..17),
            )
        ))],
    );
}

#[test]
fn test_associativity() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ a + b + c }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "+",
                bin_op(
                    "+",
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    Box::new(Expr::Var {
                        name: "b",
                        span: Span::new(7..8)
                    }),
                    Span::new(5..6)
                ),
                Box::new(Expr::Var {
                    name: "c",
                    span: Span::new(11..12)
                }),
                Span::new(9..10)
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a * b * c }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "*",
                bin_op(
                    "*",
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    Box::new(Expr::Var {
                        name: "b",
                        span: Span::new(7..8)
                    }),
                    Span::new(5..6)
                ),
                Box::new(Expr::Var {
                    name: "c",
                    span: Span::new(11..12)
                }),
                Span::new(9..10)
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a && b && c }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "&&",
                bin_op(
                    "&&",
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    Box::new(Expr::Var {
                        name: "b",
                        span: Span::new(8..9)
                    }),
                    Span::new(5..7)
                ),
                Box::new(Expr::Var {
                    name: "c",
                    span: Span::new(13..14)
                }),
                Span::new(10..12)
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a + b - c + d }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "+",
                bin_op(
                    "-",
                    bin_op(
                        "+",
                        Box::new(Expr::Var {
                            name: "a",
                            span: Span::new(3..4)
                        }),
                        Box::new(Expr::Var {
                            name: "b",
                            span: Span::new(7..8)
                        }),
                        Span::new(5..6)
                    ),
                    Box::new(Expr::Var {
                        name: "c",
                        span: Span::new(11..12)
                    }),
                    Span::new(9..10)
                ),
                Box::new(Expr::Var {
                    name: "d",
                    span: Span::new(15..16)
                }),
                Span::new(13..14)
            )
        ))],
    );
}

#[test]
fn test_odd_calls() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ a[b](c) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Index {
                    parent_item: Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(3..4)
                    }),
                    index: Box::new(Expr::Var {
                        name: "b",
                        span: Span::new(5..6)
                    }),
                    span: Span::new(4..5)
                }),
                vec![Box::new(Expr::Var {
                    name: "c",
                    span: Span::new(8..9)
                })],
                Span::new(7..8),
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (a + b)(c) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Group {
                    elem: bin_op(
                        "+",
                        Box::new(Expr::Var {
                            name: "a",
                            span: Span::new(4..5)
                        }),
                        Box::new(Expr::Var {
                            name: "b",
                            span: Span::new(8..9)
                        }),
                        Span::new(6..7)
                    ),
                    span: Span::new(3..10)
                }),
                vec![Box::new(Expr::Var {
                    name: "c",
                    span: Span::new(11..12)
                })],
                Span::new(10..11),
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a + b(c) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            bin_op(
                "+",
                Box::new(Expr::Var {
                    name: "a",
                    span: Span::new(3..4)
                }),
                call(
                    Box::new(Expr::Var {
                        name: "b",
                        span: Span::new(7..8)
                    }),
                    vec![Box::new(Expr::Var {
                        name: "c",
                        span: Span::new(9..10)
                    })],
                    Span::new(8..9),
                ),
                Span::new(5..6),
            ),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (-a)(b) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            call(
                Box::new(Expr::Group {
                    elem: Box::new(Expr::Unary {
                        operator: "-",
                        expr: Box::new(Expr::Var {
                            name: "a",
                            span: Span::new(5..6)
                        }),
                        span: Span::new(4..5)
                    }),
                    span: Span::new(3..7)
                }),
                vec![Box::new(Expr::Var {
                    name: "b",
                    span: Span::new(8..9)
                })],
                Span::new(7..8),
            )
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ -a(b) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Unary {
                operator: "-",
                expr: call(
                    Box::new(Expr::Var {
                        name: "a",
                        span: Span::new(4..5)
                    }),
                    vec![Box::new(Expr::Var {
                        name: "b",
                        span: Span::new(6..7)
                    })],
                    Span::new(5..6),
                ),
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ a(b)|c }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("c", Span::new(8..9)),
                    arguments: vec![call(
                        Box::new(Expr::Var {
                            name: "a",
                            span: Span::new(3..4)
                        }),
                        vec![Box::new(Expr::Var {
                            name: "b",
                            span: Span::new(5..6)
                        })],
                        Span::new(4..5),
                    )],
                },
                span: Span::new(7..10)
            })
        ))]
    );
    assert_eq!(
        Ast::from_str("{{ a(b)| c }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("c", Span::new(9..10)),
                    arguments: vec![call(
                        Box::new(Expr::Var {
                            name: "a",
                            span: Span::new(3..4)
                        }),
                        vec![Box::new(Expr::Var {
                            name: "b",
                            span: Span::new(5..6)
                        })],
                        Span::new(4..5),
                    )],
                },
                span: Span::new(7..11)
            }),
        ))]
    );
}

#[test]
fn test_parse_comments() {
    #[track_caller]
    fn one_comment_ws(source: &str, ws: Ws) {
        let syntax = Syntax::default();
        let mut nodes = Ast::from_str(source, None, &syntax).unwrap().nodes;
        assert_eq!(nodes.len(), 1, "expected to parse one node");
        match *nodes.pop().unwrap() {
            Node::Comment(comment) => assert_eq!(comment.ws, ws),
            node => panic!("expected a comment not, but parsed {node:?}"),
        }
    }

    one_comment_ws("{##}", Ws(None, None));
    one_comment_ws("{#- #}", Ws(Some(Whitespace::Suppress), None));
    one_comment_ws("{# -#}", Ws(None, Some(Whitespace::Suppress)));
    one_comment_ws(
        "{#--#}",
        Ws(Some(Whitespace::Suppress), Some(Whitespace::Suppress)),
    );
    one_comment_ws(
        "{#- foo\n bar -#}",
        Ws(Some(Whitespace::Suppress), Some(Whitespace::Suppress)),
    );
    one_comment_ws(
        "{#- foo\n {#- bar\n -#} baz -#}",
        Ws(Some(Whitespace::Suppress), Some(Whitespace::Suppress)),
    );
    one_comment_ws("{#+ #}", Ws(Some(Whitespace::Preserve), None));
    one_comment_ws("{# +#}", Ws(None, Some(Whitespace::Preserve)));
    one_comment_ws(
        "{#++#}",
        Ws(Some(Whitespace::Preserve), Some(Whitespace::Preserve)),
    );
    one_comment_ws(
        "{#+ foo\n bar +#}",
        Ws(Some(Whitespace::Preserve), Some(Whitespace::Preserve)),
    );
    one_comment_ws(
        "{#+ foo\n {#+ bar\n +#} baz -+#}",
        Ws(Some(Whitespace::Preserve), Some(Whitespace::Preserve)),
    );
    one_comment_ws("{#~ #}", Ws(Some(Whitespace::Minimize), None));
    one_comment_ws("{# ~#}", Ws(None, Some(Whitespace::Minimize)));
    one_comment_ws(
        "{#~~#}",
        Ws(Some(Whitespace::Minimize), Some(Whitespace::Minimize)),
    );
    one_comment_ws(
        "{#~ foo\n bar ~#}",
        Ws(Some(Whitespace::Minimize), Some(Whitespace::Minimize)),
    );
    one_comment_ws(
        "{#~ foo\n {#~ bar\n ~#} baz -~#}",
        Ws(Some(Whitespace::Minimize), Some(Whitespace::Minimize)),
    );

    one_comment_ws("{# foo {# bar #} {# {# baz #} qux #} #}", Ws(None, None));
}

#[test]
fn test_parse_tuple() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ () }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![],
                span: Span::new(3..5)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Group {
                elem: int_lit("1", Span::new(4..5)),
                span: Span::new(3..6)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1,) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![int_lit("1", Span::new(4..5))],
                span: Span::new(3..7)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1, ) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![int_lit("1", Span::new(4..5))],
                span: Span::new(3..8)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1 ,) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![int_lit("1", Span::new(4..5))],
                span: Span::new(3..8)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1 , ) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![int_lit("1", Span::new(4..5))],
                span: Span::new(3..9)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1, 2) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![int_lit("1", Span::new(4..5)), int_lit("2", Span::new(7..8))],
                span: Span::new(3..9)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1, 2,) }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![int_lit("1", Span::new(4..5)), int_lit("2", Span::new(7..8))],
                span: Span::new(3..10)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1, 2, 3) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Tuple {
                elems: vec![
                    int_lit("1", Span::new(4..5)),
                    int_lit("2", Span::new(7..8)),
                    int_lit("3", Span::new(10..11))
                ],
                span: Span::new(3..12)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ ()|abs }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("abs", Span::new(6..9)),
                    arguments: vec![Box::new(Expr::Tuple {
                        elems: vec![],
                        span: Span::new(3..5)
                    })],
                },
                span: Span::new(5..10)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1)|abs }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("abs", Span::new(7..10)),
                    arguments: vec![Box::new(Expr::Group {
                        elem: int_lit("1", Span::new(4..5)),
                        span: Span::new(3..6)
                    })],
                },
                span: Span::new(6..11)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1,)|abs }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("abs", Span::new(8..11)),
                    arguments: vec![Box::new(Expr::Tuple {
                        elems: vec![int_lit("1", Span::new(4..5))],
                        span: Span::new(3..7)
                    })],
                },
                span: Span::new(7..12)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ (1, 2)|abs }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("abs", Span::new(10..13)),
                    arguments: vec![Box::new(Expr::Tuple {
                        elems: vec![int_lit("1", Span::new(4..5)), int_lit("2", Span::new(7..8))],
                        span: Span::new(3..9)
                    })],
                },
                span: Span::new(9..14)
            }),
        ))],
    );
}

#[test]
fn test_missing_space_after_kw() {
    let syntax = Syntax::default();
    let err = Ast::from_str("{%leta=b%}", None, &syntax).unwrap_err();
    assert_eq!(
        err.to_string(),
        "unknown node `leta`\nfailed to parse template source near offset 2",
    );
}

#[test]
fn test_parse_array() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ [] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ [1] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(4..5))],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ [ 1] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(5..6))],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ [1 ] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(4..5))],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ [1,2] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(4..5)), int_lit("2", Span::new(6..7))],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ [1 ,2] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(4..5)), int_lit("2", Span::new(7..8))],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ [1, 2] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(4..5)), int_lit("2", Span::new(7..8))],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ [1,2 ] }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(4..5)), int_lit("2", Span::new(6..7))],
                span: Span::new(3..4)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ []|foo }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("foo", Span::new(6..9)),
                    arguments: vec![Box::new(Expr::Array {
                        elems: vec![],
                        span: Span::new(3..4)
                    })],
                },
                span: Span::new(5..10)
            })
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ []| foo }}", None, &syntax).unwrap().nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Identifier("foo", Span::new(7..10)),
                    arguments: vec![Box::new(Expr::Array {
                        elems: vec![],
                        span: Span::new(3..4)
                    })],
                },
                span: Span::new(5..11)
            })
        ))],
    );

    let n = |bracket: usize| {
        Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Array {
                elems: vec![int_lit("1", Span::new(bracket + 1..bracket + 2))],
                span: Span::new(bracket..bracket + 1),
            }),
        ))
    };
    assert_eq!(
        Ast::from_str(
            "{{ [1,] }}{{ [1 ,] }}{{ [1, ] }}{{ [1 , ] }}",
            None,
            &syntax
        )
        .unwrap()
        .nodes,
        [n(3), n(13), n(24), n(35)],
    );
}

#[test]
fn fuzzed_unicode_slice() {
    let d = "{eeuuu{b&{!!&{!!11{{
            0!(!1q҄א!)!!!!!!n!";
    assert!(Ast::from_str(d, None, &Syntax::default()).is_err());
}

#[test]
fn fuzzed_macro_no_end() {
    let s = "{%macro super%}{%endmacro";
    assert!(Ast::from_str(s, None, &Syntax::default()).is_err());
}

#[test]
fn fuzzed_target_recursion() {
    const TEMPLATE: &str = include_str!("../tests/target-recursion.txt");
    assert!(Ast::from_str(TEMPLATE, None, &Syntax::default()).is_err());
}

#[test]
fn fuzzed_unary_recursion() {
    const TEMPLATE: &str = include_str!("../tests/unary-recursion.txt");
    assert!(Ast::from_str(TEMPLATE, None, &Syntax::default()).is_err());
}

#[test]
fn fuzzed_comment_depth() {
    let syntax = Syntax::default();

    let (sender, receiver) = std::sync::mpsc::channel();
    let test = std::thread::spawn(move || {
        const TEMPLATE: &str = include_str!("../tests/comment-depth.txt");
        assert!(Ast::from_str(TEMPLATE, None, &syntax).is_ok());
        sender.send(()).unwrap();
    });
    receiver
        .recv_timeout(std::time::Duration::from_secs(3))
        .expect("timeout");
    test.join().unwrap();
}

#[test]
fn let_set() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{% let a = 1 %}", None, &syntax)
            .unwrap()
            .nodes(),
        Ast::from_str("{% set a = 1 %}", None, &syntax)
            .unwrap()
            .nodes(),
    );
}

#[test]
fn fuzzed_filter_recursion() {
    const TEMPLATE: &str = include_str!("../tests/filter-recursion.txt");
    assert!(Ast::from_str(TEMPLATE, None, &Syntax::default()).is_err());
}

#[test]
fn fuzzed_excessive_syntax_lengths() {
    const LONG_DELIM: Option<&str> =
        Some("\0]***NEWFILE\u{1f}***:7/v/.-3/\u{1b}/~~~~z~0/*:7/v/./t/t/.p//NEWVILE**::7/v");

    for (kind, syntax_builder) in [
        (
            "opening block",
            SyntaxBuilder {
                block_start: LONG_DELIM,
                ..SyntaxBuilder::default()
            },
        ),
        (
            "closing block",
            SyntaxBuilder {
                block_end: LONG_DELIM,
                ..SyntaxBuilder::default()
            },
        ),
        (
            "opening expression",
            SyntaxBuilder {
                expr_start: LONG_DELIM,
                ..SyntaxBuilder::default()
            },
        ),
        (
            "closing expression",
            SyntaxBuilder {
                expr_end: LONG_DELIM,
                ..SyntaxBuilder::default()
            },
        ),
        (
            "opening comment",
            SyntaxBuilder {
                comment_start: LONG_DELIM,
                ..SyntaxBuilder::default()
            },
        ),
        (
            "closing comment",
            SyntaxBuilder {
                comment_end: LONG_DELIM,
                ..SyntaxBuilder::default()
            },
        ),
    ] {
        let err = syntax_builder.to_syntax().unwrap_err();
        assert_eq!(
            err,
            format!(
                "delimiters must be at most 32 characters long. The {kind} delimiter \
                 (\"\\0]***NEWFILE\\u{{1f}}***\"...) is too long"
            ),
        );
    }
}

#[test]
fn extends_with_whitespace_control() {
    const CONTROL: &[&str] = &["", "\t", "-", "+", "~"];

    let syntax = Syntax::default();
    for front in CONTROL {
        for back in CONTROL {
            let src = format!(r#"{{%{front} extends "nothing" {back}%}} back"#);
            let keyword = src.find("extends").unwrap();
            let lit = src.find(" back").unwrap();
            assert_eq!(
                Ast::from_str(&src, None, &syntax).unwrap().nodes(),
                [
                    Box::new(Node::Extends(Extends {
                        path: "nothing",
                        span: Span::new(keyword..keyword + "extends".len()),
                    })),
                    Box::new(Node::Lit(Lit {
                        lws: " ",
                        val: "back",
                        rws: "",
                        span: Span::new(lit..src.len()),
                    })),
                ],
                "source: {src:?}",
            );
        }
    }
}

#[test]
fn test_include() {
    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str(r#"{% include "a.html" %}"#, None, &syntax)
            .unwrap()
            .nodes(),
        [Box::new(Node::Include(Include {
            ws: Ws(None, None),
            path: "a.html",
            block: None,
            span: Span::new(3..10),
        }))],
    );

    let src = r#"{%- include "a.html" block b_1 ~%}"#;
    let ast = Ast::from_str(src, None, &syntax).unwrap();
    assert_eq!(
        ast.nodes(),
        [Box::new(Node::Include(Include {
            ws: Ws(Some(Whitespace::Suppress), Some(Whitespace::Minimize)),
            path: "a.html",
            block: Some(("b_1", Span::new(27..30))),
            span: Span::new(4..11),
        }))],
    );
    let Node::Include(Include {
        block: Some((_, block_span)),
        ..
    }) = &*ast.nodes()[0]
    else {
        unreachable!();
    };
    assert_eq!(block_span.as_infix_of(src), Some("b_1"));

    for src in [
        r#"{% include "a.html" block %}"#,
        r#"{% include "a.html" block "b" %}"#,
        r#"{% include "a.html" block b c %}"#,
        r#"{% include "a.html" b %}"#,
    ] {
        assert!(
            Ast::from_str(src, None, &syntax).is_err(),
            "source: {src:?}"
        );
    }
}

#[test]
fn fuzzed_span_is_not_substring_of_source() {
    let _: Result<Ast<'_>, crate::ParseError> = Ast::from_str(
        include_str!("../tests/fuzzed_span_is_not_substring_of_source.bin"),
        None,
        &Syntax::default(),
    );
}

#[test]
fn fuzzed_excessive_filter_block() {
    let src = include_str!("../tests/excessive_filter_block.txt");
    let err = Ast::from_str(src, None, &Syntax::default()).unwrap_err();
    assert_eq!(
        err.to_string().lines().next(),
        Some("your template code is too deeply nested, or the last expression is too complex"),
    );
}

#[test]
fn test_generics_parsing() {
    let syntax = Syntax::default();

    // Method call.
    Ast::from_str("{{ a.b::<&str, H<B<C>>>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&str, H<B<C> , &u32>>() }}", None, &syntax).unwrap();

    // Call.
    Ast::from_str("{{ a::<&str, H<B<C> , &u32>>() }}", None, &syntax).unwrap();

    // Filter.
    Ast::from_str("{{ 12 | a::<&str> }}", None, &syntax).unwrap();
    Ast::from_str("{{ 12 | a::<&str, u32>('a') }}", None, &syntax).unwrap();

    // Unclosed `<`.
    assert!(Ast::from_str("{{ a.b::<&str, H<B<C> , &u32>() }}", None, &syntax).is_err());

    // With path and spaces
    Ast::from_str("{{ a.b::<&&core::primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b ::<&&core::primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b:: <&&core::primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::< &&core::primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<& &core::primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&& core::primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&&core ::primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&&core:: primitive::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&&core::primitive ::str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&&core::primitive:: str>() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&&core::primitive::str >() }}", None, &syntax).unwrap();
    Ast::from_str("{{ a.b::<&&core::primitive::str> () }}", None, &syntax).unwrap();
}

#[test]
fn fuzzed_deeply_tested_if_let() {
    let src = include_str!("../tests/fuzzed-deeply-tested-if-let.txt");
    let syntax = Syntax::default();
    let err = Ast::from_str(src, None, &syntax).unwrap_err();
    assert_eq!(
        err.to_string().lines().next(),
        Some("your template code is too deeply nested, or the last expression is too complex"),
    );
}

#[test]
fn test_filter_with_path() {
    let syntax = Syntax::default();
    assert_eq!(
        Ast::from_str("{{ strvar|::e }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Path(as_path(&[
                        ("", Span::new(10..10)),
                        ("e", Span::new(12..13))
                    ])),
                    arguments: vec![Box::new(Expr::Var {
                        name: "strvar",
                        span: Span::new(3..9)
                    })],
                },
                span: Span::new(9..14)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ strvar|::e::f }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Path(as_path(&[
                        ("", Span::new(10..10)),
                        ("e", Span::new(12..13)),
                        ("f", Span::new(15..16))
                    ])),
                    arguments: vec![Box::new(Expr::Var {
                        name: "strvar",
                        span: Span::new(3..9)
                    })],
                },
                span: Span::new(9..17)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ strvar|e::f }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Path(as_path(&[
                        ("e", Span::new(10..11)),
                        ("f", Span::new(13..14))
                    ])),
                    arguments: vec![Box::new(Expr::Var {
                        name: "strvar",
                        span: Span::new(3..9)
                    })],
                },
                span: Span::new(9..15)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ strvar|e::f() }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Filter {
                inner: Filter {
                    name: PathOrIdentifier::Path(as_path(&[
                        ("e", Span::new(10..11)),
                        ("f", Span::new(13..14))
                    ])),
                    arguments: vec![Box::new(Expr::Var {
                        name: "strvar",
                        span: Span::new(3..9)
                    })],
                },
                span: Span::new(9..17)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ strvar|e()::f }}", None, &syntax)
            .unwrap_err()
            .to_string(),
        "the token `::` was not expected at this point in the expression\n\
        failed to parse template source near offset 13",
    );
    assert_eq!(
        Ast::from_str("{{ strvar|e::f()::g }}", None, &syntax)
            .unwrap_err()
            .to_string(),
        "the token `::` was not expected at this point in the expression\n\
        failed to parse template source near offset 16",
    );
}

#[test]
fn underscore_is_an_identifier() {
    let state = State {
        syntax: Syntax::default(),
        loop_depth: Cell::new(0),
        level: Level::default(),
    };
    let mut input = InputStream {
        input: LocatingSlice::new("_"),
        state: &state,
    };
    let result = crate::identifier.parse_next(&mut input);
    assert_eq!(result.unwrap(), "_");
    assert_eq!(**input, "");
}

#[test]
fn there_is_no_digit_two_in_a_binary_integer() {
    let syntax = Syntax::default();
    assert!(Ast::from_str("{{ 0b2 }}", None, &syntax).is_err());
    assert!(Ast::from_str("{{ 0o9 }}", None, &syntax).is_err());
    assert!(Ast::from_str("{{ 0xg }}", None, &syntax).is_err());
}

#[test]
fn comparison_operators_cannot_be_chained() {
    const OPS: &[&str] = &["==", "!=", ">=", ">", "<=", "<"];

    let syntax = Syntax::default();
    for op1 in OPS {
        assert!(Ast::from_str(&format!("{{{{ a {op1} b }}}}"), None, &syntax).is_ok());
        for op2 in OPS {
            assert!(Ast::from_str(&format!("{{{{ a {op1} b {op2} c }}}}"), None, &syntax).is_err());
            for op3 in OPS {
                assert!(
                    Ast::from_str(
                        &format!("{{{{ a {op1} b {op2} c {op3} d }}}}"),
                        None,
                        &syntax,
                    )
                    .is_err()
                );
            }
        }
    }
}

#[test]
fn macro_calls_can_have_raw_prefixes() {
    // Related to issue <https://github.com/askama-rs/askama/issues/475>.
    let syntax = Syntax::default();
    let inner = r####"r#"test"# r##"test"## r###"test"### r#loop"####;
    assert_eq!(
        Ast::from_str(&format!("{{{{ z!{{{inner}}} }}}}"), None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("z", Span::new(3..4))],
                arguments: inner,
                span: Span::new(4..5)
            }),
        ))],
    );
}

#[test]
fn macro_comments_in_macro_calls() {
    // Related to <https://issues.oss-fuzz.com/issues/425145246>.
    let syntax = Syntax::default();

    assert!(Ast::from_str("{{ e!(// hello) }}", None, &syntax).is_err());
    assert!(Ast::from_str("{{ e!(/// hello) }}", None, &syntax).is_err());
    assert!(Ast::from_str("{{ e!(// hello)\n }}", None, &syntax).is_err());
    assert!(Ast::from_str("{{ e!(/// hello)\n }}", None, &syntax).is_err());

    assert_eq!(
        Ast::from_str("{{ e!(// hello\n) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("e", Span::new(3..4))],
                arguments: "// hello\n",
                span: Span::new(4..5)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ e!(/// hello\n) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("e", Span::new(3..4))],
                arguments: "/// hello\n",
                span: Span::new(4..5)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ e!(//! hello\n) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("e", Span::new(3..4))],
                arguments: "//! hello\n",
                span: Span::new(4..5)
            }),
        ))],
    );

    assert_eq!(
        Ast::from_str("{{ e!(/* hello */) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("e", Span::new(3..4))],
                arguments: "/* hello */",
                span: Span::new(4..5)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ e!(/** hello */) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("e", Span::new(3..4))],
                arguments: "/** hello */",
                span: Span::new(4..5)
            }),
        ))],
    );
    assert_eq!(
        Ast::from_str("{{ e!(/*! hello */) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("e", Span::new(3..4))],
                arguments: "/*! hello */",
                span: Span::new(4..5)
            }),
        ))],
    );
}

#[test]
fn test_raw() {
    let syntax = Syntax::default();

    let val = "hello {{ endraw %} my {%* endraw %} green {% endraw }} world";
    assert_eq!(
        Ast::from_str(
            &format!("{{%+ raw -%}} {val} {{%~ endraw ~%}}"),
            None,
            &syntax
        )
        .unwrap()
        .nodes,
        [Box::new(Node::Raw(Raw {
            ws1: Ws(Some(Whitespace::Preserve), Some(Whitespace::Suppress)),
            lit: Lit {
                lws: " ",
                val,
                rws: " ",
                span: Span::new(11..73),
            },
            ws2: Ws(Some(Whitespace::Minimize), Some(Whitespace::Minimize)),
            span: Span::new(4..7),
        }))],
    );

    // We must make sure that the character for whitespace handling, e.g. `-` is not consumed,
    // unless `{% endraw %}` was actually found. Otherwise opening block delimiters that begin with
    // `-`, `~` or `+` may break.
    let syntax = SyntaxBuilder {
        block_start: Some("-$"),
        block_end: Some("$-"),
        ..SyntaxBuilder::default()
    };
    let syntax = syntax.to_syntax().unwrap();
    assert_eq!(
        Ast::from_str("-$- raw -$- -$- endraw -$ endraw -$-", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Raw(Raw {
            ws1: Ws(Some(Whitespace::Suppress), Some(Whitespace::Suppress)),
            lit: Lit {
                lws: " ",
                val: "-$- endraw",
                rws: " ",
                span: Span::new(11..23),
            },
            ws2: Ws(None, Some(Whitespace::Suppress)),
            span: Span::new(4..7),
        }))],
    );
}

#[test]
fn test_macro_call_nested_comments() {
    // Regression test for <https://issues.oss-fuzz.com/issues/427825995>.
    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str("{{ x!(/*/*/*)*/*/*/) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("x", Span::new(3..4))],
                arguments: "/*/*/*)*/*/*/",
                span: Span::new(4..5)
            }),
        ))],
    );

    let msg = Ast::from_str("{{ x!(/*/*/) }}", None, &syntax)
        .unwrap_err()
        .to_string();
    assert!(msg.contains("missing `*/` to close block comment"));

    assert_eq!(
        Ast::from_str("{{ x!(/**/) }}", None, &syntax)
            .unwrap()
            .nodes,
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::RustMacro {
                path: vec![("x", Span::new(3..4))],
                arguments: "/**/",
                span: Span::new(4..5)
            }),
        ))],
    );
}

#[test]
fn test_try_reserved_raw_identifier() {
    // Regression test for <https://issues.oss-fuzz.com/issues/429130577>.
    let syntax = Syntax::default();

    for id in ["crate", "super", "Self"] {
        let msg = format!("`{id}` cannot be used as an identifier");
        assert!(
            Ast::from_str(&format!("{{{{ {id}? }}}}"), None, &syntax)
                .unwrap_err()
                .to_string()
                .contains(&msg),
        );
        assert!(
            Ast::from_str(&format!("{{{{ {id}|filter }}}}"), None, &syntax)
                .unwrap_err()
                .to_string()
                .contains(&msg),
        );
        assert!(
            Ast::from_str(
                &format!("{{{{ var|filter(arg1, {id}, arg3) }}}}"),
                None,
                &syntax
            )
            .unwrap_err()
            .to_string()
            .contains(&msg),
        );
        assert!(
            Ast::from_str(
                &format!("{{{{ var|filter(arg1=arg1, arg2={id}, arg3=arg3) }}}}"),
                None,
                &syntax
            )
            .unwrap_err()
            .to_string()
            .contains(&msg),
        );
    }
}

#[test]
fn test_isolated_cr_in_raw_string() {
    // Regression test for <https://issues.oss-fuzz.com/issues/429645376>.
    let syntax = Syntax::default();

    assert!(
        Ast::from_str("{{ x!(\"hello\rworld\") }}", None, &syntax)
            .unwrap_err()
            .to_string()
            .contains("a bare CR (Mac linebreak) is not allowed in string literals"),
    );
    assert!(
        Ast::from_str("{{ x!(c\"hello\rworld\") }}", None, &syntax)
            .unwrap_err()
            .to_string()
            .contains("a bare CR (Mac linebreak) is not allowed in string literals"),
    );
    assert!(
        Ast::from_str("{{ x!(b\"hello\rworld\") }}", None, &syntax)
            .unwrap_err()
            .to_string()
            .contains("a bare CR (Mac linebreak) is not allowed in string literals"),
    );
    assert!(
        Ast::from_str("{{ x!(r\"hello\rworld\") }}", None, &syntax)
            .unwrap_err()
            .to_string()
            .contains("a bare CR (Mac linebreak) is not allowed in string literals"),
    );
    assert!(
        Ast::from_str("{{ x!(cr\"hello\rworld\") }}", None, &syntax)
            .unwrap_err()
            .to_string()
            .contains("a bare CR (Mac linebreak) is not allowed in string literals"),
    );
    assert!(
        Ast::from_str("{{ x!(br\"hello\rworld\") }}", None, &syntax)
            .unwrap_err()
            .to_string()
            .contains("a bare CR (Mac linebreak) is not allowed in string literals"),
    );
}

#[test]
fn test_macro_call_illegal_raw_identifier() {
    // Regression test for <https://issues.oss-fuzz.com/issues/435218013>.
    let syntax = Syntax::default();

    for id in ["crate", "self", "Self", "super", "_"] {
        assert!(
            Ast::from_str(&format!("{{{{ z!(r#{id}) }}}}"), None, &syntax)
                .unwrap_err()
                .to_string()
                .contains("cannot be a raw identifier"),
        );
    }
}

#[test]
fn regression_tests_span_change() {
    // This test contains regression test for errors occurred during the big refactoring:
    // "Add a nightly feature which allows to manipulate spans to underline which part of the
    // template is failing compilation" <https://github.com/askama-rs/askama/issues/420>

    let syntax = Syntax::default();

    assert_eq!(
        Ast::from_str("{%- let [_] = [2] -%}", None, &syntax)
            .unwrap()
            .nodes(),
        [Box::new(Node::Let(Let {
            ws: Ws(Some(Whitespace::Suppress), Some(Whitespace::Suppress)),
            var: Target::Array(
                vec![Target::Placeholder(Span::new(9..10))],
                Span::new(8..12)
            ),
            val: LetValueOrBlock::Value(Box::new(Expr::Array {
                elems: vec![int_lit("2", Span::new(15..16))],
                span: Span::new(14..15)
            })),
            ty: None,
            is_mutable: false,
            span: Span::new(4..7),
        }))],
    );

    assert_eq!(
        Ast::from_str("{%- let (_) = [2] -%}", None, &syntax)
            .unwrap()
            .nodes(),
        [Box::new(Node::Let(Let {
            ws: Ws(Some(Whitespace::Suppress), Some(Whitespace::Suppress)),
            var: Target::Placeholder(Span::new(9..10)),
            val: LetValueOrBlock::Value(Box::new(Expr::Array {
                elems: vec![int_lit("2", Span::new(15..16))],
                span: Span::new(14..15)
            })),
            ty: None,
            is_mutable: false,
            span: Span::new(4..7),
        }))],
    );

    assert_eq!(
        Ast::from_str("Hello, {{ user | cased }}!", None, &syntax)
            .unwrap()
            .nodes(),
        [
            Box::new(Node::Lit(Lit {
                lws: "",
                val: "Hello,",
                rws: " ",
                span: Span::new(0..7),
            })),
            Box::new(Node::Expr(
                Ws(None, None),
                Box::new(Expr::Filter {
                    inner: Filter {
                        name: PathOrIdentifier::Identifier("cased", Span::new(17..22)),
                        arguments: vec![Box::new(Expr::Var {
                            name: "user",
                            span: Span::new(10..14)
                        })],
                    },
                    span: Span::new(15..23)
                })
            )),
            Box::new(Node::Lit(Lit {
                lws: "",
                val: "!",
                rws: "",
                span: Span::new(25..26),
            })),
        ],
    );

    assert_eq!(
        Ast::from_str("{{ ( 0 + 1 ) }}", None, &syntax)
            .unwrap()
            .nodes(),
        [Box::new(Node::Expr(
            Ws(None, None),
            Box::new(Expr::Group {
                elem: Box::new(Expr::BinOp {
                    inner: BinOp {
                        op: "+",
                        lhs: int_lit("0", Span::new(5..6)),
                        rhs: int_lit("1", Span::new(9..10)),
                    },
                    span: Span::new(7..8)
                }),
                span: Span::new(3..12)
            })
        ))]
    );
}

#[test]
fn test_unclosed_prefixed_string() {
    // Regression test for <https://issues.oss-fuzz.com/issues/440177293>.
    let syntax = Syntax::default();
    for test in ["{{ x!(i\") }}", "{{ x!(i\"\") }}"] {
        assert!(
            Ast::from_str(test, None, &syntax)
                .unwrap_err()
                .to_string()
                .contains("reserved prefix `i#`")
        );
    }
}

#[test]
fn test_excessive_call_depth() {
    let mut call = "a()".to_string();
    for _ in 0..1000 {
        call = format!("a({call})");
    }
    assert!(Ast::from_str(&format!("{{{{ {call} }}}}"), None, &Syntax::default()).is_err());
}

// regression test for <https://issues.oss-fuzz.com/issues/481742850>
#[test]
fn test_byte_literal_multi_byte() {
    // high ascii
    assert!(Ast::from_str("{{b'ä'}}", None, &Syntax::default()).is_err());
    assert!(Ast::from_str("{{x!(b'ä')}}", None, &Syntax::default()).is_err());
    // basic multilingual plane
    assert!(Ast::from_str("{{b'€'}}", None, &Syntax::default()).is_err());
    assert!(Ast::from_str("{{x!(b'€')}}", None, &Syntax::default()).is_err());
    // non-BMP
    assert!(Ast::from_str("{{b'𝄞'}}", None, &Syntax::default()).is_err());
    assert!(Ast::from_str("{{x!(b'𝄞')}}", None, &Syntax::default()).is_err());
}

// regression test for <https://issues.oss-fuzz.com/issues/471899485>
#[test]
fn test_expr_end_catastrophic_backtracking() {
    assert!(
        SyntaxBuilder {
            expr_end: Some("**"),
            ..SyntaxBuilder::default()
        }
        .to_syntax()
        .is_err()
    );
    assert!(
        SyntaxBuilder {
            expr_end: Some("***"),
            ..SyntaxBuilder::default()
        }
        .to_syntax()
        .is_err()
    );
}

#[test]
fn test_fallback_error_after_non_ascii_text() {
    assert_eq!(
        Ast::from_str("äöü {{a.b.c!( hello )}}", None, &Syntax::default())
            .unwrap_err()
            .to_string(),
        "the token `!` was not expected at this point in the expression\n\
        failed to parse template source near offset 14",
    );
    assert_eq!(
        Ast::from_str(
            "äöü {% block meta %}then{% else %}else{% endblock meta %}",
            None,
            &Syntax::default()
        )
        .unwrap_err()
        .to_string(),
        "node `else` was not expected in the current context: `block` block\n\
        failed to parse template source near offset 30",
    );
}

#[test]
fn test_node_spans() {
    const SRC: &str = concat!(
        r#"{% extends "b.html" %}{% import "m.html" as m %}{% macro mac(a) %}{% endmacro %}"#,
        "{% block b %}{% if a %}{%- else if b +%}{% else %}{% endif %}{% if let Some(q) = r %}",
        "{% endif %}{% match x %}{% when Some(y) %}{{ y }}{% else %}{% endmatch %}{% for i in v %}",
        "{% break %}{%- continue -%}{% endfor %}{% filter upper %}{% endfilter %}",
        "{% call m::mac(1) %}{% endcall %}{% let z = 1 %}{% set w %}{% endset %}{% decl d %}",
        r#"{% mut z += 2 %}{% raw %}r{% endraw %}{% include "i.html" %}{# c #}{% endblock %}"#,
    );

    fn walk(nodes: &[Box<Node<'_>>], out: &mut Vec<&'static str>) {
        let text = |span: Span| span.as_infix_of(SRC).unwrap();
        for node in nodes {
            out.push(text(node.span()));
            match &**node {
                Node::If(node) => node.branches.iter().for_each(|cond| {
                    out.push(text(cond.span));
                    walk(&cond.nodes, out);
                }),
                Node::Match(node) => node.arms.iter().for_each(|arm| {
                    out.push(text(arm.span));
                    walk(&arm.nodes, out);
                }),
                Node::Loop(node) => walk(&node.body, out),
                Node::BlockDef(node) => walk(&node.nodes, out),
                _ => {}
            }
        }
    }

    let ast = Ast::from_str(SRC, None, &Syntax::default()).unwrap();
    let mut spans = vec![];
    walk(ast.nodes(), &mut spans);
    assert_eq!(
        spans,
        [
            "extends", "import", "macro", "block", "if", "if", "else", "else", "if", "if", "match",
            "when", "y", "else", "for", "break", "continue", "filter", "call", "let", "set",
            "decl", "mut", "raw", "include", "{# c #}",
        ],
    );
}

#[test]
fn test_expr_spans() {
    let syntax = Syntax::default();
    for (expr, span) in [
        ("foo", "foo"),
        ("Foo::Bar", "Foo::Bar"),
        ("true", "true"),
        ("1", "1"),
        ("'c'", "'c'"),
        ("\"s\"", "\"s\""),
        ("[1, 2]", "["),
        ("[0; 3]", "["),
        ("a.b", "."),
        ("a[0]", "["),
        ("a|f", "|f "),
        ("a as i32", "as"),
        ("-a", "-"),
        ("a + b", "+"),
        ("a ~ b ~ c", " ~ "),
        ("a..b", ".."),
        ("(a)", "(a)"),
        ("(a, b)", "(a, b)"),
        ("f(x = 1)", "("),
        ("m!(x)", "!"),
        ("a?", "?"),
        ("S { x: 1 }", "{"),
        ("a is defined", "is"),
        ("a is not defined", "is"),
    ] {
        let src = format!("{{{{ {expr} }}}}");
        let ast = Ast::from_str(&src, None, &syntax).unwrap();
        let Node::Expr(_, expr) = &*ast.nodes()[0] else {
            panic!("expected an expression in {src:?}");
        };
        assert_eq!(expr.span().as_infix_of(&src), Some(span), "{src:?}");
        if let Expr::Call { call, .. } = &**expr {
            assert_eq!(call.args[0].span().as_infix_of(&src), Some("x = 1"));
        }
    }
}

#[test]
fn test_target_spans() {
    const SRC: &str = concat!(
        r#"{% match x %}{% when (a, [_, b @ ..]) or S { c, .. } %}{% when T(1, "s", 'c', true) %}"#,
        "{% when P::Q %}{% endmatch %}",
    );

    fn walk(target: &Target<'_>, out: &mut Vec<&'static str>) {
        out.push(target.span().as_infix_of(SRC).unwrap());
        match target {
            Target::Tuple(_, targets, _)
            | Target::Array(targets, _)
            | Target::OrChain(targets, _) => {
                targets.iter().for_each(|target| walk(target, out));
            }
            Target::Struct(_, targets, _) => targets.iter().for_each(|t| walk(&t.dest, out)),
            _ => {}
        }
    }

    let ast = Ast::from_str(SRC, None, &Syntax::default()).unwrap();
    let Node::Match(m) = &*ast.nodes()[0] else {
        panic!("expected a match");
    };
    let mut spans = vec![];
    for arm in &m.arms {
        arm.target
            .iter()
            .for_each(|target| walk(target, &mut spans));
    }
    assert_eq!(
        spans,
        [
            "(a, [_, b @ ..]) or S { c, .. } ",
            "(a, [_, b @ ..]) ",
            "a",
            "[_, b @ ..]",
            "_",
            "b @ ..",
            "S",
            "c",
            "..",
            "T",
            "1",
            "\"s\"",
            "'c'",
            "true",
            "P::Q",
        ],
    );
}

/// Renders an expression with explicit parentheses around every operator.
fn show(expr: &Expr<'_>) -> String {
    let join =
        |exprs: &[Box<Expr<'_>>], sep| exprs.iter().map(|e| show(e)).collect::<Vec<_>>().join(sep);
    match expr {
        Expr::Var { name, .. }
        | Expr::NumLit {
            num_with_suffix: name,
            ..
        } => name.to_string(),
        Expr::Unary { operator, expr, .. } => format!("({operator}{})", show(expr)),
        Expr::BinOp {
            inner: BinOp { op, lhs, rhs },
            ..
        } => format!("({} {op} {})", show(lhs), show(rhs)),
        Expr::Concat { exprs, .. } => format!("({})", join(exprs, " ~ ")),
        Expr::Filter {
            inner:
                Filter {
                    name: PathOrIdentifier::Identifier(name, _),
                    arguments,
                },
            ..
        } => format!("{name}({})", join(arguments, ", ")),
        Expr::As { lhs, target, .. } => format!("({} as {target})", show(lhs)),
        Expr::IsDefined { var_name, .. } => format!("({var_name} is defined)"),
        Expr::Range { inner, .. } => {
            let side = |e: &Option<Box<Expr<'_>>>| e.as_ref().map_or(String::new(), |e| show(e));
            format!("({}{}{})", side(&inner.lhs), inner.op, side(&inner.rhs))
        }
        Expr::Group { elem, .. } => format!("({})", show(elem)),
        Expr::Array { elems, .. } => format!("[{}]", join(elems, ", ")),
        Expr::Call { call, .. } => format!("{}({})", show(&call.path), join(&call.args, ", ")),
        _ => panic!("unexpected {expr:?}"),
    }
}

fn parse_expr(src: &str) -> Result<String, String> {
    let syntax = Syntax::default();
    match Ast::from_str(&format!("{{{{ {src} }}}}"), None, &syntax) {
        Ok(ast) => match &*ast.nodes {
            [node] => match &**node {
                Node::Expr(_, expr) => Ok(show(expr)),
                node => panic!("unexpected {node:?}"),
            },
            nodes => panic!("unexpected {nodes:?}"),
        },
        Err(err) => Err(err.to_string()),
    }
}

#[test]
fn test_infix_precedence_of_every_level_pair() {
    // From loosest to tightest binding; comparisons cannot be chained, so `==` is not repeated.
    const LEVELS: &[(&str, &str)] = &[
        ("||", "||"),
        ("&&", "&&"),
        ("==", "=="),
        ("bitor", "|"),
        ("xor", "^"),
        ("bitand", "&"),
        ("<<", "<<"),
        ("+", "+"),
        ("~", "~"),
        ("*", "*"),
    ];
    for (i, &(lo, lo_show)) in LEVELS.iter().enumerate() {
        for &(hi, hi_show) in &LEVELS[i + 1..] {
            let tight = |a: &str, b: &str| match hi {
                "~" => format!("({a} ~ {b})"),
                _ => format!("({a} {hi_show} {b})"),
            };
            let loose = |a: &str, b: &str| match lo {
                "~" => format!("({a} ~ {b})"),
                _ => format!("({a} {lo_show} {b})"),
            };
            assert_eq!(
                parse_expr(&format!("a {lo} b {hi} c")),
                Ok(loose("a", &tight("b", "c")))
            );
            assert_eq!(
                parse_expr(&format!("a {hi} b {lo} c")),
                Ok(loose(&tight("a", "b"), "c"))
            );
        }
        let expected = match lo {
            "==" => continue,
            "~" => "(a ~ b ~ c ~ d)".to_owned(),
            _ => format!("(((a {lo_show} b) {lo_show} c) {lo_show} d)"),
        };
        assert_eq!(parse_expr(&format!("a {lo} b {lo} c {lo} d")), Ok(expected));
    }
}

#[test]
fn test_infix_edge_cases() {
    for (src, expected) in [
        // no whitespace around operators
        ("a+b*c", "(a + (b * c))"),
        ("a&&b||c", "((a && b) || c)"),
        // prefix operators bind tighter than any infix operator
        ("-a * b", "((-a) * b)"),
        ("!a && !b", "((!a) && (!b))"),
        ("- -a", "(-(-a))"),
        ("*&a + b", "((*(&a)) + b)"),
        // the same tokens as infix and prefix operators
        ("a - -b", "(a - (-b))"),
        ("a * *b", "(a * (*b))"),
        ("a bitand &b", "(a & (&b))"),
        ("a < -b", "(a < (-b))"),
        // filters bind looser than prefix operators and tighter than infix ones
        ("-a|f", "f((-a))"),
        ("a + b|f", "(a + f(b))"),
        ("a|f(1)|g + b", "(g(f(a, 1)) + b)"),
        // `is` and `as` apply to the operand left of them
        ("a as i32 + b", "((a as i32) + b)"),
        ("-a as i32", "((-a) as i32)"),
        ("a is defined && b", "((a is defined) && b)"),
        // a `~` chain is flattened, but not across parentheses or looser operators
        ("a ~ b * c ~ d", "(a ~ (b * c) ~ d)"),
        ("(a ~ b) ~ c", "(((a ~ b)) ~ c)"),
        ("a ~ b + c ~ d", "((a ~ b) + (c ~ d))"),
        ("a ~ b|f ~ c", "(a ~ f(b) ~ c)"),
        ("a|f(1) ~ b", "(f(a, 1) ~ b)"),
        ("a as i32 ~ b", "((a as i32) ~ b)"),
        ("f(1) ~ b", "(f(1) ~ b)"),
        ("a is defined ~ b", "((a is defined) ~ b)"),
        ("[a] ~ b", "([a] ~ b)"),
        // ranges take whole expressions on either side
        ("a + 1..b * 2", "((a + 1)..(b * 2))"),
        ("..a || b", "(..(a || b))"),
        ("a + b..", "((a + b)..)"),
        ("a * (b + c)", "(a * ((b + c)))"),
    ] {
        assert_eq!(parse_expr(src).as_deref(), Ok(expected), "{src}");
    }
}

#[test]
fn test_infix_errors() {
    for src in [
        "a ~b",
        "a~ b",
        "a~b",
        "a|f~ b",
        "a ~ b ~",
        "a +",
        "a + / b",
        "a && || b",
        "+a",
        "a + )",
    ] {
        assert!(parse_expr(src).is_err(), "{src}");
    }
    assert!(
        parse_expr("a~b")
            .unwrap_err()
            .contains("the concat operator `~` must be surrounded by spaces")
    );

    // `~` and `-` next to the delimiters are whitespace control, not operators
    let syntax = Syntax::default();
    for src in [
        "{{ a ~}}",
        "{{~ a ~}}",
        "{{ a -}}",
        "{%~ if a ~%}{%~ endif ~%}",
        "{%- if a + b -%}{%- endif -%}",
    ] {
        assert!(Ast::from_str(src, None, &syntax).is_ok(), "{src}");
    }
}

#[test]
fn test_infix_nesting_limit() {
    assert!(parse_expr(&format!("{}a", "-".repeat(100))).is_ok());
    assert!(parse_expr(&format!("{}a", "-".repeat(1000))).is_err());
    assert!(parse_expr(&format!("a{}", " ~ a".repeat(1000))).is_ok());
    assert!(parse_expr(&format!("a{}", " + a".repeat(1000))).is_err());

    // A chain holds one level per operator and gives them back when it ends, so these limits
    // are about the parser's state, not the depth of the AST.
    let fits = |expr: String| {
        Ast::from_str(&format!("{{{{ {expr} }}}}"), None, &Syntax::default()).is_ok()
    };
    assert!(fits(format!("a{}", " * a".repeat(127))));
    assert!(!fits(format!("a{}", " * a".repeat(128))));
    assert!(fits(format!(
        "a{}{}",
        " * a".repeat(127),
        " + a".repeat(127)
    )));
    assert!(fits(format!("{}a{}", "!".repeat(127), " * a".repeat(127))));
    assert!(fits(format!("a{}|f{}", " * a".repeat(62), "|f".repeat(62))));
    assert!(!fits(format!(
        "a{}|f{}",
        " * a".repeat(64),
        "|f".repeat(64)
    )));
}
