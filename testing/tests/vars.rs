#![allow(clippy::useless_let_if_seq)]

use askama::Template;

#[test]
fn test_let() {
    #[derive(Template)]
    #[template(source = "{% let v = s %}{{ v }}", ext = "txt")]
    struct LetTemplate<'a> {
        s: &'a str,
    }

    let t = LetTemplate { s: "foo" };
    assert_eq!(t.render().unwrap(), "foo");
}

#[test]
fn test_let_tuple() {
    #[derive(Template)]
    #[template(path = "let.html")]
    struct LetTupleTemplate<'a> {
        s: &'a str,
        t: (&'a str, &'a str),
    }

    let t = LetTupleTemplate {
        s: "foo",
        t: ("bar", "bazz"),
    };
    assert_eq!(t.render().unwrap(), "foo\nbarbazz");
}

#[test]
fn test_let_decl() {
    #[derive(Template)]
    #[template(path = "let-decl.html")]
    struct LetDeclTemplate<'a> {
        cond: bool,
        s: &'a str,
    }

    let t = LetDeclTemplate {
        cond: false,
        s: "bar",
    };
    assert_eq!(t.render().unwrap(), "bar");
}

#[test]
fn test_let_shadow() {
    #[derive(Template)]
    #[template(path = "let-shadow.html")]
    struct LetShadowTemplate {
        cond: bool,
    }

    impl LetShadowTemplate {
        fn tuple() -> (i32, i32) {
            (4, 5)
        }
    }

    let t = LetShadowTemplate { cond: true };
    assert_eq!(t.render().unwrap(), "22-1-33-11-22");

    let t = LetShadowTemplate { cond: false };
    assert_eq!(t.render().unwrap(), "222-1-333-4-5-11-222");
}

#[test]
fn test_self_iter() {
    #[derive(Template)]
    #[template(source = "{% for v in self.0 %}{{ v }}{% endfor %}", ext = "txt")]
    struct SelfIterTemplate(Vec<usize>);

    let t = SelfIterTemplate(vec![1, 2, 3]);
    assert_eq!(t.render().unwrap(), "123");
}

#[test]
fn test_if_let() {
    #[derive(Template)]
    #[template(
        source = "{% if true %}{% let t = a.unwrap() %}{{ t }}{% endif %}",
        ext = "txt"
    )]
    struct IfLet {
        a: Option<&'static str>,
    }

    let t = IfLet { a: Some("foo") };
    assert_eq!(t.render().unwrap(), "foo");
}

#[test]
fn test_destruct_tuple() {
    #[derive(Template)]
    #[template(path = "let-destruct-tuple.html")]
    struct LetDestructTupleTemplate {
        abcd: (char, ((char, char), char)),
    }

    let t = LetDestructTupleTemplate {
        abcd: ('w', (('x', 'y'), 'z')),
    };
    assert_eq!(t.render().unwrap(), "wxyz\nwz\nw");
}

#[test]
fn test_decl_range() {
    #[derive(Template)]
    #[template(
        source = "{% let x = 1 %}{% for x in x..=x %}{{ x }}{% endfor %}",
        ext = "txt"
    )]
    struct DeclRange;

    let t = DeclRange;
    assert_eq!(t.render().unwrap(), "1");
}

#[test]
fn test_decl_assign_range() {
    #[derive(Template)]
    #[template(
        source = "{% decl x %}{% let x = 1 %}{% for x in x..=x %}{{ x }}{% endfor %}",
        ext = "txt"
    )]
    struct DeclAssignRange;

    let t = DeclAssignRange;
    assert_eq!(t.render().unwrap(), "1");
}

#[test]
fn test_not_moving_fields_in_var() {
    #[derive(Template)]
    #[template(
        source = "
{%- set t = title -%}
{{t}}/{{title -}}
",
        ext = "txt"
    )]
    struct DoNotMoveFields {
        title: String,
    }

    let x = DoNotMoveFields {
        title: "a".to_string(),
    };
    assert_eq!(x.render().unwrap(), "a/a");
}

// Ensure that using a local variable as value when creating
// another variable will not be behind a reference.
#[test]
fn test_moving_local_vars() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- let a = 1 -%}
{%- if a == 1 %}A{% endif -%}
{%- let b = a -%}
{%- if b == 1 %}B{% endif -%}
{%- let c = a + 0 -%}
{%- if c == 1 %}C{% endif -%}
{% let d = x %}
{%- if *d == 1 %}D{% endif -%}
{%- let e = y -%}
{%- if e == "a" %}E{% endif -%}
{%- let f = Bla::new() -%}
{%- if f.x == 0 %}F{% endif -%}
{%- let g = f.x -%}
{%- if *g == 0 %}G{% endif -%}
    "#,
        ext = "txt"
    )]
    struct X {
        x: u32,
        y: String,
    }
    struct Bla {
        x: u32,
    }

    impl Bla {
        fn new() -> Self {
            Self { x: 0 }
        }
    }

    let x = X {
        x: 1,
        y: "a".to_owned(),
    };
    assert_eq!(x.render().unwrap(), "ABCDEFG");
}

// Ensure that if a variable initialization expression ends with a `?`, we don't put it behind
// a reference.
#[test]
fn test_variable_from_question_mark_init_expr() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- let v2 = v.as_str().ok_or("error")? %}
{%- if v2 == "foo" %}1{% endif -%}
"#,
        ext = "txt"
    )]
    struct X {
        v: B,
    }

    struct B;
    impl B {
        fn as_str(&self) -> Option<&'static str> {
            Some("foo")
        }
    }

    assert_eq!(X { v: B }.render().unwrap(), "1");
}

// Test that we can have mutable variable declarations.
#[test]
fn mutable_var() {
    #[derive(Template)]
    #[template(
        ext = "html",
        source = "
{%- let mut x = [1, 2].iter() %}
{{- x.next().unwrap() -}}
{{- x.next().unwrap() -}}
"
    )]
    struct Mut;

    assert_eq!(Mut.render().unwrap(), "12");
}
