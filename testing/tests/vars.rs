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
        source = "{% let x %}{% let x = 1 %}{% for x in x..=x %}{{ x }}{% endfor %}",
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
