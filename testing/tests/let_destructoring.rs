use askama::Template;

#[test]
fn test_let_destruct_tuple() {
    #[derive(Template)]
    #[template(source = "{% let (a, b, c) = v %}{{a}}{{b}}{{c}}", ext = "txt")]
    struct LetDestructoringTuple {
        v: (i32, i32, i32),
    }

    let t = LetDestructoringTuple { v: (1, 2, 3) };
    assert_eq!(t.render().unwrap(), "123");
}

struct UnnamedStruct(i32, i32, i32);

#[test]
fn test_let_destruct_unnamed_struct() {
    #[derive(Template)]
    #[template(
        source = "{% let UnnamedStruct(a, b, c) = v %}{{a}}{{b}}{{c}}",
        ext = "txt"
    )]
    struct LetDestructoringUnnamedStruct {
        v: UnnamedStruct,
    }

    let t = LetDestructoringUnnamedStruct {
        v: UnnamedStruct(1, 2, 3),
    };
    assert_eq!(t.render().unwrap(), "123");
}

#[test]
fn test_let_destruct_unnamed_struct_ref() {
    #[derive(Template)]
    #[template(
        source = "{% let UnnamedStruct(a, b, c) = v %}{{a}}{{b}}{{c}}",
        ext = "txt"
    )]
    struct LetDestructoringUnnamedStructRef<'a> {
        v: &'a UnnamedStruct,
    }

    let v = UnnamedStruct(1, 2, 3);
    let t = LetDestructoringUnnamedStructRef { v: &v };
    assert_eq!(t.render().unwrap(), "123");
}

struct NamedStruct {
    a: i32,
    b: i32,
    c: i32,
}

#[test]
fn test_let_destruct_named_struct() {
    #[derive(Template)]
    #[template(
        source = "{% let NamedStruct { a, b: d, c } = v %}{{a}}{{d}}{{c}}",
        ext = "txt"
    )]
    struct LetDestructoringNamedStruct {
        v: NamedStruct,
    }

    let t = LetDestructoringNamedStruct {
        v: NamedStruct { a: 1, b: 2, c: 3 },
    };
    assert_eq!(t.render().unwrap(), "123");
}

#[test]
fn test_let_destruct_named_struct_ref() {
    #[derive(Template)]
    #[template(
        source = "{% let NamedStruct { a, b: d, c } = v %}{{a}}{{d}}{{c}}",
        ext = "txt"
    )]
    struct LetDestructoringNamedStructRef<'a> {
        v: &'a NamedStruct,
    }

    let v = NamedStruct { a: 1, b: 2, c: 3 };
    let t = LetDestructoringNamedStructRef { v: &v };
    assert_eq!(t.render().unwrap(), "123");
}

mod some {
    pub mod path {
        pub struct Struct<'a>(pub &'a str);
    }
}

#[test]
fn test_let_destruct_with_path() {
    #[derive(Template)]
    #[template(source = "{% let some::path::Struct(v) = v %}{{v}}", ext = "txt")]
    struct LetDestructoringWithPath<'a> {
        v: some::path::Struct<'a>,
    }

    let t = LetDestructoringWithPath {
        v: some::path::Struct("hello"),
    };
    assert_eq!(t.render().unwrap(), "hello");
}

#[test]
fn test_let_destruct_with_path_and_with_keyword() {
    #[derive(Template)]
    #[template(source = "{% let some::path::Struct with (v) = v %}{{v}}", ext = "txt")]
    struct LetDestructoringWithPathAndWithKeyword<'a> {
        v: some::path::Struct<'a>,
    }

    let t = LetDestructoringWithPathAndWithKeyword {
        v: some::path::Struct("hello"),
    };
    assert_eq!(t.render().unwrap(), "hello");
}

#[allow(irrefutable_let_patterns)] // part of the test
#[test]
fn test_has_rest_pattern() {
    #[derive(Template)]
    #[template(
        source = "
{%- if let RestPattern2 { a, b } = x -%}hello {{ a }}{%- endif -%}
{%- if let RestPattern2 { a, b, } = x -%}hello {{ b }}{%- endif -%}
{%- if let RestPattern2 { a, .. } = x -%}hello {{ a }}{%- endif -%}
",
        ext = "html"
    )]
    struct RestPattern {
        x: RestPattern2,
    }

    struct RestPattern2 {
        a: u32,
        b: u32,
    }

    let t = RestPattern {
        x: RestPattern2 { a: 0, b: 1 },
    };
    assert_eq!(t.render().unwrap(), "hello 0hello 1hello 0");
}

#[allow(dead_code)]
struct X {
    a: u32,
    b: u32,
}

#[allow(irrefutable_let_patterns)] // part of the test
#[test]
fn test_t1() {
    #[derive(Template)]
    #[template(
        source = "
{%- if let X { a, .. } = x -%}hello {{ a }}{%- endif -%}
",
        ext = "html"
    )]
    struct T1 {
        x: X,
    }

    let t = T1 {
        x: X { a: 1, b: 2 },
    };
    assert_eq!(t.render().unwrap(), "hello 1");
}

#[allow(irrefutable_let_patterns)] // part of the test
#[test]
fn test_t2() {
    #[derive(Template)]
    #[template(
        source = "
{%- if let X { .. } = x -%}hello{%- endif -%}
",
        ext = "html"
    )]
    struct T2 {
        x: X,
    }

    let t = T2 {
        x: X { a: 1, b: 2 },
    };
    assert_eq!(t.render().unwrap(), "hello");
}
