// Tests to check parsing of generics.

use askama::Template;

#[test]
fn simple_tuple_generic() {
    fn f<F>(_f: &F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(source = r#"{{ f::<()>(()) }}"#, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}

#[test]
fn tuple_tuple_generic() {
    fn f<F>(_f: &F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(source = r#"{{ f::<((), ())>(((), ())) }}"#, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}

#[test]
fn tuple_in_type_generic() {
    fn f<F>(_f: &F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(source = r#"{{ f::<Vec<()>>(&Vec::new()) }}"#, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}

#[test]
fn tuple_in_type_generic2() {
    fn f<F>(_f: &F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(
        source = r#"{{ f::<Vec<(u32, Vec<u32>)>>(&Vec::new()) }}"#,
        ext = "txt"
    )]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}

#[test]
fn tuple_end_comma_generic() {
    fn f<F>(_f: &F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(source = r#"{{ f::<(,)>(()) }}"#, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}

#[test]
fn tuple_end_comma_generic2() {
    fn f<F>(_f: &F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(source = r#"{{ f::<(u32,)>((0)) }}"#, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}

#[test]
fn simple_array_generic() {
    fn f<F>(_f: &F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(source = r#"{{ f::<[u32; 3]>(&[0, 0, 0]) }}"#, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}

#[test]
fn simple_slice_generic() {
    fn f<F>(_f: F) -> String {
        "a".into()
    }

    #[derive(Template)]
    #[template(source = r#"{{ f::<&[u32]>([0]) }}"#, ext = "txt")]
    struct Foo;

    assert_eq!(Foo.render().unwrap(), "a");
}
