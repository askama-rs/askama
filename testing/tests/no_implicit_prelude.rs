#![no_implicit_prelude]

use ::askama::Template;

#[test]
fn test_source() {
    #[derive(Template)]
    #[template(ext = "html", source = "Hello, {{ name }}!")]
    struct HelloTemplate<'a> {
        name: &'a str,
    }

    let hello = HelloTemplate { name: "world" };
    ::std::assert_eq!("Hello, world!", hello.render().unwrap());
}

#[test]
fn test_path() {
    #[derive(Template)]
    #[template(path = "hello.html")]
    struct HelloTemplate<'a> {
        name: &'a str,
    }

    let hello = HelloTemplate { name: "world" };
    ::std::assert_eq!("Hello, world!", hello.render().unwrap());
}
