use std::fmt;

use assert_matches::assert_matches;
use some_name::Template;

pub(crate) mod some {
    pub(crate) mod deeply {
        pub(crate) mod nested {
            pub(crate) mod path {
                pub(crate) mod with {
                    #[allow(clippy::single_component_path_imports)] // false positive
                    pub(crate) use some_name;
                }
            }
        }
    }
}

#[test]
fn test_source() {
    #[derive(Template)]
    #[template(
        ext = "html",
        source = "Hello {%- if let Some(user) = user? -%} , {{ user }} {%- endif -%}!",
        askama = some::deeply::nested::path::with::some_name
    )]
    struct Hello<'a> {
        user: Result<Option<&'a str>, fmt::Error>,
    }

    test_common(|user| Hello { user });
}

#[test]
fn test_path() {
    #[derive(Template)]
    #[template(
        path = "hello-world.html",
        askama = some::deeply::nested::path::with::some_name
    )]
    struct Hello<'a> {
        user: Result<Option<&'a str>, fmt::Error>,
    }

    test_common(|user| Hello { user });
}

#[track_caller]
fn test_common<'a, T: Template + 'a>(hello: fn(Result<Option<&'a str>, fmt::Error>) -> T) {
    let tmpl = hello(Ok(None));
    let mut cursor = String::new();
    assert_matches!(tmpl.render_into(&mut cursor), Ok(()));
    assert_eq!(cursor, "Hello!");

    let tmpl = hello(Ok(Some("user")));
    let mut cursor = String::new();
    assert_matches!(tmpl.render_into(&mut cursor), Ok(()));
    assert_eq!(cursor, "Hello, user!");

    let tmpl = hello(Ok(Some("<user>")));
    let mut cursor = String::new();
    assert_matches!(tmpl.render_into(&mut cursor), Ok(()));
    assert_eq!(cursor, "Hello, &#60;user&#62;!");

    let tmpl = hello(Err(fmt::Error));
    let mut cursor = String::new();
    assert_matches!(tmpl.render_into(&mut cursor), Err(some_name::Error::Fmt));
}
