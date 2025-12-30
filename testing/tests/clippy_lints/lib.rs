#![deny(clippy::elidable_lifetime_names)]
#![deny(clippy::all)]
#![deny(clippy::unnecessary_wraps)]

/// Checks that `clippy::unnecessary_wraps` is not triggered.
#[cfg(any())] // FIXME: <https://github.com/askama-rs/askama/issues/651>
pub mod unnecessary_wraps {
    use askama::Template;

    mod filters {
        use std::fmt::Display;

        #[askama::filter_fn]
        pub(super) fn simple(
            value: impl Display,
            _env: &dyn askama::Values,
        ) -> askama::Result<String> {
            Ok(value.to_string())
        }
    }

    #[derive(Template)]
    #[template(source = r#"{{ "Hello" | simple }}"#, ext = "txt")]
    struct Test<'a> {
        _data: &'a (),
    }

    #[test]
    fn test_output() {
        let test = Test { _data: &() };
        assert_eq!(test.render().unwrap(), "Hello");
    }
}

/// Checks that `clippy::elidable_lifetime_names` is not triggered.
pub mod elidable_lifetime_names {
    use askama::Template;

    #[derive(Debug, Template)]
    #[template(source = "Hello", ext = "txt")]
    struct Test<'a> {
        _data: &'a (),
    }

    #[test]
    fn test_output() {
        let test = Test { _data: &() };
        assert_eq!(test.render().unwrap(), "Hello");
    }
}
