use std::{fmt, io};

use askama::Template;
use assert_matches::assert_matches;

#[test]
fn test_int_parser() {
    #[derive(Template)]
    #[template(source = "{% let v = self.parse()? %}{{s}}={{v}}", ext = "txt")]
    struct IntParserTemplate<'a> {
        s: &'a str,
    }

    impl IntParserTemplate<'_> {
        fn parse(&self) -> Result<i32, std::num::ParseIntError> {
            self.s.parse()
        }
    }

    let template = IntParserTemplate { s: "💯" };
    assert_matches!(template.render(), Err(askama::Error::Custom(_)));
    assert_eq!(
        format!("{}", template.render().unwrap_err()),
        "invalid digit found in string"
    );

    let template = IntParserTemplate { s: "100" };
    assert_eq!(template.render().unwrap(), "100=100");
}

#[test]
fn fail_fmt() {
    #[derive(Template)]
    #[template(source = "{{ value()? }}", ext = "txt")]
    struct FailFmt {
        inner: Option<&'static str>,
    }

    impl FailFmt {
        fn value(&self) -> Result<&'static str, fmt::Error> {
            if let Some(inner) = self.inner {
                Ok(inner)
            } else {
                Err(fmt::Error)
            }
        }
    }

    let template = FailFmt { inner: None };
    assert_matches!(template.render(), Err(askama::Error::Fmt));
    assert_eq!(
        format!("{}", template.render().unwrap_err()),
        format!("{}", std::fmt::Error)
    );

    let template = FailFmt {
        inner: Some("hello world"),
    };
    assert_eq!(template.render().unwrap(), "hello world");
}

#[test]
fn fail_str() {
    #[derive(Template)]
    #[template(source = "{{ value()? }}", ext = "txt")]
    struct FailStr {
        value: bool,
    }

    impl FailStr {
        fn value(&self) -> Result<&'static str, &'static str> {
            if !self.value {
                Err("FAIL")
            } else {
                Ok("hello world")
            }
        }
    }

    let template = FailStr { value: false };
    assert_matches!(template.render(), Err(askama::Error::Custom(_)));
    assert_eq!(format!("{}", template.render().unwrap_err()), "FAIL");

    let template = FailStr { value: true };
    assert_eq!(template.render().unwrap(), "hello world");
}

#[test]
fn error_conversion_from_fmt() {
    #[derive(Template)]
    #[template(source = "{{ value()? }}", ext = "txt")]
    struct ResultTemplate {
        succeed: bool,
    }

    impl ResultTemplate {
        fn value(&self) -> Result<&'static str, fmt::Error> {
            match self.succeed {
                true => Ok("hello"),
                false => Err(fmt::Error),
            }
        }
    }

    assert_matches!(
        ResultTemplate { succeed: true }.render().as_deref(),
        Ok("hello")
    );
    assert_matches!(
        ResultTemplate { succeed: false }.render().as_deref(),
        Err(askama::Error::Fmt)
    );
}

#[test]
fn error_conversion_from_askama_custom() {
    #[derive(Template)]
    #[template(source = "{{ value()? }}", ext = "txt")]
    struct ResultTemplate {
        succeed: bool,
    }

    impl ResultTemplate {
        fn value(&self) -> Result<&'static str, askama::Error> {
            match self.succeed {
                true => Ok("hello"),
                false => Err(askama::Error::custom(CustomError)),
            }
        }
    }

    #[derive(Debug)]
    struct CustomError;

    impl fmt::Display for CustomError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("custom")
        }
    }

    impl std::error::Error for CustomError {}

    assert_matches!(
        ResultTemplate { succeed: true }.render().as_deref(),
        Ok("hello")
    );

    let err = match (ResultTemplate { succeed: false }.render().unwrap_err()) {
        askama::Error::Custom(err) => err,
        err => panic!("Expected Error::Custom(_), got {err:#?}"),
    };
    assert!(err.is::<CustomError>());
}

#[test]
fn error_conversion_from_custom() {
    #[derive(Template)]
    #[template(source = "{{ value()? }}", ext = "txt")]
    struct ResultTemplate {
        succeed: bool,
    }

    impl ResultTemplate {
        fn value(&self) -> Result<&'static str, CustomError> {
            match self.succeed {
                true => Ok("hello"),
                false => Err(CustomError),
            }
        }
    }

    #[derive(Debug)]
    struct CustomError;

    impl fmt::Display for CustomError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("custom")
        }
    }

    impl std::error::Error for CustomError {}

    assert_matches!(
        ResultTemplate { succeed: true }.render().as_deref(),
        Ok("hello")
    );

    let err = match (ResultTemplate { succeed: false }.render().unwrap_err()) {
        askama::Error::Custom(err) => err,
        err => panic!("Expected Error::Custom(_), got {err:#?}"),
    };
    assert!(err.is::<CustomError>());
}

#[test]
fn error_conversion_from_wrapped_in_io() {
    #[derive(Template)]
    #[template(source = "{{ value()? }}", ext = "txt")]
    struct ResultTemplate {
        succeed: bool,
    }

    impl ResultTemplate {
        fn value(&self) -> Result<&'static str, io::Error> {
            match self.succeed {
                true => Ok("hello"),
                false => Err(io::Error::new(io::ErrorKind::InvalidData, CustomError)),
            }
        }
    }

    #[derive(Debug)]
    struct CustomError;

    impl fmt::Display for CustomError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("custom")
        }
    }

    impl std::error::Error for CustomError {}

    assert_matches!(
        ResultTemplate { succeed: true }.render().as_deref(),
        Ok("hello")
    );

    let err = match (ResultTemplate { succeed: false }.render().unwrap_err()) {
        askama::Error::Custom(err) => err,
        err => panic!("Expected Error::Custom(_), got {err:#?}"),
    };
    assert!(err.is::<CustomError>());
}
