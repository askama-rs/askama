#![no_std]

use core::fmt;
use core::str::Utf8Error;

use askama::Template;
use assert_matches::assert_matches;

#[test]
fn test_source() {
    #[derive(Template)]
    #[template(
        ext = "html",
        source = "Hello {%- if let Some(user) = user? -%} , {{ user }} {%- endif -%}!"
    )]
    struct Hello<'a> {
        user: Result<Option<&'a str>, CustomError>,
    }

    test_common(|user| Hello { user });
}

#[test]
fn test_path() {
    #[derive(Template)]
    #[template(path = "hello-world.html")]
    struct Hello<'a> {
        user: Result<Option<&'a str>, CustomError>,
    }

    test_common(|user| Hello { user });
}

#[track_caller]
fn test_common<'a, T: Template + 'a>(hello: fn(Result<Option<&'a str>, CustomError>) -> T) {
    let mut buffer = [0; 32];

    let tmpl = hello(Ok(None));
    let mut cursor = Cursor::new(&mut buffer);
    assert_matches!(tmpl.render_into(&mut cursor), Ok(()));
    assert_eq!(cursor.finalize(), Ok("Hello!"));

    let tmpl = hello(Ok(Some("user")));
    let mut cursor = Cursor::new(&mut buffer);
    assert_matches!(tmpl.render_into(&mut cursor), Ok(()));
    assert_eq!(cursor.finalize(), Ok("Hello, user!"));

    let tmpl = hello(Ok(Some("<user>")));
    let mut cursor = Cursor::new(&mut buffer);
    assert_matches!(tmpl.render_into(&mut cursor), Ok(()));
    assert_eq!(cursor.finalize(), Ok("Hello, &#60;user&#62;!"));

    let tmpl = hello(Err(CustomError));
    let mut cursor = Cursor::new(&mut buffer);
    let err = match tmpl.render_into(&mut cursor) {
        Err(askama::Error::Custom(err)) => err,
        err => panic!("Expected `Err(Custom(_))`, got {err:#?}"),
    };
    assert!(err.is::<CustomError>());
}

struct Cursor<'a> {
    data: &'a mut [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(data: &'a mut [u8]) -> Self {
        Self { data, pos: 0 }
    }

    fn finalize(self) -> Result<&'a str, Utf8Error> {
        core::str::from_utf8(&self.data[..self.pos])
    }
}

impl fmt::Write for Cursor<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let data = &mut self.data[self.pos..];
        if data.len() >= s.len() {
            data[..s.len()].copy_from_slice(s.as_bytes());
            self.pos += s.len();
            Ok(())
        } else {
            Err(fmt::Error)
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct CustomError;

impl fmt::Display for CustomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl core::error::Error for CustomError {}
