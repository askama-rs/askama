use std::borrow::Cow;
use std::num::{NonZeroU32, Saturating, Wrapping};
use std::pin::Pin;
use std::sync::Arc;

use askama::Template;

#[test]
fn test_default() {
    // In this test the filter |default should render the variable `value` if it is default.
    // Otherwise the default value "unknown" is rendered.

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown") }}"#, ext = "html")]
    struct SuchVariable {
        value: i64,
    }

    assert_eq!(SuchVariable { value: 42 }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown") }}"#, ext = "html")]
    struct NoSuchVariable {
        _value: i64,
    }

    assert_eq!(NoSuchVariable { _value: 42 }.render().unwrap(), "unknown");

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", false) }}"#, ext = "html")]
    struct SuchVariable2 {
        value: i64,
    }

    assert_eq!(SuchVariable2 { value: 42 }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", false) }}"#, ext = "html")]
    struct NoSuchVariable2 {
        _value: i64,
    }

    assert_eq!(NoSuchVariable2 { _value: 42 }.render().unwrap(), "unknown");
}

#[test]
fn test_defined_or() {
    // In this test the filter |defined_or should render the variable `value` if it is default.
    // Otherwise the default value "unknown" is rendered.

    #[derive(Template)]
    #[template(source = r#"{{ value | defined_or("unknown") }}"#, ext = "html")]
    struct SuchVariable {
        value: i64,
    }

    assert_eq!(SuchVariable { value: 42 }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(source = r#"{{ value | defined_or("unknown") }}"#, ext = "html")]
    struct NoSuchVariable {
        _value: i64,
    }

    assert_eq!(NoSuchVariable { _value: 42 }.render().unwrap(), "unknown");
}

#[test]
fn test_default_var_with_unwrap() {
    // In this test the filter |default should try to unwrap the variable `value`.
    // If the variable exists and the value could be unwrapped, then the value is rendered.
    // Otherwise the default value "unknown" is rendered.

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct AnOption {
        value: Option<i64>,
    }

    assert_eq!(AnOption { value: None }.render().unwrap(), "unknown");
    assert_eq!(AnOption { value: Some(42) }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct AResult {
        value: Result<i64, std::fmt::Error>,
    }

    assert_eq!(
        AResult {
            value: Err(std::fmt::Error)
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(AResult { value: Ok(42) }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct NoSuchVariable {
        _value: Option<i64>,
    }

    assert_eq!(NoSuchVariable { _value: None }.render().unwrap(), "unknown");
    assert_eq!(
        NoSuchVariable { _value: Some(42) }.render().unwrap(),
        "unknown"
    );
}

#[test]
fn test_assigned_or_var_with_unwrap() {
    // In this test the filter |assigned_or should try to unwrap the variable `value`.
    // If the variable exists and the value could be unwrapped, then the value is rendered.
    // Otherwise the default value "unknown" is rendered.

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct AnOption {
        value: Option<i64>,
    }

    assert_eq!(AnOption { value: None }.render().unwrap(), "unknown");
    assert_eq!(AnOption { value: Some(42) }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct AResult {
        value: Result<i64, std::fmt::Error>,
    }

    assert_eq!(
        AResult {
            value: Err(std::fmt::Error)
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(AResult { value: Ok(42) }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct NoSuchVariable {
        _value: Option<i64>,
    }

    assert_eq!(NoSuchVariable { _value: None }.render().unwrap(), "unknown");
    assert_eq!(
        NoSuchVariable { _value: Some(42) }.render().unwrap(),
        "unknown"
    );
}

#[test]
fn test_default_expr_with_unwrap() {
    // In this test the filter |default should try to unwrap the outcome of an expression.
    // If the outcome could be unwrapped, then the value is rendered.
    // Otherwise the default value "unknown" is rendered.

    #[derive(Template)]
    #[template(
        source = r#"{{ NonZeroU32::new(*value) | default("unknown", true) }}"#,
        ext = "html"
    )]
    struct AnOption {
        value: u32,
    }

    assert_eq!(AnOption { value: 0 }.render().unwrap(), "unknown");
    assert_eq!(AnOption { value: 42 }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(
        source = r#"{{ std::str::from_utf8(value) | default("unknown", true) }}"#,
        ext = "html"
    )]
    struct AResult<'a> {
        value: &'a [u8],
    }

    assert_eq!(AResult { value: b"H\xffllo" }.render().unwrap(), "unknown");
    assert_eq!(AResult { value: b"Hello" }.render().unwrap(), "Hello");
}

#[test]
fn test_assigned_or_expr_with_unwrap() {
    // In this test the filter |assigned_or should try to unwrap the outcome of an expression.
    // If the outcome could be unwrapped, then the value is rendered.
    // Otherwise the default value "unknown" is rendered.

    #[derive(Template)]
    #[template(
        source = r#"{{ NonZeroU32::new(*value) | assigned_or("unknown") }}"#,
        ext = "html"
    )]
    struct AnOption {
        value: u32,
    }

    assert_eq!(AnOption { value: 0 }.render().unwrap(), "unknown");
    assert_eq!(AnOption { value: 42 }.render().unwrap(), "42");

    #[derive(Template)]
    #[template(
        source = r#"{{ std::str::from_utf8(value) | assigned_or("unknown") }}"#,
        ext = "html"
    )]
    struct AResult<'a> {
        value: &'a [u8],
    }

    assert_eq!(AResult { value: b"H\xffllo" }.render().unwrap(), "unknown");
    assert_eq!(AResult { value: b"Hello" }.render().unwrap(), "Hello");
}

#[test]
fn test_default_with_int() {
    // In this test a default value should be returned for an integer value 0.

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct U8 {
        value: Arc<Pin<Box<u8>>>,
    }

    assert_eq!(
        U8 {
            value: Arc::new(Box::pin(0))
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        U8 {
            value: Arc::new(Box::pin(42))
        }
        .render()
        .unwrap(),
        "42"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct WrappingU8 {
        value: Arc<Pin<Box<Wrapping<u8>>>>,
    }

    assert_eq!(
        WrappingU8 {
            value: Arc::new(Box::pin(Wrapping(0)))
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        WrappingU8 {
            value: Arc::new(Box::pin(Wrapping(42)))
        }
        .render()
        .unwrap(),
        "42"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct SaturatingU8 {
        value: Arc<Pin<Box<Saturating<u8>>>>,
    }

    assert_eq!(
        SaturatingU8 {
            value: Arc::new(Box::pin(Saturating(0)))
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        SaturatingU8 {
            value: Arc::new(Box::pin(Saturating(42)))
        }
        .render()
        .unwrap(),
        "42"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct NzU32 {
        value: NonZeroU32,
    }

    assert_eq!(
        NzU32 {
            value: NonZeroU32::new(42).unwrap()
        }
        .render()
        .unwrap(),
        "42"
    );
}

#[test]
fn test_assigned_or_with_int() {
    // In this test a default value should be returned for an integer value 0.

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct U8 {
        value: Arc<Pin<Box<u8>>>,
    }

    assert_eq!(
        U8 {
            value: Arc::new(Box::pin(0))
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        U8 {
            value: Arc::new(Box::pin(42))
        }
        .render()
        .unwrap(),
        "42"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct WrappingU8 {
        value: Arc<Pin<Box<Wrapping<u8>>>>,
    }

    assert_eq!(
        WrappingU8 {
            value: Arc::new(Box::pin(Wrapping(0)))
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        WrappingU8 {
            value: Arc::new(Box::pin(Wrapping(42)))
        }
        .render()
        .unwrap(),
        "42"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct SaturatingU8 {
        value: Arc<Pin<Box<Saturating<u8>>>>,
    }

    assert_eq!(
        SaturatingU8 {
            value: Arc::new(Box::pin(Saturating(0)))
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        SaturatingU8 {
            value: Arc::new(Box::pin(Saturating(42)))
        }
        .render()
        .unwrap(),
        "42"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct NzU32 {
        value: NonZeroU32,
    }

    assert_eq!(
        NzU32 {
            value: NonZeroU32::new(42).unwrap()
        }
        .render()
        .unwrap(),
        "42"
    );
}

#[test]
fn test_default_with_str() {
    // In this test a default value should be returned for an empty string.

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct Str<'a> {
        value: &'a str,
    }

    assert_eq!(Str { value: "" }.render().unwrap(), "unknown");
    assert_eq!(Str { value: "Hello" }.render().unwrap(), "Hello");

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct AString {
        value: String,
    }

    assert_eq!(
        AString {
            value: "".to_owned()
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        AString {
            value: "Hello".to_owned()
        }
        .render()
        .unwrap(),
        "Hello"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct ACow<'a> {
        value: Cow<'a, str>,
    }

    assert_eq!(ACow { value: "".into() }.render().unwrap(), "unknown");
    assert_eq!(
        ACow {
            value: "Hello".into()
        }
        .render()
        .unwrap(),
        "Hello"
    );
}

#[test]
fn test_assigned_or_with_str() {
    // In this test a default value should be returned for an empty string.

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct Str<'a> {
        value: &'a str,
    }

    assert_eq!(Str { value: "" }.render().unwrap(), "unknown");
    assert_eq!(Str { value: "Hello" }.render().unwrap(), "Hello");

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct AString {
        value: String,
    }

    assert_eq!(
        AString {
            value: "".to_owned()
        }
        .render()
        .unwrap(),
        "unknown"
    );
    assert_eq!(
        AString {
            value: "Hello".to_owned()
        }
        .render()
        .unwrap(),
        "Hello"
    );

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct ACow<'a> {
        value: Cow<'a, str>,
    }

    assert_eq!(ACow { value: "".into() }.render().unwrap(), "unknown");
    assert_eq!(
        ACow {
            value: "Hello".into()
        }
        .render()
        .unwrap(),
        "Hello"
    );
}

#[test]
fn test_default_with_bool() {
    // In this test a default value should be returned for `false`.

    #[derive(Template)]
    #[template(source = r#"{{ value | default("unknown", true) }}"#, ext = "html")]
    struct Bool {
        value: bool,
    }

    assert_eq!(Bool { value: false }.render().unwrap(), "unknown");
    assert_eq!(Bool { value: true }.render().unwrap(), "true");
}

#[test]
fn test_assigned_or_with_bool() {
    // In this test a default value should be returned for `false`.

    #[derive(Template)]
    #[template(source = r#"{{ value | assigned_or("unknown") }}"#, ext = "html")]
    struct Bool {
        value: bool,
    }

    assert_eq!(Bool { value: false }.render().unwrap(), "unknown");
    assert_eq!(Bool { value: true }.render().unwrap(), "true");
}

#[test]
fn test_default_with_forward_declaration() {
    // In this test, it is ensured that a forward declared variable gets replaced with a
    // default value.

    #[derive(Template)]
    #[template(
        source = "\
        {% decl var %}\
        {{ var | default(\"unknown\") }}\
        {% if true %}{% let var = 42 %}{% endif %}",
        ext = "html"
    )]
    struct Fwd;

    assert_eq!(Fwd.render().unwrap(), "unknown");

    #[derive(Template)]
    #[template(
        source = "\
        {% decl var %}{# shadowing happens here #}\
        {{ var | default(\"unknown\") }}\
        {% if true %}{% let var = 42 %}{% endif %}",
        ext = "html"
    )]
    struct Fwd2 {
        #[allow(dead_code)]
        var: u32,
    }

    assert_eq!(Fwd2 { var: 42 }.render().unwrap(), "unknown");
}

#[test]
fn test_defined_or_with_forward_declaration() {
    // In this test, it is ensured that a forward declared variable gets replaced with a
    // default value.

    #[derive(Template)]
    #[template(
        source = "\
        {% decl var %}\
        {{ var | defined_or(\"unknown\") }}\
        {% if true %}{% let var = 42 %}{% endif %}",
        ext = "html"
    )]
    struct Fwd;

    assert_eq!(Fwd.render().unwrap(), "unknown");

    #[derive(Template)]
    #[template(
        source = "\
        {% decl var %}{# shadowing happens here #}\
        {{ var | defined_or(\"unknown\") }}\
        {% if true %}{% let var = 42 %}{% endif %}",
        ext = "html"
    )]
    struct Fwd2 {
        #[allow(dead_code)]
        var: u32,
    }

    assert_eq!(Fwd2 { var: 42 }.render().unwrap(), "unknown");
}
