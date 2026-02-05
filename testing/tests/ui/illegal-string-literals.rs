use askama::Template;

// Strings must be closed

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello world }}"#)]
struct Unclosed1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello world\" }}"#)]
struct Unclosed2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ b"hello world }}"#)]
struct Unclosed3;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ b"hello world\" }}"#)]
struct Unclosed4;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ c"hello world }}"#)]
struct Unclosed5;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ c"hello world\" }}"#)]
struct Unclosed6;

// Unprefix string literals must not contain hex escapes sequences higher than `\x7f`

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \x80 world" }}"#)]
struct HighAscii1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \xff world" }}"#)]
struct HighAscii2;

// Cstring literals must not contain null characters

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \0 world" }}"#)]
struct NulEscapeSequence1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \x00 world" }}"#)]
struct NulEscapeSequence2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \u{0} world" }}"#)]
struct NulEscapeSequence3;

#[derive(Template)]
#[template(ext = "txt", source = "{{ \"hello \0 world\" }}")]
struct NulCharacter;

// Binary slice literals must not contain non-ASCII characters

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello 😉 world" }}"#)]
struct UnicodeCharacter;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \u{128521} world" }}"#)]
struct UnicodeEscapeSequence;

// Surrogate characters (even if paired) are not allowed at all

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \u{d83d}\u{de09} world" }}"#)]
struct SurrogatePaired1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \u{d83d} world" }}"#)]
struct SurrogateLow1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ "hello \u{de09} world" }}"#)]
struct SurrogateHigh1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ b"hello \u{d83d}\u{de09} world" }}"#)]
struct SurrogatePaired2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ b"hello \u{d83d} world" }}"#)]
struct SurrogateLow2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ b"hello \u{de09} world" }}"#)]
struct SurrogateHigh2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ c"hello \u{d83d}\u{de09} world" }}"#)]
struct SurrogatePaired3;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ c"hello \u{d83d} world" }}"#)]
struct SurrogateLow3;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ c"hello \u{de09} world" }}"#)]
struct SurrogateHigh3;

// CR (\r) is only allowed if followed by NL (\n)
// (regression test for <https://github.com/askama-rs/askama/issues/482>)

#[derive(Template)]
#[template(ext = "txt", source = "{{ \"hello \r world\" }}")]
struct UnpairedCr;

#[derive(Template)]
#[template(ext = "txt", source = "{{ b\"hello \r world\" }}")]
struct UnpairedCrInBytes;

#[derive(Template)]
#[template(ext = "txt", source = "{{ c\"hello \r world\" }}")]
struct UnpairedCrInCstring;

#[derive(Template)]
#[template(ext = "txt", source = "{{ b'ä' }}")]
struct MbByteLiteral;

#[derive(Template)]
#[template(ext = "txt", source = "{{ x!(b'ä') }}")]
struct MbByteLiteralInMacro;

fn main() {}
