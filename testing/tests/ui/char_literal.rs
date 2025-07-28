use askama::Template;

#[derive(Template)]
#[template(path = "char-literals/char-literal-1.txt")]
struct Err1;

#[derive(Template)]
#[template(path = "char-literals/char-literal-2.txt")]
struct Err2;

#[derive(Template)]
#[template(path = "char-literals/char-literal-3.txt")]
struct Err3;

#[derive(Template)]
#[template(path = "char-literals/char-literal-4.txt")]
struct Err4;

#[derive(Template)]
#[template(path = "char-literals/char-literal-5.txt")]
struct Err5;

#[derive(Template)]
#[template(path = "char-literals/char-literal-6.txt")]
struct Err6;

#[derive(Template)]
#[template(path = "char-literals/char-literal-7.txt")]
struct Err7;

#[derive(Template)]
#[template(source = "{% let s = 'aaa' %}", ext = "html")]
struct Err8;

#[derive(Template)]
#[template(source = r#"{{ b'c }}"#, ext = "html")]
struct UnterminatedByteLiteral;

#[derive(Template)]
#[template(source = r#"{{ b'' }}"#, ext = "html")]
struct EmptyByteLiteral;

#[derive(Template)]
#[template(source = r#"{{ b'\u{}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralEmpty;

#[derive(Template)]
#[template(source = r#"{{ b'\u{0}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMinAscii;

#[derive(Template)]
#[template(source = r#"{{ b'\u{42}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralRandomAscii;

#[derive(Template)]
#[template(source = r#"{{ b'\u{7f}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMaxAscii;

#[derive(Template)]
#[template(source = r#"{{ b'\u{80}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMinMultilingual;

#[derive(Template)]
#[template(source = r#"{{ b'\u{1234}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralRandomMultilingual;

#[derive(Template)]
#[template(source = r#"{{ b'\u{10ffff}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMaxMultilingual;

#[derive(Template)]
#[template(source = r#"{{ a!(b'c) }}"#, ext = "html")]
struct UnterminatedByteLiteralInMacro;

#[derive(Template)]
#[template(source = r#"{{ b'' }}"#, ext = "html")]
struct EmptyByteLiteralInMacro;

#[derive(Template)]
#[template(source = r#"{{ b'\u{}' }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralEmptyInMacro;

#[derive(Template)]
#[template(source = r#"{{ a!(b'\u{0}') }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMinAsciiInMacro;

#[derive(Template)]
#[template(source = r#"{{ a!(b'\u{42}') }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralRandomAsciiInMacro;

#[derive(Template)]
#[template(source = r#"{{ a!(b'\u{7f}') }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMaxAsciiInMacro;

#[derive(Template)]
#[template(source = r#"{{ a!(b'\u{80}') }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMinMultilingualInMacro;

#[derive(Template)]
#[template(source = r#"{{ a!(b'\u{1234}') }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralRandomMultilingualInMacro;

#[derive(Template)]
#[template(source = r#"{{ a!(b'\u{10ffff}') }}"#, ext = "html")]
struct UnicodeEscapeInByteLiteralMaxMultilingualInMacro;

fn main() {
}
