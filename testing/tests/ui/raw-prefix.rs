// Regression test for <https://github.com/askama-rs/askama/issues/478>.

use askama::Template;

// Cstring literals must not contain NULs.

#[derive(Template)]
#[template(
    source = "{{ z!(cr#\"\0\"#) }}",
    ext = "txt"
)]
struct MacroCallRawCstring1;

#[derive(Template)]
#[template(
    source = "{{ z!(cr##\"\0\"##) }}",
    ext = "txt"
)]
struct MacroCallRawCstring2;

#[derive(Template)]
#[template(
    source = "{{ z!(cr###\"\0\"###) }}",
    ext = "txt"
)]
struct MacroCallRawCstring3;

// Binary string literals must not contain NULs.

#[derive(Template)]
#[template(
    source = "{{ z!(br#\"😶‍🌫️\"#) }}",
    ext = "txt"
)]
struct MacroCallRawBinaryString1;

#[derive(Template)]
#[template(
    source = "{{ z!(br##\"😶‍🌫️\"##) }}",
    ext = "txt"
)]
struct MacroCallRawBinaryString2;

#[derive(Template)]
#[template(
    source = "{{ z!(br###\"😶‍🌫️\"###) }}",
    ext = "txt"
)]
struct MacroCallRawBinaryString3;

// Only `r#` is allowed as prefix identifiers.

#[derive(Template)]
#[template(
    source = "{{ z!(br#async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix1;

#[derive(Template)]
#[template(
    source = "{{ z!(cr#async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix2;

#[derive(Template)]
#[template(
    source = "{{ z!(r##async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix3;

#[derive(Template)]
#[template(
    source = "{{ z!(br##async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix4;

#[derive(Template)]
#[template(
    source = "{{ z!(cr##async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix5;

#[derive(Template)]
#[template(
    source = "{{ z!(hello#world) }}",
    ext = "txt"
)]
struct MacroCallReservedPrefix1;

#[derive(Template)]
#[template(
    source = "{{ z!(hello##world) }}",
    ext = "txt"
)]
struct MacroCallReservedPrefix2;

// No more than 255 hashes

#[derive(Template)]
#[template(path = "macro-call-raw-string-many-hashes.html")]
struct MacroCallManyHashes;

// Need a space between (guarded) string literal and next prefixed string literal.
// Regression test for <https://issues.oss-fuzz.com/issues/426509683>.

#[derive(Template)]
#[template(source = r##"{{ z!(r""r#""#) }}"##, ext = "txt")]
struct UnseparatedPrefixedStrings1;

#[derive(Template)]
#[template(source = r##"{{ z!(r#""#x#"") }}"##, ext = "txt")]
struct UnseparatedPrefixedStrings2;

#[derive(Template)]
#[template(source = r##"{{ z!(c""r#""#) }}"##, ext = "txt")]
struct UnseparatedPrefixedStrings3;

// `r#self`, `r#Self`, `r#crate` and `r#super` are not valid raw identifiers:
// <https://doc.rust-lang.org/reference/identifiers.html>.
// Regression test for <https://issues.oss-fuzz.com/issues/435218013>.

#[derive(Template)]
#[template(
    source = "{{ z!(r#crate) }}",
    ext = "txt"
)]
struct RawIdentifierCrate;

#[derive(Template)]
#[template(
    source = "{{ z!(r#self) }}",
    ext = "txt"
)]
struct RawIdentifierSelf;

#[derive(Template)]
#[template(
    source = "{{ z!(r#Self) }}",
    ext = "txt"
)]
struct RawIdentifierSelfTy;

#[derive(Template)]
#[template(
    source = "{{ z!(r#super) }}",
    ext = "txt"
)]
struct RawIdentifierSuper;

#[derive(Template)]
#[template(
    source = "{{ z!(r##crate) }}",
    ext = "txt"
)]
struct RawIdentifierCrateTooManyHashes;

#[derive(Template)]
#[template(
    source = "{{ z!(r##self) }}",
    ext = "txt"
)]
struct RawIdentifierSelfTooManyHashes;

#[derive(Template)]
#[template(
    source = "{{ z!(r##Self) }}",
    ext = "txt"
)]
struct RawIdentifierSelfTyTooManyHashes;

#[derive(Template)]
#[template(
    source = "{{ z!(r##super) }}",
    ext = "txt"
)]
struct RawIdentifierSuperTooManyHashes;

fn main() {}
