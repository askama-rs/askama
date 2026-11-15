use alloc::str;
use alloc::string::String;
use core::convert::Infallible;
use core::fmt::{self, Write};

use crate::{FastWritable, Result};

/// Return an ephemeral `&str` for `$src: impl fmt::Display`
///
/// If `$str` is `&str` or `String`, this macro simply passes on its content.
/// If it is neither, then the formatted data is collection into `&buffer`.
///
/// `return`s with an error if the formatting failed.
macro_rules! try_to_str {
    ($src:expr => $buffer:ident) => {
        match format_args!("{}", $src) {
            args => {
                if let Some(s) = args.as_str() {
                    s
                } else {
                    $buffer = String::new();
                    $buffer.write_fmt(args)?;
                    &$buffer
                }
            }
        }
    };
}

/// Formats arguments according to the specified format
///
/// The *second* argument to this filter must be a string literal (unlike [format] where it's the
/// first). The two arguments are passed through to the `format!()`
/// [macro](https://doc.rust-lang.org/stable/std/macro.format.html) by
/// the Askama code generator, but the order is swapped to support filter
/// composition.
///
/// ```ignore
/// {{ value|fmt("{:?}") }}
/// ```
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ value|fmt("{:?}") }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example {
///     value: (usize, usize),
/// }
///
/// assert_eq!(
///     Example { value: (3, 4) }.to_string(),
///     "<div>(3, 4)</div>"
/// );
/// # }
/// ```
///
/// Compare with [format](./fn.format.html).
pub fn fmt() {}

/// Formats arguments according to the specified format
///
/// The first argument to this filter must be a string literal (as in normal
/// Rust). All arguments are passed through to the `format!()`
/// [macro](https://doc.rust-lang.org/stable/std/macro.format.html) by
/// the Askama code generator.
///
/// ```ignore
/// {{ "{:?}{:?}"|format(value, other_value) }}
/// ```
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ "{:?}"|format(value) }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example {
///     value: (usize, usize),
/// }
///
/// assert_eq!(
///     Example { value: (3, 4) }.to_string(),
///     "<div>(3, 4)</div>"
/// );
/// # }
/// ```
///
/// Compare with [fmt](./fn.fmt.html).
pub fn format() {}

/// Converts to lowercase
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ word|lower }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     word: &'a str,
/// }
///
/// assert_eq!(
///     Example { word: "FOO" }.to_string(),
///     "<div>foo</div>"
/// );
///
/// assert_eq!(
///     Example { word: "FooBar" }.to_string(),
///     "<div>foobar</div>"
/// );
/// # }
/// ```
#[inline]
pub fn lower<S: fmt::Display>(source: S) -> Result<Lower<S>, Infallible> {
    Ok(Lower(source))
}

pub struct Lower<S>(S);

impl<S: fmt::Display> fmt::Display for Lower<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer;
        flush_lower(dest, try_to_str!(self.0 => buffer))
    }
}

impl<S: FastWritable> FastWritable for Lower<S> {
    #[inline]
    fn write_into(
        &self,
        dest: &mut dyn fmt::Write,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        if buffer.is_ascii() {
            buffer.make_ascii_lowercase();
            Ok(dest.write_str(&buffer)?)
        } else {
            Ok(flush_lower(dest, &buffer)?)
        }
    }
}

fn flush_lower(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    dest.write_str(&s.to_lowercase())
}

/// What `flush_capitalize()` does, without a copy of the text. `s` must be ASCII.
fn capitalize_ascii(s: &mut str) {
    s.make_ascii_lowercase();
    if let Some(first) = s.get_mut(..1) {
        first.make_ascii_uppercase();
    }
}

/// What `flush_title()` does, without a copy of every word. `s` must be ASCII.
fn title_ascii(mut s: &mut str) {
    while !s.is_empty() {
        let end = s.find(char::is_whitespace).map_or(s.len(), |pos| pos + 1);
        let word;
        (word, s) = s.split_at_mut(end);
        capitalize_ascii(word);
    }
}

/// Converts to lowercase, alias for the `|lower` filter
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ word|lowercase }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     word: &'a str,
/// }
///
/// assert_eq!(
///     Example { word: "FOO" }.to_string(),
///     "<div>foo</div>"
/// );
///
/// assert_eq!(
///     Example { word: "FooBar" }.to_string(),
///     "<div>foobar</div>"
/// );
/// # }
/// ```
#[inline]
pub fn lowercase<S: fmt::Display>(source: S) -> Result<Lower<S>, Infallible> {
    lower(source)
}

/// Converts to uppercase
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ word|upper }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     word: &'a str,
/// }
///
/// assert_eq!(
///     Example { word: "foo" }.to_string(),
///     "<div>FOO</div>"
/// );
///
/// assert_eq!(
///     Example { word: "FooBar" }.to_string(),
///     "<div>FOOBAR</div>"
/// );
/// # }
/// ```
#[inline]
pub fn upper<S: fmt::Display>(source: S) -> Result<Upper<S>, Infallible> {
    Ok(Upper(source))
}

pub struct Upper<S>(S);

impl<S: fmt::Display> fmt::Display for Upper<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer;
        flush_upper(dest, try_to_str!(self.0 => buffer))
    }
}

impl<S: FastWritable> FastWritable for Upper<S> {
    #[inline]
    fn write_into(
        &self,
        dest: &mut dyn fmt::Write,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        if buffer.is_ascii() {
            buffer.make_ascii_uppercase();
            Ok(dest.write_str(&buffer)?)
        } else {
            Ok(flush_upper(dest, &buffer)?)
        }
    }
}

fn flush_upper(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    dest.write_str(&s.to_uppercase())
}

/// Converts to uppercase, alias for the `|upper` filter
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ word|uppercase }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     word: &'a str,
/// }
///
/// assert_eq!(
///     Example { word: "foo" }.to_string(),
///     "<div>FOO</div>"
/// );
///
/// assert_eq!(
///     Example { word: "FooBar" }.to_string(),
///     "<div>FOOBAR</div>"
/// );
/// # }
/// ```
#[inline]
pub fn uppercase<S: fmt::Display>(source: S) -> Result<Upper<S>, Infallible> {
    upper(source)
}

/// Strip leading and trailing whitespace
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|trim }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: " Hello\tworld\t" }.to_string(),
///     "<div>Hello\tworld</div>"
/// );
/// # }
/// ```
#[inline]
pub fn trim<S: fmt::Display>(source: S) -> Result<Trim<S>, Infallible> {
    Ok(Trim(source))
}

pub struct Trim<S>(S);

impl<S: fmt::Display> fmt::Display for Trim<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(TrimWriter::new(dest), "{}", self.0)
    }
}

impl<S: FastWritable> FastWritable for Trim<S> {
    #[inline]
    fn write_into(
        &self,
        dest: &mut dyn fmt::Write,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        self.0.write_into(&mut TrimWriter::new(dest), values)
    }
}

struct TrimWriter<W> {
    dest: W,
    /// Whether any text was written, so that whitespace is not leading anymore.
    started: bool,
    /// Whitespace that is trailing unless more text follows.
    pending: String,
}

impl<W> TrimWriter<W> {
    fn new(dest: W) -> Self {
        Self {
            dest,
            started: false,
            pending: String::new(),
        }
    }
}

impl<W: fmt::Write> fmt::Write for TrimWriter<W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let s = if self.started { s } else { s.trim_start() };
        let text = s.trim_end();
        if text.is_empty() {
            self.pending.push_str(s);
            return Ok(());
        }
        if !self.pending.is_empty() {
            self.dest.write_str(&self.pending)?;
            self.pending.clear();
        }
        self.started = true;
        self.dest.write_str(text)?;
        self.pending.push_str(&s[text.len()..]);
        Ok(())
    }
}

/// Capitalize a value. The first character will be uppercase, all others lowercase.
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|capitalize }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "hello" }.to_string(),
///     "<div>Hello</div>"
/// );
///
/// assert_eq!(
///     Example { example: "hElLO" }.to_string(),
///     "<div>Hello</div>"
/// );
/// # }
/// ```
#[inline]
pub fn capitalize<S: fmt::Display>(source: S) -> Result<Capitalize<S>, Infallible> {
    Ok(Capitalize(source))
}

pub struct Capitalize<S>(S);

impl<S: fmt::Display> fmt::Display for Capitalize<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer;
        flush_capitalize(dest, try_to_str!(self.0 => buffer))
    }
}

impl<S: FastWritable> FastWritable for Capitalize<S> {
    #[inline]
    fn write_into(
        &self,
        dest: &mut dyn fmt::Write,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        if buffer.is_ascii() {
            capitalize_ascii(&mut buffer);
            Ok(dest.write_str(&buffer)?)
        } else {
            Ok(flush_capitalize(dest, &buffer)?)
        }
    }
}

fn flush_capitalize(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    let mut chars = s.chars();
    if let Some(c) = chars.next() {
        write!(
            dest,
            "{}{}",
            c.to_uppercase(),
            chars.as_str().to_lowercase()
        )
    } else {
        Ok(())
    }
}

/// Return a title cased version of the value. Words will start with uppercase letters, all
/// remaining characters are lowercase.
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|title }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "hello WORLD" }.to_string(),
///     "<div>Hello World</div>"
/// );
/// # }
/// ```
#[inline]
pub fn title<S: fmt::Display>(source: S) -> Result<Title<S>, Infallible> {
    Ok(Title(source))
}

pub struct Title<S>(S);

impl<S: fmt::Display> fmt::Display for Title<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer;
        flush_title(dest, try_to_str!(self.0 => buffer))
    }
}

impl<S: FastWritable> FastWritable for Title<S> {
    #[inline]
    fn write_into(
        &self,
        dest: &mut dyn fmt::Write,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        if buffer.is_ascii() {
            title_ascii(&mut buffer);
            Ok(dest.write_str(&buffer)?)
        } else {
            Ok(flush_title(dest, &buffer)?)
        }
    }
}

fn flush_title(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    for word in s.split_inclusive(char::is_whitespace) {
        flush_capitalize(dest, word)?;
    }
    Ok(())
}

/// Return a title cased version of the value. Alias for the [`|title`](title) filter.
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|titlecase }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "hello WORLD" }.to_string(),
///     "<div>Hello World</div>"
/// );
/// # }
/// ```
#[inline]
pub fn titlecase<S: fmt::Display>(source: S) -> Result<Title<S>, Infallible> {
    title(source)
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;

    #[test]
    fn test_lower() {
        assert_eq!(lower("Foo").unwrap().to_string(), "foo");
        assert_eq!(lower("FOO").unwrap().to_string(), "foo");
        assert_eq!(lower("FooBar").unwrap().to_string(), "foobar");
        assert_eq!(lower("foo").unwrap().to_string(), "foo");
    }

    #[test]
    fn test_upper() {
        assert_eq!(upper("Foo").unwrap().to_string(), "FOO");
        assert_eq!(upper("FOO").unwrap().to_string(), "FOO");
        assert_eq!(upper("FooBar").unwrap().to_string(), "FOOBAR");
        assert_eq!(upper("foo").unwrap().to_string(), "FOO");
    }

    #[test]
    fn test_trim() {
        assert_eq!(trim(" Hello\tworld\t").unwrap().to_string(), "Hello\tworld");
    }

    #[test]
    fn test_capitalize() {
        assert_eq!(capitalize("foo").unwrap().to_string(), "Foo".to_string());
        assert_eq!(capitalize("f").unwrap().to_string(), "F".to_string());
        assert_eq!(capitalize("fO").unwrap().to_string(), "Fo".to_string());
        assert_eq!(capitalize("").unwrap().to_string(), String::new());
        assert_eq!(capitalize("FoO").unwrap().to_string(), "Foo".to_string());
        assert_eq!(
            capitalize("foO BAR").unwrap().to_string(),
            "Foo bar".to_string()
        );
        assert_eq!(
            capitalize("äØÄÅÖ").unwrap().to_string(),
            "Äøäåö".to_string()
        );
        assert_eq!(capitalize("ß").unwrap().to_string(), "SS".to_string());
        assert_eq!(capitalize("ßß").unwrap().to_string(), "SSß".to_string());
    }

    #[test]
    fn test_title() {
        assert_eq!(&title("").unwrap().to_string(), "");
        assert_eq!(&title(" \n\t").unwrap().to_string(), " \n\t");
        assert_eq!(&title("foo").unwrap().to_string(), "Foo");
        assert_eq!(&title(" foo").unwrap().to_string(), " Foo");
        assert_eq!(&title("foo bar").unwrap().to_string(), "Foo Bar");
        assert_eq!(&title("foo  bar ").unwrap().to_string(), "Foo  Bar ");
        assert_eq!(&title("fOO").unwrap().to_string(), "Foo");
        assert_eq!(&title("fOo BaR").unwrap().to_string(), "Foo Bar");
        assert_eq!(&title("foo\r\nbar").unwrap().to_string(), "Foo\r\nBar");
        assert_eq!(
            &title("Fo\x0boo\x0coO\u{2002}OO\u{3000}baR")
                .unwrap()
                .to_string(),
            "Fo\x0bOo\x0cOo\u{2002}Oo\u{3000}Bar"
        );
    }

    fn fast(value: impl FastWritable) -> String {
        let mut dest = String::new();
        value.write_into(&mut dest, crate::NO_VALUES).unwrap();
        dest
    }

    #[test]
    fn test_fast_writable_is_display() {
        const INPUTS: &[&str] = &[
            "",
            "f",
            "F",
            " \n\t",
            " foo BAR ",
            "hElLo wOrLD",
            "foo\x0bbAR\x0cbAZ\tqUX\r\nqUUX  x",
            "fOO\u{2002}bAR\u{3000}bAZ",
            "äØÄÅÖ",
            "ß",
            "ßß straße",
            "İSTANBUL",
            "ﬁne ǆ",
            "ὈΔΥΣΣΕΎΣ ΌΣΟΣ Σ",
        ];

        for &input in INPUTS {
            assert_eq!(fast(lower(input).unwrap()), input.to_lowercase());
            assert_eq!(fast(upper(input).unwrap()), input.to_uppercase());
            assert_eq!(
                fast(capitalize(input).unwrap()),
                capitalize(input).unwrap().to_string(),
            );
            assert_eq!(
                fast(title(input).unwrap()),
                title(input).unwrap().to_string()
            );
            assert_eq!(fast(trim(input).unwrap()), input.trim());
        }

        assert_eq!(fast(capitalize("foO BAR").unwrap()), "Foo bar");
        assert_eq!(
            fast(title("fOo  BaR\x0bbAZ\r\nqux ").unwrap()),
            "Foo  Bar\x0bBaz\r\nQux "
        );
    }

    #[test]
    fn test_trim_chunks() {
        struct Chunks(&'static [&'static str]);

        impl fmt::Display for Chunks {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.iter().try_for_each(|chunk| f.write_str(chunk))
            }
        }

        impl FastWritable for Chunks {
            fn write_into(
                &self,
                dest: &mut dyn fmt::Write,
                _: &dyn crate::Values,
            ) -> crate::Result<()> {
                Ok(self.0.iter().try_for_each(|chunk| dest.write_str(chunk))?)
            }
        }

        const INPUTS: &[&[&str]] = &[
            &[],
            &["", " ", "\n"],
            &[" ", " a ", "  ", "", "b  ", " ", ""],
            &["a", " ", "\n", "b"],
            &["a", " ", "\n"],
            &["\u{3000}a\u{2002}", "\u{2002}b\u{3000}", "\u{2002}"],
        ];

        for &input in INPUTS {
            let expected = input.concat();
            let expected = expected.trim();
            assert_eq!(trim(Chunks(input)).unwrap().to_string(), expected);
            assert_eq!(fast(trim(Chunks(input)).unwrap()), expected);
        }
    }
}
