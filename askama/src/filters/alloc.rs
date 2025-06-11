use alloc::str;
use alloc::string::String;
use core::convert::Infallible;
use core::fmt::{self, Write};

use super::escape::HtmlSafeOutput;
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
/// The *second* argument to this filter must be a string literal (as in normal
/// Rust). The two arguments are passed through to the `format!()`
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

/// Replaces line breaks in plain text with appropriate HTML
///
/// A single newline becomes an HTML line break `<br>` and a new line
/// followed by a blank line becomes a paragraph break `<p>`.
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|linebreaks }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "Foo\nBar\n\nBaz" }.to_string(),
///     "<div><p>Foo<br/>Bar</p><p>Baz</p></div>"
/// );
/// # }
/// ```
#[inline]
pub fn linebreaks<S: fmt::Display>(source: S) -> Result<HtmlSafeOutput<Linebreaks<S>>, Infallible> {
    Ok(HtmlSafeOutput(Linebreaks(source)))
}

pub struct Linebreaks<S>(S);

impl<S: fmt::Display> fmt::Display for Linebreaks<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer;
        flush_linebreaks(dest, try_to_str!(self.0 => buffer))
    }
}

impl<S: FastWritable> FastWritable for Linebreaks<S> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        Ok(flush_linebreaks(dest, &buffer)?)
    }
}

fn flush_linebreaks(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    let linebroken = s.replace("\n\n", "</p><p>").replace('\n', "<br/>");
    write!(dest, "<p>{linebroken}</p>")
}

/// Converts all newlines in a piece of plain text to HTML line breaks
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ lines|linebreaksbr }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     lines: &'a str,
/// }
///
/// assert_eq!(
///     Example { lines: "a\nb\nc" }.to_string(),
///     "<div>a<br/>b<br/>c</div>"
/// );
/// # }
/// ```
#[inline]
pub fn linebreaksbr<S: fmt::Display>(
    source: S,
) -> Result<HtmlSafeOutput<Linebreaksbr<S>>, Infallible> {
    Ok(HtmlSafeOutput(Linebreaksbr(source)))
}

pub struct Linebreaksbr<S>(S);

impl<S: fmt::Display> fmt::Display for Linebreaksbr<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer;
        flush_linebreaksbr(dest, try_to_str!(self.0 => buffer))
    }
}

impl<S: FastWritable> FastWritable for Linebreaksbr<S> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        Ok(flush_linebreaksbr(dest, &buffer)?)
    }
}

fn flush_linebreaksbr(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    dest.write_str(&s.replace('\n', "<br/>"))
}

/// Replaces only paragraph breaks in plain text with appropriate HTML
///
/// A new line followed by a blank line becomes a paragraph break `<p>`.
/// Paragraph tags only wrap content; empty paragraphs are removed.
/// No `<br/>` tags are added.
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// {{ lines|paragraphbreaks }}
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     lines: &'a str,
/// }
///
/// assert_eq!(
///     Example { lines: "Foo\nBar\n\nBaz" }.to_string(),
///     "<p>Foo\nBar</p><p>Baz</p>"
/// );
/// # }
/// ```
#[inline]
pub fn paragraphbreaks<S: fmt::Display>(
    source: S,
) -> Result<HtmlSafeOutput<Paragraphbreaks<S>>, Infallible> {
    Ok(HtmlSafeOutput(Paragraphbreaks(source)))
}

pub struct Paragraphbreaks<S>(S);

impl<S: fmt::Display> fmt::Display for Paragraphbreaks<S> {
    #[inline]
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer;
        flush_paragraphbreaks(dest, try_to_str!(self.0 => buffer))
    }
}

impl<S: FastWritable> FastWritable for Paragraphbreaks<S> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        Ok(flush_paragraphbreaks(dest, &buffer)?)
    }
}

fn flush_paragraphbreaks(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    let linebroken = s.replace("\n\n", "</p><p>").replace("<p></p>", "");
    write!(dest, "<p>{linebroken}</p>")
}

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
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        Ok(flush_lower(dest, &buffer)?)
    }
}

fn flush_lower(dest: &mut (impl fmt::Write + ?Sized), s: &str) -> fmt::Result {
    dest.write_str(&s.to_lowercase())
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
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        Ok(flush_upper(dest, &buffer)?)
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
        let mut collector = TrimCollector(String::new());
        write!(collector, "{}", self.0)?;
        flush_trim(dest, collector)
    }
}

impl<S: FastWritable> FastWritable for Trim<S> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut collector = TrimCollector(String::new());
        self.0.write_into(&mut collector, values)?;
        Ok(flush_trim(dest, collector)?)
    }
}

struct TrimCollector(String);

impl fmt::Write for TrimCollector {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self.0.is_empty() {
            true => self.0.write_str(s.trim_start()),
            false => self.0.write_str(s),
        }
    }
}

fn flush_trim(dest: &mut (impl fmt::Write + ?Sized), collector: TrimCollector) -> fmt::Result {
    dest.write_str(collector.0.trim_end())
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
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        Ok(flush_capitalize(dest, &buffer)?)
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
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut buffer = String::new();
        self.0.write_into(&mut buffer, values)?;
        Ok(flush_title(dest, &buffer)?)
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
    fn test_linebreaks() {
        assert_eq!(
            linebreaks("Foo\nBar Baz").unwrap().to_string(),
            "<p>Foo<br/>Bar Baz</p>"
        );
        assert_eq!(
            linebreaks("Foo\nBar\n\nBaz").unwrap().to_string(),
            "<p>Foo<br/>Bar</p><p>Baz</p>"
        );
    }

    #[test]
    fn test_linebreaksbr() {
        assert_eq!(linebreaksbr("Foo\nBar").unwrap().to_string(), "Foo<br/>Bar");
        assert_eq!(
            linebreaksbr("Foo\nBar\n\nBaz").unwrap().to_string(),
            "Foo<br/>Bar<br/><br/>Baz"
        );
    }

    #[test]
    fn test_paragraphbreaks() {
        assert_eq!(
            paragraphbreaks("Foo\nBar Baz").unwrap().to_string(),
            "<p>Foo\nBar Baz</p>"
        );
        assert_eq!(
            paragraphbreaks("Foo\nBar\n\nBaz").unwrap().to_string(),
            "<p>Foo\nBar</p><p>Baz</p>"
        );
        assert_eq!(
            paragraphbreaks("Foo\n\n\n\n\nBar\n\nBaz")
                .unwrap()
                .to_string(),
            "<p>Foo</p><p>\nBar</p><p>Baz</p>"
        );
    }

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
}
