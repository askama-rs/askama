#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(not(docsrs), no_std)]
#![deny(elided_lifetimes_in_paths)]
#![deny(unreachable_pub)]
#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

use core::fmt;

mod ascii_str;
mod html;

/// Escape for HTML or XML.
#[derive(Debug, Clone, Copy, Default)]
pub struct Html;

/// Escape for plain text, i.e. pass through unchanged.
#[derive(Debug, Clone, Copy, Default)]
pub struct Text;

/// An escaper for some context, e.g. [`Html`].
pub trait Escaper {
    /// Escaped the input string `string` into `dest`
    fn write_escaped<W: fmt::Write>(&self, dest: W, string: &str) -> fmt::Result;
}

impl Escaper for Html {
    #[inline]
    fn write_escaped<W: fmt::Write>(&self, dest: W, string: &str) -> fmt::Result {
        html::write_escaped_str(dest, string)
    }
}

impl Escaper for Text {
    #[inline]
    fn write_escaped<W: fmt::Write>(&self, mut dest: W, string: &str) -> fmt::Result {
        dest.write_str(string)
    }
}

/// The return type of [`escape()`].
///
/// ## Example
///
/// ```rust
/// use askama_escape::{escape, Escaped, Html};
///
/// let escaped: Escaped<'_, _> = escape("<script>alert('Hello & bye!')</script>", Html);
/// assert_eq!(
///     escaped.to_string(),
///     "&#60;script&#62;alert(&#39;Hello &#38; bye!&#39;)&#60;/script&#62;",
/// );
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Escaped<'a, E: Escaper> {
    string: &'a str,
    escaper: E,
}

impl<E: Escaper> fmt::Display for Escaped<'_, E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.escaper.write_escaped(f, self.string)
    }
}

/// Safely wrap a `string` with some [`escaper`][Escaper] e.g. for the use in [`Html`].
///
/// ## Example
///
/// ```rust
/// use askama_escape::{escape, Html};
///
/// assert_eq!(
///     escape("<script>alert('Hello & bye!')</script>", Html).to_string(),
///     "&#60;script&#62;alert(&#39;Hello &#38; bye!&#39;)&#60;/script&#62;",
/// );
/// ```
#[inline]
pub fn escape<E: Escaper>(string: &str, escaper: E) -> Escaped<'_, E> {
    Escaped { string, escaper }
}

/// HTML/XML escape a string `str` into `dest`.
///
/// ## Example
///
/// ```rust
/// use askama_escape::escape_html;
///
/// let mut dest = String::new();
/// escape_html(&mut dest, "<script>alert('Hello & bye!')</script>").unwrap();
/// assert_eq!(
///     dest,
///     "&#60;script&#62;alert(&#39;Hello &#38; bye!&#39;)&#60;/script&#62;",
/// );
/// ```
#[inline]
pub fn escape_html(dest: impl fmt::Write, src: &str) -> fmt::Result {
    html::write_escaped_str(dest, src)
}

/// HTML/XML escape a character `c` into `dest`.
///
/// ## Example
///
/// ```rust
/// use askama_escape::escape_html_char;
///
/// let mut dest = String::new();
/// escape_html_char(&mut dest, '&').unwrap();
/// assert_eq!(dest, "&#38;");
/// ```
pub fn escape_html_char(dest: impl fmt::Write, c: char) -> fmt::Result {
    html::write_escaped_char(dest, c)
}

#[cfg(test)]
mod tests {
    extern crate std;

    use std::string::ToString;

    use super::*;

    #[test]
    fn test_escape() {
        assert_eq!(escape("", Html).to_string(), "");
        assert_eq!(escape("<&>", Html).to_string(), "&#60;&#38;&#62;");
        assert_eq!(escape("bla&", Html).to_string(), "bla&#38;");
        assert_eq!(escape("<foo", Html).to_string(), "&#60;foo");
        assert_eq!(escape("bla&h", Html).to_string(), "bla&#38;h");
    }
}
