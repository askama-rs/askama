use core::convert::Infallible;
use core::fmt::{self, Write};
use core::ops::Deref;
use core::pin::Pin;
use core::str;

use crate::FastWritable;

/// Indent lines with spaces or a prefix.
///
/// The first line and blank lines are not indented by default.
/// The filter has two optional [`bool`] arguments, `first` and `blank`, that can be set to `true`
/// to indent the first and blank lines, resp.
///
/// ### Example of `indent` with spaces
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|indent(4) }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "hello\nfoo\nbar" }.to_string(),
///     "<div>hello\n    foo\n    bar</div>"
/// );
/// # }
/// ```
///
/// ### Example of `indent` with prefix a custom prefix
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|indent("$$$ ") }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "hello\nfoo\nbar" }.to_string(),
///     "<div>hello\n$$$ foo\n$$$ bar</div>"
/// );
/// # }
/// ```
#[inline]
pub fn indent<S, I: AsIndent>(
    source: S,
    indent: I,
    first: bool,
    blank: bool,
) -> Result<Indent<S, I>, Infallible> {
    Ok(Indent {
        source,
        indent,
        first,
        blank,
    })
}

pub struct Indent<S, I> {
    source: S,
    indent: I,
    first: bool,
    blank: bool,
}

impl<S: fmt::Display, I: AsIndent> fmt::Display for Indent<S, I> {
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        let indent = self.indent.as_indent();
        write!(
            IndentWriter::new(dest, indent, self.first, self.blank),
            "{}",
            self.source
        )?;
        Ok(())
    }
}

impl<S: FastWritable, I: AsIndent> FastWritable for Indent<S, I> {
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let indent = self.indent.as_indent();
        self.source.write_into(
            &mut IndentWriter::new(dest, indent, self.first, self.blank),
            values,
        )?;
        Ok(())
    }
}

struct IndentWriter<'a, W> {
    dest: W,
    indent: &'a str,
    first: bool,
    blank: bool,
    is_new_line: bool,
    is_first_line: bool,
}

impl<'a, W: fmt::Write> IndentWriter<'a, W> {
    fn new(dest: W, indent: &'a str, first: bool, blank: bool) -> Self {
        IndentWriter {
            dest,
            indent,
            first,
            blank,
            is_new_line: true,
            is_first_line: true,
        }
    }
}

impl<W: fmt::Write> fmt::Write for IndentWriter<'_, W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if self.indent.is_empty() {
            return self.dest.write_str(s);
        }

        for line in s.split_inclusive('\n') {
            if self.is_new_line {
                if self.is_first_line {
                    if self.first && (self.blank || !matches!(line, "\n" | "\r\n")) {
                        self.dest.write_str(self.indent)?;
                    }
                    self.is_first_line = false;
                } else if self.blank || !matches!(line, "\n" | "\r\n") {
                    self.dest.write_str(self.indent)?;
                }
            }
            self.dest.write_str(line)?;
            self.is_new_line = line.ends_with('\n');
        }
        Ok(())
    }
}

/// A prefix usable for indenting
#[cfg_attr(
    feature = "serde_json",
    doc = "[prettified JSON data](super::json_pretty) and"
)]
/// [`|indent`](indent).
///
/// ```
/// # use askama::filters::AsIndent;
/// assert_eq!(4.as_indent(), "    ");
/// assert_eq!(" -> ".as_indent(), " -> ");
/// ```
pub trait AsIndent {
    /// Borrow `self` as prefix to use.
    fn as_indent(&self) -> &str;
}

impl AsIndent for str {
    #[inline]
    fn as_indent(&self) -> &str {
        self
    }
}

#[cfg(feature = "alloc")]
impl AsIndent for alloc::string::String {
    #[inline]
    fn as_indent(&self) -> &str {
        self
    }
}

impl AsIndent for usize {
    #[inline]
    fn as_indent(&self) -> &str {
        spaces(*self)
    }
}

impl AsIndent for core::num::Wrapping<usize> {
    #[inline]
    fn as_indent(&self) -> &str {
        spaces(self.0)
    }
}

impl AsIndent for core::num::NonZeroUsize {
    #[inline]
    fn as_indent(&self) -> &str {
        spaces(self.get())
    }
}

fn spaces(width: usize) -> &'static str {
    const MAX_SPACES: usize = 16;
    const SPACES: &str = match str::from_utf8(&[b' '; MAX_SPACES]) {
        Ok(spaces) => spaces,
        Err(_) => panic!(),
    };

    &SPACES[..width.min(SPACES.len())]
}

#[cfg(feature = "alloc")]
impl<T: AsIndent + alloc::borrow::ToOwned + ?Sized> AsIndent for alloc::borrow::Cow<'_, T> {
    #[inline]
    fn as_indent(&self) -> &str {
        T::as_indent(self)
    }
}

crate::impl_for_ref! {
    impl AsIndent for T {
        #[inline]
        fn as_indent(&self) -> &str {
            <T>::as_indent(self)
        }
    }
}

impl<T> AsIndent for Pin<T>
where
    T: Deref,
    <T as Deref>::Target: AsIndent,
{
    #[inline]
    fn as_indent(&self) -> &str {
        self.as_ref().get_ref().as_indent()
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;

    #[test]
    fn test_indent() {
        assert_eq!(
            indent("hello", 2, false, false).unwrap().to_string(),
            "hello"
        );
        assert_eq!(
            indent("hello\n", 2, false, false).unwrap().to_string(),
            "hello\n"
        );
        assert_eq!(
            indent("hello\nfoo", 2, false, false).unwrap().to_string(),
            "hello\n  foo"
        );
        assert_eq!(
            indent("hello\nfoo\n bar", 4, false, false)
                .unwrap()
                .to_string(),
            "hello\n    foo\n     bar"
        );
        assert_eq!(
            indent("hello", 267_332_238_858, false, false)
                .unwrap()
                .to_string(),
            "hello"
        );

        assert_eq!(
            indent("hello\n\n bar", 4, false, false)
                .unwrap()
                .to_string(),
            "hello\n\n     bar"
        );
        assert_eq!(
            indent("hello\n\n bar", 4, false, true).unwrap().to_string(),
            "hello\n    \n     bar"
        );
        assert_eq!(
            indent("hello\n\n bar", 4, true, false).unwrap().to_string(),
            "    hello\n\n     bar"
        );
        assert_eq!(
            indent("hello\n\n bar", 4, true, true).unwrap().to_string(),
            "    hello\n    \n     bar"
        );
    }

    #[test]
    fn test_indent_str() {
        assert_eq!(
            indent("hello\n\n bar", "❗❓", false, false)
                .unwrap()
                .to_string(),
            "hello\n\n❗❓ bar"
        );
        assert_eq!(
            indent("hello\n\n bar", "❗❓", false, true)
                .unwrap()
                .to_string(),
            "hello\n❗❓\n❗❓ bar"
        );
        assert_eq!(
            indent("hello\n\n bar", "❗❓", true, false)
                .unwrap()
                .to_string(),
            "❗❓hello\n\n❗❓ bar"
        );
        assert_eq!(
            indent("hello\n\n bar", "❗❓", true, true)
                .unwrap()
                .to_string(),
            "❗❓hello\n❗❓\n❗❓ bar"
        );
    }

    #[test]
    fn test_indent_chunked() {
        #[derive(Clone, Copy)]
        struct Chunked<'a>(&'a str);

        impl<'a> fmt::Display for Chunked<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                for chunk in self.0.chars() {
                    write!(f, "{chunk}")?;
                }
                Ok(())
            }
        }

        assert_eq!(
            indent(Chunked("hello"), 2, false, false)
                .unwrap()
                .to_string(),
            "hello"
        );
        assert_eq!(
            indent(Chunked("hello\n"), 2, false, false)
                .unwrap()
                .to_string(),
            "hello\n"
        );
        assert_eq!(
            indent(Chunked("hello\nfoo"), 2, false, false)
                .unwrap()
                .to_string(),
            "hello\n  foo"
        );
        assert_eq!(
            indent(Chunked("hello\nfoo\n bar"), 4, false, false)
                .unwrap()
                .to_string(),
            "hello\n    foo\n     bar"
        );
        assert_eq!(
            indent(Chunked("hello"), 267_332_238_858, false, false)
                .unwrap()
                .to_string(),
            "hello"
        );

        assert_eq!(
            indent(Chunked("hello\n\n bar"), 4, false, false)
                .unwrap()
                .to_string(),
            "hello\n\n     bar"
        );
        assert_eq!(
            indent(Chunked("hello\n\n bar"), 4, false, true)
                .unwrap()
                .to_string(),
            "hello\n    \n     bar"
        );
        assert_eq!(
            indent(Chunked("hello\n\n bar"), 4, true, false)
                .unwrap()
                .to_string(),
            "    hello\n\n     bar"
        );
        assert_eq!(
            indent(Chunked("hello\n\n bar"), 4, true, true)
                .unwrap()
                .to_string(),
            "    hello\n    \n     bar"
        );
    }

    #[test]
    #[allow(clippy::arc_with_non_send_sync)] // it's only a test, it does not have to make sense
    #[allow(clippy::type_complexity)] // it's only a test, it does not have to be pretty
    fn test_indent_complicated() {
        use std::borrow::ToOwned;
        use std::boxed::Box;
        use std::cell::{RefCell, RefMut};
        use std::pin::Pin;
        use std::rc::Rc;
        use std::string::String;
        use std::sync::{Arc, Mutex, MutexGuard, RwLock, RwLockWriteGuard};

        let prefix = Mutex::new(Box::pin("❗❓".to_owned()));
        let prefix = RefCell::new(Arc::new(prefix.try_lock().unwrap()));
        let prefix = RwLock::new(Rc::new(prefix.borrow_mut()));
        let prefix: RwLockWriteGuard<'_, Rc<RefMut<'_, Arc<MutexGuard<'_, Pin<Box<String>>>>>>> =
            prefix.try_write().unwrap();

        assert_eq!(
            indent("hello\n\n bar", &prefix, false, false)
                .unwrap()
                .to_string(),
            "hello\n\n❗❓ bar"
        );
        assert_eq!(
            indent("hello\n\n bar", &prefix, false, true)
                .unwrap()
                .to_string(),
            "hello\n❗❓\n❗❓ bar"
        );
        assert_eq!(
            indent("hello\n\n bar", &prefix, true, false)
                .unwrap()
                .to_string(),
            "❗❓hello\n\n❗❓ bar"
        );
        assert_eq!(
            indent("hello\n\n bar", &prefix, true, true)
                .unwrap()
                .to_string(),
            "❗❓hello\n❗❓\n❗❓ bar"
        );
    }
}
