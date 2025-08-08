use core::cell::Cell;
use core::convert::Infallible;
use core::fmt::{self, Write};
use core::mem::replace;
use core::ops::Deref;
use core::pin::Pin;

use super::MAX_LEN;
use crate::filters::HtmlSafeOutput;
use crate::{Error, FastWritable, Result, Values};

/// Limit string length, appends '...' if truncated
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|truncate(2) }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "hello" }.to_string(),
///     "<div>he...</div>"
/// );
/// # }
/// ```
#[inline]
pub fn truncate<S: fmt::Display>(
    source: S,
    remaining: usize,
) -> Result<TruncateFilter<S>, Infallible> {
    Ok(TruncateFilter { source, remaining })
}

pub struct TruncateFilter<S> {
    source: S,
    remaining: usize,
}

impl<S: fmt::Display> fmt::Display for TruncateFilter<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(TruncateWriter::new(f, self.remaining), "{}", self.source)
    }
}

impl<S: FastWritable> FastWritable for TruncateFilter<S> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn Values,
    ) -> crate::Result<()> {
        self.source
            .write_into(&mut TruncateWriter::new(dest, self.remaining), values)
    }
}

struct TruncateWriter<W> {
    dest: Option<W>,
    remaining: usize,
}

impl<W> TruncateWriter<W> {
    fn new(dest: W, remaining: usize) -> Self {
        TruncateWriter {
            dest: Some(dest),
            remaining,
        }
    }
}

impl<W: fmt::Write> fmt::Write for TruncateWriter<W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let Some(dest) = &mut self.dest else {
            return Ok(());
        };
        let mut rem = self.remaining;
        if rem >= s.len() {
            dest.write_str(s)?;
            self.remaining -= s.len();
        } else {
            if rem > 0 {
                while !s.is_char_boundary(rem) {
                    rem += 1;
                }
                if rem == s.len() {
                    // Don't write "..." if the char bound extends to the end of string.
                    self.remaining = 0;
                    return dest.write_str(s);
                }
                dest.write_str(&s[..rem])?;
            }
            dest.write_str("...")?;
            self.dest = None;
        }
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        match self.dest.is_some() {
            true => self.write_str(c.encode_utf8(&mut [0; 4])),
            false => Ok(()),
        }
    }

    #[inline]
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        match self.dest.is_some() {
            true => fmt::write(self, args),
            false => Ok(()),
        }
    }
}

/// Joins iterable into a string separated by provided argument
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|join(", ") }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a [&'a str],
/// }
///
/// assert_eq!(
///     Example { example: &["foo", "bar", "bazz"] }.to_string(),
///     "<div>foo, bar, bazz</div>"
/// );
/// # }
/// ```
#[inline]
pub fn join<I, S>(input: I, separator: S) -> Result<JoinFilter<I, S>, Infallible>
where
    I: IntoIterator,
    I::Item: fmt::Display,
    S: fmt::Display,
{
    Ok(JoinFilter(Cell::new(Some((input, separator)))))
}

/// Result of the filter [`join()`].
///
/// ## Note
///
/// This struct implements [`fmt::Display`], but only produces a string once.
/// Any subsequent call to `.to_string()` will result in an empty string, because the iterator is
/// already consumed.
// The filter contains a [`Cell`], so we can modify iterator inside a method that takes `self` by
// reference: [`fmt::Display::fmt()`] normally has the contract that it will produce the same result
// in multiple invocations for the same object. We break this contract, because have to consume the
// iterator, unless we want to enforce `I: Clone`, nor do we want to "memorize" the result of the
// joined data.
pub struct JoinFilter<I, S>(Cell<Option<(I, S)>>);

impl<I, S> fmt::Display for JoinFilter<I, S>
where
    I: IntoIterator,
    I::Item: fmt::Display,
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some((iter, separator)) = self.0.take() else {
            return Ok(());
        };
        for (idx, token) in iter.into_iter().enumerate() {
            match idx {
                0 => f.write_fmt(format_args!("{token}"))?,
                _ => f.write_fmt(format_args!("{separator}{token}"))?,
            }
        }
        Ok(())
    }
}

/// Centers the value in a field of a given width
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>-{{ example|center(5) }}-</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "a" }.to_string(),
///     "<div>-  a  -</div>"
/// );
/// # }
/// ```
#[inline]
pub fn center<T: fmt::Display>(src: T, width: usize) -> Result<Center<T>, Infallible> {
    Ok(Center { src, width })
}

pub struct Center<T> {
    src: T,
    width: usize,
}

impl<T: fmt::Display> fmt::Display for Center<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.width < MAX_LEN {
            write!(f, "{: ^1$}", self.src, self.width)
        } else {
            write!(f, "{}", self.src)
        }
    }
}

/// For a value of `±1` by default an empty string `""` is returned, otherwise `"s"`.
///
/// # Examples
///
/// ## With default arguments
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// I have {{dogs}} dog{{dogs|pluralize}} and {{cats}} cat{{cats|pluralize}}.
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Pets {
///     dogs: i8,
///     cats: i8,
/// }
///
/// assert_eq!(
///     Pets { dogs: 0, cats: 0 }.to_string(),
///     "I have 0 dogs and 0 cats."
/// );
/// assert_eq!(
///     Pets { dogs: 1, cats: 1 }.to_string(),
///     "I have 1 dog and 1 cat."
/// );
/// assert_eq!(
///     Pets { dogs: -1, cats: 99 }.to_string(),
///     "I have -1 dog and 99 cats."
/// );
/// # }
/// ```
///
/// ## Overriding the singular case
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// I have {{dogs}} dog{{ dogs|pluralize("go") }}.
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Dog {
///     dogs: i8,
/// }
///
/// assert_eq!(
///     Dog { dogs: 0 }.to_string(),
///     "I have 0 dogs."
/// );
/// assert_eq!(
///     Dog { dogs: 1 }.to_string(),
///     "I have 1 doggo."
/// );
/// # }
/// ```
///
/// ## Overriding singular and plural cases
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// I have {{mice}} {{ mice|pluralize("mouse", "mice") }}.
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Mice {
///     mice: i8,
/// }
///
/// assert_eq!(
///     Mice { mice: 42 }.to_string(),
///     "I have 42 mice."
/// );
/// assert_eq!(
///     Mice { mice: 1 }.to_string(),
///     "I have 1 mouse."
/// );
/// # }
/// ```
///
/// ## Arguments get escaped
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// You are number {{ number|pluralize("<b>ONE</b>", number) }}!
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Number {
///     number: usize
/// }
///
/// assert_eq!(
///     Number { number: 1 }.to_string(),
///     "You are number &#60;b&#62;ONE&#60;/b&#62;!",
/// );
/// assert_eq!(
///     Number { number: 9000 }.to_string(),
///     "You are number 9000!",
/// );
/// # }
/// ```
#[inline]
pub fn pluralize<C, S, P>(count: C, singular: S, plural: P) -> Result<Either<S, P>, C::Error>
where
    C: PluralizeCount,
{
    match count.is_singular()? {
        true => Ok(Either::Left(singular)),
        false => Ok(Either::Right(plural)),
    }
}

/// An integer that can have the value `+1` and maybe `-1`.
pub trait PluralizeCount {
    /// A possible error that can occur while checking the value.
    type Error: Into<Error>;

    /// Returns `true` if and only if the value is `±1`.
    fn is_singular(&self) -> Result<bool, Self::Error>;
}

const _: () = {
    crate::impl_for_ref! {
        impl PluralizeCount for T {
            type Error = T::Error;

            #[inline]
            fn is_singular(&self) -> Result<bool, Self::Error> {
                <T>::is_singular(self)
            }
        }
    }

    impl<T> PluralizeCount for Pin<T>
    where
        T: Deref,
        <T as Deref>::Target: PluralizeCount,
    {
        type Error = <<T as Deref>::Target as PluralizeCount>::Error;

        #[inline]
        fn is_singular(&self) -> Result<bool, Self::Error> {
            self.as_ref().get_ref().is_singular()
        }
    }

    /// implement `PluralizeCount` for unsigned integer types
    macro_rules! impl_pluralize_for_unsigned_int {
        ($($ty:ty)*) => { $(
            impl PluralizeCount for $ty {
                type Error = Infallible;

                #[inline]
                fn is_singular(&self) -> Result<bool, Self::Error> {
                    Ok(*self == 1)
                }
            }
        )* };
    }

    impl_pluralize_for_unsigned_int!(u8 u16 u32 u64 u128 usize);

    /// implement `PluralizeCount` for signed integer types
    macro_rules! impl_pluralize_for_signed_int {
        ($($ty:ty)*) => { $(
            impl PluralizeCount for $ty {
                type Error = Infallible;

                #[inline]
                fn is_singular(&self) -> Result<bool, Self::Error> {
                    Ok(*self == 1 || *self == -1)
                }
            }
        )* };
    }

    impl_pluralize_for_signed_int!(i8 i16 i32 i64 i128 isize);

    /// implement `PluralizeCount` for non-zero integer types
    macro_rules! impl_pluralize_for_non_zero {
        ($($ty:ident)*) => { $(
            impl PluralizeCount for core::num::$ty {
                type Error = Infallible;

                #[inline]
                fn is_singular(&self) -> Result<bool, Self::Error> {
                    self.get().is_singular()
                }
            }
        )* };
    }

    impl_pluralize_for_non_zero! {
        NonZeroI8 NonZeroI16 NonZeroI32 NonZeroI64 NonZeroI128 NonZeroIsize
        NonZeroU8 NonZeroU16 NonZeroU32 NonZeroU64 NonZeroU128 NonZeroUsize
    }
};

/// Render either `L` or `R`
pub enum Either<L, R> {
    /// First variant
    Left(L),
    /// Second variant
    Right(R),
}

impl<L: fmt::Display, R: fmt::Display> fmt::Display for Either<L, R> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(value) => write!(f, "{value}"),
            Either::Right(value) => write!(f, "{value}"),
        }
    }
}

impl<L: FastWritable, R: FastWritable> FastWritable for Either<L, R> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn Values,
    ) -> crate::Result<()> {
        match self {
            Either::Left(value) => value.write_into(dest, values),
            Either::Right(value) => value.write_into(dest, values),
        }
    }
}

/// Returns an iterator without filtered out values.
///
/// ```
/// # use askama::Template;
/// #[derive(Template)]
/// #[template(
///       ext = "html",
///       source = r#"{% for elem in strs|reject("a") %}{{ elem }},{% endfor %}"#,
/// )]
/// struct Example<'a> {
///     strs: Vec<&'a str>,
/// }
///
/// assert_eq!(
///     Example { strs: vec!["a", "b", "c"] }.to_string(),
///     "b,c,"
/// );
/// ```
#[inline]
pub fn reject<'a, T: PartialEq + 'a>(
    it: impl Iterator<Item = T> + 'a,
    filter: &'a T,
) -> Result<impl Iterator<Item = T> + 'a, Infallible> {
    reject_with(it, move |v| v == filter)
}

/// Returns an iterator without filtered out values.
///
/// ```
/// # use askama::Template;
///
/// fn is_odd(v: &&u32) -> bool {
///     **v & 1 != 0
/// }
///
/// #[derive(Template)]
/// #[template(
///       ext = "html",
///       source = r#"{% for elem in numbers | reject(self::is_odd) %}{{ elem }},{% endfor %}"#,
/// )]
/// struct Example {
///     numbers: Vec<u32>,
/// }
///
/// # fn main() { // so `self::` can be accessed
/// assert_eq!(
///     Example { numbers: vec![1, 2, 3, 4] }.to_string(),
///     "2,4,"
/// );
/// # }
/// ```
#[inline]
pub fn reject_with<T: PartialEq>(
    it: impl Iterator<Item = T>,
    mut callback: impl FnMut(&T) -> bool,
) -> Result<impl Iterator<Item = T>, Infallible> {
    Ok(it.filter(move |v| !callback(v)))
}

/// Count the words in that string.
///
/// ```
/// # #[cfg(feature = "code-in-doc")] {
/// # use askama::Template;
/// /// ```jinja
/// /// <div>{{ example|wordcount }}</div>
/// /// ```
/// #[derive(Template)]
/// #[template(ext = "html", in_doc = true)]
/// struct Example<'a> {
///     example: &'a str,
/// }
///
/// assert_eq!(
///     Example { example: "askama is sort of cool" }.to_string(),
///     "<div>5</div>"
/// );
/// # }
/// ```
#[inline]
pub fn wordcount<S>(source: S) -> Wordcount<S> {
    Wordcount {
        source,
        count: Cell::new(WordcountInner {
            count: 0,
            ends_with_whitespace: true,
        }),
    }
}

pub struct Wordcount<S> {
    source: S,
    count: Cell<WordcountInner>,
}

impl<S> Wordcount<S> {
    pub fn into_count(self) -> usize {
        self.count.get().count
    }
}

impl<S: fmt::Display> fmt::Display for Wordcount<S> {
    #[inline]
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut inner = self.count.get();
        write!(WordCountWriter(&mut inner), "{}", self.source)?;
        self.count.set(inner);
        Ok(())
    }
}

impl<S: FastWritable> FastWritable for Wordcount<S> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        _: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        let mut inner = self.count.get();
        self.source
            .write_into(&mut WordCountWriter(&mut inner), values)?;
        self.count.set(inner);
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct WordcountInner {
    count: usize,
    ends_with_whitespace: bool,
}

struct WordCountWriter<'a>(&'a mut WordcountInner);

impl<'a> fmt::Write for WordCountWriter<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.is_empty() {
            // If the input is empty, nothing to be done.
            return Ok(());
        } else if s.trim().is_empty() {
            // If the input only contains whitespace characters, we set `ends_with_whitespace` to
            // `true`. It is to handle this case: `["a", " ", "b"]`. In total we should have two
            // words count.
            self.0.ends_with_whitespace = true;
            return Ok(());
        }
        self.0.count += s.split_whitespace().count();
        if !self.0.ends_with_whitespace && !s.starts_with(char::is_whitespace) {
            // This covers this case: `["a", "b c"]`. Here, we have two words ("ab" and "c") so we
            // need to subtract one from the count on "b c" because it returns 2 whereas "a" word is
            // not "finished".
            self.0.count -= 1;
        }
        // And again, if the string ends with a whitespace character, we change the value of
        // `ends_with_whitespace`.
        self.0.ends_with_whitespace = s.ends_with(char::is_whitespace);
        Ok(())
    }
}

/// Replaces line breaks in plain text with appropriate HTML.
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
pub fn linebreaks<S: fmt::Display>(
    source: S,
) -> Result<HtmlSafeOutput<NewlineCounting<S>>, Infallible> {
    Ok(HtmlSafeOutput(NewlineCounting {
        source,
        one: "<br/>",
    }))
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
) -> Result<HtmlSafeOutput<NewlineCounting<S>>, Infallible> {
    Ok(HtmlSafeOutput(NewlineCounting { source, one: "\n" }))
}

pub struct NewlineCounting<S> {
    source: S,
    one: &'static str,
}

impl<S> NewlineCounting<S> {
    #[inline]
    fn run<'a, F, W, E>(&self, dest: &'a mut W, inner: F) -> Result<(), E>
    where
        W: fmt::Write + ?Sized,
        F: FnOnce(&mut NewlineCountingFormatter<'a, W>) -> Result<(), E>,
        E: From<fmt::Error>,
    {
        let mut formatter = NewlineCountingFormatter {
            dest,
            counter: -1,
            one: self.one,
        };
        formatter.dest.write_str("<p>")?;
        inner(&mut formatter)?;
        formatter.dest.write_str("</p>")?;
        Ok(())
    }
}

impl<S: fmt::Display> fmt::Display for NewlineCounting<S> {
    fn fmt(&self, dest: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.run(dest, |f| write!(f, "{}", self.source))
    }
}

impl<S: FastWritable> FastWritable for NewlineCounting<S> {
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        self.run(dest, |f| self.source.write_into(f, values))
    }
}

struct NewlineCountingFormatter<'a, W: ?Sized> {
    dest: &'a mut W,
    counter: isize,
    one: &'static str,
}

impl<W: fmt::Write + ?Sized> fmt::Write for NewlineCountingFormatter<'_, W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.is_empty() {
            return Ok(());
        }
        for (has_eol, line) in split_lines(s) {
            if !line.is_empty() {
                match replace(&mut self.counter, if has_eol { 1 } else { 0 }) {
                    ..=0 => {}
                    1 => self.dest.write_str(self.one)?,
                    2.. => self.dest.write_str("</p><p>")?,
                }
                self.dest.write_str(line)?;
            } else if has_eol && self.counter >= 0 {
                self.counter += 1;
            }
        }
        Ok(())
    }
}

/// Converts all newlines in a piece of plain text to HTML line breaks.
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
        write!(LinebreaksbrFormatter(dest), "{}", self.0)
    }
}

struct LinebreaksbrFormatter<'a, W: ?Sized>(&'a mut W);

impl<S: FastWritable> FastWritable for Linebreaksbr<S> {
    #[inline]
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        values: &dyn crate::Values,
    ) -> crate::Result<()> {
        self.0.write_into(&mut LinebreaksbrFormatter(dest), values)
    }
}

impl<W: fmt::Write + ?Sized> fmt::Write for LinebreaksbrFormatter<'_, W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.is_empty() {
            return Ok(());
        }
        for (has_eol, line) in split_lines(s) {
            self.0.write_str(line)?;
            if has_eol {
                self.0.write_str("<br/>")?;
            }
        }
        Ok(())
    }
}

/// Splits the input at `/\r?\n/g``; returns whether a newline suffix was stripped and the
/// (maybe stripped) line.
fn split_lines(s: &str) -> impl Iterator<Item = (bool, &str)> {
    s.split_inclusive('\n').map(|line| {
        if let Some(line) = line.strip_suffix('\n') {
            (true, line.strip_suffix('\r').unwrap_or(line))
        } else {
            (false, line)
        }
    })
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use alloc::string::{String, ToString};
    use alloc::vec::Vec;

    use super::*;
    use crate::NO_VALUES;

    #[allow(clippy::needless_borrow)]
    #[test]
    fn test_join() {
        assert_eq!(
            join((&["hello", "world"]).iter(), ", ")
                .unwrap()
                .to_string(),
            "hello, world"
        );
        assert_eq!(
            join((&["hello"]).iter(), ", ").unwrap().to_string(),
            "hello"
        );

        let empty: &[&str] = &[];
        assert_eq!(join(empty.iter(), ", ").unwrap().to_string(), "");

        let input: Vec<String> = alloc::vec!["foo".into(), "bar".into(), "bazz".into()];
        assert_eq!(join(input.iter(), ":").unwrap().to_string(), "foo:bar:bazz");

        let input: &[String] = &["foo".into(), "bar".into()];
        assert_eq!(join(input.iter(), ":").unwrap().to_string(), "foo:bar");

        let real: String = "blah".into();
        let input: Vec<&str> = alloc::vec![&real];
        assert_eq!(join(input.iter(), ";").unwrap().to_string(), "blah");

        assert_eq!(
            join((&&&&&["foo", "bar"]).iter(), ", ")
                .unwrap()
                .to_string(),
            "foo, bar"
        );
    }

    #[test]
    fn test_center() {
        assert_eq!(center("f", 3).unwrap().to_string(), " f ".to_string());
        assert_eq!(center("f", 4).unwrap().to_string(), " f  ".to_string());
        assert_eq!(center("foo", 1).unwrap().to_string(), "foo".to_string());
        assert_eq!(
            center("foo bar", 8).unwrap().to_string(),
            "foo bar ".to_string()
        );
        assert_eq!(
            center("foo", 111_669_149_696).unwrap().to_string(),
            "foo".to_string()
        );
    }

    #[test]
    fn test_wordcount() {
        for &(word, count) in &[
            ("", 0),
            (" \n\t", 0),
            ("foo", 1),
            ("foo bar", 2),
            ("foo  bar", 2),
        ] {
            let w = wordcount(word);
            let _ = w.to_string();
            assert_eq!(w.into_count(), count, "fmt: {word:?}");

            let w = wordcount(word);
            w.write_into(&mut String::new(), NO_VALUES).unwrap();
            assert_eq!(w.into_count(), count, "FastWritable: {word:?}");
        }
    }

    #[test]
    fn test_wordcount_on_partial_input() {
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

        fn wrap(s: &str) -> usize {
            let w = wordcount(Chunked(s));
            // Needed to actually count the words.
            w.to_string();
            w.into_count()
        }

        // This test ensures that if `wordcount` returned value's `Display` impl was not called,
        // it will always return 0.
        assert_eq!(wordcount(Chunked("hello")).into_count(), 0);

        assert_eq!(wrap("hello"), 1);
        assert_eq!(wrap("hello\n"), 1);
        assert_eq!(wrap("hello\nfoo"), 2);
        assert_eq!(wrap("hello\nfoo\n bar"), 3);

        assert_eq!(wrap("hello\n\n bar"), 2);
        assert_eq!(wrap("  hello\n\n bar  "), 2);
    }

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
            "<p>Foo</p><p>Bar</p><p>Baz</p>"
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
}
