#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![deny(elided_lifetimes_in_paths)]
#![deny(unreachable_pub)]
#![allow(clippy::vec_box)] // intentional, less copying
#![doc = include_str!("../README.md")]

mod ascii_str;
pub mod expr;
pub mod node;
mod target;
#[cfg(test)]
mod tests;

use std::borrow::{Borrow, BorrowMut, Cow};
use std::cell::Cell;
use std::env::current_dir;
use std::ops::{Deref, DerefMut, Range};
use std::path::Path;
use std::sync::Arc;
use std::{fmt, str};

use rustc_hash::FxBuildHasher;
use winnow::ascii::take_escaped;
use winnow::combinator::{
    alt, cond, cut_err, delimited, empty, fail, not, opt, peek, preceded, repeat, terminated,
};
use winnow::error::ErrMode;
use winnow::stream::{AsChar, Location, Stream};
use winnow::token::{any, none_of, one_of, take_while};
use winnow::{LocatingSlice, ModalParser, ModalResult, Parser, Stateful};

use crate::ascii_str::{AsciiChar, AsciiStr};
pub use crate::expr::{AssociatedItem, Expr, Filter, PathComponent, TyGenerics};
pub use crate::node::Node;
pub use crate::target::{NamedTarget, Target};

mod _parsed {
    use std::path::Path;
    use std::sync::Arc;
    use std::{fmt, mem};

    use super::node::Node;
    use super::{Ast, ParseError, Syntax};

    pub struct Parsed {
        // `source` must outlive `ast`, so `ast` must be declared before `source`
        ast: Ast<'static>,
        #[allow(dead_code)]
        source: Arc<str>,
    }

    impl Parsed {
        /// If `file_path` is `None`, it means the `source` is an inline template. Therefore, if
        /// a parsing error occurs, we won't display the path as it wouldn't be useful.
        pub fn new(
            source: Arc<str>,
            file_path: Option<Arc<Path>>,
            syntax: &Syntax<'_>,
        ) -> Result<Self, ParseError> {
            // Self-referential borrowing: `self` will keep the source alive as `String`,
            // internally we will transmute it to `&'static str` to satisfy the compiler.
            // However, we only expose the nodes with a lifetime limited to `self`.
            let src = unsafe { mem::transmute::<&str, &'static str>(source.as_ref()) };
            let ast = Ast::from_str(src, file_path, syntax)?;
            Ok(Self { ast, source })
        }

        // The return value's lifetime must be limited to `self` to uphold the unsafe invariant.
        #[must_use]
        pub fn nodes(&self) -> &[Box<Node<'_>>] {
            &self.ast.nodes
        }

        #[must_use]
        pub fn source(&self) -> &str {
            &self.source
        }
    }

    impl fmt::Debug for Parsed {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Parsed")
                .field("nodes", &self.ast.nodes)
                .finish_non_exhaustive()
        }
    }

    impl PartialEq for Parsed {
        fn eq(&self, other: &Self) -> bool {
            self.ast.nodes == other.ast.nodes
        }
    }

    impl Default for Parsed {
        fn default() -> Self {
            Self {
                ast: Ast::default(),
                source: "".into(),
            }
        }
    }
}

pub use _parsed::Parsed;

type InputStream<'a, 'l> = Stateful<LocatingSlice<&'a str>, &'l State<'l>>;

#[derive(Debug, Default)]
pub struct Ast<'a> {
    nodes: Vec<Box<Node<'a>>>,
}

impl<'a> Ast<'a> {
    /// If `file_path` is `None`, it means the `source` is an inline template. Therefore, if
    /// a parsing error occurs, we won't display the path as it wouldn't be useful.
    pub fn from_str(
        src: &'a str,
        file_path: Option<Arc<Path>>,
        syntax: &Syntax<'_>,
    ) -> Result<Ast<'a>, ParseError> {
        let state = State {
            syntax: *syntax,
            ..State::default()
        };
        let mut src = InputStream {
            input: LocatingSlice::new(src),
            state: &state,
        };
        match Node::parse_template(&mut src) {
            Ok(nodes) if src.is_empty() => Ok(Self { nodes }),
            Ok(_) | Err(ErrMode::Incomplete(_)) => unreachable!(),
            Err(
                ErrMode::Backtrack(ErrorContext { span, message, .. })
                | ErrMode::Cut(ErrorContext { span, message, .. }),
            ) => Err(ParseError {
                message,
                offset: span.start,
                file_path,
            }),
        }
    }

    #[must_use]
    pub fn nodes(&self) -> &[Box<Node<'a>>] {
        &self.nodes
    }
}

#[derive(Clone, Copy)]
/// Struct used to wrap types with their associated "span" which is used when generating errors
/// in the code generation.
#[repr(C)] // rationale: `WithSpan<Box<T>` needs to have the same layout as `WithSpan<&T>`.
pub struct WithSpan<T> {
    inner: T,
    span: Span,
}

/// A location in `&'a str`
#[derive(Debug, Clone, Copy)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Default for Span {
    #[inline]
    fn default() -> Self {
        Self::no_span()
    }
}

impl From<&InputStream<'_, '_>> for Span {
    #[inline]
    fn from(i: &InputStream<'_, '_>) -> Self {
        (*i).into()
    }
}

impl From<InputStream<'_, '_>> for Span {
    #[inline]
    fn from(mut i: InputStream<'_, '_>) -> Self {
        let start = i.current_token_start();
        i.finish();
        Self {
            start,
            end: i.current_token_start(),
        }
    }
}

impl From<Range<usize>> for Span {
    #[inline]
    #[track_caller]
    fn from(range: Range<usize>) -> Self {
        Span::new(range)
    }
}

impl Span {
    #[inline]
    pub const fn no_span() -> Span {
        Self {
            start: usize::MAX,
            end: usize::MAX,
        }
    }

    #[inline]
    #[track_caller]
    pub fn new(range: Range<usize>) -> Self {
        let Range { start, end } = range;
        debug_assert!(start <= end);
        Span { start, end }
    }

    #[inline]
    pub fn byte_range(self) -> Option<Range<usize>> {
        (self.start != usize::MAX).then_some(self.start..self.end)
    }

    /// Returns an empty [`Span`] that points to the start of `self`.
    #[inline]
    pub fn start(self) -> Self {
        Self {
            start: self.start,
            end: self.start,
        }
    }

    /// Returns an empty [`Span`] that points to the end of `self`.
    #[inline]
    pub fn end(self) -> Self {
        Self {
            start: self.end,
            end: self.end,
        }
    }

    /// Splits `self` at `mid` into two spanned strings.
    #[track_caller]
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        let Some(Range { start, end }) = self.byte_range() else {
            return (self, self);
        };

        let mid = start.checked_add(mid).unwrap();
        assert!(mid <= end);

        let start = Self { start, end: mid };
        let end = Self { start: mid, end };
        (start, end)
    }

    /// The substring in `source` contained in [`self.byte_range()`][Self::byte_range].
    #[inline]
    pub fn as_infix_of<'a>(&self, source: &'a str) -> Option<&'a str> {
        self.byte_range().and_then(|range| source.get(range))
    }

    /// The substring in `source` starting from `self.start`.
    #[inline]
    pub fn as_suffix_of<'a>(&self, source: &'a str) -> Option<&'a str> {
        // No need to check if `self.start != usize::MAX`:
        // `source` cannot be longer than `isize::MAX`, cf. [`std::alloc`].
        source.get(self.start..)
    }

    pub fn is_overlapping(&self, other: Span) -> bool {
        (self.start < other.end) & (other.start < self.end)
    }
}

impl<T> WithSpan<T> {
    #[inline]
    #[track_caller]
    pub fn new(inner: T, span: impl Into<Span>) -> Self {
        Self {
            inner,
            span: span.into(),
        }
    }

    #[inline]
    pub const fn no_span(inner: T) -> Self {
        Self {
            inner,
            span: Span::no_span(),
        }
    }

    #[inline]
    pub fn span(&self) -> Span {
        self.span
    }

    #[inline]
    pub fn deconstruct(self) -> (T, Span) {
        let Self { inner, span } = self;
        (inner, span)
    }
}

impl WithSpan<&str> {
    /// Returns an empty [`Span`] that points to the start of the contained string.
    #[inline]
    pub fn start(self) -> Self {
        let (inner, span) = self.deconstruct();
        Self::new(&inner[..0], span.start())
    }

    /// Returns an empty [`Span`] that points to the end of the contained string.
    #[inline]
    pub fn end(self) -> Self {
        let (inner, span) = self.deconstruct();
        Self::new(&inner[inner.len()..], span.end())
    }

    /// Splits `self` at `mid` into two spanned strings.
    #[track_caller]
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        let (inner, span) = self.deconstruct();
        let (front, back) = inner.split_at(mid);
        let (front_span, back_span) = span.split_at(mid);
        (Self::new(front, front_span), Self::new(back, back_span))
    }
}

impl<T> Deref for WithSpan<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for WithSpan<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T: fmt::Debug> fmt::Debug for WithSpan<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: PartialEq, R: AsRef<T>> PartialEq<R> for WithSpan<T> {
    #[inline]
    fn eq(&self, other: &R) -> bool {
        // We never want to compare the span information.
        self.inner == *other.as_ref()
    }
}

impl<T: PartialOrd, R: AsRef<T>> PartialOrd<R> for WithSpan<T> {
    #[inline]
    fn partial_cmp(&self, other: &R) -> Option<std::cmp::Ordering> {
        self.inner.partial_cmp(other.as_ref())
    }
}

impl<T: Eq> Eq for WithSpan<T> {}

impl<T: Ord> Ord for WithSpan<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<T: std::hash::Hash> std::hash::Hash for WithSpan<T> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl<T> AsRef<T> for WithSpan<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T> Borrow<T> for WithSpan<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &self.inner
    }
}

impl<T> BorrowMut<T> for WithSpan<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: Option<Cow<'static, str>>,
    pub offset: usize,
    pub file_path: Option<Arc<Path>>,
}

impl std::error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ParseError {
            message,
            file_path,
            offset,
        } = self;

        if let Some(message) = message {
            writeln!(f, "{message}")?;
        }

        let path = file_path
            .as_ref()
            .and_then(|path| Some(strip_common(&current_dir().ok()?, path)));
        match path {
            Some(path) => write!(f, "failed to parse template source\n  --> {path}@{offset}"),
            None => write!(f, "failed to parse template source near offset {offset}"),
        }
    }
}

pub(crate) type ParseErr<'a> = ErrMode<ErrorContext>;
pub(crate) type ParseResult<'a, T = &'a str> = Result<T, ParseErr<'a>>;

/// This type is used to handle `nom` errors and in particular to add custom error messages.
/// It used to generate `ParserError`.
///
/// It cannot be used to replace `ParseError` because it expects a generic, which would make
/// `askama`'s users experience less good (since this generic is only needed for `nom`).
#[derive(Debug)]
pub(crate) struct ErrorContext {
    pub(crate) span: Span,
    pub(crate) message: Option<Cow<'static, str>>,
}

impl ErrorContext {
    #[cold]
    fn unclosed(kind: &str, tag: &str, span: impl Into<Span>) -> Self {
        Self {
            span: span.into(),
            message: Some(format!("unclosed {kind}, missing {tag:?}").into()),
        }
    }

    #[cold]
    #[inline]
    fn new(message: impl Into<Cow<'static, str>>, span: impl Into<Span>) -> Self {
        Self {
            span: span.into(),
            message: Some(message.into()),
        }
    }

    #[inline]
    fn backtrack(self) -> ErrMode<Self> {
        ErrMode::Backtrack(self)
    }

    #[inline]
    fn cut(self) -> ErrMode<Self> {
        ErrMode::Cut(self)
    }
}

impl<'a: 'l, 'l> winnow::error::ParserError<InputStream<'a, 'l>> for ErrorContext {
    type Inner = Self;

    #[inline]
    fn from_input(input: &InputStream<'a, 'l>) -> Self {
        Self {
            span: input.into(),
            message: None,
        }
    }

    #[inline(always)]
    fn into_inner(self) -> Result<Self::Inner, Self> {
        Ok(self)
    }
}

fn skip_ws0<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
    take_while(0.., |c: char| c.is_ascii_whitespace())
        .void()
        .parse_next(i)
}

fn skip_ws1<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
    take_while(1.., |c: char| c.is_ascii_whitespace())
        .void()
        .parse_next(i)
}

fn ws<'a: 'l, 'l, O>(
    inner: impl ModalParser<InputStream<'a, 'l>, O, ErrorContext>,
) -> impl ModalParser<InputStream<'a, 'l>, O, ErrorContext> {
    delimited(skip_ws0, inner, skip_ws0)
}

fn keyword<'a: 'l, 'l>(k: &str) -> impl ModalParser<InputStream<'a, 'l>, &'a str, ErrorContext> {
    identifier.verify(move |v: &str| v == k)
}

fn identifier<'a: 'l, 'l>(input: &mut InputStream<'a, 'l>) -> ParseResult<'a> {
    let head = any.verify(|&c| c == '_' || unicode_ident::is_xid_start(c));
    let tail = take_while(.., unicode_ident::is_xid_continue);
    (head, tail).take().parse_next(input)
}

fn bool_lit<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a> {
    alt((keyword("false"), keyword("true"))).parse_next(i)
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Num<'a> {
    Int(&'a str, Option<IntKind>),
    Float(&'a str, Option<FloatKind>),
}

fn check_base_digits<'a>(digits: &'a str, base: u32, span: Range<usize>) -> ParseResult<'a, ()> {
    let allowed_digits: &[char] = match base {
        2 => &['0', '1'],
        8 => &['0', '1', '2', '3', '4', '5', '6', '7'],
        16 => &[
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
        ],
        _ => panic!("unsupported base `{base}`"),
    };

    for digit in digits.chars() {
        let lower = digit.to_ascii_lowercase();
        if lower != '_' && !allowed_digits.iter().any(|c| *c == digit || *c == lower) {
            let allowed = allowed_digits.iter().collect::<String>();
            let base = match base {
                2 => 'b',
                8 => 'o',
                16 => 'x',
                _ => unreachable!(),
            };
            return cut_error!(
                format!("only expected `{allowed}` digits for `0{base}` integers, found `{digit}`"),
                span,
            );
        }
    }
    Ok(())
}

fn num_lit<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Num<'a>> {
    fn num_lit_suffix<'a: 'l, 'l, T: Copy>(
        kind: &'a str,
        list: &[(&str, T)],
        i: &mut InputStream<'a, 'l>,
    ) -> ParseResult<'a, T> {
        let (suffix, span) = identifier.with_span().parse_next(i)?;
        if let Some(value) = list
            .iter()
            .copied()
            .find_map(|(name, value)| (name == suffix).then_some(value))
        {
            Ok(value)
        } else {
            cut_error!(format!("unknown {kind} suffix `{suffix}`"), span)
        }
    }

    // Equivalent to <https://github.com/rust-lang/rust/blob/e3f909b2bbd0b10db6f164d466db237c582d3045/compiler/rustc_lexer/src/lib.rs#L587-L620>.
    let int_with_base = (opt('-'), |i: &mut _| {
        let ((base, kind), span) = preceded('0', alt(('b'.value(2), 'o'.value(8), 'x'.value(16))))
            .with_taken()
            .with_span()
            .parse_next(i)?;
        match opt(separated_digits(if base == 16 { base } else { 10 }, false)).parse_next(i)? {
            Some(digits) => check_base_digits(digits, base, span),
            None => cut_error!(format!("expected digits after `{kind}`"), span),
        }
    });

    // Equivalent to <https://github.com/rust-lang/rust/blob/e3f909b2bbd0b10db6f164d466db237c582d3045/compiler/rustc_lexer/src/lib.rs#L626-L653>:
    // no `_` directly after the decimal point `.`, or between `e` and `+/-`.
    let float = |i: &mut InputStream<'a, 'l>| -> ParseResult<'a, ()> {
        let has_dot = opt(('.', separated_digits(10, true))).parse_next(i)?;
        let has_exp = opt(|i: &mut _| {
            let ((kind, op), span) = (one_of(['e', 'E']), opt(one_of(['+', '-'])))
                .with_span()
                .parse_next(i)?;
            match opt(separated_digits(10, op.is_none())).parse_next(i)? {
                Some(_) => Ok(()),
                None => {
                    cut_error!(
                        format!("expected decimal digits, `+` or `-` after exponent `{kind}`"),
                        span,
                    )
                }
            }
        })
        .parse_next(i)?;
        match (has_dot, has_exp) {
            (Some(_), _) | (_, Some(())) => Ok(()),
            _ => fail(i),
        }
    };

    let num = if let Some(num) = opt(int_with_base.take()).parse_next(i)? {
        let suffix = opt(|i: &mut _| num_lit_suffix("integer", INTEGER_TYPES, i)).parse_next(i)?;
        Num::Int(num, suffix)
    } else {
        let (float, num) = preceded((opt('-'), separated_digits(10, true)), opt(float))
            .with_taken()
            .parse_next(i)?;
        if float.is_some() {
            let suffix = opt(|i: &mut _| num_lit_suffix("float", FLOAT_TYPES, i)).parse_next(i)?;
            Num::Float(num, suffix)
        } else {
            let suffix = opt(|i: &mut _| num_lit_suffix("number", NUM_TYPES, i)).parse_next(i)?;
            match suffix {
                Some(NumKind::Int(kind)) => Num::Int(num, Some(kind)),
                Some(NumKind::Float(kind)) => Num::Float(num, Some(kind)),
                None => Num::Int(num, None),
            }
        }
    };
    Ok(num)
}

/// Underscore separated digits of the given base, unless `start` is true this may start
/// with an underscore.
fn separated_digits<'a: 'l, 'l>(
    radix: u32,
    start: bool,
) -> impl ModalParser<InputStream<'a, 'l>, &'a str, ErrorContext> {
    (
        cond(!start, repeat(0.., '_').map(|()| ())),
        one_of(move |ch: char| ch.is_digit(radix)),
        repeat(0.., one_of(move |ch: char| ch == '_' || ch.is_digit(radix))).map(|()| ()),
    )
        .take()
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum StrPrefix {
    Binary,
    CLike,
}

impl StrPrefix {
    #[must_use]
    pub fn to_char(self) -> char {
        match self {
            Self::Binary => 'b',
            Self::CLike => 'c',
        }
    }
}

impl fmt::Display for StrPrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use std::fmt::Write;

        f.write_char(self.to_char())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StrLit<'a> {
    /// the unparsed (but validated) content
    pub content: &'a str,
    /// whether the string literal is unprefixed, a cstring or binary slice
    pub prefix: Option<StrPrefix>,
    /// contains a NUL character, either escaped `'\0'` or the very characters;
    /// not allowed in cstring literals
    pub contains_null: bool,
    /// contains a non-ASCII character, either as `\u{123456}` or as an unescaped character;
    /// not allowed in binary slices
    pub contains_unicode_character: bool,
    /// contains unicode escape sequences like `\u{12}` (regardless of its range);
    /// not allowed in binary slices
    pub contains_unicode_escape: bool,
    /// contains a non-ASCII range escape sequence like `\x80`;
    /// not allowed in unprefix strings
    pub contains_high_ascii: bool,
}

fn str_lit<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, StrLit<'a>> {
    // <https://doc.rust-lang.org/reference/tokens.html#r-lex.token.literal.str.syntax>

    fn inner<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, StrLit<'a>> {
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum Sequence<'a> {
            Text(&'a str),
            Close,
            Escape,
            CrLf,
            Cr(Range<usize>),
        }

        let mut contains_null = false;
        let mut contains_unicode_character = false;
        let mut contains_unicode_escape = false;
        let mut contains_high_ascii = false;

        while !i.is_empty() {
            let seq = alt((
                repeat::<_, _, (), _, _>(1.., none_of(['\r', '\\', '"']))
                    .take()
                    .map(Sequence::Text),
                ('\r'.span(), opt('\n')).map(|(span, has_lf)| match has_lf {
                    Some(_) => Sequence::CrLf,
                    None => Sequence::Cr(span),
                }),
                '\\'.value(Sequence::Escape),
                peek('"').value(Sequence::Close),
            ))
            .parse_next(i)?;

            match seq {
                Sequence::Text(s) => {
                    contains_unicode_character =
                        contains_unicode_character || s.bytes().any(|c: u8| !c.is_ascii());
                    contains_null = contains_null || s.bytes().any(|c: u8| c == 0);
                    continue;
                }
                Sequence::CrLf => continue,
                Sequence::Cr(span) => {
                    return cut_error!(
                        "a bare CR (Mac linebreak) is not allowed in string literals, \
                        use NL (Unix linebreak) or CRNL (Windows linebreak) instead, \
                        or type `\\r` explicitly",
                        span,
                    );
                }
                Sequence::Close => break,
                Sequence::Escape => {}
            }

            match any.parse_next(i)? {
                '\'' | '"' | 'n' | 'r' | 't' | '\\' => continue,
                '0' => {
                    contains_null = true;
                    continue;
                }
                'x' => {
                    let code = take_while(2, AsChar::is_hex_digit).parse_next(i)?;
                    match u8::from_str_radix(code, 16).unwrap() {
                        0 => contains_null = true,
                        128.. => contains_high_ascii = true,
                        _ => {}
                    }
                }
                'u' => {
                    contains_unicode_escape = true;
                    let (code, span) = delimited('{', take_while(1..=6, AsChar::is_hex_digit), '}')
                        .with_span()
                        .parse_next(i)?;
                    match u32::from_str_radix(code, 16).unwrap() {
                        0 => contains_null = true,
                        0xd800..0xe000 => {
                            return cut_error!("unicode escape must not be a surrogate", span);
                        }
                        0x110000.. => {
                            return cut_error!("unicode escape must be at most 10FFFF", span);
                        }
                        128.. => contains_unicode_character = true,
                        _ => {}
                    }
                }
                _ => return fail(i),
            }
        }

        Ok(StrLit {
            content: "",
            prefix: None,
            contains_null,
            contains_unicode_character,
            contains_unicode_escape,
            contains_high_ascii,
        })
    }

    let ((prefix, lit), span) = (
        terminated(
            opt(alt((
                'b'.value(StrPrefix::Binary),
                'c'.value(StrPrefix::CLike),
            ))),
            '"',
        ),
        opt(terminated(inner.with_taken(), '"')),
    )
        .with_span()
        .parse_next(i)?;

    let Some((mut lit, content)) = lit else {
        return cut_error!("unclosed or broken string", span);
    };
    lit.content = content;
    lit.prefix = prefix;

    let msg = match prefix {
        Some(StrPrefix::Binary) => {
            if lit.contains_unicode_character {
                Some("non-ASCII character in byte string literal")
            } else if lit.contains_unicode_escape {
                Some("unicode escape in byte string")
            } else {
                None
            }
        }
        Some(StrPrefix::CLike) => lit
            .contains_null
            .then_some("null characters in C string literals are not supported"),
        None => lit.contains_high_ascii.then_some("out of range hex escape"),
    };
    if let Some(msg) = msg {
        return cut_error!(msg, span);
    }

    not_suffix_with_hash(i)?;
    Ok(lit)
}

fn not_suffix_with_hash<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
    if let Some(span) = opt(identifier.span()).parse_next(i)? {
        return cut_error!(
            "you are missing a space to separate two string literals",
            span,
        );
    }
    Ok(())
}

fn str_lit_without_prefix<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a> {
    let (lit, span) = str_lit.with_span().parse_next(i)?;

    let kind = match lit.prefix {
        Some(StrPrefix::Binary) => Some("binary slice"),
        Some(StrPrefix::CLike) => Some("cstring"),
        None => None,
    };
    if let Some(kind) = kind {
        return cut_error!(
            format!("expected an unprefixed normal string, not a {kind}"),
            span,
        );
    }

    Ok(lit.content)
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CharPrefix {
    Binary,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CharLit<'a> {
    pub prefix: Option<CharPrefix>,
    pub content: &'a str,
}

// Information about allowed character escapes is available at:
// <https://doc.rust-lang.org/reference/tokens.html#character-literals>.
fn char_lit<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, CharLit<'a>> {
    let ((prefix, _, content, is_closed), span) = (
        alt(('b'.value(Some(CharPrefix::Binary)), empty.value(None))),
        '\'',
        opt(take_escaped(none_of(['\\', '\'']), '\\', any)),
        opt('\''),
    )
        .with_span()
        .parse_next(i)?;

    if is_closed.is_none() {
        if let Some(prefix) = prefix {
            return cut_error!(
                match prefix {
                    CharPrefix::Binary => "unterminated byte literal",
                },
                span,
            );
        } else {
            return fail(i);
        }
    }

    let content = match content.unwrap_or_default() {
        "" => {
            return cut_error!(
                match prefix {
                    Some(CharPrefix::Binary) => "empty byte literal",
                    None => "empty character literal",
                },
                span,
            );
        }
        content => content,
    };

    let mut content_i = content;
    let Ok(c) = Char::parse(&mut content_i) else {
        return cut_error!("invalid character", span);
    };
    if !content_i.is_empty() {
        let (c, s) = match prefix {
            Some(CharPrefix::Binary) => ("byte", "binary string"),
            None => ("character", "string"),
        };
        return cut_error!(
            format!(
                "cannot have multiple characters in a {c} literal, use `{}\"...\"` to write a {s}",
                match prefix {
                    Some(CharPrefix::Binary) => "b",
                    None => "",
                }
            ),
            span,
        );
    }

    let (nb, max_value, err1, err2) = match c {
        Char::Literal | Char::Escaped => {
            return Ok(CharLit { prefix, content });
        }
        Char::AsciiEscape(nb) => (
            nb,
            // `0x7F` is the maximum value for a `\x` escaped character.
            0x7F,
            "invalid character in ascii escape",
            "must be a character in the range [\\x00-\\x7f]",
        ),
        Char::UnicodeEscape(nb) => {
            match prefix {
                Some(CharPrefix::Binary) => {
                    return cut_error!(
                        "cannot use unicode escape in byte string in byte literal",
                        span,
                    );
                }
                None => (
                    nb,
                    // `0x10FFFF` is the maximum value for a `\u` escaped character.
                    0x0010_FFFF,
                    "invalid character in unicode escape",
                    "unicode escape must be at most 10FFFF",
                ),
            }
        }
    };

    let Ok(nb) = u32::from_str_radix(nb, 16) else {
        return cut_error!(err1, span);
    };
    if nb > max_value {
        return cut_error!(err2, span);
    }

    Ok(CharLit { prefix, content })
}

/// Represents the different kinds of char declarations:
#[derive(Copy, Clone)]
enum Char<'a> {
    /// Any character that is not escaped.
    Literal,
    /// An escaped character (like `\n`) which doesn't require any extra check.
    Escaped,
    /// Ascii escape (like `\x12`).
    AsciiEscape(&'a str),
    /// Unicode escape (like `\u{12}`).
    UnicodeEscape(&'a str),
}

impl<'a> Char<'a> {
    fn parse(i: &mut &'a str) -> ModalResult<Self, ()> {
        let unescaped = none_of(('\\', '\'')).value(Self::Literal);
        let escaped = preceded(
            '\\',
            alt((
                'n'.value(Self::Escaped),
                'r'.value(Self::Escaped),
                't'.value(Self::Escaped),
                '\\'.value(Self::Escaped),
                '0'.value(Self::Escaped),
                '\''.value(Self::Escaped),
                // Not useful but supported by rust.
                '"'.value(Self::Escaped),
                ('x', take_while(2, |c: char| c.is_ascii_hexdigit()))
                    .map(|(_, s)| Self::AsciiEscape(s)),
                (
                    "u{",
                    take_while(1..=6, |c: char| c.is_ascii_hexdigit()),
                    '}',
                )
                    .map(|(_, s, _)| Self::UnicodeEscape(s)),
            )),
        );
        alt((unescaped, escaped)).parse_next(i)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PathOrIdentifier<'a> {
    Path(Vec<PathComponent<'a>>),
    Identifier(WithSpan<&'a str>),
}

fn path_or_identifier<'a: 'l, 'l>(
    i: &mut InputStream<'a, 'l>,
) -> ParseResult<'a, PathOrIdentifier<'a>> {
    let mut p = |i: &mut _| {
        let root = ws(opt(terminated(empty.span(), "::")));
        let start = PathComponent::parse;
        let tail = opt(repeat(1.., preceded(ws("::"), PathComponent::parse)).map(|v: Vec<_>| v));

        let (root, start, rest) = (root, start, tail).parse_next(i)?;
        Ok((root, start, rest.unwrap_or_default()))
    };
    let (root, start, rest) = p.parse_next(i)?;

    // The returned identifier can be assumed to be path if:
    // - it is an absolute path (starts with `::`), or
    // - it has multiple components (at least one `::`), or
    // - the first letter is uppercase
    match (root, start, rest) {
        (None, arg, tail)
            if tail.is_empty()
                && arg.generics.is_none()
                && arg
                    .name
                    .chars()
                    .next()
                    .is_none_or(|c| c == '_' || c.is_lowercase()) =>
        {
            Ok(PathOrIdentifier::Identifier(arg.name))
        }
        (root, start, tail) => {
            let mut path = if let Some(root) = root {
                let mut path = Vec::with_capacity(2 + tail.len());
                path.push(PathComponent {
                    name: WithSpan::new("", root),
                    generics: None,
                });
                path
            } else {
                Vec::with_capacity(1 + tail.len())
            };
            path.push(start);
            path.extend(tail);
            Ok(PathOrIdentifier::Path(path))
        }
    }
}

#[derive(Debug, Clone, Default)]
struct State<'a> {
    syntax: Syntax<'a>,
    loop_depth: Cell<usize>,
    level: Level,
}

fn block_start<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
    i.state.syntax.block_start.void().parse_next(i)
}

fn block_end<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
    let (control, span) = alt((
        i.state.syntax.block_end.value(None),
        peek(delimited('%', alt(('-', '~', '+')).map(Some), '}')),
        fail, // rollback on partial matches in the previous line
    ))
    .with_span()
    .parse_next(i)?;

    let Some(control) = control else {
        return Ok(());
    };

    let err = ErrorContext::new(
        format!(
            "unclosed block, you likely meant to apply whitespace control: \"{}{}\"",
            control.escape_default(),
            i.state.syntax.block_end.escape_default(),
        ),
        span,
    );
    Err(err.backtrack())
}

fn expr_start<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
    i.state.syntax.expr_start.void().parse_next(i)
}

fn expr_end<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
    i.state.syntax.expr_end.void().parse_next(i)
}

impl State<'_> {
    fn enter_loop(&self) {
        self.loop_depth.set(self.loop_depth.get() + 1);
    }

    fn leave_loop(&self) {
        self.loop_depth.set(self.loop_depth.get() - 1);
    }

    fn is_in_loop(&self) -> bool {
        self.loop_depth.get() > 0
    }
}

#[derive(Default, Hash, PartialEq, Clone, Copy)]
pub struct Syntax<'a>(InnerSyntax<'a>);

// This abstraction ensures that the fields are readable, but not writable.
#[derive(Hash, PartialEq, Clone, Copy)]
pub struct InnerSyntax<'a> {
    pub block_start: &'a str,
    pub block_end: &'a str,
    pub expr_start: &'a str,
    pub expr_end: &'a str,
    pub comment_start: &'a str,
    pub comment_end: &'a str,
}

impl<'a> Deref for Syntax<'a> {
    type Target = InnerSyntax<'a>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Default for InnerSyntax<'static> {
    fn default() -> Self {
        Self {
            block_start: "{%",
            block_end: "%}",
            expr_start: "{{",
            expr_end: "}}",
            comment_start: "{#",
            comment_end: "#}",
        }
    }
}

impl fmt::Debug for Syntax<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_syntax("Syntax", self, f)
    }
}

impl fmt::Debug for InnerSyntax<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_syntax("InnerSyntax", self, f)
    }
}

fn fmt_syntax(name: &str, inner: &InnerSyntax<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct(name)
        .field("block_start", &inner.block_start)
        .field("block_end", &inner.block_end)
        .field("expr_start", &inner.expr_start)
        .field("expr_end", &inner.expr_end)
        .field("comment_start", &inner.comment_start)
        .field("comment_end", &inner.comment_end)
        .finish()
}

#[derive(Debug, Default, Clone, Copy, Hash, PartialEq)]
#[cfg_attr(feature = "config", derive(serde_derive::Deserialize))]
pub struct SyntaxBuilder<'a> {
    pub name: &'a str,
    pub block_start: Option<&'a str>,
    pub block_end: Option<&'a str>,
    pub expr_start: Option<&'a str>,
    pub expr_end: Option<&'a str>,
    pub comment_start: Option<&'a str>,
    pub comment_end: Option<&'a str>,
}

impl<'a> SyntaxBuilder<'a> {
    pub fn to_syntax(&self) -> Result<Syntax<'a>, String> {
        let default = InnerSyntax::default();
        let syntax = Syntax(InnerSyntax {
            block_start: self.block_start.unwrap_or(default.block_start),
            block_end: self.block_end.unwrap_or(default.block_end),
            expr_start: self.expr_start.unwrap_or(default.expr_start),
            expr_end: self.expr_end.unwrap_or(default.expr_end),
            comment_start: self.comment_start.unwrap_or(default.comment_start),
            comment_end: self.comment_end.unwrap_or(default.comment_end),
        });

        for (s, k, is_closing) in [
            (syntax.block_start, "opening block", false),
            (syntax.block_end, "closing block", true),
            (syntax.expr_start, "opening expression", false),
            (syntax.expr_end, "closing expression", true),
            (syntax.comment_start, "opening comment", false),
            (syntax.comment_end, "closing comment", true),
        ] {
            if s.len() < 2 {
                return Err(format!(
                    "delimiters must be at least two characters long. \
                        The {k} delimiter ({s:?}) is too short",
                ));
            } else if s.len() > 32 {
                return Err(format!(
                    "delimiters must be at most 32 characters long. \
                        The {k} delimiter ({:?}...) is too long",
                    &s[..(16..=s.len())
                        .find(|&i| s.is_char_boundary(i))
                        .unwrap_or(s.len())],
                ));
            } else if s.chars().any(char::is_whitespace) {
                return Err(format!(
                    "delimiters may not contain white spaces. \
                        The {k} delimiter ({s:?}) contains white spaces",
                ));
            } else if is_closing
                && ['(', '-', '+', '~', '.', '>', '<', '&', '|', '!']
                    .contains(&s.chars().next().unwrap())
            {
                return Err(format!(
                    "closing delimiters may not start with operators. \
                        The {k} delimiter ({s:?}) starts with operator `{}`",
                    s.chars().next().unwrap(),
                ));
            }
        }

        for ((s1, k1), (s2, k2)) in [
            (
                (syntax.block_start, "block"),
                (syntax.expr_start, "expression"),
            ),
            (
                (syntax.block_start, "block"),
                (syntax.comment_start, "comment"),
            ),
            (
                (syntax.expr_start, "expression"),
                (syntax.comment_start, "comment"),
            ),
        ] {
            if s1.starts_with(s2) || s2.starts_with(s1) {
                let (s1, k1, s2, k2) = match s1.len() < s2.len() {
                    true => (s1, k1, s2, k2),
                    false => (s2, k2, s1, k1),
                };
                return Err(format!(
                    "an opening delimiter may not be the prefix of another delimiter. \
                        The {k1} delimiter ({s1:?}) clashes with the {k2} delimiter ({s2:?})",
                ));
            }
        }

        Ok(syntax)
    }
}

/// The nesting level of nodes and expressions.
///
/// The level counts down from [`Level::MAX_DEPTH`] to 0. Once the value would reach below 0,
/// [`Level::nest()`] / [`LevelGuard::nest()`] will return an error. The same [`Level`] instance is
/// shared across all usages in a [`Parsed::new()`] / [`Ast::from_str()`] call, using a reference
/// to an interior mutable counter.
#[derive(Debug, Clone)]
struct Level(Cell<usize>);

impl Default for Level {
    #[inline]
    fn default() -> Self {
        Self(Cell::new(Level::MAX_DEPTH))
    }
}

impl Level {
    const MAX_DEPTH: usize = 128;

    /// Acquire a [`LevelGuard`] without decrementing the counter, to be used with loops.
    fn guard(&self) -> LevelGuard<'_> {
        LevelGuard {
            level: self,
            count: 0,
        }
    }

    /// Decrement the remaining level counter, and return a [`LevelGuard`] that increments it again
    /// when it's dropped.
    fn nest<'a: 'l, 'l>(&self, i: &InputStream<'a, 'l>) -> ParseResult<'a, LevelGuard<'_>> {
        if let Some(new_level) = self.0.get().checked_sub(1) {
            self.0.set(new_level);
            Ok(LevelGuard {
                level: self,
                count: 1,
            })
        } else {
            Self::_fail(i)
        }
    }

    #[cold]
    #[inline(never)]
    fn _fail<'a: 'l, 'l, T>(i: &InputStream<'a, 'l>) -> ParseResult<'a, T> {
        let msg = "your template code is too deeply nested, or the last expression is too complex";
        Err(ErrorContext::new(msg, i).cut())
    }
}

/// Used to keep track how often [`LevelGuard::nest()`] was called and to re-increment the
/// remaining level counter when it is dropped / falls out of scope.
#[must_use]
struct LevelGuard<'l> {
    level: &'l Level,
    count: usize,
}

impl Drop for LevelGuard<'_> {
    fn drop(&mut self) {
        self.level.0.set(self.level.0.get() + self.count);
    }
}

impl LevelGuard<'_> {
    /// Used to decrement the level multiple times, e.g. for every iteration of a loop.
    fn nest<'a: 'l, 'l>(&mut self, i: &InputStream<'a, 'l>) -> ParseResult<'a, ()> {
        if let Some(new_level) = self.level.0.get().checked_sub(1) {
            self.level.0.set(new_level);
            self.count += 1;
            Ok(())
        } else {
            Level::_fail(i)
        }
    }
}

fn filter<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Filter<'a>> {
    preceded(('|', not('|')), cut_err(Filter::parse)).parse_next(i)
}

/// Returns the common parts of two paths.
///
/// The goal of this function is to reduce the path length based on the `base` argument
/// (generally the path where the program is running into). For example:
///
/// ```text
/// current dir: /a/b/c
/// path:        /a/b/c/d/e.txt
/// ```
///
/// `strip_common` will return `d/e.txt`.
#[must_use]
pub fn strip_common(base: &Path, path: &Path) -> String {
    let path = match path.canonicalize() {
        Ok(path) => path,
        Err(_) => return path.display().to_string(),
    };
    let mut components_iter = path.components().peekable();

    for current_path_component in base.components() {
        let Some(path_component) = components_iter.peek() else {
            return path.display().to_string();
        };
        if current_path_component != *path_component {
            break;
        }
        components_iter.next();
    }
    let path_parts = components_iter
        .map(|c| c.as_os_str().to_string_lossy())
        .collect::<Vec<_>>();
    if path_parts.is_empty() {
        path.display().to_string()
    } else {
        path_parts.join(std::path::MAIN_SEPARATOR_STR)
    }
}

#[inline]
pub(crate) fn can_be_variable_name(name: &str) -> bool {
    !matches!(name, "self" | "Self" | "super" | "crate")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntKind {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatKind {
    F16,
    F32,
    F64,
    F128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumKind {
    Int(IntKind),
    Float(FloatKind),
}

/// Primitive integer types. Also used as number suffixes.
const INTEGER_TYPES: &[(&str, IntKind)] = &[
    ("i8", IntKind::I8),
    ("i16", IntKind::I16),
    ("i32", IntKind::I32),
    ("i64", IntKind::I64),
    ("i128", IntKind::I128),
    ("isize", IntKind::Isize),
    ("u8", IntKind::U8),
    ("u16", IntKind::U16),
    ("u32", IntKind::U32),
    ("u64", IntKind::U64),
    ("u128", IntKind::U128),
    ("usize", IntKind::Usize),
];

/// Primitive floating point types. Also used as number suffixes.
const FLOAT_TYPES: &[(&str, FloatKind)] = &[
    ("f16", FloatKind::F16),
    ("f32", FloatKind::F32),
    ("f64", FloatKind::F64),
    ("f128", FloatKind::F128),
];

/// Primitive numeric types. Also used as number suffixes.
const NUM_TYPES: &[(&str, NumKind)] = &{
    let mut list = [("", NumKind::Int(IntKind::I8)); INTEGER_TYPES.len() + FLOAT_TYPES.len()];
    let mut i = 0;
    let mut o = 0;
    while i < INTEGER_TYPES.len() {
        let (name, value) = INTEGER_TYPES[i];
        list[o] = (name, NumKind::Int(value));
        i += 1;
        o += 1;
    }
    let mut i = 0;
    while i < FLOAT_TYPES.len() {
        let (name, value) = FLOAT_TYPES[i];
        list[o] = (name, NumKind::Float(value));
        i += 1;
        o += 1;
    }
    list
};

/// Complete list of named primitive types.
const PRIMITIVE_TYPES: &[&str] = &{
    let mut list = [""; NUM_TYPES.len() + 1];
    let mut i = 0;
    let mut o = 0;
    while i < NUM_TYPES.len() {
        list[o] = NUM_TYPES[i].0;
        i += 1;
        o += 1;
    }
    list[o] = "bool";
    list
};

const MAX_RUST_KEYWORD_LEN: usize = 8;

const RUST_KEYWORDS: &[&[[AsciiChar; MAX_RUST_KEYWORD_LEN]]; MAX_RUST_KEYWORD_LEN + 1] = &{
    const NO_KWS: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[];
    const KW2: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[
        AsciiStr::new_sized("as"),
        AsciiStr::new_sized("do"),
        AsciiStr::new_sized("fn"),
        AsciiStr::new_sized("if"),
        AsciiStr::new_sized("in"),
    ];
    const KW3: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[
        AsciiStr::new_sized("box"),
        AsciiStr::new_sized("dyn"),
        AsciiStr::new_sized("for"),
        AsciiStr::new_sized("gen"),
        AsciiStr::new_sized("let"),
        AsciiStr::new_sized("mod"),
        AsciiStr::new_sized("mut"),
        AsciiStr::new_sized("pub"),
        AsciiStr::new_sized("ref"),
        AsciiStr::new_sized("try"),
        AsciiStr::new_sized("use"),
    ];
    const KW4: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[
        AsciiStr::new_sized("else"),
        AsciiStr::new_sized("enum"),
        AsciiStr::new_sized("impl"),
        AsciiStr::new_sized("loop"),
        AsciiStr::new_sized("move"),
        AsciiStr::new_sized("priv"),
        AsciiStr::new_sized("self"),
        AsciiStr::new_sized("Self"),
        AsciiStr::new_sized("true"),
        AsciiStr::new_sized("type"),
    ];
    const KW5: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[
        AsciiStr::new_sized("async"),
        AsciiStr::new_sized("await"),
        AsciiStr::new_sized("break"),
        AsciiStr::new_sized("const"),
        AsciiStr::new_sized("crate"),
        AsciiStr::new_sized("false"),
        AsciiStr::new_sized("final"),
        AsciiStr::new_sized("macro"),
        AsciiStr::new_sized("match"),
        AsciiStr::new_sized("super"),
        AsciiStr::new_sized("trait"),
        AsciiStr::new_sized("union"),
        AsciiStr::new_sized("where"),
        AsciiStr::new_sized("while"),
        AsciiStr::new_sized("yield"),
    ];
    const KW6: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[
        AsciiStr::new_sized("become"),
        AsciiStr::new_sized("extern"),
        AsciiStr::new_sized("return"),
        AsciiStr::new_sized("static"),
        AsciiStr::new_sized("struct"),
        AsciiStr::new_sized("typeof"),
        AsciiStr::new_sized("unsafe"),
        AsciiStr::new_sized("caller"),
    ];
    const KW7: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[
        AsciiStr::new_sized("unsized"),
        AsciiStr::new_sized("virtual"),
    ];
    const KW8: &[[AsciiChar; MAX_RUST_KEYWORD_LEN]] = &[
        AsciiStr::new_sized("abstract"),
        AsciiStr::new_sized("continue"),
        AsciiStr::new_sized("override"),
    ];

    [NO_KWS, NO_KWS, KW2, KW3, KW4, KW5, KW6, KW7, KW8]
};

pub fn is_rust_keyword(ident: &str) -> bool {
    let ident_len = ident.len();
    if ident_len > MAX_RUST_KEYWORD_LEN {
        return false;
    }
    let kws = RUST_KEYWORDS[ident.len()];

    let mut padded_ident = [0; MAX_RUST_KEYWORD_LEN];
    padded_ident[..ident_len].copy_from_slice(ident.as_bytes());

    // Since the individual buckets are quite short, a linear search is faster than a binary search.
    for probe in kws {
        if padded_ident == *AsciiChar::slice_as_bytes(probe) {
            return true;
        }
    }
    false
}

macro_rules! cut_error {
    ($message:expr, $span:expr $(,)?) => {{
        use ::std::convert::Into;
        use ::std::option::Option::Some;
        use $crate::ErrorContext;

        $crate::cut_context_err(
            #[cold]
            #[inline(always)]
            move || ErrorContext {
                span: Into::into($span),
                message: Some(Into::into($message)),
            },
        )
    }};
}

pub(crate) use cut_error;

#[cold]
#[inline(never)]
fn cut_context_err<'a, T>(gen_err: impl FnOnce() -> ErrorContext) -> ParseResult<'a, T> {
    Err(ErrMode::Cut(gen_err()))
}

type HashSet<T> = std::collections::hash_set::HashSet<T, FxBuildHasher>;

#[cfg(test)]
mod test {
    use std::path::Path;

    use super::*;

    #[cfg(not(windows))]
    #[test]
    fn test_strip_common() {
        // Full path is returned instead of empty when the entire path is in common.
        assert_eq!(strip_common(Path::new("home"), Path::new("home")), "home");

        let cwd = std::env::current_dir().expect("current_dir failed");

        // We need actual existing paths for `canonicalize` to work, so let's do that.
        let entry = cwd
            .read_dir()
            .expect("read_dir failed")
            .filter_map(std::result::Result::ok)
            .find(|f| f.path().is_file())
            .expect("no entry");

        // Since they have the complete path in common except for the folder entry name, it should
        // return only the folder entry name.
        assert_eq!(
            strip_common(&cwd, &entry.path()),
            entry.file_name().to_string_lossy()
        );

        // In this case it cannot canonicalize `/a/b/c` so it returns the path as is.
        assert_eq!(strip_common(&cwd, Path::new("/a/b/c")), "/a/b/c");
    }

    #[track_caller]
    fn parse_peek<'a: 'l, 'l, T>(
        state: &'l State<'l>,
        parser: impl FnOnce(&mut InputStream<'a, 'l>) -> ParseResult<'a, T>,
        input: &'a str,
    ) -> ParseResult<'a, (&'a str, T)> {
        let mut i = InputStream {
            input: LocatingSlice::new(input),
            state,
        };
        let value = parser(&mut i)?;
        Ok((**i, value))
    }

    #[test]
    fn test_num_lit() {
        let s = State::default();

        // Should fail.
        assert!(parse_peek(&s, num_lit, ".").is_err());
        // Should succeed.
        assert_eq!(
            parse_peek(&s, num_lit, "1.2E-02").unwrap(),
            ("", Num::Float("1.2E-02", None))
        );
        assert_eq!(
            parse_peek(&s, num_lit, "4e3").unwrap(),
            ("", Num::Float("4e3", None)),
        );
        assert_eq!(
            parse_peek(&s, num_lit, "4e+_3").unwrap(),
            ("", Num::Float("4e+_3", None)),
        );
        // Not supported because Rust wants a number before the `.`.
        assert!(parse_peek(&s, num_lit, ".1").is_err());
        assert!(parse_peek(&s, num_lit, ".1E-02").is_err());
        // A `_` directly after the `.` denotes a field.
        assert_eq!(
            parse_peek(&s, num_lit, "1._0").unwrap(),
            ("._0", Num::Int("1", None))
        );
        assert_eq!(
            parse_peek(&s, num_lit, "1_.0").unwrap(),
            ("", Num::Float("1_.0", None))
        );
        // Not supported (voluntarily because of `1..` syntax).
        assert_eq!(
            parse_peek(&s, num_lit, "1.").unwrap(),
            (".", Num::Int("1", None))
        );
        assert_eq!(
            parse_peek(&s, num_lit, "1_.").unwrap(),
            (".", Num::Int("1_", None))
        );
        assert_eq!(
            parse_peek(&s, num_lit, "1_2.").unwrap(),
            (".", Num::Int("1_2", None))
        );
        // Numbers with suffixes
        assert_eq!(
            parse_peek(&s, num_lit, "-1usize").unwrap(),
            ("", Num::Int("-1", Some(IntKind::Usize)))
        );
        assert_eq!(
            parse_peek(&s, num_lit, "123_f32").unwrap(),
            ("", Num::Float("123_", Some(FloatKind::F32)))
        );
        assert_eq!(
            parse_peek(&s, num_lit, "1_.2_e+_3_f64|into_isize").unwrap(),
            (
                "|into_isize",
                Num::Float("1_.2_e+_3_", Some(FloatKind::F64))
            )
        );
        assert_eq!(
            parse_peek(&s, num_lit, "4e3f128").unwrap(),
            ("", Num::Float("4e3", Some(FloatKind::F128))),
        );
    }

    #[test]
    fn test_char_lit() {
        let lit = |s: &'static str| crate::CharLit {
            prefix: None,
            content: s,
        };
        let s = State::default();

        assert_eq!(parse_peek(&s, char_lit, "'a'").unwrap(), ("", lit("a")));
        assert_eq!(parse_peek(&s, char_lit, "'字'").unwrap(), ("", lit("字")));

        // Escaped single characters.
        assert_eq!(
            parse_peek(&s, char_lit, "'\\\"'").unwrap(),
            ("", lit("\\\""))
        );
        assert_eq!(parse_peek(&s, char_lit, "'\\''").unwrap(), ("", lit("\\'")));
        assert_eq!(parse_peek(&s, char_lit, "'\\t'").unwrap(), ("", lit("\\t")));
        assert_eq!(parse_peek(&s, char_lit, "'\\n'").unwrap(), ("", lit("\\n")));
        assert_eq!(parse_peek(&s, char_lit, "'\\r'").unwrap(), ("", lit("\\r")));
        assert_eq!(parse_peek(&s, char_lit, "'\\0'").unwrap(), ("", lit("\\0")));
        // Escaped ascii characters (up to `0x7F`).
        assert_eq!(
            parse_peek(&s, char_lit, "'\\x12'").unwrap(),
            ("", lit("\\x12"))
        );
        assert_eq!(
            parse_peek(&s, char_lit, "'\\x02'").unwrap(),
            ("", lit("\\x02"))
        );
        assert_eq!(
            parse_peek(&s, char_lit, "'\\x6a'").unwrap(),
            ("", lit("\\x6a"))
        );
        assert_eq!(
            parse_peek(&s, char_lit, "'\\x7F'").unwrap(),
            ("", lit("\\x7F"))
        );
        // Escaped unicode characters (up to `0x10FFFF`).
        assert_eq!(
            parse_peek(&s, char_lit, "'\\u{A}'").unwrap(),
            ("", lit("\\u{A}"))
        );
        assert_eq!(
            parse_peek(&s, char_lit, "'\\u{10}'").unwrap(),
            ("", lit("\\u{10}"))
        );
        assert_eq!(
            parse_peek(&s, char_lit, "'\\u{aa}'").unwrap(),
            ("", lit("\\u{aa}"))
        );
        assert_eq!(
            parse_peek(&s, char_lit, "'\\u{10FFFF}'").unwrap(),
            ("", lit("\\u{10FFFF}"))
        );

        // Check with `b` prefix.
        assert_eq!(
            parse_peek(&s, char_lit, "b'a'").unwrap(),
            (
                "",
                crate::CharLit {
                    prefix: Some(crate::CharPrefix::Binary),
                    content: "a"
                }
            )
        );

        // Should fail.
        assert!(parse_peek(&s, char_lit, "''").is_err());
        assert!(parse_peek(&s, char_lit, "'\\o'").is_err());
        assert!(parse_peek(&s, char_lit, "'\\x'").is_err());
        assert!(parse_peek(&s, char_lit, "'\\x1'").is_err());
        assert!(parse_peek(&s, char_lit, "'\\x80'").is_err());
        assert!(parse_peek(&s, char_lit, "'\\u'").is_err());
        assert!(parse_peek(&s, char_lit, "'\\u{}'").is_err());
        assert!(parse_peek(&s, char_lit, "'\\u{110000}'").is_err());
    }

    #[test]
    fn test_str_lit() {
        let s = State::default();
        assert_eq!(
            parse_peek(&s, str_lit, r#"b"hello""#).unwrap(),
            (
                "",
                StrLit {
                    prefix: Some(StrPrefix::Binary),
                    content: "hello",
                    contains_null: false,
                    contains_unicode_character: false,
                    contains_unicode_escape: false,
                    contains_high_ascii: false,
                }
            )
        );
        assert_eq!(
            parse_peek(&s, str_lit, r#"c"hello""#).unwrap(),
            (
                "",
                StrLit {
                    prefix: Some(StrPrefix::CLike),
                    content: "hello",
                    contains_null: false,
                    contains_unicode_character: false,
                    contains_unicode_escape: false,
                    contains_high_ascii: false,
                }
            )
        );
        assert!(parse_peek(&s, str_lit, r#"d"hello""#).is_err());
    }

    #[test]
    fn test_is_rust_keyword() {
        assert!(is_rust_keyword("caller"));
        assert!(is_rust_keyword("super"));
        assert!(is_rust_keyword("become"));
        assert!(!is_rust_keyword("supeeeer"));
        assert!(!is_rust_keyword("sur"));
    }

    #[test]
    fn test_check_base_digits() {
        assert!(check_base_digits("10", 2, 0..1).is_ok());
        assert!(check_base_digits("13", 2, 0..1).is_err());
        assert!(check_base_digits("13", 8, 0..1).is_ok());
        assert!(check_base_digits("79", 8, 0..1).is_err());
        // Checking that it's case insensitive.
        assert!(check_base_digits("13F", 16, 0..1).is_ok());
        assert!(check_base_digits("13f", 16, 0..1).is_ok());
        // Checking that `_` is allowed.
        assert!(check_base_digits("13_f", 16, 0..1).is_ok());
    }
}
