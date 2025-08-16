mod rustc_literal_escaper;

use std::ops::Range;

use proc_macro2::{Literal, Span};
use syn::LitStr;

use crate::CompileError;
use crate::spans::rustc_literal_escaper::unescape;

#[allow(private_interfaces)] // don't look behind the curtain
#[derive(Clone, Debug)]
pub(crate) enum SourceSpan {
    Empty(Span),
    Source(SpannedSource),
    #[cfg(feature = "external-sources")]
    Path(SpannedPath),
    // TODO: implement for "code-in-doc"
    #[cfg_attr(not(feature = "code-in-doc"), allow(dead_code))]
    CodeInDoc(Span),
}

impl SourceSpan {
    pub(crate) fn empty() -> SourceSpan {
        Self::Empty(Span::call_site())
    }

    pub(crate) fn from_source(source: LitStr) -> Result<(String, Self), CompileError> {
        let (source, span) = SpannedSource::new(source)?;
        Ok((source, Self::Source(span)))
    }

    #[cfg(feature = "external-sources")]
    pub(crate) fn from_path(config: LitStr) -> Result<SourceSpan, CompileError> {
        Ok(Self::Path(SpannedPath::new(config)?))
    }

    pub(crate) fn config_span(&self) -> Span {
        match self {
            SourceSpan::Source(v) => v.config_span(),
            #[cfg(feature = "external-sources")]
            SourceSpan::Path(v) => v.config_span(),
            SourceSpan::CodeInDoc(span) | Self::Empty(span) => *span,
        }
    }

    pub(crate) fn content_subspan(&self, bytes: Range<usize>) -> Option<Span> {
        match self {
            Self::Source(v) => v.content_subspan(bytes),
            #[cfg(feature = "external-sources")]
            SourceSpan::Path(v) => v.content_subspan(bytes),
            Self::CodeInDoc(_) | Self::Empty(_) => None,
        }
    }

    #[cfg(all(feature = "external-sources", feature = "nightly-spans"))]
    pub(crate) fn resolve_path(&self, path: &str) {
        if let Self::Path(v) = self {
            v.resolve_path(path);
        }
    }
}

#[derive(Clone, Debug)]
struct SpannedSource {
    literal: Literal,
    positions: Vec<(usize, usize)>,
}

impl SpannedSource {
    fn config_span(&self) -> Span {
        self.literal.span()
    }

    fn content_subspan(&self, bytes: Range<usize>) -> Option<Span> {
        let start = self.find_position(bytes.start);
        let end = self.find_position(bytes.end);
        self.literal.subspan(start..end)
    }

    fn find_position(&self, position: usize) -> usize {
        match self
            .positions
            .binary_search_by_key(&position, |&(pos, _)| pos)
        {
            Ok(idx) => self.positions[idx].1,
            Err(idx) => {
                let (start_out, start_in) = self.positions[idx - 1];
                start_in + (position - start_out)
            }
        }
    }

    fn new(source: LitStr) -> Result<(String, Self), CompileError> {
        let literal = source.token();
        let unparsed = literal.to_string();
        let result = if unparsed.starts_with('r') {
            Self::from_raw(&unparsed, literal)
        } else {
            Self::from_string(&unparsed, literal)
        };
        result.map_err(|msg| CompileError::no_file_info(msg, Some(source.span())))
    }

    fn from_raw(unparsed: &str, literal: Literal) -> Result<(String, Self), &'static str> {
        let start = unparsed
            .find('"')
            .ok_or("raw string literal should contain `\"` at its start")?
            + 1;
        let end = unparsed
            .rfind('"')
            .ok_or("raw string literal should contain `\"` at its end")?;

        let source = unparsed[start..end].to_owned();
        let span = Self {
            literal,
            positions: vec![(0, start), (source.len(), end)],
        };
        Ok((source, span))
    }

    fn from_string(unparsed: &str, literal: Literal) -> Result<(String, Self), &'static str> {
        let start = unparsed
            .find('"')
            .ok_or("string literal should have `\"` at its start")?
            + 1;
        let end = unparsed
            .rfind('"')
            .ok_or("string literal should have `\"` at its end")?;
        let unparsed = &unparsed[start..end];

        let mut source = String::with_capacity(unparsed.len());
        let mut positions = vec![(0, start)];
        let mut expected_start = 0usize;
        let result = unescape(unparsed, |range, c| {
            if range.start != expected_start {
                positions.push((source.len(), range.start + start));
                expected_start = range.start;
            }
            expected_start += c.len_utf8();

            source.push(c);
        });
        if result.is_err() {
            return Err("input string literal should be well-formed");
        }

        positions.push((source.len(), end));
        Ok((source, Self { literal, positions }))
    }
}

#[cfg(feature = "external-sources")]
#[cfg_attr(not(feature = "nightly-spans"), derive(Debug, Clone))]
struct SpannedPath {
    config: Span,
    #[cfg(feature = "nightly-spans")]
    literal: std::cell::Cell<Option<Literal>>,
}

#[cfg(feature = "external-sources")]
impl SpannedPath {
    fn new(config: LitStr) -> Result<Self, CompileError> {
        Ok(Self {
            config: config.span(),
            #[cfg(feature = "nightly-spans")]
            literal: std::cell::Cell::new(None),
        })
    }

    #[inline]
    fn config_span(&self) -> Span {
        self.config
    }
}

#[cfg(all(feature = "external-sources", not(feature = "nightly-spans")))]
impl SpannedPath {
    #[inline]
    fn content_subspan(&self, _: Range<usize>) -> Option<Span> {
        None
    }
}

#[cfg(all(feature = "external-sources", feature = "nightly-spans"))]
const _: () = {
    use std::cell::Cell;
    use std::fmt;

    use proc_macro::TokenStream as TokenStream1;
    use proc_macro2::{TokenStream as TokenStream2, TokenTree};
    use quote::quote_spanned;

    impl fmt::Debug for SpannedPath {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("SpannedPath")
                .field("config", &self.config)
                .field("span", &self.literal_span())
                .finish()
        }
    }

    impl Clone for SpannedPath {
        fn clone(&self) -> Self {
            Self {
                config: self.config.clone(),
                literal: Cell::new(self.literal()),
            }
        }
    }

    impl SpannedPath {
        fn content_subspan(&self, bytes: Range<usize>) -> Option<Span> {
            let literal = self.literal.take()?;
            let span = literal.subspan(bytes);
            self.literal.set(Some(literal));
            span
        }

        fn literal_span(&self) -> Option<Span> {
            let literal = self.literal.take()?;
            let span = literal.span();
            self.literal.set(Some(literal));
            Some(span)
        }

        fn literal(&self) -> Option<Literal> {
            let literal = self.literal.take()?;
            self.literal.set(Some(literal.clone()));
            Some(literal)
        }

        fn resolve_path(&self, path: &str) {
            if proc_macro::is_available()
                && let Ok(stream) = TokenStream1::from(quote_spanned! {
                    // In token expansion, `extern crate some_name` does not work. Only crates that
                    // were imported output _before_ the `#[derive(Template)]` invocation can be
                    // used.
                    //
                    // In the macro expansion, using an identifier that was not defined will emit
                    // an error `Diagnostic`. We cannot un-emit a `Diagnostic`, so this would be a
                    // hard compilation error.
                    //
                    // At `call_site()`, macro `include_str!` may not exist (`#[no_implicit_prelude]`),
                    // or may be shadowed. The symbol `askama` may not exist or be shadowed, too.
                    //
                    // At `def_site()`, the we know that the macro exists. We do not know if `core`
                    // or `::core` exists, but the unprefixed macro `include_str!` does exist, and
                    // it cannot be shadowed from outside of this function call.
                    //
                    // <https://doc.rust-lang.org/reference/names/preludes.html#r-names.preludes.lang.entities>
                    proc_macro::Span::def_site().into() => include_str!(#path)
                })
                .expand_expr()
                && let Some(TokenTree::Literal(literal)) =
                    TokenStream2::from(stream).into_iter().next()
            {
                self.literal.set(Some(literal));
            }
        }
    }
};
