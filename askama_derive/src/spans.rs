mod rustc_literal_escaper;

use std::ops::Range;

use proc_macro2::{Literal, Span};
use syn::LitStr;

use crate::CompileError;
use crate::spans::rustc_literal_escaper::unescape;

#[allow(private_interfaces)] // don't look behind the curtain
#[derive(Clone, Debug)]
pub(crate) enum SourceSpan {
    Source(SpannedSource),
    // TODO: transclude source file
    Path(Span),
    // TODO: implement for "code-in-doc"
    #[cfg_attr(not(feature = "code-in-doc"), allow(dead_code))]
    Span(Span),
}

impl SourceSpan {
    pub(crate) fn from_source(source: LitStr) -> Result<(String, Self), CompileError> {
        let (source, span) = SpannedSource::from_source(source)?;
        Ok((source, Self::Source(span)))
    }

    pub(crate) fn config_span(&self) -> Span {
        match self {
            SourceSpan::Source(literal) => literal.config_span(),
            SourceSpan::Path(span) | SourceSpan::Span(span) => *span,
        }
    }

    pub(crate) fn content_subspan(&self, bytes: Range<usize>) -> Option<Span> {
        match self {
            Self::Source(source) => source.content_subspan(bytes),
            Self::Path(_) | Self::Span(_) => None,
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

    fn from_source(source: LitStr) -> Result<(String, Self), CompileError> {
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
