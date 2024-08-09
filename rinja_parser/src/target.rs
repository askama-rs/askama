use winnow::combinator::{alt, opt, peek, preceded, separated1};
use winnow::token::one_of;
use winnow::{Parser, unpeek};

use crate::{
    CharLit, ErrorContext, InputParseResult, Num, ParseErr, PathOrIdentifier, State, StrLit,
    WithSpan, bool_lit, char_lit, identifier, keyword, num_lit, path_or_identifier, str_lit, ws,
};

#[derive(Clone, Debug, PartialEq)]
pub enum Target<'a> {
    Name(&'a str),
    Tuple(Vec<&'a str>, Vec<Target<'a>>),
    Array(Vec<&'a str>, Vec<Target<'a>>),
    Struct(Vec<&'a str>, Vec<(&'a str, Target<'a>)>),
    NumLit(&'a str, Num<'a>),
    StrLit(StrLit<'a>),
    CharLit(CharLit<'a>),
    BoolLit(&'a str),
    Path(Vec<&'a str>),
    OrChain(Vec<Target<'a>>),
    Placeholder(WithSpan<'a, ()>),
    /// The `Option` is the variable name (if any) in `var_name @ ..`.
    Rest(WithSpan<'a, Option<&'a str>>),
}

impl<'a> Target<'a> {
    /// Parses multiple targets with `or` separating them
    pub(super) fn parse(i: &'a str, s: &State<'_>) -> InputParseResult<'a, Self> {
        separated1(
            unpeek(|i| s.nest(i, unpeek(|i| Self::parse_one(i, s)))),
            ws("or"),
        )
        .map(|v: Vec<_>| v)
        .map(|mut opts| match opts.len() {
            1 => opts.pop().unwrap(),
            _ => Self::OrChain(opts),
        })
        .parse_peek(i)
    }

    /// Parses a single target without an `or`, unless it is wrapped in parentheses.
    fn parse_one(i: &'a str, s: &State<'_>) -> InputParseResult<'a, Self> {
        let mut opt_opening_paren = opt(ws('(')).map(|o| o.is_some());
        let mut opt_opening_brace = opt(ws('{')).map(|o| o.is_some());
        let mut opt_opening_bracket = opt(ws('[')).map(|o| o.is_some());

        let (i, lit) = opt(unpeek(Self::lit)).parse_peek(i)?;
        if let Some(lit) = lit {
            return Ok((i, lit));
        }

        // match tuples and unused parentheses
        let (i, target_is_tuple) = opt_opening_paren.parse_peek(i)?;
        if target_is_tuple {
            let (i, (singleton, mut targets)) =
                collect_targets(i, ')', unpeek(|i| Self::unnamed(i, s)))?;
            if singleton {
                return Ok((i, targets.pop().unwrap()));
            }
            return Ok((
                i,
                Self::Tuple(Vec::new(), only_one_rest_pattern(targets, false, "tuple")?),
            ));
        }
        let (i, target_is_array) = opt_opening_bracket.parse_peek(i)?;
        if target_is_array {
            let (i, (singleton, mut targets)) =
                collect_targets(i, ']', unpeek(|i| Self::unnamed(i, s)))?;
            if singleton {
                return Ok((i, targets.pop().unwrap()));
            }
            return Ok((
                i,
                Self::Array(Vec::new(), only_one_rest_pattern(targets, true, "array")?),
            ));
        }

        let path = unpeek(path_or_identifier).try_map(|v| match v {
            PathOrIdentifier::Path(v) => Ok(v),
            PathOrIdentifier::Identifier(v) => Err(v),
        });

        // match structs
        let (i, path) = opt(path).parse_peek(i)?;
        if let Some(path) = path {
            let i_before_matching_with = i;
            let (i, _) = opt(ws(keyword("with"))).parse_peek(i)?;

            let (i, is_unnamed_struct) = opt_opening_paren.parse_peek(i)?;
            if is_unnamed_struct {
                let (i, (_, targets)) = collect_targets(i, ')', unpeek(|i| Self::unnamed(i, s)))?;
                return Ok((
                    i,
                    Self::Tuple(path, only_one_rest_pattern(targets, false, "struct")?),
                ));
            }

            let (i, is_named_struct) = opt_opening_brace.parse_peek(i)?;
            if is_named_struct {
                let (i, (_, targets)) = collect_targets(i, '}', unpeek(|i| Self::named(i, s)))?;
                return Ok((i, Self::Struct(path, targets)));
            }

            return Ok((i_before_matching_with, Self::Path(path)));
        }

        // neither literal nor struct nor path
        let i_before_identifier = i;
        let (i, name) = identifier.parse_peek(i)?;
        let target = match name {
            "_" => Self::Placeholder(WithSpan::new((), i_before_identifier)),
            _ => verify_name(i_before_identifier, name)?,
        };
        Ok((i, target))
    }

    fn lit(i: &'a str) -> InputParseResult<'a, Self> {
        alt((
            unpeek(str_lit).map(Self::StrLit),
            unpeek(char_lit).map(Self::CharLit),
            unpeek(num_lit)
                .with_recognized()
                .map(|(num, full)| Target::NumLit(full, num)),
            unpeek(bool_lit).map(Self::BoolLit),
        ))
        .parse_peek(i)
    }

    fn unnamed(i: &'a str, s: &State<'_>) -> InputParseResult<'a, Self> {
        alt((unpeek(Self::rest), unpeek(|i| Self::parse(i, s)))).parse_peek(i)
    }

    fn named(i: &'a str, s: &State<'_>) -> InputParseResult<'a, (&'a str, Self)> {
        let start = i;
        let (i, rest) = opt(unpeek(Self::rest).with_recognized()).parse_peek(i)?;
        if let Some(rest) = rest {
            let (i, chr) = peek(ws(opt(one_of([',', ':'])))).parse_peek(i)?;
            if let Some(chr) = chr {
                return Err(winnow::error::ErrMode::Cut(ErrorContext::new(
                    format!(
                        "unexpected `{chr}` character after `..`\n\
                         note that in a named struct, `..` must come last to ignore other members"
                    ),
                    i,
                )));
            }
            if let Target::Rest(ref s) = rest.0 {
                if s.inner.is_some() {
                    return Err(winnow::error::ErrMode::Cut(ErrorContext::new(
                        "`@ ..` cannot be used in struct",
                        s.span,
                    )));
                }
            }
            return Ok((i, (rest.1, rest.0)));
        }

        let i = start;
        let (i, (src, target)) = (
            identifier,
            opt(preceded(ws(':'), unpeek(|i| Self::parse(i, s)))),
        )
            .parse_peek(i)?;

        if src == "_" {
            let i = start;
            return Err(winnow::error::ErrMode::Cut(ErrorContext::new(
                "cannot use placeholder `_` as source in named struct",
                i,
            )));
        }

        let target = match target {
            Some(target) => target,
            None => verify_name(start, src)?,
        };
        Ok((i, (src, target)))
    }

    fn rest(i: &'a str) -> InputParseResult<'a, Self> {
        let start = i;
        let (i, (ident, _)) = (opt((identifier, ws('@'))), "..").parse_peek(i)?;
        Ok((
            i,
            Self::Rest(WithSpan::new(ident.map(|(ident, _)| ident), start)),
        ))
    }
}

fn verify_name<'a>(
    input: &'a str,
    name: &'a str,
) -> Result<Target<'a>, winnow::error::ErrMode<ErrorContext<'a>>> {
    match name {
        "self" | "writer" => Err(winnow::error::ErrMode::Cut(ErrorContext::new(
            format!("cannot use `{name}` as a name"),
            input,
        ))),
        _ => Ok(Target::Name(name)),
    }
}

fn collect_targets<'a, T>(
    i: &'a str,
    delim: char,
    one: impl Parser<&'a str, T, ErrorContext<'a>>,
) -> InputParseResult<'a, (bool, Vec<T>)> {
    let opt_comma = ws(opt(',')).map(|o| o.is_some());
    let mut opt_end = ws(opt(one_of(delim))).map(|o| o.is_some());

    let (i, has_end) = opt_end.parse_peek(i)?;
    if has_end {
        return Ok((i, (false, Vec::new())));
    }

    let (i, targets) = opt(separated1(one, ws(',')).map(|v: Vec<_>| v)).parse_peek(i)?;
    let Some(targets) = targets else {
        return Err(winnow::error::ErrMode::Cut(ErrorContext::new(
            "expected comma separated list of members",
            i,
        )));
    };

    let (i, (has_comma, has_end)) = (opt_comma, opt_end).parse_peek(i)?;
    if !has_end {
        let msg = match has_comma {
            true => format!("expected member, or `{delim}` as terminator"),
            false => format!("expected `,` for more members, or `{delim}` as terminator"),
        };
        return Err(winnow::error::ErrMode::Cut(ErrorContext::new(msg, i)));
    }

    let singleton = !has_comma && targets.len() == 1;
    Ok((i, (singleton, targets)))
}

fn only_one_rest_pattern<'a>(
    targets: Vec<Target<'a>>,
    allow_named_rest: bool,
    type_kind: &str,
) -> Result<Vec<Target<'a>>, ParseErr<'a>> {
    let mut found_rest = false;

    for target in &targets {
        if let Target::Rest(s) = target {
            if !allow_named_rest && s.inner.is_some() {
                return Err(winnow::error::ErrMode::Cut(ErrorContext::new(
                    "`@ ..` is only allowed in slice patterns",
                    s.span,
                )));
            }
            if found_rest {
                return Err(winnow::error::ErrMode::Cut(ErrorContext::new(
                    format!("`..` can only be used once per {type_kind} pattern"),
                    s.span,
                )));
            }
            found_rest = true;
        }
    }
    Ok(targets)
}
