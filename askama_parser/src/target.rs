use winnow::combinator::{alt, opt, peek, preceded, separated, terminated};
use winnow::error::ErrMode;
use winnow::stream::{Location, Stream};
use winnow::token::one_of;
use winnow::{ModalParser, Parser};

use crate::{
    CharLit, ErrorContext, InputStream, Num, ParseErr, ParseResult, PathComponent,
    PathOrIdentifier, Span, State, StrLit, WithSpan, bool_lit, can_be_variable_name, char_lit,
    cut_error, identifier, is_rust_keyword, keyword, num_lit, path_or_identifier, str_lit, ws,
};

#[derive(Clone, Debug, PartialEq)]
pub enum Target<'a> {
    Name(WithSpan<&'a str>),
    Tuple(WithSpan<(Vec<PathComponent<'a>>, Vec<Target<'a>>)>),
    Array(WithSpan<Vec<Target<'a>>>),
    Struct(WithSpan<(Vec<PathComponent<'a>>, Vec<NamedTarget<'a>>)>),
    NumLit(WithSpan<&'a str>, Num<'a>),
    StrLit(WithSpan<StrLit<'a>>),
    CharLit(WithSpan<CharLit<'a>>),
    BoolLit(WithSpan<&'a str>),
    Path(WithSpan<Vec<PathComponent<'a>>>),
    OrChain(WithSpan<Vec<Target<'a>>>),
    Placeholder(WithSpan<()>),
    /// The `Option` is the variable name (if any) in `var_name @ ..`.
    Rest(WithSpan<Option<WithSpan<&'a str>>>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct NamedTarget<'a> {
    pub src: WithSpan<&'a str>,
    pub dest: Target<'a>,
}

impl<'a> From<(WithSpan<&'a str>, Target<'a>)> for NamedTarget<'a> {
    #[inline]
    fn from((src, dest): (WithSpan<&'a str>, Target<'a>)) -> Self {
        Self { src, dest }
    }
}

impl<'a> Target<'a> {
    pub fn span(&self) -> Span {
        match self {
            Target::Name(v) => v.span(),
            Target::Tuple(v) => v.span(),
            Target::Array(v) => v.span(),
            Target::Struct(v) => v.span(),
            Target::NumLit(v, _) => v.span(),
            Target::StrLit(v) => v.span(),
            Target::CharLit(v) => v.span(),
            Target::BoolLit(v) => v.span(),
            Target::Path(v) => v.span(),
            Target::OrChain(v) => v.span(),
            Target::Placeholder(v) => v.span(),
            Target::Rest(v) => v.span(),
        }
    }

    /// Parses multiple targets with `or` separating them
    pub(super) fn parse(i: &mut InputStream<'a>, s: &State<'_, '_>) -> ParseResult<'a, Self> {
        enum OneOrMany<'a> {
            One(Target<'a>),
            Many(Vec<Target<'a>>),
        }

        let mut or_more = opt(preceded(ws(keyword("or")), |i: &mut _| {
            Self::parse_one(i, s)
        }));
        let one_or_many = |i: &mut _| {
            let target = Self::parse_one(i, s)?;
            let Some(snd_target) = or_more.parse_next(i)? else {
                return Ok(OneOrMany::One(target));
            };

            let mut targets = vec![target, snd_target];
            while let Some(target) = or_more.parse_next(i)? {
                targets.push(target);
            }
            Ok(OneOrMany::Many(targets))
        };

        let _level_guard = s.level.nest(i)?;
        let (inner, span) = one_or_many.with_span().parse_next(i)?;
        match inner {
            OneOrMany::One(target) => Ok(target),
            OneOrMany::Many(targets) => Ok(Self::OrChain(WithSpan::new(targets, span))),
        }
    }

    /// Parses a single target without an `or`, unless it is wrapped in parentheses.
    fn parse_one(i: &mut InputStream<'a>, s: &State<'_, '_>) -> ParseResult<'a, Self> {
        let mut opt_opening_paren = opt(ws('(').span()).map(|o| o.is_some());
        let mut opt_opening_brace = opt(ws('{').span()).map(|o| o.is_some());
        let mut opt_opening_bracket = opt(ws('[').span()).map(|o| o.is_some());

        let lit = ws(opt(Self::lit)).parse_next(i)?;
        if let Some(lit) = lit {
            return Ok(lit);
        }

        let start = i.current_token_start();

        // match tuples
        let target_is_tuple = opt_opening_paren.parse_next(i)?;
        if target_is_tuple {
            let (is_singleton, mut targets) =
                collect_targets(i, ')', |i: &mut _| Self::unnamed(i, s))?;
            if is_singleton && let Some(target) = targets.pop() {
                return Ok(target);
            }

            let range = start..i.current_token_start();
            let targets = only_one_rest_pattern(targets, false, "tuple")?;
            return Ok(Self::Tuple(WithSpan::new((Vec::new(), targets), range)));
        }

        // match array
        let target_is_array = opt_opening_bracket.parse_next(i)?;
        if target_is_array {
            let targets = collect_targets(i, ']', |i: &mut _| Self::unnamed(i, s))?.1;
            let inner = only_one_rest_pattern(targets, true, "array")?;
            let range = start..i.current_token_start();
            return Ok(Self::Array(WithSpan::new(inner, range)));
        }

        // match structs
        let path = (|i: &mut _| path_or_identifier(i, s.level)).verify_map(|r| match r {
            PathOrIdentifier::Path(v) => Some(v),
            PathOrIdentifier::Identifier(_) => None,
        });
        let path = opt(path.with_span()).parse_next(i)?;
        if let Some((path, path_span)) = path {
            let i_before_matching_with = i.checkpoint();
            let _ = opt(ws(keyword("with"))).parse_next(i)?;

            let is_unnamed_struct = opt_opening_paren.parse_next(i)?;
            if is_unnamed_struct {
                let targets = collect_targets(i, ')', |i: &mut _| Self::unnamed(i, s))?.1;
                let inner = only_one_rest_pattern(targets, false, "struct")?;
                return Ok(Self::Tuple(WithSpan::new((path, inner), path_span)));
            }

            let is_named_struct = opt_opening_brace.parse_next(i)?;
            if is_named_struct {
                let targets = collect_targets(i, '}', |i: &mut _| Self::named(i, s))?.1;
                return Ok(Self::Struct(WithSpan::new((path, targets), path_span)));
            }

            if let [arg] = path.as_slice() {
                // If the path only contains one item, we need to check the name.
                if !can_be_variable_name(*arg.name) {
                    return cut_error!(
                        format!(
                            "`{}` cannot be used as an identifier",
                            arg.name.escape_debug()
                        ),
                        arg.name.span
                    );
                }
            } else {
                // Otherwise we need to check every element but the first.
                if let Some(arg) = path.iter().skip(1).find(|n| !can_be_variable_name(*n.name)) {
                    return cut_error!(
                        format!(
                            "`{}` cannot be used as an identifier",
                            arg.name.escape_debug()
                        ),
                        arg.name.span
                    );
                }
            }

            i.reset(&i_before_matching_with);
            return Ok(Self::Path(WithSpan::new(path, path_span)));
        }

        // neither literal nor struct nor path
        let (name, span) = identifier.with_span().parse_next(i)?;
        match name {
            "_" => Ok(Self::Placeholder(WithSpan::new((), span))),
            _ => verify_name(WithSpan::new(name, span)),
        }
    }

    fn lit(i: &mut InputStream<'a>) -> ParseResult<'a, Self> {
        enum Lit<'a> {
            Str(StrLit<'a>),
            Bool(&'a str),
            Char(CharLit<'a>),
            Num(&'a str, Num<'a>),
        }

        let p = alt((
            str_lit.map(Lit::Str),
            char_lit.map(Lit::Char),
            bool_lit.map(Lit::Bool),
            num_lit.with_taken().map(|(num, full)| Lit::Num(full, num)),
        ));
        let (inner, span) = p.with_span().parse_next(i)?;
        let span = Span::new(span);
        match inner {
            Lit::Str(v) => Ok(Target::StrLit(WithSpan::new(v, span))),
            Lit::Bool(v) => Ok(Target::BoolLit(WithSpan::new(v, span))),
            Lit::Char(v) => Ok(Target::CharLit(WithSpan::new(v, span))),
            Lit::Num(v, num) => Ok(Target::NumLit(WithSpan::new(v, span), num)),
        }
    }

    fn unnamed(i: &mut InputStream<'a>, s: &State<'_, '_>) -> ParseResult<'a, Self> {
        alt((Self::rest, |i: &mut _| Self::parse(i, s))).parse_next(i)
    }

    fn named<O: From<(WithSpan<&'a str>, Self)>>(
        i: &mut InputStream<'a>,
        s: &State<'_, '_>,
    ) -> ParseResult<'a, O> {
        if let Some(rest) = opt(Self::rest_inner).parse_next(i)? {
            let chr = peek(ws(opt(one_of([',', ':']).with_span()))).parse_next(i)?;
            if let Some((chr, span)) = chr {
                return cut_error!(
                    format!(
                        "unexpected `{}` character after `..`\n\
                         note that in a named struct, `..` must come last to ignore other members",
                        chr.escape_debug()
                    ),
                    span,
                );
            }
            if rest.inner.is_some() {
                return cut_error!("`@ ..` cannot be used in struct", rest.span);
            }
            Ok((WithSpan::new("..", rest.span), Target::Rest(rest)).into())
        } else {
            let ((src, span), target) = (
                identifier.with_span(),
                opt(preceded(ws(':'), |i: &mut _| Self::parse(i, s))),
            )
                .parse_next(i)?;

            let src = WithSpan::new(src, span);
            if *src == "_" {
                return cut_error!(
                    "cannot use placeholder `_` as source in named struct",
                    src.span,
                );
            }

            let target = match target {
                Some(target) => target,
                None => verify_name(src)?,
            };
            Ok((src, target).into())
        }
    }

    fn rest(i: &mut InputStream<'a>) -> ParseResult<'a, Self> {
        Self::rest_inner.map(Self::Rest).parse_next(i)
    }

    fn rest_inner(i: &mut InputStream<'a>) -> ParseResult<'a, WithSpan<Option<WithSpan<&'a str>>>> {
        let p = |i: &mut _| {
            let id =
                terminated(opt(terminated(identifier.with_span(), ws('@'))), "..").parse_next(i)?;
            Ok(id.map(|(id, span)| WithSpan::new(id, span)))
        };
        let (id, span) = ws(p.with_span()).parse_next(i)?;
        Ok(WithSpan::new(id, span))
    }
}

fn verify_name<'a>(name: WithSpan<&'a str>) -> Result<Target<'a>, ErrMode<ErrorContext>> {
    if !can_be_variable_name(*name) {
        cut_error!(
            format!("`{}` cannot be used as an identifier", name.escape_debug()),
            name.span,
        )
    } else if is_rust_keyword(*name) {
        cut_error!(
            format!(
                "cannot use `{}` as a name: it is a rust keyword",
                name.escape_debug(),
            ),
            name.span,
        )
    } else if name.starts_with("__askama") {
        cut_error!(
            format!(
                "cannot use `{}` as a name: it is reserved for `askama`",
                name.escape_debug()
            ),
            name.span,
        )
    } else {
        Ok(Target::Name(name))
    }
}

fn collect_targets<'a, T>(
    i: &mut InputStream<'a>,
    delim: char,
    one: impl ModalParser<InputStream<'a>, T, ErrorContext>,
) -> ParseResult<'a, (bool, Vec<T>)> {
    let opt_comma = ws(opt(',')).map(|o| o.is_some());
    let mut opt_end = ws(opt(one_of(delim))).map(|o| o.is_some());

    let has_end = opt_end.parse_next(i)?;
    if has_end {
        return Ok((false, Vec::new()));
    }

    let (targets, span) = opt(separated(1.., one, ws(',')).map(|v: Vec<_>| v))
        .with_span()
        .parse_next(i)?;
    let Some(targets) = targets else {
        return cut_error!("expected comma separated list of members", span);
    };

    let (has_comma, has_end) = (opt_comma, opt_end).parse_next(i)?;
    if !has_end {
        let delim = delim.escape_debug();
        return cut_error!(
            match has_comma {
                true => format!("expected member, or `{delim}` as terminator"),
                false => format!("expected `,` for more members, or `{delim}` as terminator"),
            },
            *i
        );
    }

    let singleton = !has_comma && targets.len() == 1;
    Ok((singleton, targets))
}

fn only_one_rest_pattern<'a>(
    targets: Vec<Target<'a>>,
    allow_named_rest: bool,
    type_kind: &str,
) -> Result<Vec<Target<'a>>, ParseErr<'a>> {
    let mut found_rest = false;
    for target in &targets {
        if let Target::Rest(s) = target {
            if !allow_named_rest && s.is_some() {
                return cut_error!("`@ ..` is only allowed in slice patterns", s.span);
            } else if found_rest {
                return cut_error!(
                    format!("`..` can only be used once per {type_kind} pattern"),
                    s.span,
                );
            } else {
                found_rest = true;
            }
        }
    }
    Ok(targets)
}
