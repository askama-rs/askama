use std::collections::HashSet;
use std::str;

use winnow::Parser;
use winnow::ascii::digit1;
use winnow::combinator::{
    alt, cut_err, empty, fail, not, opt, peek, preceded, repeat, separated, terminated,
};
use winnow::error::{ErrMode, ParserError as _};
use winnow::token::take_until;

use crate::node::CondTest;
use crate::{
    CharLit, ErrorContext, Level, Num, ParseErr, ParseResult, PathOrIdentifier, Span, StrLit,
    StrPrefix, WithSpan, char_lit, filter, identifier, keyword, not_suffix_with_hash, num_lit,
    path_or_identifier, skip_ws0, skip_ws1, str_lit, ws,
};

macro_rules! expr_prec_layer {
    ( $name:ident, $inner:ident, $op:expr ) => {
        fn $name(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
            expr_prec_layer(i, level, Expr::$inner, |i: &mut _| $op.parse_next(i))
        }
    };
}

fn expr_prec_layer<'a>(
    i: &mut &'a str,
    level: Level<'_>,
    inner: fn(&mut &'a str, Level<'_>) -> ParseResult<'a, WithSpan<'a, Expr<'a>>>,
    op: fn(&mut &'a str) -> ParseResult<'a>,
) -> ParseResult<'a, WithSpan<'a, Expr<'a>>> {
    let start = *i;
    let mut expr = inner(i, level)?;

    let mut i_before = *i;
    let mut level_guard = level.guard();
    while let Some((op, rhs)) = opt((ws(op), |i: &mut _| inner(i, level))).parse_next(i)? {
        level_guard.nest(i_before)?;
        i_before = *i;
        expr = WithSpan::new(Expr::BinOp(Box::new(BinOp { op, lhs: expr, rhs })), start);
    }

    Ok(expr)
}

#[derive(Clone, Copy, Default)]
struct Allowed {
    underscore: bool,
    super_keyword: bool,
}

fn check_expr<'a>(expr: &WithSpan<'a, Expr<'a>>, allowed: Allowed) -> Result<(), ParseErr<'a>> {
    match &expr.inner {
        &Expr::Var(name) => {
            // List can be found in rust compiler "can_be_raw" function (although in our case, it's
            // also used in cases like `match`, so `self` is allowed in this case).
            if (!allowed.super_keyword && name == "super") || matches!(name, "crate" | "Self") {
                Err(err_reserved_identifier(name))
            } else if !allowed.underscore && name == "_" {
                Err(err_underscore_identifier(name))
            } else {
                Ok(())
            }
        }
        &Expr::IsDefined(var) | &Expr::IsNotDefined(var) => {
            if var == "_" {
                Err(err_underscore_identifier(var))
            } else {
                Ok(())
            }
        }
        Expr::Path(path) => {
            if let &[name] = path.as_slice() {
                if !crate::can_be_variable_name(name) {
                    return Err(err_reserved_identifier(name));
                }
            }
            Ok(())
        }
        Expr::Array(elems) | Expr::Tuple(elems) | Expr::Concat(elems) => {
            for elem in elems {
                check_expr(elem, allowed)?;
            }
            Ok(())
        }
        Expr::AssociatedItem(elem, associated_item) => {
            if associated_item.name == "_" {
                Err(err_underscore_identifier(associated_item.name))
            } else if !crate::can_be_variable_name(associated_item.name) {
                Err(err_reserved_identifier(associated_item.name))
            } else {
                check_expr(elem, Allowed::default())
            }
        }
        Expr::Index(elem1, elem2) => {
            check_expr(elem1, Allowed::default())?;
            check_expr(elem2, Allowed::default())
        }
        Expr::BinOp(v) => {
            check_expr(&v.lhs, Allowed::default())?;
            check_expr(&v.rhs, Allowed::default())
        }
        Expr::Range(v) => {
            if let Some(elem1) = v.lhs.as_ref() {
                check_expr(elem1, Allowed::default())?;
            }
            if let Some(elem2) = v.rhs.as_ref() {
                check_expr(elem2, Allowed::default())?;
            }
            Ok(())
        }
        Expr::As(elem, _) | Expr::Unary(_, elem) | Expr::Group(elem) => {
            check_expr(elem, Allowed::default())
        }
        Expr::Call(v) => {
            check_expr(
                &v.path,
                Allowed {
                    underscore: false,
                    super_keyword: true,
                },
            )?;
            for arg in &v.args {
                check_expr(arg, Allowed::default())?;
            }
            Ok(())
        }
        Expr::ArgumentPlaceholder => Err(ErrMode::Cut(ErrorContext::new("unreachable", expr.span))),
        Expr::BoolLit(_)
        | Expr::NumLit(_, _)
        | Expr::StrLit(_)
        | Expr::CharLit(_)
        | Expr::Filter(_)
        | Expr::NamedArgument(_, _)
        | Expr::RustMacro(_, _)
        | Expr::Try(_)
        | Expr::FilterSource
        | Expr::LetCond(_) => Ok(()),
    }
}

fn err_underscore_identifier(name: &str) -> ErrMode<ErrorContext<'_>> {
    ErrMode::Cut(ErrorContext::new(
        "reserved keyword `_` cannot be used here",
        name,
    ))
}

fn err_reserved_identifier(name: &str) -> ErrMode<ErrorContext<'_>> {
    ErrMode::Cut(ErrorContext::new(
        format!("`{name}` cannot be used as an identifier"),
        name,
    ))
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    BoolLit(bool),
    NumLit(&'a str, Num<'a>),
    StrLit(StrLit<'a>),
    CharLit(CharLit<'a>),
    Var(&'a str),
    Path(Vec<&'a str>),
    Array(Vec<WithSpan<'a, Expr<'a>>>),
    AssociatedItem(Box<WithSpan<'a, Expr<'a>>>, AssociatedItem<'a>),
    Index(Box<WithSpan<'a, Expr<'a>>>, Box<WithSpan<'a, Expr<'a>>>),
    Filter(Box<Filter<'a>>),
    As(Box<WithSpan<'a, Expr<'a>>>, &'a str),
    NamedArgument(&'a str, Box<WithSpan<'a, Expr<'a>>>),
    Unary(&'a str, Box<WithSpan<'a, Expr<'a>>>),
    BinOp(Box<BinOp<'a>>),
    Range(Box<Range<'a>>),
    Group(Box<WithSpan<'a, Expr<'a>>>),
    Tuple(Vec<WithSpan<'a, Expr<'a>>>),
    Call(Box<Call<'a>>),
    RustMacro(Vec<&'a str>, &'a str),
    Try(Box<WithSpan<'a, Expr<'a>>>),
    /// This variant should never be used directly. It is created when generating filter blocks.
    FilterSource,
    IsDefined(&'a str),
    IsNotDefined(&'a str),
    Concat(Vec<WithSpan<'a, Expr<'a>>>),
    /// If you have `&& let Some(y)`, this variant handles it.
    LetCond(Box<WithSpan<'a, CondTest<'a>>>),
    /// This variant should never be used directly.
    /// It is used for the handling of named arguments in the generator, esp. with filters.
    ArgumentPlaceholder,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Call<'a> {
    pub path: WithSpan<'a, Expr<'a>>,
    pub args: Vec<WithSpan<'a, Expr<'a>>>,
    pub generics: Vec<WithSpan<'a, TyGenerics<'a>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Range<'a> {
    pub op: &'a str,
    pub lhs: Option<WithSpan<'a, Expr<'a>>>,
    pub rhs: Option<WithSpan<'a, Expr<'a>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinOp<'a> {
    pub op: &'a str,
    pub lhs: WithSpan<'a, Expr<'a>>,
    pub rhs: WithSpan<'a, Expr<'a>>,
}

impl<'a> Expr<'a> {
    pub(super) fn arguments(
        i: &mut &'a str,
        level: Level<'_>,
        is_template_macro: bool,
    ) -> ParseResult<'a, Vec<WithSpan<'a, Self>>> {
        let _level_guard = level.nest(i)?;
        let mut named_arguments = HashSet::new();
        let start = *i;

        preceded(
            ws('('),
            cut_err(terminated(
                separated(
                    0..,
                    ws(move |i: &mut _| {
                        // Needed to prevent borrowing it twice between this closure and the one
                        // calling `Self::named_arguments`.
                        let named_arguments = &mut named_arguments;
                        let has_named_arguments = !named_arguments.is_empty();

                        let expr = alt((
                            move |i: &mut _| {
                                Self::named_argument(
                                    i,
                                    level,
                                    named_arguments,
                                    start,
                                    is_template_macro,
                                )
                            },
                            move |i: &mut _| Self::parse(i, level, false),
                        ))
                        .parse_next(i)?;
                        if has_named_arguments && !matches!(*expr, Self::NamedArgument(_, _)) {
                            Err(ErrMode::Cut(ErrorContext::new(
                                "named arguments must always be passed last",
                                start,
                            )))
                        } else {
                            Ok(expr)
                        }
                    }),
                    ',',
                ),
                (opt(ws(',')), ')'),
            )),
        )
        .parse_next(i)
    }

    fn named_argument(
        i: &mut &'a str,
        level: Level<'_>,
        named_arguments: &mut HashSet<&'a str>,
        start: &'a str,
        is_template_macro: bool,
    ) -> ParseResult<'a, WithSpan<'a, Self>> {
        if !is_template_macro {
            // If this is not a template macro, we don't want to parse named arguments so
            // we instead return an error which will allow to continue the parsing.
            return fail.parse_next(i);
        }

        let (argument, _, value) = (identifier, ws('='), move |i: &mut _| {
            Self::parse(i, level, false)
        })
            .parse_next(i)?;
        if named_arguments.insert(argument) {
            Ok(WithSpan::new(
                Self::NamedArgument(argument, Box::new(value)),
                start,
            ))
        } else {
            Err(ErrMode::Cut(ErrorContext::new(
                format!("named argument `{argument}` was passed more than once"),
                start,
            )))
        }
    }

    pub(super) fn parse(
        i: &mut &'a str,
        level: Level<'_>,
        allow_underscore: bool,
    ) -> ParseResult<'a, WithSpan<'a, Self>> {
        let _level_guard = level.nest(i)?;
        let start = Span::from(*i);
        let range_right = move |i: &mut _| {
            (
                ws(alt(("..=", ".."))),
                opt(move |i: &mut _| Self::or(i, level)),
            )
                .parse_next(i)
        };
        let expr = alt((
            range_right.map(move |(op, right)| {
                WithSpan::new(
                    Self::Range(Box::new(Range {
                        op,
                        lhs: None,
                        rhs: right,
                    })),
                    start,
                )
            }),
            (move |i: &mut _| Self::or(i, level), opt(range_right)).map(move |(left, right)| {
                match right {
                    Some((op, right)) => WithSpan::new(
                        Self::Range(Box::new(Range {
                            op,
                            lhs: Some(left),
                            rhs: right,
                        })),
                        start,
                    ),
                    None => left,
                }
            }),
        ))
        .parse_next(i)?;
        check_expr(
            &expr,
            Allowed {
                underscore: allow_underscore,
                super_keyword: false,
            },
        )?;
        Ok(expr)
    }

    expr_prec_layer!(or, and, "||");
    expr_prec_layer!(and, compare, "&&");

    fn compare(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        let right = |i: &mut _| {
            let op = alt(("==", "!=", ">=", ">", "<=", "<"));
            (ws(op), |i: &mut _| Self::bor(i, level)).parse_next(i)
        };

        let start = *i;
        let expr = Self::bor(i, level)?;
        let Some((op, rhs)) = opt(right).parse_next(i)? else {
            return Ok(expr);
        };
        let expr = WithSpan::new(Expr::BinOp(Box::new(BinOp { op, lhs: expr, rhs })), start);

        if let Some((op2, _)) = opt(right).parse_next(i)? {
            return Err(ErrMode::Cut(ErrorContext::new(
                format!(
                    "comparison operators cannot be chained; \
                    consider using explicit parentheses, e.g.  `(_ {op} _) {op2} _`"
                ),
                op,
            )));
        }

        Ok(expr)
    }

    expr_prec_layer!(bor, bxor, "bitor".value("|"));
    expr_prec_layer!(bxor, band, token_xor);
    expr_prec_layer!(band, shifts, token_bitand);
    expr_prec_layer!(shifts, addsub, alt((">>", "<<")));
    expr_prec_layer!(addsub, concat, alt(("+", "-")));

    fn concat(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        fn concat_expr<'a>(
            i: &mut &'a str,
            level: Level<'_>,
        ) -> ParseResult<'a, Option<WithSpan<'a, Expr<'a>>>> {
            let ws1 = |i: &mut _| opt(skip_ws1).parse_next(i);

            let start = *i;
            let data = opt((ws1, '~', ws1, |i: &mut _| Expr::muldivmod(i, level))).parse_next(i)?;
            if let Some((t1, _, t2, expr)) = data {
                if t1.is_none() || t2.is_none() {
                    return Err(ErrMode::Cut(ErrorContext::new(
                        "the concat operator `~` must be surrounded by spaces",
                        start,
                    )));
                }
                Ok(Some(expr))
            } else {
                Ok(None)
            }
        }

        let start = *i;
        let expr = Self::muldivmod(i, level)?;
        let expr2 = concat_expr(i, level)?;
        if let Some(expr2) = expr2 {
            let mut exprs = vec![expr, expr2];
            while let Some(expr) = concat_expr(i, level)? {
                exprs.push(expr);
            }
            Ok(WithSpan::new(Self::Concat(exprs), start))
        } else {
            Ok(expr)
        }
    }

    expr_prec_layer!(muldivmod, is_as, alt(("*", "/", "%")));

    fn is_as(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;
        let lhs = Self::filtered(i, level)?;
        let before_keyword = *i;
        let rhs = opt(ws(identifier)).parse_next(i)?;
        match rhs {
            Some("is") => {}
            Some("as") => {
                let target = opt(identifier).parse_next(i)?;
                let target = target.unwrap_or_default();
                if crate::PRIMITIVE_TYPES.contains(&target) {
                    return Ok(WithSpan::new(Self::As(Box::new(lhs), target), start));
                } else if target.is_empty() {
                    return Err(ErrMode::Cut(ErrorContext::new(
                        "`as` operator expects the name of a primitive type on its right-hand side",
                        before_keyword.trim_start(),
                    )));
                } else {
                    return Err(ErrMode::Cut(ErrorContext::new(
                        format!(
                            "`as` operator expects the name of a primitive type on its right-hand \
                              side, found `{target}`"
                        ),
                        before_keyword.trim_start(),
                    )));
                }
            }
            _ => {
                *i = before_keyword;
                return Ok(lhs);
            }
        }

        let rhs = opt(terminated(opt(keyword("not")), ws(keyword("defined")))).parse_next(i)?;
        let ctor = match rhs {
            None => {
                return Err(ErrMode::Cut(ErrorContext::new(
                    "expected `defined` or `not defined` after `is`",
                    // We use `start` to show the whole `var is` thing instead of the current token.
                    start,
                )));
            }
            Some(None) => Self::IsDefined,
            Some(Some(_)) => Self::IsNotDefined,
        };
        let var_name = match *lhs {
            Self::Var(var_name) => var_name,
            Self::AssociatedItem(_, _) => {
                return Err(ErrMode::Cut(ErrorContext::new(
                    "`is defined` operator can only be used on variables, not on their fields",
                    start,
                )));
            }
            _ => {
                return Err(ErrMode::Cut(ErrorContext::new(
                    "`is defined` operator can only be used on variables",
                    start,
                )));
            }
        };
        Ok(WithSpan::new(ctor(var_name), start))
    }

    fn filtered(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        let mut res = Self::prefix(i, level)?;

        let mut level_guard = level.guard();
        let mut i_before = *i;
        while let Some(mut filter) = opt(|i: &mut _| filter(i, level)).parse_next(i)? {
            level_guard.nest(i_before)?;
            filter.arguments.insert(0, res);
            res = WithSpan::new(Self::Filter(Box::new(filter)), i_before);
            i_before = *i;
        }
        Ok(res)
    }

    fn prefix(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;

        // This is a rare place where we create recursion in the parsed AST
        // without recursing the parser call stack. However, this can lead
        // to stack overflows in drop glue when the AST is very deep.
        let mut level_guard = level.guard();
        let mut ops = vec![];
        let mut i_before = *i;
        while let Some(op) = opt(ws(alt(("!", "-", "*", "&")))).parse_next(i)? {
            level_guard.nest(i_before)?;
            ops.push(op);
            i_before = *i;
        }

        let mut expr = Suffix::parse(i, level)?;
        for op in ops.iter().rev() {
            expr = WithSpan::new(Self::Unary(op, Box::new(expr)), start);
        }

        Ok(expr)
    }

    fn single(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        alt((
            Self::num,
            Self::str,
            Self::char,
            Self::path_var_bool,
            move |i: &mut _| Self::array(i, level),
            move |i: &mut _| Self::group(i, level),
        ))
        .parse_next(i)
    }

    fn group(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;
        let expr = preceded(ws('('), opt(|i: &mut _| Self::parse(i, level, true))).parse_next(i)?;
        let Some(expr) = expr else {
            let _ = ')'.parse_next(i)?;
            return Ok(WithSpan::new(Self::Tuple(vec![]), start));
        };

        let comma = ws(opt(peek(','))).parse_next(i)?;
        if comma.is_none() {
            let _ = ')'.parse_next(i)?;
            return Ok(WithSpan::new(Self::Group(Box::new(expr)), start));
        }

        let mut exprs = vec![expr];
        repeat(
            0..,
            preceded(',', ws(|i: &mut _| Self::parse(i, level, true))),
        )
        .fold(
            || (),
            |(), expr| {
                exprs.push(expr);
            },
        )
        .parse_next(i)?;
        let _ = (ws(opt(',')), ')').parse_next(i)?;
        Ok(WithSpan::new(Self::Tuple(exprs), start))
    }

    fn array(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;
        let array = preceded(
            ws('['),
            cut_err(terminated(
                opt(terminated(
                    separated(1.., ws(move |i: &mut _| Self::parse(i, level, true)), ','),
                    ws(opt(',')),
                )),
                ']',
            )),
        )
        .parse_next(i)?;
        Ok(WithSpan::new(Self::Array(array.unwrap_or_default()), start))
    }

    fn path_var_bool(i: &mut &'a str) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;
        path_or_identifier
            .map(|v| match v {
                PathOrIdentifier::Path(v) => Self::Path(v),
                PathOrIdentifier::Identifier("true") => Self::BoolLit(true),
                PathOrIdentifier::Identifier("false") => Self::BoolLit(false),
                PathOrIdentifier::Identifier(v) => Self::Var(v),
            })
            .parse_next(i)
            .map(|expr| WithSpan::new(expr, start))
    }

    fn str(i: &mut &'a str) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;
        str_lit
            .map(|i| WithSpan::new(Self::StrLit(i), start))
            .parse_next(i)
    }

    fn num(i: &mut &'a str) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;
        let (num, full) = num_lit.with_taken().parse_next(i)?;
        Ok(WithSpan::new(Expr::NumLit(full, num), start))
    }

    fn char(i: &mut &'a str) -> ParseResult<'a, WithSpan<'a, Self>> {
        let start = *i;
        char_lit
            .map(|i| WithSpan::new(Self::CharLit(i), start))
            .parse_next(i)
    }

    #[must_use]
    pub fn contains_bool_lit_or_is_defined(&self) -> bool {
        match self {
            Self::BoolLit(_) | Self::IsDefined(_) | Self::IsNotDefined(_) => true,
            Self::Unary(_, expr) | Self::Group(expr) => expr.contains_bool_lit_or_is_defined(),
            Self::BinOp(v) if matches!(v.op, "&&" | "||") => {
                v.lhs.contains_bool_lit_or_is_defined() || v.rhs.contains_bool_lit_or_is_defined()
            }
            Self::NumLit(_, _)
            | Self::StrLit(_)
            | Self::CharLit(_)
            | Self::Var(_)
            | Self::FilterSource
            | Self::RustMacro(_, _)
            | Self::As(_, _)
            | Self::Call { .. }
            | Self::Range(_)
            | Self::Try(_)
            | Self::NamedArgument(_, _)
            | Self::Filter(_)
            | Self::AssociatedItem(_, _)
            | Self::Index(_, _)
            | Self::Tuple(_)
            | Self::Array(_)
            | Self::BinOp(_)
            | Self::Path(_)
            | Self::Concat(_)
            | Self::LetCond(_)
            | Self::ArgumentPlaceholder => false,
        }
    }
}

fn token_xor<'a>(i: &mut &'a str) -> ParseResult<'a> {
    let good = alt((keyword("xor").value(true), '^'.value(false))).parse_next(i)?;
    if good {
        Ok("^")
    } else {
        Err(ErrMode::Cut(ErrorContext::new(
            "the binary XOR operator is called `xor` in askama",
            *i,
        )))
    }
}

fn token_bitand<'a>(i: &mut &'a str) -> ParseResult<'a> {
    let good = alt((keyword("bitand").value(true), ('&', not('&')).value(false))).parse_next(i)?;
    if good {
        Ok("&")
    } else {
        Err(ErrMode::Cut(ErrorContext::new(
            "the binary AND operator is called `bitand` in askama",
            *i,
        )))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Filter<'a> {
    pub name: PathOrIdentifier<'a>,
    pub arguments: Vec<WithSpan<'a, Expr<'a>>>,
    pub generics: Vec<WithSpan<'a, TyGenerics<'a>>>,
}

impl<'a> Filter<'a> {
    pub(crate) fn parse(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, Self> {
        let (name, generics, arguments) = (
            ws(path_or_identifier),
            opt(|i: &mut _| call_generics(i, level)),
            opt(|i: &mut _| Expr::arguments(i, level, true)),
        )
            .parse_next(i)?;
        Ok(Self {
            name,
            arguments: arguments.unwrap_or_default(),
            generics: generics.unwrap_or_default(),
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct AssociatedItem<'a> {
    pub name: &'a str,
    pub generics: Vec<WithSpan<'a, TyGenerics<'a>>>,
}

enum Suffix<'a> {
    AssociatedItem(AssociatedItem<'a>),
    Index(WithSpan<'a, Expr<'a>>),
    Call {
        args: Vec<WithSpan<'a, Expr<'a>>>,
        generics: Vec<WithSpan<'a, TyGenerics<'a>>>,
    },
    // The value is the arguments of the macro call.
    MacroCall(&'a str),
    Try,
}

impl<'a> Suffix<'a> {
    fn parse(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, WithSpan<'a, Expr<'a>>> {
        let mut level_guard = level.guard();
        let mut expr = Expr::single(i, level)?;
        let mut right = opt(alt((
            |i: &mut _| Self::associated_item(i, level),
            |i: &mut _| Self::index(i, level),
            |i: &mut _| Self::call(i, level),
            Self::r#try,
            Self::r#macro,
        )));
        loop {
            let before_suffix = *i;
            let suffix = right.parse_next(i)?;
            let Some(suffix) = suffix else {
                break;
            };
            level_guard.nest(before_suffix)?;

            match suffix {
                Self::AssociatedItem(associated_item) => {
                    expr = WithSpan::new(
                        Expr::AssociatedItem(expr.into(), associated_item),
                        before_suffix,
                    )
                }
                Self::Index(index) => {
                    expr = WithSpan::new(Expr::Index(expr.into(), index.into()), before_suffix);
                }
                Self::Call { args, generics } => {
                    expr = WithSpan::new(
                        Expr::Call(Box::new(Call {
                            path: expr,
                            args,
                            generics,
                        })),
                        before_suffix,
                    )
                }
                Self::Try => expr = WithSpan::new(Expr::Try(expr.into()), before_suffix),
                Self::MacroCall(args) => match expr.inner {
                    Expr::Path(path) => {
                        ensure_macro_name(path.last().unwrap())?;
                        expr = WithSpan::new(Expr::RustMacro(path, args), before_suffix)
                    }
                    Expr::Var(name) => {
                        ensure_macro_name(name)?;
                        expr = WithSpan::new(Expr::RustMacro(vec![name], args), before_suffix)
                    }
                    _ => {
                        return Err(ErrMode::from_input(&before_suffix).cut());
                    }
                },
            }
        }
        Ok(expr)
    }

    fn r#macro(i: &mut &'a str) -> ParseResult<'a, Self> {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum Token {
            SomeOther,
            Open(Group),
            Close(Group),
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum Group {
            Paren,   // `(`
            Brace,   // `{`
            Bracket, // `[`
        }

        impl Group {
            fn as_close_char(self) -> char {
                match self {
                    Group::Paren => ')',
                    Group::Brace => '}',
                    Group::Bracket => ']',
                }
            }
        }

        fn macro_arguments<'a>(i: &mut &'a str, open_token: Group) -> ParseResult<'a, Suffix<'a>> {
            let start = *i;
            let mut open_list: Vec<Group> = vec![open_token];
            loop {
                let before = *i;
                let (token, token_span) = ws(opt(token).with_taken()).parse_next(i)?;
                let Some(token) = token else {
                    return Err(ErrMode::Cut(ErrorContext::new(
                        "expected valid tokens in macro call",
                        token_span,
                    )));
                };
                let close_token = match token {
                    Token::SomeOther => continue,
                    Token::Open(group) => {
                        open_list.push(group);
                        continue;
                    }
                    Token::Close(close_token) => close_token,
                };
                let open_token = open_list.pop().unwrap();

                if open_token != close_token {
                    return Err(ErrMode::Cut(ErrorContext::new(
                        format!(
                            "expected `{}` but found `{}`",
                            open_token.as_close_char(),
                            close_token.as_close_char(),
                        ),
                        token_span,
                    )));
                } else if open_list.is_empty() {
                    return Ok(Suffix::MacroCall(&start[..start.len() - before.len()]));
                }
            }
        }

        fn token<'a>(i: &mut &'a str) -> ParseResult<'a, Token> {
            // <https://doc.rust-lang.org/reference/tokens.html>
            let some_other = alt((
                // literals
                char_lit.value(Token::SomeOther),
                str_lit.value(Token::SomeOther),
                num_lit.value(Token::SomeOther),
                // keywords + (raw) identifiers + raw strings
                identifier_or_prefixed_string.value(Token::SomeOther),
                // lifetimes
                ('\'', identifier, not(peek('\''))).value(Token::SomeOther),
                // comments
                line_comment.value(Token::SomeOther),
                block_comment.value(Token::SomeOther),
                // punctuations
                punctuation.value(Token::SomeOther),
                hash,
            ));
            alt((open.map(Token::Open), close.map(Token::Close), some_other)).parse_next(i)
        }

        fn line_comment<'a>(i: &mut &'a str) -> ParseResult<'a, ()> {
            let start = "//".parse_next(i)?;
            let is_doc_comment = alt((
                ('/', not(peek('/'))).value(true),
                '!'.value(true),
                empty.value(false),
            ))
            .parse_next(i)?;
            if opt(take_until(.., '\n')).parse_next(i)?.is_none() {
                return Err(ErrMode::Cut(ErrorContext::new(
                    format!(
                        "you are probably missing a line break to end {}comment",
                        if is_doc_comment { "doc " } else { "" }
                    ),
                    start,
                )));
            }
            Ok(())
        }

        fn block_comment<'a>(i: &mut &'a str) -> ParseResult<'a, ()> {
            let start = "/*".parse_next(i)?;
            let is_doc_comment = alt((
                ('*', not(peek('*'))).value(true),
                '!'.value(true),
                empty.value(false),
            ))
            .parse_next(i)?;
            if opt(take_until(.., "*/")).parse_next(i)?.is_none() {
                return Err(ErrMode::Cut(ErrorContext::new(
                    format!(
                        "missing `*/` to close block {}comment",
                        if is_doc_comment { "doc " } else { "" }
                    ),
                    start,
                )));
            }
            Ok(())
        }

        fn identifier_or_prefixed_string<'a>(i: &mut &'a str) -> ParseResult<'a, ()> {
            // <https://doc.rust-lang.org/reference/tokens.html#r-lex.token.literal.str-raw.syntax>

            let prefix = identifier.parse_next(i)?;
            let hashes: usize = repeat(.., '#').parse_next(i)?;
            if hashes >= 256 {
                return Err(ErrMode::Cut(ErrorContext::new(
                    "a maximum of 255 hashes `#` are allowed with raw strings",
                    prefix,
                )));
            }

            let str_kind = match prefix {
                // raw cstring or byte slice
                "br" => Some(StrPrefix::Binary),
                "cr" => Some(StrPrefix::CLike),
                // raw string string or identifier
                "r" => None,
                // a simple identifier
                _ if hashes == 0 => return Ok(()),
                // reserved prefix: reject
                _ => {
                    return Err(ErrMode::Cut(ErrorContext::new(
                        format!("reserved prefix `{}#`", prefix.escape_debug()),
                        prefix,
                    )));
                }
            };

            if opt('"').parse_next(i)?.is_some() {
                // got a raw string

                let Some((inner, j)) = i.split_once(&format!("\"{:#<hashes$}", "")) else {
                    return Err(ErrMode::Cut(ErrorContext::new(
                        "unterminated raw string",
                        prefix,
                    )));
                };
                *i = j;

                let msg = match str_kind {
                    Some(StrPrefix::Binary) => inner
                        .bytes()
                        .any(|b| !b.is_ascii())
                        .then_some("binary string literals must not contain non-ASCII characters"),
                    Some(StrPrefix::CLike) => inner
                        .bytes()
                        .any(|b| b == 0)
                        .then_some("cstring literals must not contain NUL characters"),
                    None => None,
                };
                if let Some(msg) = msg {
                    return Err(ErrMode::Cut(ErrorContext::new(msg, prefix)));
                }

                not_suffix_with_hash(i)?;
                Ok(())
            } else if hashes == 0 {
                // a simple identifier
                Ok(())
            } else if opt(identifier).parse_next(i)?.is_some() {
                // got a raw identifier

                if str_kind.is_some() {
                    // an invalid raw identifier like `cr#async`
                    Err(ErrMode::Cut(ErrorContext::new(
                        format!(
                            "reserved prefix `{}#`, only `r#` is allowed with raw identifiers",
                            prefix.escape_debug(),
                        ),
                        prefix,
                    )))
                } else if hashes > 1 {
                    // an invalid raw identifier like `r##async`
                    Err(ErrMode::Cut(ErrorContext::new(
                        "only one `#` is allowed in raw identifier delimitation",
                        prefix,
                    )))
                } else {
                    // a raw identifier like `r#async`
                    Ok(())
                }
            } else {
                Err(ErrMode::Cut(ErrorContext::new(
                    format!(
                        "prefix `{}#` is only allowed with raw identifiers and raw strings",
                        prefix.escape_debug(),
                    ),
                    prefix,
                )))
            }
        }

        fn hash<'a>(i: &mut &'a str) -> ParseResult<'a, Token> {
            let start = *i;
            '#'.parse_next(i)?;
            if opt('"').parse_next(i)?.is_some() {
                return Err(ErrMode::Cut(ErrorContext::new(
                    "unprefixed guarded string literals are reserved for future use",
                    start,
                )));
            }
            Ok(Token::SomeOther)
        }

        fn punctuation<'a>(i: &mut &'a str) -> ParseResult<'a, ()> {
            // <https://doc.rust-lang.org/reference/tokens.html#punctuation>
            // hash '#' omitted

            const ONE_CHAR: &[u8] = b"+-*/%^!&|=><@_.,;:$?~";
            const TWO_CHARS: &[&str] = &[
                "&&", "||", "<<", ">>", "+=", "-=", "*=", "/=", "%=", "^=", "&=", "|=", "==", "!=",
                ">=", "<=", "..", "::", "->", "=>", "<-",
            ];
            const THREE_CHARS: &[&str] = &["<<=", ">>=", "...", "..="];

            // need to check long to short
            if let Some((head, tail)) = i.split_at_checked(3) {
                if THREE_CHARS.contains(&head) {
                    *i = tail;
                    return Ok(());
                }
            }
            if let Some((head, tail)) = i.split_at_checked(2) {
                if TWO_CHARS.contains(&head) {
                    *i = tail;
                    return Ok(());
                }
            }
            if let Some((head, tail)) = i.split_at_checked(1) {
                if let [head] = head.as_bytes() {
                    if ONE_CHAR.contains(head) {
                        *i = tail;
                        return Ok(());
                    }
                }
            }
            fail(i)
        }

        fn open<'a>(i: &mut &'a str) -> ParseResult<'a, Group> {
            alt((
                '('.value(Group::Paren),
                '{'.value(Group::Brace),
                '['.value(Group::Bracket),
            ))
            .parse_next(i)
        }

        fn close<'a>(i: &mut &'a str) -> ParseResult<'a, Group> {
            alt((
                ')'.value(Group::Paren),
                '}'.value(Group::Brace),
                ']'.value(Group::Bracket),
            ))
            .parse_next(i)
        }

        let open_token = preceded(ws('!'), open).parse_next(i)?;
        (|i: &mut _| macro_arguments(i, open_token)).parse_next(i)
    }

    fn associated_item(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, Self> {
        preceded(
            ws(('.', not('.'))),
            cut_err((
                |i: &mut _| {
                    let name = alt((digit1, identifier)).parse_next(i)?;
                    if !crate::can_be_variable_name(name) {
                        Err(ErrMode::Cut(ErrorContext::new(
                            format!("`{name}` cannot be used as an identifier"),
                            name,
                        )))
                    } else {
                        Ok(name)
                    }
                },
                opt(|i: &mut _| call_generics(i, level)),
            )),
        )
        .map(|(name, generics)| {
            Self::AssociatedItem(AssociatedItem {
                name,
                generics: generics.unwrap_or_default(),
            })
        })
        .parse_next(i)
    }

    fn index(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, Self> {
        preceded(
            ws('['),
            cut_err(terminated(
                ws(move |i: &mut _| Expr::parse(i, level, true)),
                ']',
            )),
        )
        .map(Self::Index)
        .parse_next(i)
    }

    fn call(i: &mut &'a str, level: Level<'_>) -> ParseResult<'a, Self> {
        (opt(|i: &mut _| call_generics(i, level)), |i: &mut _| {
            Expr::arguments(i, level, false)
        })
            .map(|(generics, args)| Self::Call {
                args,
                generics: generics.unwrap_or_default(),
            })
            .parse_next(i)
    }

    fn r#try(i: &mut &'a str) -> ParseResult<'a, Self> {
        preceded(skip_ws0, '?').map(|_| Self::Try).parse_next(i)
    }
}

fn ensure_macro_name(name: &str) -> ParseResult<'_, ()> {
    match name {
        "crate" | "super" | "Self" | "self" => Err(ErrMode::Cut(ErrorContext::new(
            format!("`{name}` is not a valid macro name"),
            name,
        ))),
        _ => Ok(()),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TyGenerics<'a> {
    pub refs: usize,
    pub path: Vec<&'a str>,
    pub args: Vec<WithSpan<'a, TyGenerics<'a>>>,
}

impl<'i> TyGenerics<'i> {
    fn parse(i: &mut &'i str, level: Level<'_>) -> ParseResult<'i, WithSpan<'i, Self>> {
        let start = *i;
        let (refs, path, args): (_, Vec<_>, _) = (
            repeat(0.., ws('&')),
            separated(1.., ws(identifier), "::"),
            opt(|i: &mut _| Self::args(i, level)).map(|generics| generics.unwrap_or_default()),
        )
            .parse_next(i)?;

        if let &[name] = path.as_slice() {
            if matches!(name, "super" | "self" | "crate") {
                // `Self` and `_` are allowed
                return Err(err_reserved_identifier(name));
            }
        } else {
            for (idx, &name) in path.iter().enumerate() {
                if name == "_" {
                    // `_` is never allowed
                    return Err(err_underscore_identifier(name));
                } else if idx > 0 && matches!(name, "super" | "self" | "Self" | "crate") {
                    // At the front of the path, "super" | "self" | "Self" | "crate" are allowed.
                    // Inside the path, they are not allowed.
                    return Err(err_reserved_identifier(name));
                }
            }
        }

        Ok(WithSpan::new(TyGenerics { refs, path, args }, start))
    }

    fn args(
        i: &mut &'i str,
        level: Level<'_>,
    ) -> ParseResult<'i, Vec<WithSpan<'i, TyGenerics<'i>>>> {
        ws('<').parse_next(i)?;
        let _level_guard = level.nest(i)?;
        cut_err(terminated(
            terminated(
                separated(0.., |i: &mut _| TyGenerics::parse(i, level), ws(',')),
                ws(opt(',')),
            ),
            '>',
        ))
        .parse_next(i)
    }
}

pub(crate) fn call_generics<'i>(
    i: &mut &'i str,
    level: Level<'_>,
) -> ParseResult<'i, Vec<WithSpan<'i, TyGenerics<'i>>>> {
    preceded(ws("::"), cut_err(|i: &mut _| TyGenerics::args(i, level))).parse_next(i)
}
