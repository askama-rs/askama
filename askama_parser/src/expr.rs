use std::str;

use winnow::Parser;
use winnow::ascii::digit1;
use winnow::combinator::{
    alt, cut_err, empty, fail, not, opt, peek, preceded, repeat, separated, terminated,
};
use winnow::stream::Stream;
use winnow::token::{any, one_of, take, take_until};

use crate::node::CondTest;
use crate::{
    CharLit, ErrorContext, HashSet, InputStream, Level, Num, ParseResult, PathOrIdentifier, StrLit,
    StrPrefix, WithSpan, can_be_variable_name, char_lit, cut_error, filter, identifier, keyword,
    not_suffix_with_hash, num_lit, path_or_identifier, skip_ws0, skip_ws1, str_lit, ws,
};

macro_rules! expr_prec_layer {
    ( $name:ident, $inner:ident, $op:expr ) => {
        fn $name(
            i: &mut InputStream<'a>,
            level: Level<'_>,
        ) -> ParseResult<'a, WithSpan<Box<Self>>> {
            expr_prec_layer(i, level, Expr::$inner, |i: &mut _| $op.parse_next(i))
        }
    };
}

fn expr_prec_layer<'a>(
    i: &mut InputStream<'a>,
    level: Level<'_>,
    inner: fn(&mut InputStream<'a>, Level<'_>) -> ParseResult<'a, WithSpan<Box<Expr<'a>>>>,
    op: fn(&mut InputStream<'a>) -> ParseResult<'a>,
) -> ParseResult<'a, WithSpan<Box<Expr<'a>>>> {
    let start = ***i;
    let mut expr = inner(i, level)?;

    let mut level_guard = level.guard();
    while let Some(((op, rhs), i_before)) =
        opt((ws(op), |i: &mut _| inner(i, level)).with_taken()).parse_next(i)?
    {
        level_guard.nest(i_before)?;
        expr = WithSpan::new(
            Box::new(Expr::BinOp(BinOp { op, lhs: expr, rhs })),
            start,
            i,
        );
    }

    Ok(expr)
}

#[derive(Clone, Copy, Default)]
struct Allowed {
    underscore: bool,
    super_keyword: bool,
}

fn check_expr<'a>(expr: &WithSpan<Box<Expr<'a>>>, allowed: Allowed) -> ParseResult<'a, ()> {
    match &*expr.inner {
        &Expr::Var(name) => {
            // List can be found in rust compiler "can_be_raw" function (although in our case, it's
            // also used in cases like `match`, so `self` is allowed in this case).
            if (!allowed.super_keyword && name == "super") || matches!(name, "crate" | "Self") {
                err_reserved_identifier(name)
            } else if !allowed.underscore && name == "_" {
                err_underscore_identifier(name)
            } else {
                Ok(())
            }
        }
        &Expr::IsDefined(var) | &Expr::IsNotDefined(var) => {
            if var == "_" {
                err_underscore_identifier(var)
            } else {
                Ok(())
            }
        }
        Expr::Path(path) => {
            if let [arg] = path.as_slice()
                && !crate::can_be_variable_name(arg.name)
            {
                return err_reserved_identifier(arg.name);
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
                err_underscore_identifier(associated_item.name)
            } else if !crate::can_be_variable_name(associated_item.name) {
                err_reserved_identifier(associated_item.name)
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
        Expr::As(elem, _)
        | Expr::Unary(_, elem)
        | Expr::Group(elem)
        | Expr::NamedArgument(_, elem)
        | Expr::Try(elem) => check_expr(elem, Allowed::default()),
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
        Expr::Filter(filter) => {
            for arg in &filter.arguments {
                check_expr(arg, Allowed::default())?;
            }
            Ok(())
        }
        Expr::LetCond(cond) => check_expr(&cond.expr, Allowed::default()),
        Expr::ArgumentPlaceholder => cut_error!("unreachable", expr.span),
        Expr::BoolLit(_)
        | Expr::NumLit(_, _)
        | Expr::StrLit(_)
        | Expr::CharLit(_)
        | Expr::RustMacro(_, _)
        | Expr::FilterSource => Ok(()),
    }
}

#[inline(always)]
fn err_underscore_identifier<T>(name: &str) -> ParseResult<'_, T> {
    cut_error!("reserved keyword `_` cannot be used here", name)
}

#[inline(always)]
fn err_reserved_identifier<T>(name: &str) -> ParseResult<'_, T> {
    cut_error!(format!("`{name}` cannot be used as an identifier"), name)
}

#[derive(Clone, Debug, PartialEq)]
pub struct PathComponent<'a> {
    pub name: &'a str,
    pub generics: Vec<WithSpan<TyGenerics<'a>>>,
}

impl<'a> PathComponent<'a> {
    pub fn new_with_name(name: &'a str) -> Self {
        Self {
            name,
            generics: Vec::new(),
        }
    }

    pub(crate) fn parse(
        i: &mut InputStream<'a>,
        level: Level<'_>,
    ) -> ParseResult<'a, WithSpan<Self>> {
        (
            identifier,
            opt((ws("::"), |i: &mut _| TyGenerics::args(i, level))),
        )
            .with_taken()
            .parse_next(i)
            .map(|((name, generics), span)| {
                WithSpan::new_with_full(
                    Self {
                        name,
                        generics: generics.map(|(_, generics)| generics).unwrap_or_default(),
                    },
                    span,
                )
            })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    BoolLit(bool),
    NumLit(&'a str, Num<'a>),
    StrLit(StrLit<'a>),
    CharLit(CharLit<'a>),
    Var(&'a str),
    Path(Vec<WithSpan<PathComponent<'a>>>),
    Array(Vec<WithSpan<Box<Expr<'a>>>>),
    AssociatedItem(WithSpan<Box<Expr<'a>>>, AssociatedItem<'a>),
    Index(WithSpan<Box<Expr<'a>>>, WithSpan<Box<Expr<'a>>>),
    Filter(Filter<'a>),
    As(WithSpan<Box<Expr<'a>>>, &'a str),
    NamedArgument(&'a str, WithSpan<Box<Expr<'a>>>),
    Unary(&'a str, WithSpan<Box<Expr<'a>>>),
    BinOp(BinOp<'a>),
    Range(Range<'a>),
    Group(WithSpan<Box<Expr<'a>>>),
    Tuple(Vec<WithSpan<Box<Expr<'a>>>>),
    Call(Call<'a>),
    RustMacro(Vec<&'a str>, &'a str),
    Try(WithSpan<Box<Expr<'a>>>),
    /// This variant should never be used directly. It is created when generating filter blocks.
    FilterSource,
    IsDefined(&'a str),
    IsNotDefined(&'a str),
    Concat(Vec<WithSpan<Box<Expr<'a>>>>),
    /// If you have `&& let Some(y)`, this variant handles it.
    LetCond(WithSpan<CondTest<'a>>),
    /// This variant should never be used directly.
    /// It is used for the handling of named arguments in the generator, esp. with filters.
    ArgumentPlaceholder,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Call<'a> {
    pub path: WithSpan<Box<Expr<'a>>>,
    pub args: Vec<WithSpan<Box<Expr<'a>>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Range<'a> {
    pub op: &'a str,
    pub lhs: Option<WithSpan<Box<Expr<'a>>>>,
    pub rhs: Option<WithSpan<Box<Expr<'a>>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinOp<'a> {
    pub op: &'a str,
    pub lhs: WithSpan<Box<Expr<'a>>>,
    pub rhs: WithSpan<Box<Expr<'a>>>,
}

impl<'a> Expr<'a> {
    pub(super) fn arguments(
        i: &mut InputStream<'a>,
        level: Level<'_>,
    ) -> ParseResult<'a, Vec<WithSpan<Box<Self>>>> {
        let _level_guard = level.nest(i)?;
        let mut named_arguments = HashSet::default();
        let start = ***i;

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
                            move |i: &mut _| Self::named_argument(i, level, named_arguments, start),
                            move |i: &mut _| Self::parse(i, level, false),
                        ))
                        .parse_next(i)?;
                        if has_named_arguments && !matches!(**expr, Self::NamedArgument(_, _)) {
                            cut_error!("named arguments must always be passed last", start)
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
        i: &mut InputStream<'a>,
        level: Level<'_>,
        named_arguments: &mut HashSet<&'a str>,
        start: &'a str,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let ((argument, _, value), span) = (identifier, ws('='), move |i: &mut _| {
            Self::parse(i, level, false)
        })
            .with_taken()
            .parse_next(i)?;
        if named_arguments.insert(argument) {
            Ok(WithSpan::new_with_full(
                Box::new(Self::NamedArgument(argument, value)),
                span,
            ))
        } else {
            cut_error!(
                format!("named argument `{argument}` was passed more than once"),
                start
            )
        }
    }

    pub(super) fn parse(
        i: &mut InputStream<'a>,
        level: Level<'_>,
        allow_underscore: bool,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let _level_guard = level.nest(i)?;
        let range_right = move |i: &mut _| {
            (
                ws(alt(("..=", ".."))),
                opt(move |i: &mut _| Self::or(i, level)),
            )
                .parse_next(i)
        };
        let expr = alt((
            range_right.with_taken().map(move |((op, right), i)| {
                WithSpan::new_with_full(
                    Box::new(Self::Range(Range {
                        op,
                        lhs: None,
                        rhs: right,
                    })),
                    i,
                )
            }),
            (move |i: &mut _| Self::or(i, level), opt(range_right))
                .with_taken()
                .map(move |((left, right), i)| match right {
                    Some((op, right)) => WithSpan::new_with_full(
                        Box::new(Self::Range(Range {
                            op,
                            lhs: Some(left),
                            rhs: right,
                        })),
                        i,
                    ),
                    None => left,
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

    fn compare(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let right = |i: &mut _| {
            let op = alt(("==", "!=", ">=", ">", "<=", "<"));
            (ws(op), |i: &mut _| Self::bor(i, level)).parse_next(i)
        };

        let ((expr, rhs), span) = (|i: &mut _| Self::bor(i, level), opt(right))
            .with_taken()
            .parse_next(i)?;
        let Some((op, rhs)) = rhs else {
            return Ok(expr);
        };
        let expr =
            WithSpan::new_with_full(Box::new(Expr::BinOp(BinOp { op, lhs: expr, rhs })), span);

        if let Some((op2, _)) = opt(right).parse_next(i)? {
            return cut_error!(
                format!(
                    "comparison operators cannot be chained; \
                    consider using explicit parentheses, e.g.  `(_ {op} _) {op2} _`"
                ),
                op,
            );
        }

        Ok(expr)
    }

    expr_prec_layer!(bor, bxor, "bitor".value("|"));
    expr_prec_layer!(bxor, band, token_xor);
    expr_prec_layer!(band, shifts, token_bitand);
    expr_prec_layer!(shifts, addsub, alt((">>", "<<")));
    expr_prec_layer!(addsub, concat, alt(("+", "-")));

    fn concat(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        fn concat_expr<'a>(
            i: &mut InputStream<'a>,
            level: Level<'_>,
        ) -> ParseResult<'a, Option<WithSpan<Box<Expr<'a>>>>> {
            let ws1 = |i: &mut _| opt(skip_ws1).parse_next(i);

            let start = ***i;
            let data = opt((ws1, '~', ws1, |i: &mut _| Expr::muldivmod(i, level))).parse_next(i)?;
            if let Some((t1, _, t2, expr)) = data {
                if t1.is_none() || t2.is_none() {
                    return cut_error!(
                        "the concat operator `~` must be surrounded by spaces",
                        start,
                    );
                }
                Ok(Some(expr))
            } else {
                Ok(None)
            }
        }

        let start = ***i;
        let expr = Self::muldivmod(i, level)?;
        let expr2 = concat_expr(i, level)?;
        if let Some(expr2) = expr2 {
            let mut exprs = vec![expr, expr2];
            while let Some(expr) = concat_expr(i, level)? {
                exprs.push(expr);
            }
            Ok(WithSpan::new(Box::new(Self::Concat(exprs)), start, i))
        } else {
            Ok(expr)
        }
    }

    expr_prec_layer!(muldivmod, is_as, alt(("*", "/", "%")));

    fn is_as(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let start = ***i;
        let lhs = Self::filtered(i, level)?;
        let before_keyword = *i;
        let rhs = opt(ws(identifier)).parse_next(i)?;
        match rhs {
            Some("is") => {}
            Some("as") => {
                let target = opt(identifier).parse_next(i)?;
                let target = target.unwrap_or_default();
                if crate::PRIMITIVE_TYPES.contains(&target) {
                    return Ok(WithSpan::new(Box::new(Self::As(lhs, target)), start, i));
                } else if target.is_empty() {
                    return cut_error!(
                        "`as` operator expects the name of a primitive type on its right-hand side",
                        before_keyword.trim_start(),
                    );
                } else {
                    return cut_error!(
                        format!(
                            "`as` operator expects the name of a primitive type on its right-hand \
                              side, found `{target}`"
                        ),
                        before_keyword.trim_start(),
                    );
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
                return cut_error!(
                    "expected `defined` or `not defined` after `is`",
                    // We use `start` to show the whole `var is` thing instead of the current token.
                    start,
                );
            }
            Some(None) => Self::IsDefined,
            Some(Some(_)) => Self::IsNotDefined,
        };
        let var_name = match &**lhs {
            Self::Var(var_name) => var_name,
            Self::AssociatedItem(_, _) => {
                return cut_error!(
                    "`is defined` operator can only be used on variables, not on their fields",
                    start,
                );
            }
            _ => {
                return cut_error!("`is defined` operator can only be used on variables", start);
            }
        };
        Ok(WithSpan::new(Box::new(ctor(var_name)), start, i))
    }

    fn filtered(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let mut res = Self::prefix(i, level)?;

        let mut level_guard = level.guard();
        let mut start = ***i;
        while let Some((mut filter, i_before)) =
            opt(ws((|i: &mut _| filter(i, level)).with_taken())).parse_next(i)?
        {
            level_guard.nest(i_before)?;
            filter.arguments.insert(0, res);
            res = WithSpan::new(Box::new(Self::Filter(filter)), start.trim_start(), i);
            start = ***i;
        }
        Ok(res)
    }

    fn prefix(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let start = ***i;

        // This is a rare place where we create recursion in the parsed AST
        // without recursing the parser call stack. However, this can lead
        // to stack overflows in drop glue when the AST is very deep.
        let mut level_guard = level.guard();
        let mut ops = vec![];
        while let Some((op, i_before)) =
            opt(ws(alt(("!", "-", "*", "&")).with_taken())).parse_next(i)?
        {
            level_guard.nest(i_before)?;
            ops.push(op);
        }

        let mut expr = Suffix::parse(i, level)?;
        for op in ops.iter().rev() {
            expr = WithSpan::new(Box::new(Self::Unary(op, expr)), start, i);
        }

        Ok(expr)
    }

    fn single(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        alt((
            Self::num,
            Self::str,
            Self::char,
            move |i: &mut _| Self::path_var_bool(i, level),
            move |i: &mut _| Self::array(i, level),
            move |i: &mut _| Self::group(i, level),
        ))
        .parse_next(i)
    }

    fn group(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        ws('(').parse_next(i)?;
        Self::group_actually(i, level)
    }

    // `Self::group()` is quite big. Let's only put it on the stack if needed.
    #[inline(never)]
    fn group_actually(
        i: &mut InputStream<'a>,
        level: Level<'_>,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let (expr, span) = cut_err(|i: &mut _| Self::group_actually_inner(i, level))
            .with_taken()
            .parse_next(i)?;
        Ok(WithSpan::new_with_full(expr, span.trim_ascii()))
    }

    #[inline]
    fn group_actually_inner(
        i: &mut InputStream<'a>,
        level: Level<'_>,
    ) -> ParseResult<'a, Box<Self>> {
        enum GroupResult<'a> {
            Tuple(WithSpan<Box<Expr<'a>>>),
            Expr(Box<Expr<'a>>),
            Err(&'static str),
        }

        let (expr, comma, closing) = (
            opt(|i: &mut _| Self::parse(i, level, true)),
            ws(opt(','.take())),
            opt(')'),
        )
            .parse_next(i)?;

        let result = match (expr, comma, closing) {
            // `(expr,`
            (Some(expr), Some(_), None) => GroupResult::Tuple(expr),
            // `()`
            (None, None, Some(_)) => GroupResult::Expr(Box::new(Self::Tuple(vec![]))),
            // `(expr)`
            (Some(expr), None, Some(_)) => GroupResult::Expr(Box::new(Self::Group(expr))),
            // `(expr,)`
            (Some(expr), Some(_), Some(_)) => GroupResult::Expr(Box::new(Self::Tuple(vec![expr]))),
            // `(`
            (None, None, None) => GroupResult::Err("expected closing `)` or an expression"),
            // `(expr`
            (Some(_), None, None) => GroupResult::Err("expected `,` or `)`"),
            // `(,`
            (None, Some(span), _) => return cut_error!("stray comma after opening `(`", span),
        };
        let expr = match result {
            GroupResult::Tuple(expr) => expr,
            GroupResult::Expr(expr) => return Ok(expr),
            GroupResult::Err(msg) => return cut_error!(msg, ***i),
        };

        let mut exprs = vec![expr];
        let collect_items = opt(separated(
            1..,
            |i: &mut _| {
                exprs.push(Self::parse(i, level, true)?);
                Ok(())
            },
            ws(','),
        )
        .map(|()| ()));

        let ((items, comma, close), span) = cut_err((collect_items, ws(opt(',')), opt(')')))
            .with_taken()
            .parse_next(i)?;
        let msg = if items.is_none() {
            "expected `)` or an expression"
        } else if close.is_some() {
            return Ok(Box::new(Self::Tuple(exprs)));
        } else if comma.is_some() {
            "expected `)` or an expression"
        } else {
            "expected `,` or `)`"
        };
        cut_error!(msg, span)
    }

    fn array(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let start = ***i;
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
        Ok(WithSpan::new(
            Box::new(Self::Array(array.unwrap_or_default())),
            start,
            i,
        ))
    }

    fn path_var_bool(
        i: &mut InputStream<'a>,
        level: Level<'_>,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let start = ***i;
        let ret = match path_or_identifier(i, level)? {
            PathOrIdentifier::Path(v) => Box::new(Self::Path(v)),
            PathOrIdentifier::Identifier("true") => Box::new(Self::BoolLit(true)),
            PathOrIdentifier::Identifier("false") => Box::new(Self::BoolLit(false)),
            PathOrIdentifier::Identifier(v) => Box::new(Self::Var(v)),
        };
        Ok(WithSpan::new(ret, start, i))
    }

    fn str(i: &mut InputStream<'a>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let start = ***i;
        let s = str_lit.parse_next(i)?;
        Ok(WithSpan::new(Box::new(Self::StrLit(s)), start, i))
    }

    fn num(i: &mut InputStream<'a>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let start = ***i;
        let (num, full) = num_lit.with_taken().parse_next(i)?;
        Ok(WithSpan::new(Box::new(Expr::NumLit(full, num)), start, i))
    }

    fn char(i: &mut InputStream<'a>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let start = ***i;
        let c = char_lit.parse_next(i)?;
        Ok(WithSpan::new(Box::new(Self::CharLit(c)), start, i))
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

fn token_xor<'a>(i: &mut InputStream<'a>) -> ParseResult<'a> {
    let good = alt((keyword("xor").value(true), '^'.value(false))).parse_next(i)?;
    if good {
        Ok("^")
    } else {
        cut_error!("the binary XOR operator is called `xor` in askama", ***i)
    }
}

fn token_bitand<'a>(i: &mut InputStream<'a>) -> ParseResult<'a> {
    let good = alt((keyword("bitand").value(true), ('&', not('&')).value(false))).parse_next(i)?;
    if good {
        Ok("&")
    } else {
        cut_error!("the binary AND operator is called `bitand` in askama", ***i)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Filter<'a> {
    pub name: PathOrIdentifier<'a>,
    pub arguments: Vec<WithSpan<Box<Expr<'a>>>>,
}

impl<'a> Filter<'a> {
    pub(crate) fn parse(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, Self> {
        let (name, arguments) = (
            ws(|i: &mut _| path_or_identifier(i, level)),
            opt(|i: &mut _| Expr::arguments(i, level)),
        )
            .parse_next(i)?;
        Ok(Self {
            name,
            arguments: arguments.unwrap_or_default(),
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct AssociatedItem<'a> {
    pub name: &'a str,
    pub generics: Vec<WithSpan<TyGenerics<'a>>>,
}

enum Suffix<'a> {
    AssociatedItem(AssociatedItem<'a>),
    Index(WithSpan<Box<Expr<'a>>>),
    Call { args: Vec<WithSpan<Box<Expr<'a>>>> },
    // The value is the arguments of the macro call.
    MacroCall(&'a str),
    Try,
}

impl<'a> Suffix<'a> {
    fn parse(
        i: &mut InputStream<'a>,
        level: Level<'_>,
    ) -> ParseResult<'a, WithSpan<Box<Expr<'a>>>> {
        let i_start = ***i;
        let mut level_guard = level.guard();
        let mut expr = Expr::single(i, level)?;
        let mut right = alt((
            |i: &mut _| Self::associated_item(i, level),
            |i: &mut _| Self::index(i, level),
            |i: &mut _| Self::call(i, level),
            Self::r#try,
            Self::r#macro,
        ));

        let start = ***i;
        let mut i_before = i.checkpoint();
        while let Some(suffix) = opt(right.by_ref()).parse_next(i)? {
            level_guard.nest(i)?;
            match suffix {
                Self::AssociatedItem(associated_item) => {
                    expr = WithSpan::new(
                        Box::new(Expr::AssociatedItem(expr, associated_item)),
                        start,
                        i,
                    )
                }
                Self::Index(index) => {
                    expr = WithSpan::new(Box::new(Expr::Index(expr, index)), start, i);
                }
                Self::Call { args } => {
                    expr = WithSpan::new(Box::new(Expr::Call(Call { path: expr, args })), start, i)
                }
                Self::Try => expr = WithSpan::new(Box::new(Expr::Try(expr)), start, i),
                Self::MacroCall(args) => match *expr.inner {
                    Expr::Path(path) => {
                        ensure_macro_name(path.last().unwrap().name)?;
                        if path.iter().any(|r| !r.generics.is_empty()) {
                            return Err(ErrorContext::new(
                                "macro paths cannot have generics",
                                i_start,
                            )
                            .backtrack());
                        }
                        expr = WithSpan::new(
                            Box::new(Expr::RustMacro(
                                path.into_iter().map(|c| c.name).collect(),
                                args,
                            )),
                            start,
                            i,
                        )
                    }
                    Expr::Var(name) => {
                        ensure_macro_name(name)?;
                        expr = WithSpan::new(Box::new(Expr::RustMacro(vec![name], args)), start, i)
                    }
                    _ => {
                        i.reset(&i_before);
                        return fail(i);
                    }
                },
            }
            i_before = i.checkpoint();
        }
        Ok(expr)
    }

    fn r#macro(i: &mut InputStream<'a>) -> ParseResult<'a, Self> {
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

        fn macro_arguments<'a>(
            i: &mut InputStream<'a>,
            open_token: Group,
        ) -> ParseResult<'a, Suffix<'a>> {
            let start = ***i;
            let mut open_list: Vec<Group> = vec![open_token];
            loop {
                let before = *i;
                let (token, token_span) = ws(opt(token).with_taken()).parse_next(i)?;
                let Some(token) = token else {
                    return cut_error!("expected valid tokens in macro call", token_span);
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
                    return cut_error!(
                        format!(
                            "expected `{}` but found `{}`",
                            open_token.as_close_char(),
                            close_token.as_close_char(),
                        ),
                        token_span,
                    );
                } else if open_list.is_empty() {
                    return Ok(Suffix::MacroCall(&start[..start.len() - before.len()]));
                }
            }
        }

        fn lifetime<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, ()> {
            // Before the 2021 edition, we can have whitespace characters between "r#" and the
            // identifier so we allow it here.
            let start = *i;
            '\''.parse_next(i)?;
            let Some((is_raw, identifier)) = opt(alt((
                ('r', '#', identifier).map(|(_, _, ident)| (true, ident)),
                (identifier, not(peek('#'))).map(|(ident, _)| (false, ident)),
            )))
            .parse_next(i)?
            else {
                return cut_error!("wrong lifetime format", **start);
            };
            if !is_raw {
                if crate::is_rust_keyword(identifier) {
                    return cut_error!(
                        "a non-raw lifetime cannot be named like an existing keyword",
                        **start,
                    );
                }
            } else if ["Self", "self", "crate", "super", "_"].contains(&identifier) {
                return cut_error!(format!("`{identifier}` cannot be a raw lifetime"), **start,);
            }
            if opt(peek('\'')).parse_next(i)?.is_some() {
                return cut_error!("unexpected `'` after lifetime", **start);
            }
            Ok(())
        }

        fn token<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, Token> {
            // <https://doc.rust-lang.org/reference/tokens.html>
            let some_other = alt((
                // literals
                char_lit.value(Token::SomeOther),
                str_lit.value(Token::SomeOther),
                num_lit.value(Token::SomeOther),
                // keywords + (raw) identifiers + raw strings
                identifier_or_prefixed_string.value(Token::SomeOther),
                lifetime.value(Token::SomeOther),
                // comments
                line_comment.value(Token::SomeOther),
                block_comment.value(Token::SomeOther),
                // punctuations
                punctuation.value(Token::SomeOther),
                hash,
            ));
            alt((open.map(Token::Open), close.map(Token::Close), some_other)).parse_next(i)
        }

        fn line_comment<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, ()> {
            fn inner<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, bool> {
                let start = "//".parse_next(i)?;
                let is_doc_comment = alt((
                    ('/', not(peek('/'))).value(true),
                    '!'.value(true),
                    empty.value(false),
                ))
                .parse_next(i)?;
                if opt((take_until(.., '\n'), '\n')).parse_next(i)?.is_none() {
                    return cut_error!(
                        format!(
                            "you are probably missing a line break to end {}comment",
                            if is_doc_comment { "doc " } else { "" }
                        ),
                        start,
                    );
                };
                Ok(is_doc_comment)
            }

            doc_comment_no_bare_cr(i, inner)
        }

        fn block_comment<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, ()> {
            fn inner<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, bool> {
                let start = "/*".parse_next(i)?;
                let is_doc_comment = alt((
                    ('*', not(peek(one_of(['*', '/'])))).value(true),
                    '!'.value(true),
                    empty.value(false),
                ))
                .parse_next(i)?;

                let mut depth = 0usize;
                loop {
                    if opt(take_until(.., ("/*", "*/"))).parse_next(i)?.is_none() {
                        return cut_error!(
                            format!(
                                "missing `*/` to close block {}comment",
                                if is_doc_comment { "doc " } else { "" }
                            ),
                            start,
                        );
                    } else if alt(("/*".value(true), "*/".value(false))).parse_next(i)? {
                        // cannot overflow: `i` cannot be longer than `isize::MAX`, cf. [std::alloc::Layout]
                        depth += 1;
                    } else if let Some(new_depth) = depth.checked_sub(1) {
                        depth = new_depth;
                    } else {
                        return Ok(is_doc_comment);
                    }
                }
            }

            doc_comment_no_bare_cr(i, inner)
        }

        fn identifier_or_prefixed_string<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, ()> {
            // <https://doc.rust-lang.org/reference/tokens.html#r-lex.token.literal.str-raw.syntax>

            let prefix = identifier.parse_next(i)?;
            let hashes: usize = repeat(.., '#').parse_next(i)?;
            if hashes >= 256 {
                return cut_error!(
                    "a maximum of 255 hashes `#` are allowed with raw strings",
                    prefix,
                );
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
                    return cut_error!(
                        format!("reserved prefix `{}#`", prefix.escape_debug()),
                        prefix,
                    );
                }
            };

            if opt('"').parse_next(i)?.is_some() {
                // got a raw string

                let delim = format!("\"{:#<hashes$}", "");
                let Some(inner) = opt(terminated(take_until(.., delim.as_str()), delim.as_str()))
                    .parse_next(i)?
                else {
                    return cut_error!("unterminated raw string", prefix);
                };

                if inner.split('\r').skip(1).any(|s| !s.starts_with('\n')) {
                    return cut_error!(
                        format!(
                            "a bare CR (Mac linebreak) is not allowed in string literals, \
                            use NL (Unix linebreak) or CRNL (Windows linebreak) instead, \
                            or type `\\r` explicitly",
                        ),
                        prefix,
                    );
                }

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
                    return cut_error!(msg, prefix);
                }

                not_suffix_with_hash(i)?;
                Ok(())
            } else if hashes == 0 {
                // a simple identifier
                Ok(())
            } else if let Some(id) = opt(identifier).parse_next(i)? {
                // got a raw identifier

                if str_kind.is_some() {
                    // an invalid raw identifier like `cr#async`
                    cut_error!(
                        format!(
                            "reserved prefix `{}#`, only `r#` is allowed with raw identifiers",
                            prefix.escape_debug(),
                        ),
                        prefix,
                    )
                } else if hashes > 1 {
                    // an invalid raw identifier like `r##async`
                    cut_error!(
                        "only one `#` is allowed in raw identifier delimitation",
                        prefix,
                    )
                } else {
                    // a raw identifier like `r#async`
                    if !can_be_variable_name(id) {
                        cut_error!(format!("`{id}` cannot be a raw identifier"), id)
                    } else {
                        Ok(())
                    }
                }
            } else {
                cut_error!(
                    format!(
                        "prefix `{}#` is only allowed with raw identifiers and raw strings",
                        prefix.escape_debug(),
                    ),
                    prefix,
                )
            }
        }

        fn hash<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, Token> {
            let start = ***i;
            '#'.parse_next(i)?;
            if opt('"').parse_next(i)?.is_some() {
                return cut_error!(
                    "unprefixed guarded string literals are reserved for future use",
                    start,
                );
            }
            Ok(Token::SomeOther)
        }

        fn punctuation<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, ()> {
            // <https://doc.rust-lang.org/reference/tokens.html#punctuation>
            // hash '#' omitted

            const ONE_CHAR: &[u8] = b"+-*/%^!&|=><@_.,;:$?~";
            const TWO_CHARS: &[[u8; 2]] = &[
                *b"&&", *b"||", *b"<<", *b">>", *b"+=", *b"-=", *b"*=", *b"/=", *b"%=", *b"^=",
                *b"&=", *b"|=", *b"==", *b"!=", *b">=", *b"<=", *b"..", *b"::", *b"->", *b"=>",
                *b"<-",
            ];
            const THREE_CHARS: &[[u8; 3]] = &[*b"<<=", *b">>=", *b"...", *b"..="];

            let three_chars = take(3usize).verify_map(|head: &str| {
                if let Ok(head) = head.as_bytes().try_into()
                    && THREE_CHARS.contains(head)
                {
                    Some(())
                } else {
                    None
                }
            });
            let two_chars = take(2usize).verify_map(|head: &str| {
                if let Ok(head) = head.as_bytes().try_into()
                    && TWO_CHARS.contains(head)
                {
                    Some(())
                } else {
                    None
                }
            });
            let one_char = any.verify_map(|head: char| {
                if let Ok(head) = head.try_into()
                    && ONE_CHAR.contains(&head)
                {
                    Some(())
                } else {
                    None
                }
            });

            // need to check long to short
            alt((three_chars, two_chars, one_char)).parse_next(i)
        }

        fn open<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, Group> {
            alt((
                '('.value(Group::Paren),
                '{'.value(Group::Brace),
                '['.value(Group::Bracket),
            ))
            .parse_next(i)
        }

        fn close<'a>(i: &mut InputStream<'a>) -> ParseResult<'a, Group> {
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

    fn associated_item(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, Self> {
        preceded(
            ws(('.', not('.'))),
            cut_err((
                |i: &mut _| {
                    let name = alt((digit1, identifier)).parse_next(i)?;
                    if !crate::can_be_variable_name(name) {
                        cut_error!(format!("`{name}` cannot be used as an identifier"), name)
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

    fn index(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, Self> {
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

    fn call(i: &mut InputStream<'a>, level: Level<'_>) -> ParseResult<'a, Self> {
        (opt(|i: &mut _| call_generics(i, level)), |i: &mut _| {
            Expr::arguments(i, level)
        })
            .map(|(_generics, args)| Self::Call { args })
            .parse_next(i)
    }

    fn r#try(i: &mut InputStream<'a>) -> ParseResult<'a, Self> {
        preceded(skip_ws0, '?').map(|_| Self::Try).parse_next(i)
    }
}

fn doc_comment_no_bare_cr<'a>(
    i: &mut InputStream<'a>,
    inner: fn(i: &mut InputStream<'a>) -> ParseResult<'a, bool>,
) -> ParseResult<'a, ()> {
    let (is_doc_comment, comment) = inner.with_taken().parse_next(i)?;
    if is_doc_comment && comment.split('\r').skip(1).any(|s| !s.starts_with('\n')) {
        cut_error!(
            "bare CR not allowed in doc comment, 
            use NL (Unix linebreak) or CRNL (Windows linebreak) instead",
            comment,
        )
    } else {
        Ok(())
    }
}

fn ensure_macro_name(name: &str) -> ParseResult<'_, ()> {
    match name {
        "crate" | "super" | "Self" | "self" => {
            cut_error!(format!("`{name}` is not a valid macro name"), name)
        }
        _ => Ok(()),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TyGenerics<'a> {
    pub refs: usize,
    pub path: Vec<&'a str>,
    pub args: Vec<WithSpan<TyGenerics<'a>>>,
}

impl<'i> TyGenerics<'i> {
    fn parse(i: &mut InputStream<'i>, level: Level<'_>) -> ParseResult<'i, WithSpan<Self>> {
        let start = ***i;
        let (refs, path, args): (_, Vec<_>, _) = (
            repeat(0.., ws('&')),
            separated(1.., ws(identifier), "::"),
            opt(|i: &mut _| Self::args(i, level)).map(|generics| generics.unwrap_or_default()),
        )
            .parse_next(i)?;

        if let &[name] = path.as_slice() {
            if matches!(name, "super" | "self" | "crate") {
                // `Self` and `_` are allowed
                return err_reserved_identifier(name);
            }
        } else {
            for (idx, &name) in path.iter().enumerate() {
                if name == "_" {
                    // `_` is never allowed
                    return err_underscore_identifier(name);
                } else if idx > 0 && matches!(name, "super" | "self" | "Self" | "crate") {
                    // At the front of the path, "super" | "self" | "Self" | "crate" are allowed.
                    // Inside the path, they are not allowed.
                    return err_reserved_identifier(name);
                }
            }
        }

        Ok(WithSpan::new(TyGenerics { refs, path, args }, start, i))
    }

    fn args(
        i: &mut InputStream<'i>,
        level: Level<'_>,
    ) -> ParseResult<'i, Vec<WithSpan<TyGenerics<'i>>>> {
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
    i: &mut InputStream<'i>,
    level: Level<'_>,
) -> ParseResult<'i, Vec<WithSpan<TyGenerics<'i>>>> {
    preceded(ws("::"), cut_err(|i: &mut _| TyGenerics::args(i, level))).parse_next(i)
}
