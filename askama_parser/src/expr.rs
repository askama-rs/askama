use winnow::Parser;
use winnow::ascii::digit1;
use winnow::combinator::{
    alt, cut_err, empty, fail, not, opt, peek, preceded, repeat, separated, terminated,
};
use winnow::stream::Stream;
use winnow::token::{any, one_of, take, take_until};

use crate::node::CondTest;
use crate::{
    CharLit, ErrorContext, HashSet, InputStream, Num, ParseResult, PathOrIdentifier, StrLit,
    StrPrefix, WithSpan, char_lit, cut_error, filter, identifier, is_rust_keyword, keyword,
    not_suffix_with_hash, num_lit, path_or_identifier, skip_ws0, skip_ws1, str_lit, ws,
};

macro_rules! expr_prec_layer {
    ( $name:ident, $inner:ident, $op:expr ) => {
        fn $name(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
            expr_prec_layer(i, Expr::$inner, |i: &mut _| $op.parse_next(i))
        }
    };
}

fn expr_prec_layer<'a: 'l, 'l>(
    i: &mut InputStream<'a, 'l>,
    inner: fn(&mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Expr<'a>>>>,
    op: fn(&mut InputStream<'a, 'l>) -> ParseResult<'a>,
) -> ParseResult<'a, WithSpan<Box<Expr<'a>>>> {
    let mut expr = inner(i)?;

    let mut i_before = *i;
    let mut level_guard = i.state.level.guard();
    while let Some(((op, span), rhs)) = opt((ws(op.with_span()), inner)).parse_next(i)? {
        level_guard.nest(&i_before)?;
        expr = WithSpan::new(Box::new(Expr::BinOp(BinOp { op, lhs: expr, rhs })), span);
        i_before = *i;
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
                err_reserved_identifier(&WithSpan::new(name, expr.span))
            } else if !allowed.underscore && name == "_" {
                err_underscore_identifier(&WithSpan::new(name, expr.span))
            } else {
                Ok(())
            }
        }
        &Expr::IsDefined(var) | &Expr::IsNotDefined(var) => {
            if var == "_" {
                err_underscore_identifier(&WithSpan::new(var, expr.span))
            } else {
                Ok(())
            }
        }
        Expr::Path(path) => {
            if let [arg] = path.as_slice()
                && !crate::can_be_variable_name(*arg.name)
            {
                return err_reserved_identifier(&arg.name);
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
            if *associated_item.name == "_" {
                err_underscore_identifier(&associated_item.name)
            } else if !crate::can_be_variable_name(*associated_item.name) {
                err_reserved_identifier(&associated_item.name)
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
fn err_underscore_identifier<'a, T>(name: &WithSpan<&str>) -> ParseResult<'a, T> {
    cut_error!("reserved keyword `_` cannot be used here", name.span)
}

#[inline(always)]
fn err_reserved_identifier<'a, T>(name: &WithSpan<&str>) -> ParseResult<'a, T> {
    cut_error!(
        format!("`{}` cannot be used as an identifier", name.inner),
        name.span
    )
}

#[derive(Clone, Debug, PartialEq)]
pub struct PathComponent<'a> {
    pub name: WithSpan<&'a str>,
    pub generics: Option<WithSpan<Vec<WithSpan<TyGenerics<'a>>>>>,
}

impl<'a: 'l, 'l> PathComponent<'a> {
    #[inline]
    pub fn new_with_name(name: WithSpan<&'a str>) -> Self {
        Self {
            name,
            generics: None,
        }
    }

    pub(crate) fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Self> {
        let mut p = (
            identifier.with_span(),
            opt(preceded(ws("::"), TyGenerics::args)),
        );
        let ((name, name_span), generics) = p.parse_next(i)?;
        Ok(Self {
            name: WithSpan::new(name, name_span),
            generics,
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
    Path(Vec<PathComponent<'a>>),
    Array(Vec<WithSpan<Box<Expr<'a>>>>),
    AssociatedItem(WithSpan<Box<Expr<'a>>>, AssociatedItem<'a>),
    Index(WithSpan<Box<Expr<'a>>>, WithSpan<Box<Expr<'a>>>),
    Filter(Filter<'a>),
    As(WithSpan<Box<Expr<'a>>>, WithSpan<&'a str>),
    NamedArgument(WithSpan<&'a str>, WithSpan<Box<Expr<'a>>>),
    Unary(&'a str, WithSpan<Box<Expr<'a>>>),
    BinOp(BinOp<'a>),
    Range(Range<'a>),
    Group(WithSpan<Box<Expr<'a>>>),
    Tuple(Vec<WithSpan<Box<Expr<'a>>>>),
    Call(Call<'a>),
    RustMacro(Vec<WithSpan<&'a str>>, WithSpan<&'a str>),
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
    pub generics: Option<WithSpan<Vec<WithSpan<TyGenerics<'a>>>>>,
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

impl<'a: 'l, 'l> Expr<'a> {
    pub(super) fn arguments(
        i: &mut InputStream<'a, 'l>,
    ) -> ParseResult<'a, WithSpan<Vec<WithSpan<Box<Self>>>>> {
        let _level_guard = i.state.level.nest(i)?;
        let mut named_arguments = HashSet::default();
        let mut p = (
            ws('('.span()),
            cut_err((
                separated(
                    0..,
                    ws(move |i: &mut _| {
                        // Needed to prevent borrowing it twice between this closure and the one
                        // calling `Self::named_arguments`.
                        let named_arguments = &mut named_arguments;
                        let has_named_arguments = !named_arguments.is_empty();

                        let mut p = alt((
                            move |i: &mut _| Self::named_argument(i, named_arguments),
                            move |i: &mut _| Self::parse(i, false),
                        ));
                        let expr = p.parse_next(i)?;
                        if has_named_arguments && !matches!(**expr, Self::NamedArgument(..)) {
                            return cut_error!(
                                "named arguments must always be passed last",
                                expr.span,
                            );
                        }
                        Ok(expr)
                    }),
                    ',',
                ),
                opt(ws(',')),
                opt(')'),
            )),
        );
        let (span, (args, _, closed)) = p.parse_next(i)?;
        if closed.is_none() {
            return cut_error!("matching closing `)` is missing", span);
        }
        Ok(WithSpan::new(args, span))
    }

    fn named_argument(
        i: &mut InputStream<'a, 'l>,
        named_arguments: &mut HashSet<&'a str>,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let (((argument, arg_span), _, value), span) =
            (identifier.with_span(), ws('='), move |i: &mut _| {
                Self::parse(i, false)
            })
                .with_span()
                .parse_next(i)?;
        if !named_arguments.insert(argument) {
            return cut_error!(
                format!(
                    "named argument `{}` was passed more than once",
                    argument.escape_debug()
                ),
                arg_span,
            );
        }

        Ok(WithSpan::new(
            Box::new(Self::NamedArgument(
                WithSpan::new(argument, arg_span),
                value,
            )),
            span,
        ))
    }

    pub(super) fn parse(
        i: &mut InputStream<'a, 'l>,
        allow_underscore: bool,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let _level_guard = i.state.level.nest(i)?;
        Self::range(i, allow_underscore)
    }

    fn range(
        i: &mut InputStream<'a, 'l>,
        allow_underscore: bool,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let range_right = move |i: &mut InputStream<'a, 'l>| {
            let ((op, span), rhs) =
                (ws(alt(("..=", "..")).with_span()), opt(Self::or)).parse_next(i)?;
            Ok((op, rhs, span))
        };

        // `..expr` or `..`
        let range_to = range_right.map(move |(op, rhs, span)| {
            WithSpan::new(Box::new(Self::Range(Range { op, lhs: None, rhs })), span)
        });

        // `expr..expr` or `expr..`
        let range_from = (Self::or, opt(range_right)).map(move |(lhs, rhs)| match rhs {
            Some((op, rhs, span)) => WithSpan::new(
                Box::new(Self::Range(Range {
                    op,
                    lhs: Some(lhs),
                    rhs,
                })),
                span,
            ),
            None => lhs,
        });

        let expr = alt((range_to, range_from)).parse_next(i)?;
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

    fn compare(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let mut parse_op = ws(alt(("==", "!=", ">=", ">", "<=", "<")).with_span());

        let (expr, rhs) = (Self::bor, opt((parse_op.by_ref(), Self::bor))).parse_next(i)?;
        let Some(((op, span), rhs)) = rhs else {
            return Ok(expr);
        };
        let expr = WithSpan::new(Box::new(Expr::BinOp(BinOp { op, lhs: expr, rhs })), span);

        if let Some((op2, span)) = opt(parse_op).parse_next(i)? {
            return cut_error!(
                format!(
                    "comparison operators cannot be chained; \
                    consider using explicit parentheses, e.g.  `(_ {op} _) {op2} _`"
                ),
                span,
            );
        }

        Ok(expr)
    }

    expr_prec_layer!(bor, bxor, "bitor".value("|"));
    expr_prec_layer!(bxor, band, token_xor);
    expr_prec_layer!(band, shifts, token_bitand);
    expr_prec_layer!(shifts, addsub, alt((">>", "<<")));
    expr_prec_layer!(addsub, concat, alt(("+", "-")));

    fn concat(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        #[allow(clippy::type_complexity)]
        fn concat_expr<'a: 'l, 'l>(
            i: &mut InputStream<'a, 'l>,
        ) -> ParseResult<'a, Option<(WithSpan<Box<Expr<'a>>>, std::ops::Range<usize>)>> {
            let ws1 = |i: &mut _| opt(skip_ws1).parse_next(i);
            let tilde = (ws1, '~', ws1).with_span();
            let data = opt((tilde, Expr::muldivmod)).parse_next(i)?;

            let Some((((t1, _, t2), span), expr)) = data else {
                return Ok(None);
            };
            if t1.is_none() || t2.is_none() {
                return cut_error!("the concat operator `~` must be surrounded by spaces", span);
            }

            Ok(Some((expr, span)))
        }

        let expr = Self::muldivmod(i)?;
        let expr2 = concat_expr(i)?;
        if let Some((expr2, span)) = expr2 {
            let mut exprs = vec![expr, expr2];
            while let Some((expr, _)) = concat_expr(i)? {
                exprs.push(expr);
            }
            Ok(WithSpan::new(Box::new(Self::Concat(exprs)), span))
        } else {
            Ok(expr)
        }
    }

    expr_prec_layer!(muldivmod, is_as, alt(("*", "/", "%")));

    fn is_as(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let lhs = Self::filtered(i)?;
        let checkpoint = i.checkpoint();
        let rhs = opt(ws(identifier.with_span())).parse_next(i)?;
        match rhs {
            Some(("is", span)) => Self::is_as_handle_is(i, lhs, span),
            Some(("as", span)) => Self::is_as_handle_as(i, lhs, span),
            _ => {
                i.reset(&checkpoint);
                Ok(lhs)
            }
        }
    }

    fn is_as_handle_is(
        i: &mut InputStream<'a, 'l>,
        lhs: WithSpan<Box<Expr<'a>>>,
        span: std::ops::Range<usize>,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let mut rhs = opt(terminated(opt(keyword("not")), ws(keyword("defined"))));
        let ctor = match rhs.parse_next(i)? {
            None => {
                return cut_error!("expected `defined` or `not defined` after `is`", span);
            }
            Some(None) => Self::IsDefined,
            Some(Some(_)) => Self::IsNotDefined,
        };
        let var_name = match &**lhs {
            Self::Var(var_name) => var_name,
            Self::AssociatedItem(_, _) => {
                return cut_error!(
                    "`is defined` operator can only be used on variables, not on their fields",
                    span,
                );
            }
            _ => {
                return cut_error!("`is defined` operator can only be used on variables", span);
            }
        };
        Ok(WithSpan::new(Box::new(ctor(var_name)), span))
    }

    fn is_as_handle_as(
        i: &mut InputStream<'a, 'l>,
        lhs: WithSpan<Box<Expr<'a>>>,
        span: std::ops::Range<usize>,
    ) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let target = opt(path_or_identifier).parse_next(i)?;
        let Some(PathOrIdentifier::Identifier(target)) = target else {
            return cut_error!(
                "`as` operator expects the name of a primitive type on its right-hand side, \
                not a path or alias",
                span,
            );
        };

        if crate::PRIMITIVE_TYPES.contains(&target) {
            Ok(WithSpan::new(Box::new(Self::As(lhs, target)), span))
        } else if target.is_empty() {
            cut_error!(
                "`as` operator expects the name of a primitive type on its right-hand side",
                span,
            )
        } else {
            cut_error!(
                format!(
                    "`as` operator expects the name of a primitive type on its right-hand \
                    side, found `{}`",
                    target.escape_debug()
                ),
                span,
            )
        }
    }

    fn filtered(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let mut res = Self::prefix(i)?;

        let mut level_guard = i.state.level.guard();
        let mut i_before = *i;
        while let Some((mut filter, span)) = opt(ws(filter.with_span())).parse_next(i)? {
            level_guard.nest(&i_before)?;
            filter.arguments.insert(0, res);
            res = WithSpan::new(Box::new(Self::Filter(filter)), span);
            i_before = *i;
        }
        Ok(res)
    }

    fn prefix(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        // This is a rare place where we create recursion in the parsed AST
        // without recursing the parser call stack. However, this can lead
        // to stack overflows in drop glue when the AST is very deep.
        let mut level_guard = i.state.level.guard();
        let mut i_before = *i;
        let mut ops = vec![];
        while let Some(op) = opt(ws(alt(("!", "-", "*", "&")).with_span())).parse_next(i)? {
            level_guard.nest(&i_before)?;
            ops.push(op);
            i_before = *i;
        }

        let mut expr = Suffix::parse(i)?;
        for (op, span) in ops.into_iter().rev() {
            expr = WithSpan::new(Box::new(Self::Unary(op, expr)), span);
        }

        Ok(expr)
    }

    fn single(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        alt((
            Self::num,
            Self::str,
            Self::char,
            Self::path_var_bool,
            Self::array,
            Self::group,
        ))
        .parse_next(i)
    }

    fn group(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        (skip_ws0, peek('(')).parse_next(i)?;
        Self::group_actually(i)
    }

    // `Self::group()` is quite big. Let's only put it on the stack if needed.
    #[inline(never)]
    fn group_actually(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let (expr, span) = cut_err(preceded('(', Self::group_actually_inner))
            .with_span()
            .parse_next(i)?;
        Ok(WithSpan::new(expr, span))
    }

    #[inline]
    fn group_actually_inner(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let (expr, comma, closing) = (
            ws(opt(|i: &mut _| Self::parse(i, true))),
            opt(terminated(','.span(), skip_ws0)),
            opt(')'),
        )
            .parse_next(i)?;

        let expr = match (expr, comma, closing) {
            // `(expr,`
            (Some(expr), Some(_), None) => expr,
            // `()`
            (None, None, Some(_)) => return Ok(Box::new(Self::Tuple(vec![]))),
            // `(expr)`
            (Some(expr), None, Some(_)) => return Ok(Box::new(Self::Group(expr))),
            // `(expr,)`
            (Some(expr), Some(_), Some(_)) => return Ok(Box::new(Self::Tuple(vec![expr]))),
            // `(`
            (None, None, None) => return cut_error!("expected closing `)` or an expression", *i),
            // `(expr`
            (Some(_), None, None) => return cut_error!("expected `,` or `)`", *i),
            // `(,`
            (None, Some(span), _) => return cut_error!("stray comma after opening `(`", span),
        };

        let mut exprs = vec![expr];
        let collect_items = opt(separated(
            1..,
            |i: &mut _| {
                exprs.push(Self::parse(i, true)?);
                Ok(())
            },
            ws(','),
        )
        .map(|()| ()));

        let ((items, comma, close), span) = cut_err((collect_items, ws(opt(',')), opt(')')))
            .with_span()
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

    fn array(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let (array, span) = preceded(
            ws('['),
            cut_err(terminated(
                opt(terminated(
                    separated(1.., ws(move |i: &mut _| Self::parse(i, true)), ','),
                    ws(opt(',')),
                )),
                ']',
            )),
        )
        .with_span()
        .parse_next(i)?;
        Ok(WithSpan::new(
            Box::new(Self::Array(array.unwrap_or_default())),
            span,
        ))
    }

    fn path_var_bool(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let (ret, span) = path_or_identifier.with_span().parse_next(i)?;
        let ret = match ret {
            PathOrIdentifier::Path(v) => Box::new(Self::Path(v)),
            PathOrIdentifier::Identifier(v) if *v == "true" => Box::new(Self::BoolLit(true)),
            PathOrIdentifier::Identifier(v) if *v == "false" => Box::new(Self::BoolLit(false)),
            PathOrIdentifier::Identifier(v) => Box::new(Self::Var(*v)),
        };
        Ok(WithSpan::new(ret, span))
    }

    fn str(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let (s, span) = str_lit.with_span().parse_next(i)?;
        Ok(WithSpan::new(Box::new(Self::StrLit(s)), span))
    }

    fn num(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let ((num, full), span) = num_lit.with_taken().with_span().parse_next(i)?;
        Ok(WithSpan::new(Box::new(Expr::NumLit(full, num)), span))
    }

    fn char(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Self>>> {
        let (c, span) = char_lit.with_span().parse_next(i)?;
        Ok(WithSpan::new(Box::new(Self::CharLit(c)), span))
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

fn token_xor<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a> {
    let (good, span) = alt((keyword("xor").value(true), '^'.value(false)))
        .with_span()
        .parse_next(i)?;
    if good {
        Ok("^")
    } else {
        cut_error!("the binary XOR operator is called `xor` in askama", span)
    }
}

fn token_bitand<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a> {
    let (good, span) = alt((keyword("bitand").value(true), ('&', not('&')).value(false)))
        .with_span()
        .parse_next(i)?;
    if good {
        Ok("&")
    } else {
        cut_error!("the binary AND operator is called `bitand` in askama", span)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Filter<'a> {
    pub name: PathOrIdentifier<'a>,
    pub arguments: Vec<WithSpan<Box<Expr<'a>>>>,
}

impl<'a: 'l, 'l> Filter<'a> {
    pub(crate) fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Self> {
        let mut p = (ws(path_or_identifier), opt(Expr::arguments));
        let (name, arguments) = p.parse_next(i)?;
        Ok(Self {
            name,
            arguments: arguments.map_or_else(Vec::new, |arguments| arguments.inner),
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct AssociatedItem<'a> {
    pub name: WithSpan<&'a str>,
    pub generics: Option<WithSpan<Vec<WithSpan<TyGenerics<'a>>>>>,
}

enum Suffix<'a> {
    AssociatedItem(AssociatedItem<'a>),
    Index(WithSpan<Box<Expr<'a>>>),
    Call {
        generics: Option<WithSpan<Vec<WithSpan<TyGenerics<'a>>>>>,
        args: Vec<WithSpan<Box<Expr<'a>>>>,
    },
    // The value is the arguments of the macro call.
    MacroCall(&'a str),
    Try,
}

impl<'a: 'l, 'l> Suffix<'a> {
    fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Box<Expr<'a>>>> {
        let mut level_guard = i.state.level.guard();
        let mut expr = Expr::single(i)?;
        let mut right = opt(alt((
            Self::associated_item,
            Self::index,
            Self::call,
            Self::r#try,
            Self::r#macro,
        )));

        let mut i_before = i.checkpoint();
        while let Some(suffix) = right.parse_next(i)? {
            level_guard.nest(i)?;
            let (suffix, span) = suffix.deconstruct();
            let inner = match suffix {
                Self::AssociatedItem(associated_item) => {
                    Box::new(Expr::AssociatedItem(expr, associated_item))
                }
                Self::Index(index) => Box::new(Expr::Index(expr, index)),
                Self::Call { generics, args } => Box::new(Expr::Call(Call {
                    path: expr,
                    generics,
                    args,
                })),
                Self::Try => Box::new(Expr::Try(expr)),
                Self::MacroCall(args) => {
                    let args = WithSpan::new(args, span);
                    match *expr.inner {
                        Expr::Path(path) => {
                            let last = path.last().unwrap();
                            ensure_macro_name(&last.name)?;

                            if let Some(r) = path.iter().find_map(|r| r.generics.as_ref()) {
                                return Err(ErrorContext::new(
                                    "macro paths cannot have generics",
                                    r.span,
                                )
                                .cut());
                            }

                            Box::new(Expr::RustMacro(
                                path.into_iter()
                                    .map(|c: PathComponent<'_>| c.name)
                                    .collect(),
                                args,
                            ))
                        }
                        Expr::Var(name) => {
                            let name = WithSpan::new(name, expr.span);
                            ensure_macro_name(&name)?;
                            Box::new(Expr::RustMacro(vec![name], args))
                        }
                        _ => {
                            i.reset(&i_before);
                            return fail(i);
                        }
                    }
                }
            };
            expr = WithSpan::new(inner, span);
            i_before = i.checkpoint();
        }
        Ok(expr)
    }

    fn r#macro(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Self>> {
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

        fn macro_arguments<'a: 'l, 'l>(
            i: &mut InputStream<'a, 'l>,
            open_token: Group,
        ) -> ParseResult<'a, Suffix<'a>> {
            fn inner<'a: 'l, 'l>(
                i: &mut InputStream<'a, 'l>,
                open_token: Group,
            ) -> ParseResult<'a, <InputStream<'a, 'l> as Stream>::Checkpoint> {
                let mut open_list = vec![open_token];
                loop {
                    let before = i.checkpoint();
                    let token = ws(opt(token.with_span())).parse_next(i)?;
                    let after = i.checkpoint();
                    let Some((token, span)) = token else {
                        return cut_error!("expected valid tokens in macro call", *i);
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
                            span,
                        );
                    } else if open_list.is_empty() {
                        i.reset(&before);
                        return Ok(after);
                    }
                }
            }

            let p = |i: &mut _| inner(i, open_token);
            let (checkpoint, inner) = p.with_taken().parse_next(i)?;
            i.reset(&checkpoint);
            Ok(Suffix::MacroCall(inner))
        }

        fn lifetime<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
            // this code assumes that we tried to match char literals before calling this function
            let p = (
                '\''.void(),
                identifier,
                opt((repeat(1.., '#'), opt(identifier))),
                opt('\'').map(|o| o.is_some()),
            );
            let ((_, front, back, quot), span) = p.with_span().parse_next(i)?;
            match (front, back, quot) {
                // this case should never be encountered
                (_, _, true) => cut_error!(
                    "cannot have multiple characters in a character literal, \
                    use `\"...\"` to write a string",
                    span
                ),
                // a normal lifetime
                (identifier, None, _) => {
                    if !is_rust_keyword(identifier) {
                        Ok(())
                    } else {
                        cut_error!(
                            "a non-raw lifetime cannot be named like an existing keyword",
                            span,
                        )
                    }
                }
                // a raw lifetime
                ("r", Some((1, Some(identifier))), _) => {
                    if matches!(identifier, "Self" | "self" | "crate" | "super" | "_") {
                        cut_error!(
                            format!("`{}` cannot be a raw lifetime", identifier.escape_debug()),
                            span,
                        )
                    } else {
                        Ok(())
                    }
                }
                // an illegal prefix (not `'r#..`, multiple `#` or no identifier after `#`)
                (_, Some(_), _) => cut_error!("wrong lifetime format", span),
            }
        }

        fn token<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Token> {
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

        fn line_comment<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
            fn inner<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, bool> {
                let mut p = (
                    "//".span(),
                    alt((
                        ('/', not(peek('/'))).value(true),
                        '!'.value(true),
                        empty.value(false),
                    )),
                );
                let (start, is_doc_comment) = p.parse_next(i)?;
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

        fn block_comment<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
            fn inner<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, bool> {
                let is_doc_comment = alt((
                    ('*', not(peek(one_of(['*', '/'])))).value(true),
                    '!'.value(true),
                    empty.value(false),
                ));
                let (is_doc_comment, start) =
                    preceded("/*", is_doc_comment).with_span().parse_next(i)?;

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

        fn identifier_or_prefixed_string<'a: 'l, 'l>(
            i: &mut InputStream<'a, 'l>,
        ) -> ParseResult<'a, ()> {
            // <https://doc.rust-lang.org/reference/tokens.html#r-lex.token.literal.str-raw.syntax>

            let ((prefix, hashes, quot), prefix_span): ((_, usize, _), _) =
                (identifier, repeat(.., '#'), opt('"'))
                    .with_span()
                    .parse_next(i)?;
            if hashes >= 256 {
                return cut_error!(
                    "a maximum of 255 hashes `#` are allowed with raw and prefixed strings",
                    prefix_span,
                );
            }

            let str_kind = match prefix {
                // raw cstring or byte slice
                "br" => Some(StrPrefix::Binary),
                "cr" => Some(StrPrefix::CLike),
                // raw string string or identifier
                "r" => None,
                // a simple identifier
                _ if hashes == 0 && quot.is_none() => return Ok(()),
                // reserved prefix: reject
                _ => {
                    return cut_error!(
                        format!("reserved prefix `{}#`", prefix.escape_debug()),
                        prefix_span,
                    );
                }
            };

            if quot.is_some() {
                // got a raw string

                let delim = format!("\"{:#<hashes$}", "");
                let p = terminated(take_until(.., delim.as_str()).with_span(), delim.as_str());
                let Some((inner, inner_span)) = opt(p).parse_next(i)? else {
                    return cut_error!("unterminated raw string", prefix_span);
                };

                if inner.split('\r').skip(1).any(|s| !s.starts_with('\n')) {
                    return cut_error!(
                        format!(
                            "a bare CR (Mac linebreak) is not allowed in string literals, \
                            use NL (Unix linebreak) or CRNL (Windows linebreak) instead, \
                            or type `\\r` explicitly",
                        ),
                        inner_span,
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
                    return cut_error!(msg, prefix_span);
                }

                not_suffix_with_hash(i)?;
                Ok(())
            } else if hashes == 0 {
                // a simple identifier
                Ok(())
            } else if let Some((id, span)) = opt(identifier.with_span()).parse_next(i)? {
                // got a raw identifier

                if str_kind.is_some() {
                    // an invalid raw identifier like `cr#async`
                    cut_error!(
                        format!(
                            "reserved prefix `{}#`, only `r#` is allowed with raw identifiers",
                            prefix.escape_debug(),
                        ),
                        prefix_span,
                    )
                } else if hashes > 1 {
                    // an invalid raw identifier like `r##async`
                    cut_error!(
                        "only one `#` is allowed in raw identifier delimitation",
                        prefix_span,
                    )
                } else {
                    // a raw identifier like `r#async`
                    if matches!(id, "self" | "Self" | "super" | "crate" | "_") {
                        cut_error!(
                            format!("`{}` cannot be a raw identifier", id.escape_debug()),
                            span,
                        )
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
                    prefix_span,
                )
            }
        }

        fn hash<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Token> {
            let (quot, span) = preceded('#', opt('"')).with_span().parse_next(i)?;
            if quot.is_some() {
                return cut_error!(
                    "unprefixed guarded string literals are reserved for future use",
                    span,
                );
            }
            Ok(Token::SomeOther)
        }

        fn punctuation<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
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

        fn open<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Group> {
            alt((
                '('.value(Group::Paren),
                '{'.value(Group::Brace),
                '['.value(Group::Bracket),
            ))
            .parse_next(i)
        }

        fn close<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Group> {
            alt((
                ')'.value(Group::Paren),
                '}'.value(Group::Brace),
                ']'.value(Group::Bracket),
            ))
            .parse_next(i)
        }

        let (span, open_token) = (ws('!'.span()), open).parse_next(i)?;
        let inner = (|i: &mut _| macro_arguments(i, open_token)).parse_next(i)?;
        Ok(WithSpan::new(inner, span))
    }

    fn associated_item(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Self>> {
        let mut p = (
            ws(terminated('.'.span(), not('.'))),
            cut_err((
                |i: &mut _| {
                    let (name, span) = alt((digit1, identifier)).with_span().parse_next(i)?;
                    if !crate::can_be_variable_name(name) {
                        return cut_error!(
                            format!("`{}` cannot be used as an identifier", name.escape_debug()),
                            span,
                        );
                    }
                    Ok(WithSpan::new(name, span))
                },
                opt(call_generics),
            )),
        );
        let (span, (name, generics)) = p.parse_next(i)?;
        Ok(WithSpan::new(
            Self::AssociatedItem(AssociatedItem { name, generics }),
            span,
        ))
    }

    fn index(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Self>> {
        let mut p = (
            ws('['.span()),
            cut_err((ws(move |i: &mut _| Expr::parse(i, true)), opt(']'))),
        );
        let (span, (expr, closed)) = p.parse_next(i)?;
        if closed.is_none() {
            return cut_error!("matching closing `]` is missing", span);
        }
        Ok(WithSpan::new(Self::Index(expr), span))
    }

    fn call(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Self>> {
        let mut p = (opt(call_generics), Expr::arguments);
        let (generics, args) = p.parse_next(i)?;
        let (args, span) = args.deconstruct();
        Ok(WithSpan::new(Self::Call { generics, args }, span))
    }

    fn r#try(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Self>> {
        let span = preceded(skip_ws0, '?'.span()).parse_next(i)?;
        Ok(WithSpan::new(Self::Try, span))
    }
}

fn doc_comment_no_bare_cr<'a: 'l, 'l>(
    i: &mut InputStream<'a, 'l>,
    inner: fn(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, bool>,
) -> ParseResult<'a, ()> {
    let ((is_doc_comment, comment), span) = inner.with_taken().with_span().parse_next(i)?;
    if is_doc_comment && comment.split('\r').skip(1).any(|s| !s.starts_with('\n')) {
        cut_error!(
            "bare CR not allowed in doc comment, 
            use NL (Unix linebreak) or CRNL (Windows linebreak) instead",
            span,
        )
    } else {
        Ok(())
    }
}

fn ensure_macro_name<'a>(name: &WithSpan<&'a str>) -> ParseResult<'a, ()> {
    if matches!(**name, "_" | "crate" | "super" | "Self" | "self") {
        return cut_error!(format!("`{}` is not a valid macro name", **name), name.span);
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq)]
pub struct TyGenerics<'a> {
    pub refs: usize,
    pub path: Vec<WithSpan<&'a str>>,
    pub args: Option<WithSpan<Vec<WithSpan<TyGenerics<'a>>>>>,
}

impl<'a: 'l, 'l> TyGenerics<'a> {
    fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, WithSpan<Self>> {
        let path = separated(
            1..,
            ws(identifier
                .with_span()
                .map(|(name, span)| WithSpan::new(name, span))),
            "::",
        )
        .map(|v: Vec<_>| v);

        let p = ws((repeat(0.., ws('&')), path, opt(Self::args)));
        let ((refs, path, args), span) = p.with_span().parse_next(i)?;
        let max_refs = 20;
        if refs > max_refs {
            return cut_error!(format!("too many references (> {max_refs})"), span);
        }

        if let [name] = path.as_slice() {
            if matches!(**name, "super" | "self" | "crate") {
                // `Self` and `_` are allowed
                return err_reserved_identifier(name);
            }
        } else {
            for (idx, name) in path.iter().enumerate() {
                if **name == "_" {
                    // `_` is never allowed
                    return err_underscore_identifier(name);
                } else if idx > 0 && matches!(**name, "super" | "self" | "Self" | "crate") {
                    // At the front of the path, "super" | "self" | "Self" | "crate" are allowed.
                    // Inside the path, they are not allowed.
                    return err_reserved_identifier(name);
                }
            }
        }

        Ok(WithSpan::new(TyGenerics { refs, path, args }, span))
    }

    fn args(
        i: &mut InputStream<'a, 'l>,
    ) -> ParseResult<'a, WithSpan<Vec<WithSpan<TyGenerics<'a>>>>> {
        let mut p = cut_err(terminated(
            opt(terminated(
                separated(1.., TyGenerics::parse, ws(',')),
                ws(opt(',')),
            )),
            '>',
        ));

        let span = ws('<'.span()).parse_next(i)?;
        let _level_guard = i.state.level.nest(i)?;
        let args = p.parse_next(i)?;
        Ok(WithSpan::new(args.unwrap_or_default(), span))
    }
}

pub(crate) fn call_generics<'a: 'l, 'l>(
    i: &mut InputStream<'a, 'l>,
) -> ParseResult<'a, WithSpan<Vec<WithSpan<TyGenerics<'a>>>>> {
    preceded(ws("::"), cut_err(TyGenerics::args)).parse_next(i)
}
