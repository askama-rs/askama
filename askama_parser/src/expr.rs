use winnow::Parser;
use winnow::ascii::digit1;
use winnow::combinator::{
    alt, cut_err, empty, fail, not, opt, peek, preceded, repeat, separated, terminated,
};
use winnow::error::ErrMode;
use winnow::stream::{Location, Stream};
use winnow::token::{any, one_of, take, take_until};

use crate::node::CondTest;
use crate::{
    CharLit, ErrorContext, HashSet, InputStream, LevelGuard, Num, ParseResult, PathOrIdentifier,
    Span, StrLit, StrPrefix, WithSpan, any_rust_token, char_lit, cut_error, deny_any_rust_token,
    filter, identifier, is_rust_keyword, keyword, not_suffix_with_hash, num_lit,
    path_or_identifier, skip_ws0, skip_ws1, str_lit, ws,
};

const MAX_REFS: usize = 20;

#[derive(Clone, Copy, Default)]
struct Allowed {
    underscore: bool,
    super_keyword: bool,
}

fn check_expr<'a>(expr: &Expr<'a>, allowed: Allowed) -> ParseResult<'a, ()> {
    match *expr {
        Expr::Var { name, span } => {
            // List can be found in rust compiler "can_be_raw" function (although in our case, it's
            // also used in cases like `match`, so `self` is allowed in this case).
            if (!allowed.super_keyword && name == "super") || matches!(name, "crate" | "Self") {
                err_reserved_identifier(&WithSpan::new(name, span))
            } else if !allowed.underscore && name == "_" {
                err_underscore_identifier(&WithSpan::new(name, span))
            } else {
                Ok(())
            }
        }
        Expr::IsDefined { var_name, span } | Expr::IsNotDefined { var_name, span } => {
            if var_name == "_" {
                err_underscore_identifier(&WithSpan::new(var_name, span))
            } else {
                Ok(())
            }
        }
        Expr::Path { ref components, .. } => {
            if let [arg] = components.as_slice()
                && !crate::can_be_variable_name(*arg.name)
            {
                return err_reserved_identifier(&arg.name);
            }
            Ok(())
        }
        Expr::Array { ref elems, .. }
        | Expr::Tuple { ref elems, .. }
        | Expr::Concat {
            exprs: ref elems, ..
        } => {
            for elem in elems {
                check_expr(elem, allowed)?;
            }
            Ok(())
        }
        Expr::ArrayRepeat {
            ref value,
            ref repeat,
            ..
        } => {
            check_expr(value, allowed)?;
            check_expr(repeat, allowed)?;
            Ok(())
        }
        Expr::AssociatedItem {
            ref parent_item,
            ref associated_item,
            ..
        } => {
            if *associated_item.name == "_" {
                err_underscore_identifier(&associated_item.name)
            } else if !crate::can_be_variable_name(*associated_item.name) {
                err_reserved_identifier(&associated_item.name)
            } else {
                check_expr(parent_item, Allowed::default())
            }
        }
        Expr::Index {
            ref parent_item,
            ref index,
            ..
        } => {
            check_expr(parent_item, Allowed::default())?;
            check_expr(index, Allowed::default())
        }
        Expr::BinOp { ref inner, .. } => {
            check_expr(&inner.lhs, Allowed::default())?;
            check_expr(&inner.rhs, Allowed::default())
        }
        Expr::Range { ref inner, .. } => {
            if let Some(elem1) = inner.lhs.as_ref() {
                check_expr(elem1, Allowed::default())?;
            }
            if let Some(elem2) = inner.rhs.as_ref() {
                check_expr(elem2, Allowed::default())?;
            }
            Ok(())
        }
        Expr::As { lhs: ref elem, .. }
        | Expr::Unary { expr: ref elem, .. }
        | Expr::Group { ref elem, .. }
        | Expr::NamedArgument {
            value: ref elem, ..
        }
        | Expr::Try { expr: ref elem, .. } => check_expr(elem, Allowed::default()),
        Expr::Call { ref call, .. } => {
            check_expr(
                &call.path,
                Allowed {
                    underscore: false,
                    super_keyword: true,
                },
            )?;
            for arg in &call.args {
                check_expr(arg, Allowed::default())?;
            }
            Ok(())
        }
        Expr::Filter { ref inner, .. } => {
            for arg in &inner.arguments {
                check_expr(arg, Allowed::default())?;
            }
            Ok(())
        }
        Expr::Struct { ref inner, .. } => {
            check_expr(
                &inner.path,
                Allowed {
                    underscore: false,
                    super_keyword: true,
                },
            )?;
            for field in &inner.fields {
                if field.name.inner == "_" {
                    return err_underscore_identifier(&field.name);
                } else if !crate::can_be_variable_name(field.name.inner) {
                    return err_reserved_identifier(&field.name);
                }
                if let Some(ref value) = field.value {
                    check_expr(value, Allowed::default())?;
                }
            }
            Ok(())
        }
        Expr::LetCond { ref cond, .. } => check_expr(&cond.expr, Allowed::default()),
        Expr::Closure {
            ref params,
            ref body,
            ..
        } => {
            for param in params {
                if !crate::can_be_variable_name(param.inner) {
                    return err_reserved_identifier(param);
                }
            }
            check_expr(body, Allowed::default())
        }
        Expr::ArgumentPlaceholder(span) => cut_error!("unreachable", span),
        Expr::BoolLit { .. }
        | Expr::NumLit { .. }
        | Expr::StrLit { .. }
        | Expr::CharLit { .. }
        | Expr::RustMacro { .. }
        | Expr::FilterSource(_) => Ok(()),
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
    pub generics: Option<TyGenericArgs<'a>>,
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
    BoolLit {
        value: bool,
        span: Span,
    },
    NumLit {
        num_with_suffix: &'a str,
        num: Num<'a>,
        span: Span,
    },
    StrLit {
        inner: StrLit<'a>,
        span: Span,
    },
    CharLit {
        inner: CharLit<'a>,
        span: Span,
    },
    Var {
        name: &'a str,
        span: Span,
    },
    Path {
        components: Vec<PathComponent<'a>>,
        span: Span,
    },
    Array {
        elems: Vec<Box<Expr<'a>>>,
        span: Span,
    },
    ArrayRepeat {
        value: Box<Expr<'a>>,
        repeat: Box<Expr<'a>>,
        span: Span,
    },
    AssociatedItem {
        parent_item: Box<Expr<'a>>,
        associated_item: AssociatedItem<'a>,
        span: Span,
    },
    Index {
        parent_item: Box<Expr<'a>>,
        index: Box<Expr<'a>>,
        span: Span,
    },
    Filter {
        inner: Filter<'a>,
        span: Span,
    },
    As {
        lhs: Box<Expr<'a>>,
        target: WithSpan<&'a str>,
        span: Span,
    },
    NamedArgument {
        name: WithSpan<&'a str>,
        value: Box<Expr<'a>>,
        span: Span,
    },
    Unary {
        operator: &'a str,
        expr: Box<Expr<'a>>,
        span: Span,
    },
    BinOp {
        inner: BinOp<'a>,
        span: Span,
    },
    Range {
        inner: Range<'a>,
        span: Span,
    },
    /// Potentially a tuple with one element without a comma: `(expr)`. Or could just be an element
    /// between parens.
    Group {
        elem: Box<Expr<'a>>,
        span: Span,
    },
    Tuple {
        elems: Vec<Box<Expr<'a>>>,
        span: Span,
    },
    Call {
        call: Call<'a>,
        span: Span,
    },
    RustMacro {
        path: Vec<WithSpan<&'a str>>,
        arguments: WithSpan<&'a str>,
        span: Span,
    },
    /// An expression followed by `?`.
    Try {
        expr: Box<Expr<'a>>,
        span: Span,
    },
    /// A struct expression (ie `Foo {a: u32, ..Default::default() })`).
    Struct {
        inner: ExprStruct<'a>,
        span: Span,
    },
    /// This variant should never be used directly. It is created when generating filter blocks.
    FilterSource(Span),
    /// The `is defined` "keyword" (or keywords, whatever).
    IsDefined {
        var_name: &'a str,
        span: Span,
    },
    /// The `is not defined` "keyword" (or keywords, whatever).
    IsNotDefined {
        var_name: &'a str,
        span: Span,
    },
    /// String concatenation with the `~` operator.
    Concat {
        exprs: Vec<Box<Expr<'a>>>,
        span: Span,
    },
    /// If you have `&& let Some(y)`, this variant handles it.
    LetCond {
        cond: CondTest<'a>,
        span: Span,
    },
    /// This variant should never be used directly.
    /// It is used for the handling of named arguments in the generator, esp. with filters.
    ArgumentPlaceholder(Span),
    /// A closure, only allowed as an argument: `|a, b| a.cmp(b)`.
    Closure {
        params: Vec<WithSpan<&'a str>>,
        body: Box<Expr<'a>>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Call<'a> {
    pub path: Box<Expr<'a>>,
    pub generics: Option<TyGenericArgs<'a>>,
    pub args: Vec<Box<Expr<'a>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Range<'a> {
    pub op: &'a str,
    pub lhs: Option<Box<Expr<'a>>>,
    pub rhs: Option<Box<Expr<'a>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinOp<'a> {
    pub op: &'a str,
    pub lhs: Box<Expr<'a>>,
    pub rhs: Box<Expr<'a>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprStruct<'a> {
    pub path: Box<Expr<'a>>,
    pub fields: Vec<ExprStructField<'a>>,
    pub base: Option<Box<Expr<'a>>>,
}

impl<'a: 'l, 'l> Expr<'a> {
    pub fn span(&self) -> Span {
        match *self {
            Self::BoolLit { span, .. }
            | Self::NumLit { span, .. }
            | Self::StrLit { span, .. }
            | Self::CharLit { span, .. }
            | Self::Var { span, .. }
            | Self::Path { span, .. }
            | Self::Array { span, .. }
            | Self::ArrayRepeat { span, .. }
            | Self::AssociatedItem { span, .. }
            | Self::Index { span, .. }
            | Self::Filter { span, .. }
            | Self::As { span, .. }
            | Self::NamedArgument { span, .. }
            | Self::Unary { span, .. }
            | Self::BinOp { span, .. }
            | Self::Range { span, .. }
            | Self::Group { span, .. }
            | Self::Tuple { span, .. }
            | Self::Call { span, .. }
            | Self::RustMacro { span, .. }
            | Self::Try { span, .. }
            | Self::Struct { span, .. }
            | Self::FilterSource(span)
            | Self::IsDefined { span, .. }
            | Self::IsNotDefined { span, .. }
            | Self::Concat { span, .. }
            | Self::LetCond { span, .. }
            | Self::ArgumentPlaceholder(span)
            | Self::Closure { span, .. } => span,
        }
    }

    pub(super) fn arguments(
        i: &mut InputStream<'a, 'l>,
    ) -> ParseResult<'a, (Vec<Box<Self>>, Span)> {
        fn comma<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
            (ws(','), no_comma).void().parse_next(i)
        }

        fn no_comma<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, ()> {
            if let Some(span) = opt(','.span()).parse_next(i)? {
                cut_error!(
                    "expected an expression, found a comma in argument list",
                    span
                )
            } else {
                Ok(())
            }
        }

        let span = terminated(ws('('.span()), no_comma).parse_next(i)?;

        // The stack footprint of this function is huge. Effectively, we half the maximum nesting
        // level of function calls `a(b(c(d(..))))` to make sure not to exceed the stack limit.
        let mut _level_guard = i.state.level.nest_multiple(i, 2)?;

        let mut named_arguments = HashSet::default();
        let arguments = separated(
            1..,
            move |i: &mut _| {
                // Needed to prevent borrowing it twice between this closure and the one
                // calling `Self::named_arguments`.
                let named_arguments = &mut named_arguments;
                let has_named_arguments = !named_arguments.is_empty();

                let mut p = alt((
                    move |i: &mut _| Self::named_argument(i, named_arguments),
                    Self::argument,
                ));
                let expr = p.parse_next(i)?;
                if has_named_arguments && !matches!(*expr, Self::NamedArgument { .. }) {
                    return cut_error!("named arguments must always be passed last", expr.span());
                }
                Ok(expr)
            },
            comma,
        );

        let (args, closed) =
            cut_err((opt(terminated(arguments, opt(comma))), opt(ws(')')))).parse_next(i)?;
        if closed.is_none() {
            cut_error!("matching closing `)` is missing", span)
        } else {
            Ok((args.unwrap_or_default(), span.into()))
        }
    }

    fn named_argument(
        i: &mut InputStream<'a, 'l>,
        named_arguments: &mut HashSet<&'a str>,
    ) -> ParseResult<'a, Box<Self>> {
        let (((argument, arg_span), _, value), span) =
            (identifier.with_span(), ws('='), Self::argument)
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

        Ok(Box::new(Self::NamedArgument {
            name: WithSpan::new(argument, arg_span),
            value,
            span: span.into(),
        }))
    }

    fn argument(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        // A leading `|` can only start a closure: in an argument there is nothing to filter.
        if i.trim_ascii_start().starts_with('|') {
            Self::closure(i)
        } else {
            Self::parse(i, false)
        }
    }

    fn closure(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let param = ws(identifier.with_span()).map(|(name, span)| WithSpan::new(name, span));
        let ((_, params, closing), span): ((_, Option<Vec<_>>, _), _) =
            (ws('|'), opt(separated(1.., param, ws(','))), opt(ws('|')))
                .with_span()
                .parse_next(i)?;
        let (Some(params), Some(_)) = (params, closing) else {
            return cut_error!(
                "expected a closure with one or more parameters, like `|a, b| a.cmp(b)`",
                span,
            );
        };
        let body = cut_err(move |i: &mut _| Self::parse(i, false)).parse_next(i)?;
        Ok(Box::new(Self::Closure {
            params,
            body,
            span: span.into(),
        }))
    }

    pub(super) fn parse(
        i: &mut InputStream<'a, 'l>,
        allow_underscore: bool,
    ) -> ParseResult<'a, Box<Self>> {
        let _level_guard = i.state.level.nest(i)?;
        let mut result = Self::range(i, allow_underscore);
        if let Err(err) = &mut result {
            try_assign_fallback_error(i, err);
        }
        result
    }

    fn range(i: &mut InputStream<'a, 'l>, allow_underscore: bool) -> ParseResult<'a, Box<Self>> {
        let range_right = move |i: &mut InputStream<'a, 'l>| {
            let ((op, span), rhs) =
                (ws(alt(("..=", "..")).with_span()), opt(Self::infix)).parse_next(i)?;
            Ok((op, rhs, span))
        };

        // `..expr` or `..`
        let range_to = range_right.map(move |(op, rhs, span)| {
            Box::new(Self::Range {
                inner: Range { op, lhs: None, rhs },
                span: span.into(),
            })
        });

        // `expr..expr` or `expr..`
        let range_from = (Self::infix, opt(range_right)).map(move |(lhs, rhs)| match rhs {
            Some((op, rhs, span)) => Box::new(Self::Range {
                inner: Range {
                    op,
                    lhs: Some(lhs),
                    rhs,
                },
                span: span.into(),
            }),
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

    /// Parses the binary operators with the
    /// [Double-E method](https://erikeidt.github.io/The-Double-E-Method): instead of one function
    /// per precedence level, it alternates between an operand and an operator, and keeps the
    /// operators that wait for their right-hand side on a stack, with their left-hand side.
    fn infix(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let mut stack: Vec<(Box<Self>, InfixOp<'a>, LevelGuard<'l>)> = Vec::new();
        let mut operand_start = *i;
        let mut expr = Self::is_as(i)?;
        loop {
            let before = *i;
            let Some((op, spaced)) = infix_op(i, &operand_start)? else {
                break;
            };
            // All binary operators are left-associative. A chain of one precedence keeps
            // counting on the same guard, which is given back once a looser operator ends it.
            let mut guard = None;
            while let Some((lhs, top, top_guard)) = stack.pop_if(|(_, top, _)| top.prec >= op.prec)
            {
                if top.prec == op.prec {
                    if op.prec == Prec::Compare {
                        return cut_error!(
                            format!(
                                "comparison operators cannot be chained; \
                                consider using explicit parentheses, e.g.  `(_ {} _) {} _`",
                                top.op, op.op,
                            ),
                            op.span,
                        );
                    }
                    guard = Some(top_guard);
                }
                expr = top.apply(lhs, expr);
            }
            let mut guard = guard.unwrap_or_else(|| i.state.level.guard());
            // `~` flattens into one `Concat`, and a comparison cannot chain: neither nests.
            if !matches!(op.prec, Prec::Compare | Prec::Concat) {
                guard.nest(&before)?;
            }

            operand_start = *i;
            match Self::is_as(i) {
                Ok(rhs) if spaced => stack.push((std::mem::replace(&mut expr, rhs), op, guard)),
                Ok(_) => {
                    let msg = "the concat operator `~` must be surrounded by spaces";
                    return cut_error!(msg, op.span);
                }
                // An operator without a right-hand side is not part of the expression.
                Err(ErrMode::Backtrack(_)) => {
                    *i = before;
                    break;
                }
                Err(err) => return Err(err),
            }
        }
        while let Some((lhs, op, _)) = stack.pop() {
            expr = op.apply(lhs, expr);
        }
        Ok(expr)
    }

    fn is_as(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let lhs = Self::filtered(i)?;
        if !i.trim_ascii_start().starts_with(['i', 'a']) {
            return Ok(lhs);
        }
        let checkpoint = i.checkpoint();
        let rhs = opt(ws(identifier.with_span())).parse_next(i)?;
        match rhs {
            Some(("is", span)) => Self::is_as_handle_is(i, &lhs, span),
            Some(("as", span)) => Self::is_as_handle_as(i, lhs, span),
            _ => {
                i.reset(&checkpoint);
                Ok(lhs)
            }
        }
    }

    fn is_as_handle_is(
        i: &mut InputStream<'a, 'l>,
        lhs: &Expr<'a>,
        span: std::ops::Range<usize>,
    ) -> ParseResult<'a, Box<Self>> {
        let mut rhs = opt(terminated(opt(keyword("not")), ws(keyword("defined"))));
        let is_not = match rhs.parse_next(i)? {
            None => {
                return cut_error!("expected `defined` or `not defined` after `is`", span);
            }
            Some(not) => not.is_some(),
        };
        let var_name = match *lhs {
            Self::Var { name, .. } => name,
            Self::AssociatedItem { .. } => {
                return cut_error!(
                    "`is defined` operator can only be used on variables, not on their fields",
                    span,
                );
            }
            _ => {
                return cut_error!("`is defined` operator can only be used on variables", span);
            }
        };
        let span = span.into();
        Ok(Box::new(if is_not {
            Self::IsNotDefined { var_name, span }
        } else {
            Self::IsDefined { var_name, span }
        }))
    }

    fn is_as_handle_as(
        i: &mut InputStream<'a, 'l>,
        lhs: Box<Expr<'a>>,
        span: std::ops::Range<usize>,
    ) -> ParseResult<'a, Box<Self>> {
        let target = opt(path_or_identifier).parse_next(i)?;
        let Some(PathOrIdentifier::Identifier(target)) = target else {
            return cut_error!(
                "`as` operator expects the name of a primitive type on its right-hand side, \
                not a path or alias",
                span,
            );
        };

        if crate::PRIMITIVE_TYPES.contains(&target) {
            Ok(Box::new(Self::As {
                lhs,
                target,
                span: span.into(),
            }))
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

    fn filtered(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let mut res = Self::prefix(i)?;

        let mut level_guard = i.state.level.guard();
        let mut i_before = *i;
        while i.trim_ascii_start().starts_with('|')
            && let Some((mut filter, span)) = opt(ws(filter.with_span())).parse_next(i)?
        {
            level_guard.nest(&i_before)?;
            filter.arguments.insert(0, res);
            res = Box::new(Self::Filter {
                inner: filter,
                span: span.into(),
            });
            i_before = *i;
        }
        Ok(res)
    }

    fn prefix(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        // This is a rare place where we create recursion in the parsed AST
        // without recursing the parser call stack. However, this can lead
        // to stack overflows in drop glue when the AST is very deep.
        let mut level_guard = i.state.level.guard();
        let mut i_before = *i;
        let mut ops = vec![];
        while i.trim_ascii_start().starts_with(['!', '-', '*', '&'])
            && let Some(op) = opt(ws(alt(("!", "-", "*", "&")).with_span())).parse_next(i)?
        {
            level_guard.nest(&i_before)?;
            ops.push(op);
            i_before = *i;
        }

        let mut expr = Suffix::parse(i)?;
        for (op, span) in ops.into_iter().rev() {
            expr = Box::new(Self::Unary {
                operator: op,
                expr,
                span: span.into(),
            });
        }

        Ok(expr)
    }

    fn single(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        // Only `b"…"`, `b'…'` and `c"…"` are literals that start with a letter.
        if let [b'a' | b'd'..=b'z' | b'A'..=b'Z', ..] = i.as_bytes() {
            return Self::path_var_bool(i);
        }
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

    fn group(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        (skip_ws0, peek('(')).parse_next(i)?;
        Self::group_actually(i)
    }

    // `Self::group()` is quite big. Let's only put it on the stack if needed.
    #[inline(never)]
    fn group_actually(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let start = i.current_token_start();
        cut_err(preceded('(', |i: &mut _| {
            Self::group_actually_inner(i, start)
        }))
        .parse_next(i)
    }

    #[inline]
    fn group_actually_inner(
        i: &mut InputStream<'a, 'l>,
        start: usize,
    ) -> ParseResult<'a, Box<Self>> {
        let group_span = |i: &InputStream<'a, 'l>| Span::new(start..i.current_token_start());
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
            (None, None, Some(_)) => {
                return Ok(Box::new(Self::Tuple {
                    elems: vec![],
                    span: group_span(i),
                }));
            }
            // `(expr)`
            (Some(expr), None, Some(_)) => {
                return Ok(Box::new(Self::Group {
                    elem: expr,
                    span: group_span(i),
                }));
            }
            // `(expr,)`
            (Some(expr), Some(_), Some(_)) => {
                return Ok(Box::new(Self::Tuple {
                    elems: vec![expr],
                    span: group_span(i),
                }));
            }
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
            return Ok(Box::new(Self::Tuple {
                elems: exprs,
                span: group_span(i),
            }));
        } else if comma.is_some() {
            "expected `)` or an expression"
        } else {
            "expected `,` or `)`"
        };
        cut_error!(msg, span)
    }

    fn array(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let _level_guard = i.state.level.nest(i)?;
        let (span, mut elements): (std::ops::Range<usize>, Vec<_>) = (
            '['.span(),
            separated(0.., ws(move |i: &mut _| Self::parse(i, true)), ','),
        )
            .parse_next(i)?;

        let expr = if let Some(semicolon) = opt(ws(';'.span())).parse_next(i)? {
            // array repeat [<el_expr>; <cnt_expr>]
            let Some(elem) = elements.pop() else {
                return cut_error!(
                    "expected element expression for array repeat syntax",
                    semicolon
                );
            };
            if !elements.is_empty() {
                return cut_error!("unexpected `;` after expression", semicolon);
            }
            let Some(count) = opt(ws(move |i: &mut _| Expr::parse(i, true))).parse_next(i)? else {
                return cut_error!(
                    "expected count expression for array repeat syntax after `;`",
                    semicolon
                );
            };
            if let Some((delim, span)) = ws(opt(one_of((',', ';')).with_span())).parse_next(i)? {
                return cut_error!(
                    format!(
                        "unexpected delimiter `{}`.\n\
                        Use nested syntax to write a multi-dimensional array: [[expr; N]; M]",
                        delim.escape_debug()
                    ),
                    span
                );
            }
            Self::ArrayRepeat {
                value: elem,
                repeat: count,
                span: span.clone().into(),
            }
        } else {
            // normal array [<expr>,...?]
            if !elements.is_empty() {
                // strip optional trailing comma
                ws(opt(',')).parse_next(i)?;
            }
            Self::Array {
                elems: elements,
                span: span.clone().into(),
            }
        };

        if ws(opt(']')).parse_next(i)?.is_none() {
            let (next, span) = match opt(any_rust_token.with_span()).parse_next(i)? {
                Some((next, span)) => (Some(next), span),
                None => (None, span),
            };
            return cut_error!(
                match next {
                    Some(delim @ (")" | "}")) => format!(
                        "mismatched closing delimiter `{}`, expected `]`",
                        delim.escape_debug()
                    ),
                    Some(token) =>
                        format!("unexpected token `{}`, expected `]`", token.escape_debug()),
                    _ => "missing closing delimiter `]`".to_owned(),
                },
                span
            );
        }
        Ok(Box::new(expr))
    }

    fn path_var_bool(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let (ret, span) = path_or_identifier.with_span().parse_next(i)?;
        let span = Span::new(span);
        Ok(Box::new(match ret {
            PathOrIdentifier::Path(v) => Self::Path {
                components: v,
                span,
            },
            PathOrIdentifier::Identifier(v) if *v == "true" => Self::BoolLit { value: true, span },
            PathOrIdentifier::Identifier(v) if *v == "false" => {
                Self::BoolLit { value: false, span }
            }
            PathOrIdentifier::Identifier(v) => Self::Var { name: *v, span },
        }))
    }

    fn str(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let (s, span) = str_lit.with_span().parse_next(i)?;
        Ok(Box::new(Self::StrLit {
            inner: s,
            span: span.into(),
        }))
    }

    fn num(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let ((num, full), span) = num_lit.with_taken().with_span().parse_next(i)?;
        Ok(Box::new(Expr::NumLit {
            num_with_suffix: full,
            num,
            span: span.into(),
        }))
    }

    fn char(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Self>> {
        let (c, span) = char_lit.with_span().parse_next(i)?;
        Ok(Box::new(Self::CharLit {
            inner: c,
            span: span.into(),
        }))
    }

    #[must_use]
    pub fn contains_bool_lit_or_is_defined(&self) -> bool {
        match self {
            Self::BoolLit { .. } | Self::IsDefined { .. } | Self::IsNotDefined { .. } => true,
            Self::Unary { expr, .. } | Self::Group { elem: expr, .. } => {
                expr.contains_bool_lit_or_is_defined()
            }
            Self::BinOp { inner, .. } if matches!(inner.op, "&&" | "||") => {
                inner.lhs.contains_bool_lit_or_is_defined()
                    || inner.rhs.contains_bool_lit_or_is_defined()
            }
            Self::NumLit { .. }
            | Self::StrLit { .. }
            | Self::CharLit { .. }
            | Self::Var { .. }
            | Self::FilterSource(..)
            | Self::RustMacro { .. }
            | Self::As { .. }
            | Self::Call { .. }
            | Self::Range { .. }
            | Self::Try { .. }
            | Self::Struct { .. }
            | Self::NamedArgument { .. }
            | Self::Filter { .. }
            | Self::AssociatedItem { .. }
            | Self::Index { .. }
            | Self::Tuple { .. }
            | Self::Array { .. }
            | Self::ArrayRepeat { .. }
            | Self::BinOp { .. }
            | Self::Path { .. }
            | Self::Concat { .. }
            | Self::LetCond { .. }
            | Self::ArgumentPlaceholder(..)
            | Self::Closure { .. } => false,
        }
    }
}

/// Precedence of the operators [`Expr::infix()`] handles, from the loosest to the tightest
/// binding.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Or,
    And,
    Compare,
    BitOr,
    BitXor,
    BitAnd,
    Shift,
    AddSub,
    Concat,
    MulDivMod,
}

struct InfixOp<'a> {
    prec: Prec,
    op: &'a str,
    span: std::ops::Range<usize>,
}

impl<'a> InfixOp<'a> {
    fn apply(self, mut lhs: Box<Expr<'a>>, rhs: Box<Expr<'a>>) -> Box<Expr<'a>> {
        let span = Span::new(self.span);
        Box::new(match self.prec {
            // `a ~ b ~ c` is one `Concat`; a parenthesized one would be a `Group`.
            Prec::Concat => {
                if let Expr::Concat { exprs, .. } = &mut *lhs {
                    exprs.push(rhs);
                    return lhs;
                }
                Expr::Concat {
                    exprs: vec![lhs, rhs],
                    span,
                }
            }
            _ => Expr::BinOp {
                inner: BinOp {
                    op: self.op,
                    lhs,
                    rhs,
                },
                span,
            },
        })
    }
}

/// Parses a binary operator. The `bool` is `false` for a `~` without spaces around it; `operand`
/// is the input before the operand in front of it, because many operands swallow the space after
/// them.
fn infix_op<'a: 'l, 'l>(
    i: &mut InputStream<'a, 'l>,
    operand: &InputStream<'a, 'l>,
) -> ParseResult<'a, Option<(InfixOp<'a>, bool)>> {
    let before = *i;
    skip_ws0(i)?;
    let start = i.current_token_start();
    let op = match i.as_bytes() {
        [b'*' | b'/' | b'%', ..] => Some((Prec::MulDivMod, 1usize)),
        [b'~', ..] => Some((Prec::Concat, 1)),
        [b'+' | b'-', ..] => Some((Prec::AddSub, 1)),
        [b'>', b'>', ..] | [b'<', b'<', ..] => Some((Prec::Shift, 2)),
        [b'=' | b'!' | b'>' | b'<', b'=', ..] => Some((Prec::Compare, 2)),
        [b'>' | b'<', ..] => Some((Prec::Compare, 1)),
        [b'&', b'&', ..] => Some((Prec::And, 2)),
        [b'|', b'|', ..] => Some((Prec::Or, 2)),
        [b'&' | b'^' | b'b' | b'x', ..] => None,
        _ => {
            *i = before;
            return Ok(None);
        }
    };
    let op = match op {
        Some((prec, len)) => Some((prec, take(len).parse_next(i)?)),
        None => opt(alt((
            token_bitand.map(|op| (Prec::BitAnd, op)),
            token_xor.map(|op| (Prec::BitXor, op)),
            "bitor".value((Prec::BitOr, "|")),
        )))
        .parse_next(i)?,
    };
    let Some((prec, op)) = op else {
        *i = before;
        return Ok(None);
    };
    if prec != Prec::Concat {
        let span = start..i.current_token_start();
        skip_ws0(i)?;
        return Ok(Some((InfixOp { prec, op, span }, true)));
    }

    // `~` is also whitespace control, so an unspaced one is only an error before an operand.
    let ws_before = operand[..operand.len() - (i.len() + 1)].ends_with(char::is_whitespace);
    let spaced = opt(skip_ws1).parse_next(i)?.is_some() && ws_before;
    let span = before.current_token_start()..i.current_token_start();
    Ok(Some((InfixOp { prec, op, span }, spaced)))
}

fn token_xor<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a> {
    let good = keyword("xor").value(None);
    let bad = ('^', not('=')).span().map(Some);
    if let Some(span) = alt((good, bad)).parse_next(i)? {
        cut_error!("the binary XOR operator is called `xor` in askama", span)
    } else {
        Ok("^")
    }
}

fn token_bitand<'a: 'l, 'l>(i: &mut InputStream<'a, 'l>) -> ParseResult<'a> {
    let good = keyword("bitand").value(None);
    let bad = ('&', not(one_of(['&', '=']))).span().map(Some);
    if let Some(span) = alt((good, bad)).parse_next(i)? {
        cut_error!("the binary AND operator is called `bitand` in askama", span)
    } else {
        Ok("&")
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Filter<'a> {
    pub name: PathOrIdentifier<'a>,
    pub arguments: Vec<Box<Expr<'a>>>,
}

impl<'a: 'l, 'l> Filter<'a> {
    pub(crate) fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Self> {
        let mut p = (ws(path_or_identifier), opt(Expr::arguments));
        let (name, arguments) = p.parse_next(i)?;
        Ok(Self {
            name,
            arguments: arguments.map_or_else(Vec::new, |(arguments, _)| arguments),
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct AssociatedItem<'a> {
    pub name: WithSpan<&'a str>,
    pub generics: Option<TyGenericArgs<'a>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprStructField<'a> {
    pub name: WithSpan<&'a str>,
    pub value: Option<Box<Expr<'a>>>,
}

enum Suffix<'a> {
    AssociatedItem(AssociatedItem<'a>),
    Index(Box<Expr<'a>>),
    Call {
        generics: Option<TyGenericArgs<'a>>,
        args: Vec<Box<Expr<'a>>>,
    },
    Struct {
        fields: Vec<ExprStructField<'a>>,
        base: Option<Box<Expr<'a>>>,
    },
    // The value is the arguments of the macro call.
    MacroCall(&'a str),
    Try,
}

#[derive(Debug)]
enum Field<'a> {
    Base(Box<Expr<'a>>),
    Field(ExprStructField<'a>),
}

impl<'a: 'l, 'l> Suffix<'a> {
    fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Box<Expr<'a>>> {
        let mut level_guard = i.state.level.guard();
        let mut expr = Expr::single(i)?;
        let mut right = opt(alt((
            Self::associated_item,
            Self::index,
            Self::call,
            Self::r#try,
            Self::r#macro,
            Self::r#struct,
        )));

        let mut i_before = i.checkpoint();
        // Most operands have no suffix: don't let all six alternatives fail one after the other.
        while i
            .trim_ascii_start()
            .starts_with(['.', '[', '(', '?', '!', '{', ':'])
            && let Some(suffix) = right.parse_next(i)?
        {
            level_guard.nest(i)?;
            let (suffix, span) = suffix;
            expr = Box::new(match suffix {
                Self::AssociatedItem(associated_item) => Expr::AssociatedItem {
                    parent_item: expr,
                    associated_item,
                    span,
                },
                Self::Index(index) => Expr::Index {
                    parent_item: expr,
                    index,
                    span,
                },
                Self::Call { generics, args } => Expr::Call {
                    call: Call {
                        path: expr,
                        generics,
                        args,
                    },
                    span,
                },
                Self::Struct { fields, base } => Expr::Struct {
                    inner: ExprStruct {
                        path: expr,
                        fields,
                        base,
                    },
                    span,
                },
                Self::Try => Expr::Try { expr, span },
                Self::MacroCall(arguments) => {
                    let arguments = WithSpan::new(arguments, span);
                    match *expr {
                        Expr::Path { components, .. } => {
                            let last = components.last().unwrap();
                            ensure_macro_name(&last.name)?;

                            if let Some(r) = components.iter().find_map(|r| r.generics.as_ref()) {
                                return Err(ErrorContext::new(
                                    "macro paths cannot have generics",
                                    r.span,
                                )
                                .cut());
                            }

                            Expr::RustMacro {
                                path: components
                                    .into_iter()
                                    .map(|c: PathComponent<'_>| c.name)
                                    .collect(),
                                arguments,
                                span,
                            }
                        }
                        Expr::Var {
                            name,
                            span: name_span,
                        } => {
                            let name = WithSpan::new(name, name_span);
                            ensure_macro_name(&name)?;
                            Expr::RustMacro {
                                path: vec![name],
                                arguments,
                                span,
                            }
                        }
                        _ => {
                            i.reset(&i_before);
                            return fail(i);
                        }
                    }
                }
            });
            i_before = i.checkpoint();
        }
        Ok(expr)
    }

    fn r#macro(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, (Self, Span)> {
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
                        "a bare CR (Mac linebreak) is not allowed in string literals, \
                         use NL (Unix linebreak) or CRNL (Windows linebreak) instead, \
                         or type `\\r` explicitly",
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
        Ok((inner, span.into()))
    }

    fn associated_item(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, (Self, Span)> {
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
        Ok((
            Self::AssociatedItem(AssociatedItem { name, generics }),
            span.into(),
        ))
    }

    fn index(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, (Self, Span)> {
        let mut p = (
            ws('['.span()),
            cut_err((ws(move |i: &mut _| Expr::parse(i, true)), opt(']'))),
        );
        let (span, (expr, closed)) = p.parse_next(i)?;
        if closed.is_none() {
            return cut_error!("matching closing `]` is missing", span);
        }
        Ok((Self::Index(expr), span.into()))
    }

    fn call(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, (Self, Span)> {
        let mut p = (opt(call_generics), Expr::arguments);
        let (generics, (args, span)) = p.parse_next(i)?;
        Ok((Self::Call { generics, args }, span))
    }

    fn r#try(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, (Self, Span)> {
        let span = preceded(skip_ws0, '?'.span()).parse_next(i)?;
        Ok((Self::Try, span.into()))
    }

    fn r#struct(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, (Self, Span)> {
        let span = ws('{'.span()).parse_next(i)?;
        let _level_guard = i.state.level.nest(i)?;
        let mut p = (
            cut_err((separated(
                0..,
                alt((Self::struct_field, Self::struct_base)),
                ws(','),
            ),)),
            opt(ws(',')), // Trailing comma.
            opt(ws(winnow::token::any.with_span())),
        );
        let ((all_fields,), trailing_comma, closed): ((Vec<Field<'_>>,), Option<_>, Option<_>) =
            p.parse_next(i)?;
        if trailing_comma.is_some() && all_fields.is_empty() {
            return cut_error!("missing field before `,`", span);
        }
        let mut base: Option<Box<Expr<'a>>> = None;
        let mut fields = Vec::with_capacity(all_fields.len());
        for field in all_fields {
            match field {
                Field::Field(field) => {
                    if base.is_some() {
                        return cut_error!(
                            "expected end of struct expression after `..` was used",
                            field.name.span()
                        );
                    }
                    fields.push(field);
                }
                Field::Base(new_base) => {
                    if base.is_some() {
                        return cut_error!(
                            "expected end of struct expression after `..` was used",
                            new_base.span()
                        );
                    }
                    base = Some(new_base);
                }
            }
        }
        if closed.as_ref().is_none_or(|(c, _)| *c != '}') {
            let err_span = match closed {
                Some((_, span)) => span,
                _ => span,
            };
            if base.is_some() {
                return cut_error!(
                    "expected end of struct expression after `..` was used",
                    err_span
                );
            } else if !fields.is_empty() {
                return cut_error!("expected `,`, `..`, field name or `}`", err_span);
            } else {
                return cut_error!("expected field name, `..` or `}`", err_span);
            }
        }

        Ok((Self::Struct { fields, base }, span.into()))
    }

    fn struct_base(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Field<'a>> {
        let ((_, base_expr), span) = (ws(".."), opt(ws(move |i: &mut _| Expr::parse(i, true))))
            .with_span()
            .parse_next(i)?;
        match base_expr {
            Some(base_expr) => Ok(Field::Base(base_expr)),
            None => cut_error!("expected expression after `..`", span),
        }
    }

    fn struct_field(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Field<'a>> {
        let ((name, name_span), has_colon, value) = alt((
            (
                alt((identifier, digit1)).with_span(),
                ws(':'),
                opt(ws(|i: &mut _| Expr::parse(i, true))),
            )
                .map(|(name, _, expr)| (name, true, expr)),
            identifier.with_span().map(|name| (name, false, None)),
        ))
        .parse_next(i)?;
        if has_colon && value.is_none() {
            cut_error!("expected expression after `:`", *i)
        } else {
            Ok(Field::Field(ExprStructField {
                name: WithSpan::new(name, name_span),
                value,
            }))
        }
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
    pub kind: TyGenericsKind<'a>,
    pub span: Span,
}

/// Generic arguments like the `<u32, &str>` in `x::<u32, &str>()`.
#[derive(Clone, Debug, PartialEq)]
pub struct TyGenericArgs<'a> {
    pub args: Vec<TyGenerics<'a>>,
    /// The span of the `<`.
    pub span: Span,
}

impl<'a: 'l, 'l> TyGenerics<'a> {
    pub(crate) fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Self> {
        let p = ws((repeat(0.., ws('&')), TyGenericsKind::parse));
        let ((refs, kind), span) = p.with_span().parse_next(i)?;
        if refs > MAX_REFS {
            return cut_error!(format!("too many references (> {MAX_REFS})"), span);
        }
        Ok(TyGenerics {
            refs,
            kind,
            span: span.into(),
        })
    }

    fn args(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, TyGenericArgs<'a>> {
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
        Ok(TyGenericArgs {
            args: args.unwrap_or_default(),
            span: span.into(),
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TyGenericsKind<'a> {
    Path {
        path: Vec<WithSpan<&'a str>>,
        args: Option<TyGenericArgs<'a>>,
    },
    Tuple(Vec<TyGenerics<'a>>),
    Array {
        ty: Box<TyGenerics<'a>>,
        nb_elems: Option<&'a str>,
    },
}

impl<'a: 'l, 'l> TyGenericsKind<'a> {
    fn parse(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, Self> {
        let _level_guard = i.state.level.nest(i)?;
        alt((Self::tuple, Self::array, Self::ty_path)).parse_next(i)
    }

    fn ty_path(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, TyGenericsKind<'a>> {
        let path = separated(
            1..,
            ws(identifier
                .with_span()
                .map(|(name, span)| WithSpan::new(name, span))),
            "::",
        )
        .map(|v: Vec<_>| v);

        let (path, args) = (path, opt(TyGenerics::args)).parse_next(i)?;

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
        Ok(TyGenericsKind::Path { path, args })
    }

    fn tuple(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, TyGenericsKind<'a>> {
        let start = *i;
        // We ensure we're in the right function to get better errors later on.
        ws('(').parse_next(i)?;
        let Ok(tuple_elems) = separated(0.., TyGenerics::parse, ws(',')).parse_next(i) else {
            return cut_error!("expected a list of type separated by a comma", start);
        };
        if (opt(ws(',')), ws(')')).parse_next(i).is_err() {
            return cut_error!("expected a list of type separated by a comma", start);
        }
        Ok(TyGenericsKind::Tuple(tuple_elems))
    }

    fn array(i: &mut InputStream<'a, 'l>) -> ParseResult<'a, TyGenericsKind<'a>> {
        let start = *i;
        // We ensure we're in the right function to get better errors later on.
        ws('[').parse_next(i)?;

        let ty = match TyGenerics::parse.parse_next(i) {
            Ok(ty) => ty,
            Err(error @ ErrMode::Cut(_)) => return Err(error),
            Err(_) => return cut_error!("expected a type", *i),
        };
        let mut nb_elems = None;
        if let Ok((_, colon_span)) = ws(';').with_span().parse_next(i) {
            let Ok((parsed_nb, nb_span)) = num_lit.with_span().parse_next(i) else {
                return cut_error!("expected a number after `;`", colon_span);
            };
            match parsed_nb {
                Num::Int(nb, Some(crate::IntKind::Usize) | None) => nb_elems = Some(nb),
                Num::Int(_, Some(kind)) => {
                    return cut_error!(
                        format!("array size should be `usize`, found `{kind}`"),
                        nb_span,
                    );
                }
                Num::Float(nb, _) => {
                    return cut_error!(
                        format!("expected a number after `;`, found a float (`{nb}`)"),
                        nb_span,
                    );
                }
            }
        }
        if ws(']').parse_next(i).is_err() {
            return cut_error!("missing `]` to close the array", start);
        }
        Ok(TyGenericsKind::Array {
            ty: Box::new(ty),
            nb_elems,
        })
    }
}

pub(crate) fn call_generics<'a: 'l, 'l>(
    i: &mut InputStream<'a, 'l>,
) -> ParseResult<'a, TyGenericArgs<'a>> {
    preceded(ws("::"), cut_err(TyGenerics::args)).parse_next(i)
}

#[cold]
#[inline(never)]
fn try_assign_fallback_error<'a: 'l, 'l>(
    i: &mut InputStream<'a, 'l>,
    err: &mut ErrMode<ErrorContext>,
) {
    if let ErrMode::Backtrack(err_ctx) | ErrMode::Cut(err_ctx) = err
        && err_ctx.message.is_none()
    {
        let checkpoint = i.checkpoint();
        i.input.reset_to_start();
        // `span.start` is a byte offset, so seek with `next_slice()`: `take()` counts chars
        if i.is_char_boundary(err_ctx.span.start) {
            i.next_slice(err_ctx.span.start);
            if let Err(better_err) = opt(deny_any_rust_token).parse_next(i)
                && let ErrMode::Backtrack(better_ctx) | ErrMode::Cut(better_ctx) = better_err
                && better_ctx.message.is_some()
            {
                *err_ctx = better_ctx;
            }
        }
        i.reset(&checkpoint);
    }
}
