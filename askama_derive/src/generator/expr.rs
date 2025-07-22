use std::borrow::Cow;
use std::str::FromStr;

use parser::node::CondTest;
use parser::{
    AssociatedItem, CharLit, CharPrefix, Expr, PathComponent, Span, StrLit, Target, TyGenerics,
    WithSpan,
};
use proc_macro2::TokenStream;
use quote::quote;

use super::{
    DisplayWrap, FILTER_SOURCE, Generator, LocalMeta, Writable, compile_time_escape, is_copyable,
    normalize_identifier,
};
use crate::CompileError;
use crate::heritage::Context;
use crate::integration::Buffer;

impl<'a> Generator<'a, '_> {
    pub(crate) fn visit_expr_root(
        &mut self,
        ctx: &Context<'_>,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<TokenStream, CompileError> {
        let mut buf = Buffer::new();
        self.visit_expr(ctx, &mut buf, expr)?;
        Ok(buf.into_token_stream())
    }

    pub(super) fn visit_loop_iter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        iter: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        let expr_code = self.visit_expr_root(ctx, iter)?;
        match &***iter {
            Expr::Range(..) => buf.write(expr_code, ctx.span_for_node(iter.span())),
            Expr::Array(..) => buf.write(
                format_args!("{expr_code}.iter()"),
                ctx.span_for_node(iter.span()),
            ),
            // If `iter` is a call then we assume it's something that returns
            // an iterator. If not then the user can explicitly add the needed
            // call without issues.
            Expr::Call { .. } | Expr::Index(..) => {
                buf.write(
                    format_args!("({expr_code}).into_iter()"),
                    ctx.span_for_node(iter.span()),
                );
            }
            // If accessing `self` then it most likely needs to be
            // borrowed, to prevent an attempt of moving.
            // FIXME: Remove this `to_string()` call, it's terrible performance-wise.
            _ if expr_code.to_string().trim_start().starts_with("self.") => {
                buf.write(
                    format_args!("(&{expr_code}).into_iter()"),
                    ctx.span_for_node(iter.span()),
                );
            }
            // If accessing a field then it most likely needs to be
            // borrowed, to prevent an attempt of moving.
            Expr::AssociatedItem(..) => buf.write(
                format_args!("(&{expr_code}).into_iter()"),
                ctx.span_for_node(iter.span()),
            ),
            // Otherwise, we borrow `iter` assuming that it implements `IntoIterator`.
            _ => buf.write(
                format_args!("({expr_code}).into_iter()"),
                ctx.span_for_node(iter.span()),
            ),
        }
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_expr(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        Ok(match ***expr {
            Expr::BoolLit(s) => self.visit_bool_lit(ctx, buf, s, expr.span()),
            Expr::NumLit(s, _) => self.visit_num_lit(buf, s, ctx.span_for_node(expr.span())),
            Expr::StrLit(ref s) => self.visit_str_lit(buf, s, ctx.span_for_node(expr.span())),
            Expr::CharLit(ref s) => self.visit_char_lit(buf, s, ctx.span_for_node(expr.span())),
            Expr::Var(s) => self.visit_var(ctx, buf, s, expr.span()),
            Expr::Path(ref path) => self.visit_path(ctx, buf, path),
            Expr::Array(ref elements) => self.visit_array(ctx, buf, elements, expr.span())?,
            Expr::AssociatedItem(ref obj, ref associated_item) => {
                self.visit_associated_item(ctx, buf, obj, associated_item)?
            }
            Expr::Index(ref obj, ref key) => self.visit_index(ctx, buf, obj, key)?,
            Expr::Filter(ref v) => {
                self.visit_filter(ctx, buf, &v.name, &v.arguments, expr.span())?
            }
            Expr::Unary(op, ref inner) => self.visit_unary(ctx, buf, op, inner, expr.span())?,
            Expr::BinOp(ref v) => self.visit_binop(ctx, buf, v.op, &v.lhs, &v.rhs, expr.span())?,
            Expr::Range(ref v) => {
                self.visit_range(ctx, buf, v.op, v.lhs.as_ref(), v.rhs.as_ref(), expr.span())?
            }
            Expr::Group(ref inner) => self.visit_group(ctx, buf, inner, expr.span())?,
            Expr::Call(ref v) => self.visit_call(ctx, buf, &v.path, &v.args)?,
            Expr::RustMacro(ref path, args) => {
                self.visit_rust_macro(ctx, buf, path, args, expr.span())
            }
            Expr::Try(ref expr) => self.visit_try(ctx, buf, expr)?,
            Expr::Tuple(ref exprs) => self.visit_tuple(ctx, buf, exprs, expr.span())?,
            Expr::NamedArgument(_, ref expr) => self.visit_named_argument(ctx, buf, expr)?,
            Expr::FilterSource => self.visit_filter_source(ctx, buf, expr.span()),
            Expr::IsDefined(var_name) => {
                self.visit_is_defined(ctx, buf, true, var_name, expr.span())?
            }
            Expr::IsNotDefined(var_name) => {
                self.visit_is_defined(ctx, buf, false, var_name, expr.span())?
            }
            Expr::As(ref expr, target) => self.visit_as(ctx, buf, expr, target)?,
            Expr::Concat(ref exprs) => self.visit_concat(ctx, buf, exprs)?,
            Expr::LetCond(ref cond) => self.visit_let_cond(ctx, buf, cond)?,
            Expr::ArgumentPlaceholder => DisplayWrap::Unwrapped,
        })
    }

    /// This method and `visit_expr_not_first` are needed because in case we have
    /// `{% if let Some(x) = x && x == "a" %}`, if we first start to visit `Some(x)`, then we end
    /// up with `if let Some(x) = x && x == "a"`, however if we first visit the expr, we end up with
    /// `if let Some(x) = self.x && self.x == "a"`. It's all a big "variable declaration" mess.
    ///
    /// So instead, we first visit the expression, but only the first "level" to ensure we won't
    /// go after the `&&` and badly generate the rest of the expression.
    pub(super) fn visit_expr_first(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        match ***expr {
            Expr::BinOp(ref v) if matches!(v.op, "&&" | "||") => {
                let ret = self.visit_expr(ctx, buf, &v.lhs)?;
                buf.write(format_args!(" {} ", &v.op), ctx.span_for_node(expr.span()));
                return Ok(ret);
            }
            Expr::Unary(op, ref inner) => {
                buf.write(op, ctx.span_for_node(expr.span()));
                return self.visit_expr_first(ctx, buf, inner);
            }
            _ => {}
        }
        self.visit_expr(ctx, buf, expr)
    }

    pub(super) fn visit_expr_not_first(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
        prev_display_wrap: DisplayWrap,
    ) -> Result<DisplayWrap, CompileError> {
        match ***expr {
            Expr::BinOp(ref v) if matches!(v.op, "&&" | "||") => {
                self.visit_condition(ctx, buf, &v.rhs)?;
                Ok(DisplayWrap::Unwrapped)
            }
            Expr::Unary(_, ref inner) => {
                self.visit_expr_not_first(ctx, buf, inner, prev_display_wrap)
            }
            _ => Ok(prev_display_wrap),
        }
    }

    pub(super) fn visit_condition(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<(), CompileError> {
        match &***expr {
            Expr::BoolLit(_) | Expr::IsDefined(_) | Expr::IsNotDefined(_) => {
                self.visit_expr(ctx, buf, expr)?;
            }
            Expr::Unary("!", expr) => {
                buf.write('!', ctx.span_for_node(expr.span()));
                self.visit_condition(ctx, buf, expr)?;
            }
            Expr::BinOp(v) if matches!(v.op, "&&" | "||") => {
                self.visit_condition(ctx, buf, &v.lhs)?;
                buf.write(format_args!(" {} ", v.op), ctx.span_for_node(expr.span()));
                self.visit_condition(ctx, buf, &v.rhs)?;
            }
            Expr::Group(expr) => {
                let mut tmp = Buffer::new();

                self.visit_condition(ctx, &mut tmp, expr)?;
                let tmp = tmp.into_token_stream();
                let span = ctx.span_for_node(expr.span());
                buf.write_tokens(spanned!(span=> ( #tmp )));
            }
            Expr::LetCond(cond) => {
                self.visit_let_cond(ctx, buf, cond)?;
            }
            _ => {
                let mut tmp = Buffer::new();
                self.visit_expr(ctx, &mut tmp, expr)?;
                let tmp = tmp.into_token_stream();
                let span = ctx.span_for_node(expr.span());
                buf.write_tokens(spanned!(span=> askama::helpers::as_bool(&( #tmp ))));
            }
        }
        Ok(())
    }

    fn visit_is_defined(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        is_defined: bool,
        left: &str,
        span: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);
        match (is_defined, self.is_var_defined(left)) {
            (true, true) | (false, false) => buf.write_tokens(spanned!(span => true)),
            _ => buf.write_tokens(spanned!(span => false)),
        }
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_as(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
        target: &str,
    ) -> Result<DisplayWrap, CompileError> {
        let mut tmp = Buffer::new();
        self.visit_expr(ctx, &mut tmp, expr)?;
        let tmp = tmp.into_token_stream();
        let span = ctx.span_for_node(expr.span());
        let target = proc_macro2::Ident::new(target, span);
        buf.write_tokens(spanned!(
            span=> askama::helpers::get_primitive_value(&(#tmp)) as askama::helpers::core::primitive::#target
        ));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_concat(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        exprs: &[WithSpan<'a, Box<Expr<'a>>>],
    ) -> Result<DisplayWrap, CompileError> {
        match exprs {
            [] => unreachable!(),
            [expr] => self.visit_expr(ctx, buf, expr),
            exprs => {
                let (l, r) = exprs.split_at(exprs.len().div_ceil(2));
                // FIXME: Is this valid?
                let span = ctx.span_for_node(l[0].span());
                let mut buf_l = Buffer::new();
                let mut buf_r = Buffer::new();
                self.visit_concat(ctx, &mut buf_l, l)?;
                self.visit_concat(ctx, &mut buf_r, r)?;
                let buf_l = buf_l.into_token_stream();
                let buf_r = buf_r.into_token_stream();
                buf.write_tokens(spanned!(
                    span=> askama::helpers::Concat(&(#buf_l), &(#buf_r))
                ));
                Ok(DisplayWrap::Unwrapped)
            }
        }
    }

    fn visit_let_cond(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        cond: &WithSpan<'a, CondTest<'a>>,
    ) -> Result<DisplayWrap, CompileError> {
        let mut expr_buf = Buffer::new();
        let display_wrap = self.visit_expr_first(ctx, &mut expr_buf, &cond.expr)?;
        let expr_buf = expr_buf.into_token_stream();
        let span = ctx.span_for_node(cond.span());
        buf.write(" let ", span);
        if let Some(ref target) = cond.target {
            self.visit_target(ctx, buf, true, true, target);
        }
        buf.write_tokens(spanned!(span=> = &#expr_buf));
        self.visit_expr_not_first(ctx, buf, &cond.expr, display_wrap)
    }

    fn visit_try(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        let mut tmp = Buffer::new();
        let span = ctx.span_for_node(expr.span());
        self.visit_expr(ctx, &mut tmp, expr)?;
        let tmp = tmp.into_token_stream();

        buf.write_tokens(spanned!(span=> match (#tmp) {
            res => (&&askama::helpers::ErrorMarker::of(&res)).askama_conv_result(res)?
        }));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_rust_macro(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        path: &[&str],
        args: &str,
        node: Span<'_>,
    ) -> DisplayWrap {
        let [path @ .., name] = path else {
            unreachable!("path cannot be empty");
        };
        let name = match normalize_identifier(name) {
            "loop" => quote::format_ident!("r#loop"),
            name => quote::format_ident!("{}", name),
        };

        let span = ctx.span_for_node(node);
        if !path.is_empty() {
            self.visit_macro_path(buf, path, span);
            buf.write("::", span);
        }
        let args = TokenStream::from_str(args).unwrap();
        buf.write_tokens(spanned!(span=> #name !(#args)));

        DisplayWrap::Unwrapped
    }

    pub(super) fn visit_value(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        generics: &[WithSpan<'a, TyGenerics<'a>>],
        node: Span<'_>,
        kind: &str,
    ) -> Result<DisplayWrap, CompileError> {
        let [key] = args else {
            return Err(ctx.generate_error(
                format_args!("{kind} only takes one argument, found {}", args.len()),
                node,
            ));
        };
        let [r#gen] = generics else {
            return Err(ctx.generate_error(
                format_args!("{kind} expects one generic, found {}", generics.len()),
                node,
            ));
        };
        let mut ty_generics = Buffer::new();
        self.visit_ty_generic(
            ctx,
            &mut ty_generics,
            r#gen,
            ctx.span_for_node(r#gen.span()),
        );
        let span = ctx.span_for_node(node);
        let args = self.visit_arg(ctx, key, span)?;

        let ty_generics = ty_generics.into_token_stream();
        buf.write_tokens(spanned!(span=> askama::helpers::get_value::<#ty_generics>(
            &__askama_values, &(#args)
        )));
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_args(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
    ) -> Result<(), CompileError> {
        for (i, arg) in args.iter().enumerate() {
            let span = ctx.span_for_node(arg.span());
            if i > 0 {
                buf.write(',', span);
            }
            buf.write(self.visit_arg(ctx, arg, span)?, ctx.template_span);
        }
        Ok(())
    }

    pub(super) fn visit_arg(
        &mut self,
        ctx: &Context<'_>,
        arg: &WithSpan<'a, Box<Expr<'a>>>,
        span: proc_macro2::Span,
    ) -> Result<TokenStream, CompileError> {
        self.visit_arg_inner(ctx, arg, span, false)
    }

    fn visit_arg_inner(
        &mut self,
        ctx: &Context<'_>,
        arg: &WithSpan<'a, Box<Expr<'a>>>,
        span: proc_macro2::Span,
        // This parameter is needed because even though Expr::Unary is not copyable, we might still
        // be able to skip a few levels.
        need_borrow: bool,
    ) -> Result<TokenStream, CompileError> {
        if let Expr::Unary(expr @ ("*" | "&"), ref arg) = ***arg {
            let inner = self.visit_arg_inner(ctx, arg, ctx.span_for_node(arg.span()), true)?;
            let operator = TokenStream::from_str(expr).unwrap();
            return Ok(spanned!(span=> #operator #inner));
        }
        let borrow = need_borrow || !is_copyable(arg);
        let mut buf = Buffer::new();
        let stream = match ***arg {
            Expr::Call(ref v) if !matches!(**v.path, Expr::Path(_)) => {
                self.visit_expr(ctx, &mut buf, arg)?;
                let buf = buf.into_token_stream();
                spanned!(span=> {#buf})
            }
            _ => {
                self.visit_expr(ctx, &mut buf, arg)?;
                buf.into_token_stream()
            }
        };
        if borrow {
            Ok(spanned!(span=> &(#stream)))
        } else {
            Ok(stream)
        }
    }

    pub(super) fn visit_auto_escaped_arg(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        arg: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<(), CompileError> {
        let span = ctx.span_for_node(arg.span());
        if let Some(Writable::Lit(arg)) = compile_time_escape(arg, self.input.escaper) {
            if !arg.is_empty() {
                let mut tmp = Buffer::new();
                tmp.write_escaped_str(&arg, span);
                let tmp = tmp.into_token_stream();
                buf.write_tokens(spanned!(span=> askama::filters::Safe(#tmp)));
            } else {
                buf.write("askama::helpers::Empty", span);
            }
        } else {
            let arg = self.visit_arg(ctx, arg, span)?;
            let escaper = TokenStream::from_str(self.input.escaper).unwrap();
            buf.write_tokens(spanned!(span=> (
                    &&askama::filters::AutoEscaper::new(#arg, #escaper)
                ).askama_auto_escape()?
            ));
        }
        Ok(())
    }

    pub(crate) fn visit_associated_item(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        obj: &WithSpan<'a, Box<Expr<'a>>>,
        associated_item: &AssociatedItem<'a>,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(obj.span());
        if let Expr::Var("loop") = ***obj {
            buf.write(
                match associated_item.name {
                    "index0" => "__askama_item.index0",
                    "index" => "(__askama_item.index0 + 1)",
                    "first" => "(__askama_item.index0 == 0)",
                    "last" => "__askama_item.last",
                    name => {
                        return Err(ctx.generate_error(
                            format!("unknown loop variable `{}`", name.escape_debug()),
                            obj.span(),
                        ));
                    }
                },
                span,
            );
            return Ok(DisplayWrap::Unwrapped);
        }

        let mut expr = Buffer::new();
        self.visit_expr(ctx, &mut expr, obj)?;
        let expr = expr.into_token_stream();
        let identifier = TokenStream::from_str(normalize_identifier(associated_item.name)).unwrap();
        let mut call_generics = Buffer::new();
        self.visit_call_generics(ctx, &mut call_generics, &associated_item.generics);
        let call_generics = call_generics.into_token_stream();

        buf.write_tokens(spanned!(span=> #expr. #identifier #call_generics));
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_call_generics(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        generics: &[WithSpan<'a, TyGenerics<'a>>],
    ) {
        if let Some(first) = generics.first() {
            buf.write("::", ctx.span_for_node(first.span()));
            self.visit_ty_generics(ctx, buf, generics);
        }
    }

    fn visit_ty_generics(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        generics: &[WithSpan<'a, TyGenerics<'a>>],
    ) {
        if generics.is_empty() {
            return;
        }
        let mut tmp = Buffer::new();
        for generic in generics {
            let span = ctx.span_for_node(generic.span());
            self.visit_ty_generic(ctx, &mut tmp, generic, span);
            tmp.write(',', span);
        }
        let tmp = tmp.into_token_stream();
        // FIXME: use a better span
        buf.write(quote!(<#tmp>), ctx.template_span);
    }

    pub(super) fn visit_ty_generic(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        generic: &WithSpan<'a, TyGenerics<'a>>,
        span: proc_macro2::Span,
    ) {
        let TyGenerics { refs, path, args } = &**generic;
        let mut refs_s = String::new();
        for _ in 0..*refs {
            refs_s.push('&');
        }
        buf.write(refs_s, span);
        self.visit_macro_path(buf, path, span);
        self.visit_ty_generics(ctx, buf, args);
    }

    fn visit_index(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        obj: &WithSpan<'a, Box<Expr<'a>>>,
        key: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        buf.write('&', ctx.span_for_node(obj.span()));
        self.visit_expr(ctx, buf, obj)?;

        let key_span = ctx.span_for_node(key.span());
        let mut key_buf = Buffer::new();

        self.visit_expr(ctx, &mut key_buf, key)?;

        let key_buf = key_buf.into_token_stream();
        buf.write_tokens(spanned!(key_span=> [#key_buf]));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_call(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        left: &WithSpan<'a, Box<Expr<'a>>>,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
    ) -> Result<DisplayWrap, CompileError> {
        // ensure that no named args are used in normal rust call expressions
        if let Some(arg) = args
            .iter()
            .find(|&arg| matches!(***arg, Expr::NamedArgument(_, _)))
        {
            return Err(ctx.generate_error("Unsupported use of named arguments", arg.span()));
        }

        match &***left {
            Expr::AssociatedItem(sub_left, AssociatedItem { name, generics })
                if ***sub_left == Expr::Var("loop") =>
            {
                match *name {
                    "cycle" => {
                        if let [generic, ..] = generics.as_slice() {
                            return Err(ctx.generate_error(
                                "loop.cycle(…) doesn't use generics",
                                generic.span(),
                            ));
                        }
                        match args {
                            [arg] => {
                                if matches!(***arg, Expr::Array(ref arr) if arr.is_empty()) {
                                    return Err(ctx.generate_error(
                                        "loop.cycle(…) cannot use an empty array",
                                        arg.span(),
                                    ));
                                }
                                let mut expr_buf = Buffer::new();
                                self.visit_expr(ctx, &mut expr_buf, arg)?;
                                let expr_buf = expr_buf.into_token_stream();
                                let arg_span = ctx.span_for_node(arg.span());

                                buf.write_tokens(
                                    spanned!(arg_span=> ({
                                        let _cycle = &(#expr_buf);
                                        let __askama_len = _cycle.len();
                                        if __askama_len == 0 {
                                            return askama::helpers::core::result::Result::Err(askama::Error::Fmt);
                                        }
                                        _cycle[__askama_item.index0 % __askama_len]
                                    })),
                                );
                            }
                            _ => {
                                return Err(ctx.generate_error(
                                    "loop.cycle(…) cannot use an empty array",
                                    left.span(),
                                ));
                            }
                        }
                    }
                    s => {
                        return Err(ctx.generate_error(
                            format_args!("unknown loop method: {s:?}"),
                            left.span(),
                        ));
                    }
                }
            }
            // We special-case "askama::get_value".
            Expr::Path(path) if matches!(path.as_slice(), [part1, part2] if part1.generics.is_empty() && part1.name == "askama" && part2.name == "get_value") =>
            {
                self.visit_value(
                    ctx,
                    buf,
                    args,
                    // Generics of the `get_value` call.
                    &path[1].generics,
                    left.span(),
                    "`get_value` function",
                )?;
            }
            sub_left => {
                let span = ctx.span_for_node(left.span());
                match *sub_left {
                    Expr::Var(name) => match self.locals.resolve(name) {
                        Some(resolved) => buf.write(resolved, span),
                        None => {
                            buf.write(format_args!("self.{}", normalize_identifier(name)), span)
                        }
                    },
                    _ => {
                        self.visit_expr(ctx, buf, left)?;
                    }
                }
                let mut tmp = Buffer::new();
                self.visit_args(ctx, &mut tmp, args)?;
                let tmp = tmp.into_token_stream();
                buf.write_tokens(spanned!(span=> (#tmp)));
            }
        }
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_unary(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        op: &str,
        inner: &WithSpan<'a, Box<Expr<'a>>>,
        span: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        buf.write(op, ctx.span_for_node(span));
        self.visit_expr(ctx, buf, inner)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_range(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        op: &str,
        left: Option<&WithSpan<'a, Box<Expr<'a>>>>,
        right: Option<&WithSpan<'a, Box<Expr<'a>>>>,
        span: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        if let Some(left) = left {
            self.visit_expr(ctx, buf, left)?;
        }
        buf.write(op, ctx.span_for_node(span));
        if let Some(right) = right {
            self.visit_expr(ctx, buf, right)?;
        }
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_binop(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        op: &str,
        left: &WithSpan<'a, Box<Expr<'a>>>,
        right: &WithSpan<'a, Box<Expr<'a>>>,
        span: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_expr(ctx, buf, left)?;
        buf.write(format_args!(" {op} "), ctx.span_for_node(span));
        self.visit_expr(ctx, buf, right)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_group(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        inner: &WithSpan<'a, Box<Expr<'a>>>,
        span: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);
        let mut tmp = Buffer::new();
        self.visit_expr(ctx, &mut tmp, inner)?;

        let tmp = tmp.into_token_stream();
        buf.write_tokens(spanned!(span=> (#tmp)));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_tuple(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        exprs: &[WithSpan<'a, Box<Expr<'a>>>],
        span: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);

        let mut tmp = Buffer::new();
        for expr in exprs {
            self.visit_expr(ctx, &mut tmp, expr)?;
            tmp.write(',', span);
        }
        let tmp = tmp.into_token_stream();
        buf.write_tokens(spanned!(span=> (#tmp)));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_named_argument(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_expr(ctx, buf, expr)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_array(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        elements: &[WithSpan<'a, Box<Expr<'a>>>],
        span: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);

        let mut tmp = Buffer::new();
        for el in elements {
            self.visit_expr(ctx, &mut tmp, el)?;
            tmp.write(',', span);
        }
        let tmp = tmp.into_token_stream();
        buf.write_tokens(spanned!(span=> [#tmp]));
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_macro_path(
        &self,
        buf: &mut Buffer,
        path: &[&str],
        span: proc_macro2::Span,
    ) {
        for (i, part) in path.iter().copied().enumerate() {
            if i > 0 {
                buf.write("::", span);
            } else if let Some(enum_ast) = self.input.enum_ast
                && part == "Self"
            {
                let this = &enum_ast.ident;
                let (_, generics, _) = enum_ast.generics.split_for_impl();
                let generics = generics.as_turbofish();
                buf.write_tokens(spanned!(span=> #this #generics));
                continue;
            }
            buf.write(part, span);
        }
    }

    pub(super) fn visit_path(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        path: &[WithSpan<'a, PathComponent<'a>>],
    ) -> DisplayWrap {
        for (i, part) in path.iter().enumerate() {
            let span = ctx.span_for_node(part.span());
            if i > 0 {
                buf.write("::", span);
            } else if let Some(enum_ast) = self.input.enum_ast
                && part.name == "Self"
            {
                let this = &enum_ast.ident;
                let (_, generics, _) = enum_ast.generics.split_for_impl();
                let generics = generics.as_turbofish();
                buf.write_tokens(spanned!(span=> #this #generics));
                continue;
            }
            buf.write(part.name, span);
            if !part.generics.is_empty() {
                buf.write("::", span);
                self.visit_ty_generics(ctx, buf, &part.generics);
            }
        }
        DisplayWrap::Unwrapped
    }

    fn visit_var(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        s: &str,
        node: Span<'_>,
    ) -> DisplayWrap {
        let span = ctx.span_for_node(node);
        if s == "self" {
            buf.write(s, span);
            return DisplayWrap::Unwrapped;
        }

        buf.write(normalize_identifier(&self.locals.resolve_or_self(s)), span);
        DisplayWrap::Unwrapped
    }

    fn visit_filter_source(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        node: Span<'_>,
    ) -> DisplayWrap {
        // We can assume that the body of the `{% filter %}` was already escaped.
        // And if it's not, then this was done intentionally.
        buf.write(
            format_args!("askama::filters::Safe(&{FILTER_SOURCE})"),
            ctx.span_for_node(node),
        );
        DisplayWrap::Wrapped
    }

    fn visit_bool_lit(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        s: bool,
        node: Span<'_>,
    ) -> DisplayWrap {
        let span = ctx.span_for_node(node);
        if s {
            buf.write("true", span);
        } else {
            buf.write("false", span);
        }
        DisplayWrap::Unwrapped
    }

    pub(super) fn visit_str_lit(
        &mut self,
        buf: &mut Buffer,
        StrLit {
            content, prefix, ..
        }: &StrLit<'_>,
        span: proc_macro2::Span,
    ) -> DisplayWrap {
        if let Some(prefix) = prefix {
            buf.write(format!("{}\"{content}\"", prefix.to_char()), span);
        } else {
            buf.write(format!("\"{content}\""), span);
        }
        DisplayWrap::Unwrapped
    }

    fn visit_char_lit(
        &mut self,
        buf: &mut Buffer,
        c: &CharLit<'_>,
        span: proc_macro2::Span,
    ) -> DisplayWrap {
        if c.prefix == Some(CharPrefix::Binary) {
            buf.write(format_args!("b'{}'", c.content), span);
        } else {
            buf.write(format_args!("'{}'", c.content), span);
        }
        DisplayWrap::Unwrapped
    }

    fn visit_num_lit(&mut self, buf: &mut Buffer, s: &str, span: proc_macro2::Span) -> DisplayWrap {
        buf.write(s, span);
        DisplayWrap::Unwrapped
    }

    // FIXME: This function should have a `Span`, but `cond.target` isn't `WithSpan`.
    pub(super) fn visit_target(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        initialized: bool,
        first_level: bool,
        target: &Target<'a>,
    ) {
        match target {
            Target::Placeholder(_) => buf.write('_', ctx.template_span),
            Target::Rest(s) => {
                if let Some(var_name) = &**s {
                    self.locals
                        .insert(Cow::Borrowed(var_name), LocalMeta::var_def());
                    buf.write(*var_name, ctx.template_span);
                    buf.write(" @ ", ctx.template_span);
                }
                buf.write("..", ctx.template_span);
            }
            Target::Name(name) => {
                let name = normalize_identifier(name);
                match initialized {
                    true => self
                        .locals
                        .insert(Cow::Borrowed(name), LocalMeta::var_def()),
                    false => self.locals.insert_with_default(Cow::Borrowed(name)),
                }
                buf.write(name, ctx.template_span);
            }
            Target::OrChain(targets) => match targets.first() {
                None => buf.write('_', ctx.template_span),
                Some(first_target) => {
                    self.visit_target(ctx, buf, initialized, first_level, first_target);
                    for target in &targets[1..] {
                        buf.write('|', ctx.template_span);
                        self.visit_target(ctx, buf, initialized, first_level, target);
                    }
                }
            },
            Target::Tuple(path, targets) => {
                buf.write_separated_path(ctx, path);
                let mut targets_buf = Buffer::new();
                for target in targets {
                    self.visit_target(ctx, &mut targets_buf, initialized, false, target);
                    targets_buf.write(',', ctx.template_span);
                }
                let targets_buf = targets_buf.into_token_stream();
                buf.write(
                    quote!(
                        (#targets_buf)
                    ),
                    ctx.template_span,
                );
            }
            Target::Array(path, targets) => {
                buf.write_separated_path(ctx, path);
                let mut targets_buf = Buffer::new();
                for target in targets {
                    self.visit_target(ctx, &mut targets_buf, initialized, false, target);
                    targets_buf.write(',', ctx.template_span);
                }
                let targets_buf = targets_buf.into_token_stream();
                buf.write(
                    quote!(
                        [#targets_buf]
                    ),
                    ctx.template_span,
                );
            }
            Target::Struct(path, targets) => {
                buf.write_separated_path(ctx, path);
                let mut targets_buf = Buffer::new();
                for (name, target) in targets {
                    if let Target::Rest(_) = target {
                        targets_buf.write("..", ctx.template_span);
                        continue;
                    }

                    targets_buf.write(normalize_identifier(name), ctx.template_span);
                    targets_buf.write(": ", ctx.template_span);
                    self.visit_target(ctx, &mut targets_buf, initialized, false, target);
                    targets_buf.write(',', ctx.template_span);
                }
                let targets_buf = targets_buf.into_token_stream();
                buf.write(
                    quote!(
                        {
                            #targets_buf
                        }
                    ),
                    ctx.template_span,
                );
            }
            Target::Path(path) => {
                self.visit_path(ctx, buf, path);
                buf.write("{}", ctx.template_span);
            }
            Target::StrLit(s) => {
                if first_level {
                    buf.write('&', ctx.template_span);
                }
                // FIXME: `Span` should not be `ctx.template_span`.
                self.visit_str_lit(buf, s, ctx.template_span);
            }
            Target::NumLit(s, _) => {
                if first_level {
                    buf.write('&', ctx.template_span);
                }
                // FIXME: `Span` should not be `ctx.template_span`.
                self.visit_num_lit(buf, s, ctx.template_span);
            }
            Target::CharLit(s) => {
                if first_level {
                    buf.write('&', ctx.template_span);
                }
                // FIXME: `Span` should not be `ctx.template_span`.
                self.visit_char_lit(buf, s, ctx.template_span);
            }
            Target::BoolLit(s) => {
                if first_level {
                    buf.write('&', ctx.template_span);
                }
                buf.write(*s, ctx.template_span);
            }
        }
    }
}
