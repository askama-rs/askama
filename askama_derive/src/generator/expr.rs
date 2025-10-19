use std::borrow::Cow;
use std::str::FromStr;

use parser::node::CondTest;
use parser::{
    AssociatedItem, CharLit, CharPrefix, Expr, PathComponent, Span, StrLit, StrPrefix, Target,
    TyGenerics, WithSpan,
};
use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::quote_spanned;
use syn::Token;

use super::{
    DisplayWrap, Generator, LocalMeta, Writable, binary_op, compile_time_escape, is_copyable,
    logic_op, range_op, unary_op,
};
use crate::heritage::Context;
use crate::integration::Buffer;
use crate::{CompileError, field_new, quote_into};

impl<'a> Generator<'a, '_> {
    pub(crate) fn visit_expr_root(
        &mut self,
        ctx: &Context<'_>,
        expr: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<TokenStream, CompileError> {
        let mut buf = Buffer::new();
        self.visit_expr(ctx, &mut buf, expr)?;
        Ok(buf.into_token_stream())
    }

    pub(super) fn visit_loop_iter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        iter: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        let expr_code = self.visit_expr_root(ctx, iter)?;
        let span = ctx.span_for_node(iter.span());
        buf.write_tokens(match &***iter {
            Expr::Range(..) => expr_code,
            Expr::Array(..) => quote_spanned!(span => #expr_code.iter()),
            // If `iter` is a call then we assume it's something that returns
            // an iterator. If not then the user can explicitly add the needed
            // call without issues.
            Expr::Call { .. } | Expr::Index(..) => quote_spanned!(span => (#expr_code).into_iter()),
            // If accessing `self` then it most likely needs to be
            // borrowed, to prevent an attempt of moving.
            _ if starts_with_self_dot(&expr_code) => {
                quote_spanned!(span => (&#expr_code).into_iter())
            }
            // If accessing a field then it most likely needs to be
            // borrowed, to prevent an attempt of moving.
            Expr::AssociatedItem(..) => quote_spanned!(span => (&#expr_code).into_iter()),
            // Otherwise, we borrow `iter` assuming that it implements `IntoIterator`.
            _ => quote_spanned!(span => (#expr_code).into_iter()),
        });
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_expr(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<Box<Expr<'a>>>,
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
            Expr::Struct(ref s) => self.visit_struct(ctx, buf, s, expr.span())?,
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
        expr: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        match ***expr {
            Expr::BinOp(ref v) if matches!(v.op, "&&" | "||") => {
                let ret = self.visit_expr(ctx, buf, &v.lhs)?;
                buf.write_tokens(logic_op(v.op, ctx.span_for_node(expr.span())));
                return Ok(ret);
            }
            Expr::Unary(op, ref inner) => {
                buf.write_tokens(unary_op(op, ctx.span_for_node(expr.span())));
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
        expr: &WithSpan<Box<Expr<'a>>>,
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
        expr: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<(), CompileError> {
        match &***expr {
            Expr::BoolLit(_) | Expr::IsDefined(_) | Expr::IsNotDefined(_) => {
                self.visit_expr(ctx, buf, expr)?;
            }
            Expr::Unary("!", expr) => {
                buf.write_token(Token![!], ctx.span_for_node(expr.span()));
                self.visit_condition(ctx, buf, expr)?;
            }
            Expr::BinOp(v) if matches!(v.op, "&&" | "||") => {
                self.visit_condition(ctx, buf, &v.lhs)?;
                buf.write_tokens(logic_op(v.op, ctx.span_for_node(expr.span())));
                self.visit_condition(ctx, buf, &v.rhs)?;
            }
            Expr::Group(expr) => {
                let mut tmp = Buffer::new();

                self.visit_condition(ctx, &mut tmp, expr)?;
                let tmp = tmp.into_token_stream();
                let span = ctx.span_for_node(expr.span());
                quote_into!(buf, span, { (#tmp) });
            }
            Expr::LetCond(cond) => {
                self.visit_let_cond(ctx, buf, cond)?;
            }
            _ => {
                let mut tmp = Buffer::new();
                self.visit_expr(ctx, &mut tmp, expr)?;
                let tmp = tmp.into_token_stream();
                let span = ctx.span_for_node(expr.span());
                quote_into!(buf, span, { askama::helpers::as_bool(&( #tmp )) });
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
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        let result = is_defined == self.is_var_defined(left);
        quote_into!(buf, ctx.span_for_node(span), { #result });
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_as(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<Box<Expr<'a>>>,
        target: WithSpan<&str>,
    ) -> Result<DisplayWrap, CompileError> {
        let mut tmp = Buffer::new();
        self.visit_expr(ctx, &mut tmp, expr)?;
        let tmp = tmp.into_token_stream();
        let target = field_new(*target, ctx.span_for_node(target.span()));
        quote_into!( buf, ctx.span_for_node(expr.span()), {
            askama::helpers::get_primitive_value(&(#tmp)) as askama::helpers::core::primitive::#target
        });
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_concat(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        exprs: &[WithSpan<Box<Expr<'a>>>],
    ) -> Result<DisplayWrap, CompileError> {
        match exprs {
            [] => unreachable!(),
            [expr] => self.visit_expr(ctx, buf, expr),
            exprs => {
                let (l, r) = exprs.split_at(exprs.len().div_ceil(2));
                let span = ctx.span_for_node(l[0].span());
                let mut buf_l = Buffer::new();
                let mut buf_r = Buffer::new();
                self.visit_concat(ctx, &mut buf_l, l)?;
                self.visit_concat(ctx, &mut buf_r, r)?;
                let buf_l = buf_l.into_token_stream();
                let buf_r = buf_r.into_token_stream();
                quote_into!(buf, span, { askama::helpers::Concat(&(#buf_l), &(#buf_r)) });
                Ok(DisplayWrap::Unwrapped)
            }
        }
    }

    fn visit_let_cond(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        cond: &WithSpan<CondTest<'a>>,
    ) -> Result<DisplayWrap, CompileError> {
        let mut expr_buf = Buffer::new();
        let display_wrap = self.visit_expr_first(ctx, &mut expr_buf, &cond.expr)?;
        let expr_buf = expr_buf.into_token_stream();
        let span = ctx.span_for_node(cond.span());
        buf.write_token(Token![let], span);
        if let Some(ref target) = cond.target {
            self.visit_target(ctx, buf, true, true, target, span);
        }
        quote_into!(buf, span, { = &#expr_buf });
        self.visit_expr_not_first(ctx, buf, &cond.expr, display_wrap)
    }

    fn visit_try(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        let mut tmp = Buffer::new();
        let span = ctx.span_for_node(expr.span());
        self.visit_expr(ctx, &mut tmp, expr)?;
        let tmp = tmp.into_token_stream();

        quote_into!(buf, span, {
            match (#tmp) {
                res => (&&askama::helpers::ErrorMarker::of(&res)).askama_conv_result(res)?
            }
        });
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_rust_macro(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        path: &[WithSpan<&str>],
        args: WithSpan<&str>,
        node: Span,
    ) -> DisplayWrap {
        let [path @ .., name] = path else {
            unreachable!("path cannot be empty");
        };

        let span = ctx.span_for_node(node);
        let name = field_new(name, span);
        if !path.is_empty() {
            self.visit_macro_path(buf, path, span);
            buf.write_token(Token![::], span);
        }

        let args = set_span_recursively(
            TokenStream::from_str(*args).unwrap(),
            ctx.span_for_node(args.span()),
        );

        quote_into!(buf, span, { #name !(#args) });

        DisplayWrap::Unwrapped
    }

    pub(super) fn visit_value(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<Box<Expr<'a>>>],
        generics: Option<&WithSpan<Vec<WithSpan<TyGenerics<'a>>>>>,
        node: Span,
        kind: &str,
    ) -> Result<DisplayWrap, CompileError> {
        let [key] = args else {
            return Err(ctx.generate_error(
                format_args!("{kind} only takes one argument, found {}", args.len()),
                node,
            ));
        };

        let Some(generics) = generics else {
            return Err(
                ctx.generate_error(format_args!("{kind} expects one generic, found none"), node)
            );
        };
        let [r#gen] = generics.as_slice() else {
            return Err(ctx.generate_error(
                format_args!("{kind} expects one generic, found {}", generics.len()),
                generics.span(),
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
        let var_values = crate::var_values();
        quote_into!(buf, span, {
            askama::helpers::get_value::<#ty_generics>(&#var_values, &(#args))
        });
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_args(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<Box<Expr<'a>>>],
    ) -> Result<(), CompileError> {
        for (i, arg) in args.iter().enumerate() {
            let span = ctx.span_for_node(arg.span());
            if i > 0 {
                buf.write_token(Token![,], span);
            }
            buf.write_tokens(self.visit_arg(ctx, arg, span)?);
        }
        Ok(())
    }

    pub(super) fn visit_arg(
        &mut self,
        ctx: &Context<'_>,
        arg: &WithSpan<Box<Expr<'a>>>,
        span: proc_macro2::Span,
    ) -> Result<TokenStream, CompileError> {
        self.visit_arg_inner(ctx, arg, span, false)
    }

    fn visit_arg_inner(
        &mut self,
        ctx: &Context<'_>,
        arg: &WithSpan<Box<Expr<'a>>>,
        span: proc_macro2::Span,
        // This parameter is needed because even though Expr::Unary is not copyable, we might still
        // be able to skip a few levels.
        need_borrow: bool,
    ) -> Result<TokenStream, CompileError> {
        if let Expr::Unary(expr @ ("*" | "&"), ref arg) = ***arg {
            let inner = self.visit_arg_inner(ctx, arg, ctx.span_for_node(arg.span()), true)?;
            let operator = TokenStream::from_str(expr).unwrap();
            return Ok(quote_spanned!(span=> #operator #inner));
        }
        let borrow = need_borrow || !is_copyable(arg);
        let mut buf = Buffer::new();
        let stream = match ***arg {
            Expr::Call(ref v) if !matches!(**v.path, Expr::Path(_)) => {
                self.visit_expr(ctx, &mut buf, arg)?;
                let buf = buf.into_token_stream();
                quote_spanned!(span=> { #buf })
            }
            _ => {
                self.visit_expr(ctx, &mut buf, arg)?;
                buf.into_token_stream()
            }
        };
        if borrow {
            Ok(quote_spanned!(span=> &(#stream)))
        } else {
            Ok(stream)
        }
    }

    pub(super) fn visit_auto_escaped_arg(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        arg: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<(), CompileError> {
        let span = ctx.span_for_node(arg.span());
        if let Some(Writable::Lit(arg)) = compile_time_escape(arg, self.input.escaper) {
            if !arg.is_empty() {
                let mut tmp = Buffer::new();
                tmp.write_escaped_str(&arg, span);
                let tmp = tmp.into_token_stream();
                quote_into!(buf, span, { askama::filters::Safe(#tmp) });
            } else {
                quote_into!(buf, span, { askama::helpers::Empty });
            }
        } else {
            let arg = self.visit_arg(ctx, arg, span)?;
            let escaper = TokenStream::from_str(self.input.escaper).unwrap();
            quote_into!(
                buf,
                span,
                { (&&askama::filters::AutoEscaper::new(#arg, #escaper)).askama_auto_escape()? }
            );
        }
        Ok(())
    }

    pub(crate) fn visit_associated_item(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        obj: &WithSpan<Box<Expr<'a>>>,
        associated_item: &AssociatedItem<'a>,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(obj.span());
        if let Expr::Var("loop") = ***obj {
            let var_item = crate::var_item();
            buf.write_tokens(match *associated_item.name {
                "index0" => quote_spanned!(span => #var_item.index0),
                "index" => quote_spanned!(span => (#var_item.index0 + 1)),
                "first" => quote_spanned!(span => (#var_item.index0 == 0)),
                "last" => quote_spanned!(span => #var_item.last),
                name => {
                    return Err(ctx.generate_error(
                        format!("unknown loop variable `{}`", name.escape_debug()),
                        associated_item.name.span(),
                    ));
                }
            });
            return Ok(DisplayWrap::Unwrapped);
        }

        let mut expr = Buffer::new();
        self.visit_expr(ctx, &mut expr, obj)?;
        let expr = expr.into_token_stream();
        let identifier = field_new(
            *associated_item.name,
            ctx.span_for_node(associated_item.name.span()),
        );
        let mut call_generics = Buffer::new();
        if let Some(generics) = associated_item.generics.as_ref() {
            self.visit_call_generics(ctx, &mut call_generics, generics);
        }
        let call_generics = call_generics.into_token_stream();

        quote_into!(buf, span, { #expr. #identifier #call_generics });
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_call_generics(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        generics: &WithSpan<Vec<WithSpan<TyGenerics<'a>>>>,
    ) {
        buf.write_token(Token![::], ctx.span_for_node(generics.span()));
        self.visit_ty_generics(ctx, buf, generics);
    }

    pub(super) fn visit_ty_generics(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        generics: &WithSpan<Vec<WithSpan<TyGenerics<'a>>>>,
    ) {
        let mut tmp = Buffer::new();
        for generic in &**generics {
            let span = ctx.span_for_node(generic.span());
            self.visit_ty_generic(ctx, &mut tmp, generic, span);
            tmp.write_token(Token![,], span);
        }
        let tmp = tmp.into_token_stream();
        quote_into!(buf, ctx.span_for_node(generics.span()), { <#tmp> });
    }

    pub(super) fn visit_ty_generic(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        generic: &WithSpan<TyGenerics<'a>>,
        span: proc_macro2::Span,
    ) {
        let TyGenerics {
            refs,
            ref path,
            ref args,
        } = **generic;
        for _ in 0..refs {
            buf.write_token(Token![&], span);
        }
        self.visit_macro_path(buf, path, span);
        if let Some(generics) = args.as_ref() {
            self.visit_ty_generics(ctx, buf, generics);
        }
    }

    fn visit_index(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        obj: &WithSpan<Box<Expr<'a>>>,
        key: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        buf.write_token(Token![&], ctx.span_for_node(obj.span()));
        self.visit_expr(ctx, buf, obj)?;

        let mut key_buf = Buffer::new();
        self.visit_expr(ctx, &mut key_buf, key)?;
        let key_buf = key_buf.into_token_stream();

        quote_into!(buf, ctx.span_for_node(key.span()), { [#key_buf] });
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_call(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        left: &WithSpan<Box<Expr<'a>>>,
        args: &[WithSpan<Box<Expr<'a>>>],
    ) -> Result<DisplayWrap, CompileError> {
        // ensure that no named args are used in normal rust call expressions
        if let Some(arg) = args
            .iter()
            .find(|&arg| matches!(***arg, Expr::NamedArgument(_, _)))
        {
            return Err(ctx.generate_error("unsupported use of named arguments", arg.span()));
        }

        match &***left {
            Expr::AssociatedItem(sub_left, AssociatedItem { name, generics })
                if ***sub_left == Expr::Var("loop") =>
            {
                match **name {
                    "cycle" => {
                        if generics.is_some() {
                            return Err(ctx.generate_error(
                                "loop.cycle(…) doesn't use generics",
                                name.span(),
                            ));
                        }
                        match args {
                            [arg] => {
                                if matches!(***arg, Expr::Array(ref arr) if arr.is_empty()) {
                                    return Err(ctx.generate_error(
                                        "loop.cycle(…) cannot use an empty array",
                                        name.span(),
                                    ));
                                }
                                let mut expr_buf = Buffer::new();
                                self.visit_expr(ctx, &mut expr_buf, arg)?;
                                let expr_buf = expr_buf.into_token_stream();
                                let arg_span = ctx.span_for_node(arg.span());

                                let var_cycle = crate::var_cycle();
                                let var_item = crate::var_item();
                                let var_len = crate::var_len();
                                quote_into!(buf, arg_span, {
                                    ({
                                        let #var_cycle = &(#expr_buf);
                                        let #var_len = #var_cycle.len();
                                        if #var_len == 0 {
                                            return askama::helpers::core::result::Result::Err(askama::Error::Fmt);
                                        }
                                        #var_cycle[#var_item.index0 % #var_len]
                                    })
                                });
                            }
                            _ => {
                                return Err(ctx.generate_error(
                                    "loop.cycle(…) cannot use an empty array",
                                    name.span(),
                                ));
                            }
                        }
                    }
                    s => {
                        return Err(ctx.generate_error(
                            format_args!("unknown loop method: `{}`", s.escape_debug()),
                            name.span(),
                        ));
                    }
                }
            }
            sub_left => {
                // We special-case "askama::get_value".
                if let Expr::Path(path) = sub_left
                    && let [part1, part2] = path.as_slice()
                    && part1.generics.is_none()
                    && *part1.name == "askama"
                    && *part2.name == "get_value"
                {
                    return self.visit_value(
                        ctx,
                        buf,
                        args,
                        part2.generics.as_ref(),
                        left.span(),
                        "`get_value` function",
                    );
                }

                let span = ctx.span_for_node(left.span());
                match *sub_left {
                    Expr::Var(name) => match self.locals.resolve(name) {
                        Some(resolved) => write_resolved(buf, &resolved, span),
                        None => {
                            let id = field_new(name, span);
                            quote_into!(buf, span, { self.#id });
                        }
                    },
                    _ => {
                        self.visit_expr(ctx, buf, left)?;
                    }
                }
                let mut tmp = Buffer::new();
                self.visit_args(ctx, &mut tmp, args)?;
                let tmp = tmp.into_token_stream();
                quote_into!(buf, span, { (#tmp) });
            }
        }
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_struct(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        struct_: &parser::expr::ExprStruct<'a>,
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);
        let path_span = ctx.span_for_node(struct_.path.span());
        match &**struct_.path {
            Expr::Var(name) => match self.locals.resolve(name) {
                Some(resolved) => write_resolved(buf, &resolved, path_span),
                None => {
                    let id = field_new(name, path_span);
                    quote_into!(buf, path_span, { self.#id });
                }
            },
            _ => {
                self.visit_expr(ctx, buf, &struct_.path)?;
            }
        }
        let mut tmp = Buffer::new();
        for (i, field) in struct_.fields.iter().enumerate() {
            let span = ctx.span_for_node(field.name.span());
            if i > 0 {
                tmp.write_token(Token![,], span);
            }
            tmp.write_field(&field.name, span);
            if let Some(ref value) = field.value {
                tmp.write_token(Token![:], span);
                tmp.write_tokens(self.visit_arg(ctx, value, span)?);
            }
        }
        if let Some(ref base) = struct_.base {
            let span = ctx.span_for_node(base.span());
            if !struct_.fields.is_empty() {
                tmp.write_token(Token![,], span);
            }
            tmp.write_token(Token![..], span);
            self.visit_expr(ctx, &mut tmp, base)?;
        }
        let tmp = tmp.into_token_stream();
        quote_into!(buf, span, { {#tmp} });
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_unary(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        op: &str,
        inner: &WithSpan<Box<Expr<'a>>>,
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        buf.write_tokens(unary_op(op, ctx.span_for_node(span)));
        self.visit_expr(ctx, buf, inner)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_range(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        op: &str,
        left: Option<&WithSpan<Box<Expr<'a>>>>,
        right: Option<&WithSpan<Box<Expr<'a>>>>,
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        if let Some(left) = left {
            self.visit_expr(ctx, buf, left)?;
        }
        buf.write_tokens(range_op(op, ctx.span_for_node(span)));
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
        left: &WithSpan<Box<Expr<'a>>>,
        right: &WithSpan<Box<Expr<'a>>>,
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_expr(ctx, buf, left)?;
        buf.write_tokens(binary_op(op, ctx.span_for_node(span)));
        self.visit_expr(ctx, buf, right)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_group(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        inner: &WithSpan<Box<Expr<'a>>>,
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);
        let mut tmp = Buffer::new();
        self.visit_expr(ctx, &mut tmp, inner)?;

        let tmp = tmp.into_token_stream();
        quote_into!(buf, span, { (#tmp) });
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_tuple(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        exprs: &[WithSpan<Box<Expr<'a>>>],
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);

        let mut tmp = Buffer::new();
        for expr in exprs {
            self.visit_expr(ctx, &mut tmp, expr)?;
            tmp.write_token(Token![,], span);
        }
        let tmp = tmp.into_token_stream();
        quote_into!(buf, span, { (#tmp) });
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_named_argument(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        expr: &WithSpan<Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_expr(ctx, buf, expr)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_array(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        elements: &[WithSpan<Box<Expr<'a>>>],
        span: Span,
    ) -> Result<DisplayWrap, CompileError> {
        let span = ctx.span_for_node(span);

        let mut tmp = Buffer::new();
        for el in elements {
            self.visit_expr(ctx, &mut tmp, el)?;
            tmp.write_token(Token![,], span);
        }
        let tmp = tmp.into_token_stream();
        quote_into!(buf, span, { [#tmp] });
        Ok(DisplayWrap::Unwrapped)
    }

    pub(super) fn visit_macro_path(
        &self,
        buf: &mut Buffer,
        path: &[WithSpan<&str>],
        span: proc_macro2::Span,
    ) {
        for (i, part) in path.iter().enumerate() {
            if i > 0 {
                buf.write_token(Token![::], span);
            } else if let Some(enum_ast) = self.input.enum_ast
                && **part == "Self"
            {
                let this = &enum_ast.ident;
                let (_, generics, _) = enum_ast.generics.split_for_impl();
                let generics = generics.as_turbofish();
                quote_into!(buf, span, { #this #generics });
                continue;
            }
            if i != 0 || !part.is_empty() {
                // Paths can start with `::`, meaning we can have an empty identifier first.
                buf.write_field(part, span);
            }
        }
    }

    pub(super) fn visit_path(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        path: &[PathComponent<'a>],
    ) -> DisplayWrap {
        for (i, part) in path.iter().enumerate() {
            let span = ctx.span_for_node(part.name.span());
            if i > 0 {
                buf.write_token(Token![::], span);
            } else if let Some(enum_ast) = self.input.enum_ast
                && *part.name == "Self"
            {
                let this = &enum_ast.ident;
                let (_, generics, _) = enum_ast.generics.split_for_impl();
                let generics = generics.as_turbofish();
                quote_into!(buf, span, { #this #generics });
                continue;
            }

            if !part.name.is_empty() {
                buf.write_field(*part.name, span);
            }
            if let Some(generics) = &part.generics {
                buf.write_token(Token![::], span);
                self.visit_ty_generics(ctx, buf, generics);
            }
        }
        DisplayWrap::Unwrapped
    }

    fn visit_var(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        s: &str,
        node: Span,
    ) -> DisplayWrap {
        let span = ctx.span_for_node(node);
        if s == "self" {
            quote_into!(buf, span, { self });
        } else {
            write_resolved(buf, &self.locals.resolve_or_self(s), span);
        }
        DisplayWrap::Unwrapped
    }

    fn visit_filter_source(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        node: Span,
    ) -> DisplayWrap {
        // We can assume that the body of the `{% filter %}` was already escaped.
        // And if it's not, then this was done intentionally.
        let span = ctx.span_for_node(node);
        let id = crate::var_filter_source();
        quote_into!(buf, span, { askama::filters::Safe(&#id) });
        DisplayWrap::Wrapped
    }

    fn visit_bool_lit(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        s: bool,
        node: Span,
    ) -> DisplayWrap {
        let span = ctx.span_for_node(node);
        if s {
            quote_into!(buf, span, { true });
        } else {
            quote_into!(buf, span, { false });
        }
        DisplayWrap::Unwrapped
    }

    pub(super) fn visit_str_lit(
        &mut self,
        buf: &mut Buffer,
        &StrLit {
            content, prefix, ..
        }: &StrLit<'_>,
        span: proc_macro2::Span,
    ) -> DisplayWrap {
        let repr = match prefix {
            Some(StrPrefix::Binary) => format!(r#"b"{content}""#),
            Some(StrPrefix::CLike) => format!(r#"c"{content}""#),
            None => format!(r#""{content}""#),
        };
        buf.write_literal(&repr, span);
        DisplayWrap::Unwrapped
    }

    fn visit_char_lit(
        &mut self,
        buf: &mut Buffer,
        &CharLit { prefix, content }: &CharLit<'_>,
        span: proc_macro2::Span,
    ) -> DisplayWrap {
        let repr = match prefix {
            Some(CharPrefix::Binary) => format!(r#"b'{content}'"#),
            None => format!(r#"'{content}'"#),
        };
        buf.write_literal(&repr, span);
        DisplayWrap::Unwrapped
    }

    fn visit_num_lit(&mut self, buf: &mut Buffer, s: &str, span: proc_macro2::Span) -> DisplayWrap {
        buf.write_literal(s, span);
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
        span: proc_macro2::Span,
    ) {
        match target {
            Target::Placeholder(s) => quote_into!(buf, ctx.span_for_node(s.span()), { _ }),
            Target::Rest(s) => {
                let span = ctx.span_for_node(s.span());
                if let Some(var_name) = &**s {
                    let id = field_new(var_name, span);
                    self.locals
                        .insert(Cow::Borrowed(var_name), LocalMeta::var_def());
                    quote_into!(buf, span, { #id @ });
                }
                buf.write_token(Token![..], span);
            }
            Target::Name(name) => {
                match initialized {
                    true => self
                        .locals
                        .insert(Cow::Borrowed(name), LocalMeta::var_def()),
                    false => self.locals.insert_with_default(Cow::Borrowed(name)),
                }
                buf.write_field(name, ctx.span_for_node(name.span()));
            }
            Target::OrChain(targets) => match targets.as_slice() {
                [] => quote_into!(buf, ctx.span_for_node(targets.span()), { _ }),
                [first_target, targets @ ..] => {
                    self.visit_target(ctx, buf, initialized, first_level, first_target, span);
                    for target in targets {
                        buf.write_token(Token![|], ctx.span_for_node(target.span()));
                        self.visit_target(ctx, buf, initialized, first_level, target, span);
                    }
                }
            },
            Target::Tuple(v) => {
                let (path, targets) = &**v;
                buf.write_separated_path(ctx, path);
                let mut targets_buf = Buffer::new();
                for target in targets {
                    self.visit_target(ctx, &mut targets_buf, initialized, false, target, span);
                    targets_buf.write_token(Token![,], ctx.span_for_node(target.span()));
                }
                let targets_buf = targets_buf.into_token_stream();
                quote_into!(buf, span, { (#targets_buf) });
            }
            Target::Array(targets) => {
                let mut targets_buf = Buffer::new();
                for target in &**targets {
                    self.visit_target(ctx, &mut targets_buf, initialized, false, target, span);
                    targets_buf.write_token(Token![,], ctx.span_for_node(target.span()));
                }
                let targets_buf = targets_buf.into_token_stream();
                quote_into!(buf, span, { [#targets_buf] });
            }
            Target::Struct(v) => {
                let (path, targets) = &**v;
                buf.write_separated_path(ctx, path);
                let mut targets_buf = Buffer::new();
                for named_target in targets {
                    if let Target::Rest(rest) = named_target.dest {
                        targets_buf.write_token(Token![..], ctx.span_for_node(rest.span()));
                        continue;
                    }

                    let span = ctx.span_for_node(named_target.src.span());
                    targets_buf.write_field(&named_target.src, span);
                    targets_buf.write_token(Token![:], ctx.span_for_node(named_target.src.span()));
                    self.visit_target(
                        ctx,
                        &mut targets_buf,
                        initialized,
                        false,
                        &named_target.dest,
                        span,
                    );
                    targets_buf.write_token(Token![,], ctx.span_for_node(named_target.src.span()));
                }
                let targets_buf = targets_buf.into_token_stream();
                quote_into!(buf, span, { { #targets_buf } });
            }
            Target::Path(path) => {
                self.visit_path(ctx, buf, path);
                quote_into!(buf, ctx.span_for_node(path.span()), { {} });
            }
            Target::StrLit(s) => {
                let span = ctx.span_for_node(s.span());
                if first_level {
                    buf.write_token(Token![&], span);
                }
                self.visit_str_lit(buf, s, span);
            }
            &Target::NumLit(repr, _) => {
                let span = ctx.span_for_node(repr.span());
                if first_level {
                    buf.write_token(Token![&], span);
                }
                self.visit_num_lit(buf, *repr, span);
            }
            Target::CharLit(s) => {
                let span = ctx.span_for_node(s.span());
                if first_level {
                    buf.write_token(Token![&], span);
                }
                self.visit_char_lit(buf, s, span);
            }
            &Target::BoolLit(s) => {
                let span = ctx.span_for_node(s.span());
                if first_level {
                    buf.write_token(Token![&], span);
                }
                match *s {
                    "true" => quote_into!(buf, span, { true }),
                    "false" => quote_into!(buf, span, { false }),
                    _ => unreachable!(),
                }
            }
        }
    }
}

fn set_span_recursively(input: TokenStream, span: proc_macro2::Span) -> TokenStream {
    input
        .into_iter()
        .map(move |mut tt| {
            tt.set_span(span);
            if let TokenTree::Group(group) = tt {
                TokenTree::Group(proc_macro2::Group::new(
                    group.delimiter(),
                    set_span_recursively(group.stream(), span),
                ))
            } else {
                tt
            }
        })
        .collect()
}

fn starts_with_self_dot(expr_code: &TokenStream) -> bool {
    let mut stream = expr_code.clone().into_iter().peekable();
    while let Some(TokenTree::Group(group)) = stream.peek()
        && group.delimiter() == Delimiter::None
    {
        stream = group.stream().into_iter().peekable();
    }

    if let Some(TokenTree::Ident(id)) = stream.next()
        && id == "self"
        && let Some(TokenTree::Punct(punct)) = stream.next()
        && punct.spacing() == Spacing::Alone
        && punct.as_char() == '.'
    {
        true
    } else {
        false
    }
}

fn write_resolved(buf: &mut Buffer, resolved: &str, span: proc_macro2::Span) {
    for (idx, name) in resolved.split('.').enumerate() {
        if idx > 0 {
            buf.write_token(Token![.], span);
        }
        buf.write_field(name, span);
    }
}
