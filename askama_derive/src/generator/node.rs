use std::borrow::Cow;
use std::collections::hash_map::{Entry, HashMap};
use std::fmt::Debug;
use std::mem;
use std::ops::ControlFlow;
use std::str::FromStr;

use parser::expr::BinOp;
use parser::node::{
    Call, Comment, Cond, CondTest, FilterBlock, If, Include, Let, Lit, Loop, Match, Whitespace, Ws,
};
use parser::{Expr, Node, Span, Target, WithSpan};
use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::Token;

use super::{DisplayWrap, Generator, LocalMeta, MapChain, compile_time_escape, is_copyable};
use crate::generator::{LocalCallerMeta, Writable, helpers, logic_op};
use crate::heritage::{Context, Heritage};
use crate::integration::{Buffer, string_escape};
use crate::{CompileError, FileInfo, field_new, fmt_left, fmt_right, quote_into};

impl<'a> Generator<'a, '_> {
    pub(super) fn impl_template_inner(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
    ) -> Result<usize, CompileError> {
        buf.set_discard(self.buf_writable.discard);
        let size_hint = if let Some(heritage) = self.heritage {
            self.handle(heritage.root, heritage.root.nodes, buf, AstLevel::Top)
        } else {
            self.handle(ctx, ctx.nodes, buf, AstLevel::Top)
        }?;
        self.flush_ws(Ws(None, None));
        buf.set_discard(false);
        Ok(size_hint)
    }

    pub(crate) fn push_locals<T, F>(&mut self, callback: F) -> Result<T, CompileError>
    where
        F: FnOnce(&mut Self) -> Result<T, CompileError>,
    {
        self.locals.stack_push();
        let res = callback(self);
        self.locals.stack_pop();
        res
    }

    fn with_child<'b, T, F>(
        &mut self,
        heritage: Option<&'b Heritage<'a, 'b>>,
        callback: F,
    ) -> Result<T, CompileError>
    where
        F: FnOnce(&mut Generator<'a, 'b>) -> Result<T, CompileError>,
    {
        self.locals.stack_push();

        let buf_writable = mem::take(&mut self.buf_writable);
        let locals = mem::replace(&mut self.locals, MapChain::new_empty());

        let mut child = Generator::new(
            self.input,
            self.contexts,
            heritage,
            locals,
            self.buf_writable.discard,
            self.is_in_filter_block,
        );
        child.buf_writable = buf_writable;
        let res = callback(&mut child);
        Generator {
            locals: self.locals,
            buf_writable: self.buf_writable,
            ..
        } = child;

        self.locals.stack_pop();
        res
    }

    pub(crate) fn handle(
        &mut self,
        ctx: &Context<'a>,
        nodes: &'a [Box<Node<'_>>],
        buf: &mut Buffer,
        level: AstLevel,
    ) -> Result<usize, CompileError> {
        let mut size_hint = 0;
        for n in nodes {
            match **n {
                Node::Lit(ref lit) => {
                    self.write_lit(lit);
                }
                Node::Comment(ref comment) => {
                    self.write_comment(comment);
                }
                Node::Expr(ws, ref val) => {
                    size_hint += self.write_expr(ctx, buf, ws, val)?;
                }
                Node::Let(ref l) => {
                    self.write_let(ctx, buf, l)?;
                }
                Node::If(ref i) => {
                    size_hint += self.write_if(ctx, buf, i)?;
                }
                Node::Match(ref m) => {
                    size_hint += self.write_match(ctx, buf, m)?;
                }
                Node::Loop(ref loop_block) => {
                    size_hint += self.write_loop(ctx, buf, loop_block)?;
                }
                Node::BlockDef(ref b) => {
                    size_hint +=
                        self.write_block(ctx, buf, Some(b.name), Ws(b.ws1.0, b.ws2.1), b.span())?;
                }
                Node::Include(ref i) => {
                    size_hint += self.handle_include(ctx, buf, i)?;
                }
                Node::Call(ref call) => {
                    size_hint += self.write_call(ctx, buf, call)?;
                }
                Node::FilterBlock(ref filter) => {
                    size_hint += self.write_filter_block(ctx, buf, filter)?;
                }
                Node::Macro(ref m) => {
                    if level != AstLevel::Top {
                        return Err(ctx.generate_error(
                            "macro blocks only allowed at the top level",
                            m.span(),
                        ));
                    }
                    self.flush_ws(m.ws1);
                    self.prepare_ws(m.ws2);
                }
                Node::Raw(ref raw) => {
                    self.handle_ws(raw.ws1);
                    self.write_lit(&raw.lit);
                    self.handle_ws(raw.ws2);
                }
                Node::Import(ref i) => {
                    if level != AstLevel::Top {
                        return Err(ctx.generate_error(
                            "import blocks only allowed at the top level",
                            i.span(),
                        ));
                    }
                    self.handle_ws(i.ws);
                }
                Node::Extends(ref e) => {
                    if level != AstLevel::Top {
                        return Err(ctx.generate_error(
                            "extend blocks only allowed at the top level",
                            e.span(),
                        ));
                    }
                    // No whitespace handling: child template top-level is not used,
                    // except for the blocks defined in it.
                }
                Node::Break(ref ws) => {
                    self.handle_ws(**ws);
                    self.write_buf_writable(ctx, buf)?;
                    quote_into!(buf, ctx.template_span, {
                        break;
                    });
                }
                Node::Continue(ref ws) => {
                    self.handle_ws(**ws);
                    self.write_buf_writable(ctx, buf)?;
                    quote_into!(buf, ctx.template_span, {
                        continue;
                    });
                }
            }
        }

        if AstLevel::Top == level {
            // Handle any pending whitespace.
            if self.next_ws.is_some() {
                self.flush_ws(Ws(Some(self.skip_ws), None));
            }

            size_hint += self.write_buf_writable(ctx, buf)?;
        }
        Ok(size_hint)
    }

    fn evaluate_condition(
        &self,
        expr: WithSpan<'a, Box<Expr<'a>>>,
        only_contains_is_defined: &mut bool,
    ) -> EvaluatedResult<'a> {
        let (expr, span) = expr.deconstruct();

        match *expr {
            Expr::NumLit(_, _)
            | Expr::StrLit(_)
            | Expr::CharLit(_)
            | Expr::Var(_)
            | Expr::Path(_)
            | Expr::Array(_)
            | Expr::AssociatedItem(_, _)
            | Expr::Index(_, _)
            | Expr::Filter(_)
            | Expr::Range(_)
            | Expr::Call { .. }
            | Expr::RustMacro(_, _)
            | Expr::Try(_)
            | Expr::Tuple(_)
            | Expr::NamedArgument(_, _)
            | Expr::FilterSource
            | Expr::As(_, _)
            | Expr::Concat(_)
            | Expr::LetCond(_)
            | Expr::ArgumentPlaceholder => {
                *only_contains_is_defined = false;
                EvaluatedResult::Unknown(WithSpan::new_with_full(expr, span))
            }
            Expr::BoolLit(true) => EvaluatedResult::AlwaysTrue,
            Expr::BoolLit(false) => EvaluatedResult::AlwaysFalse,
            Expr::Unary("!", inner) => {
                match self.evaluate_condition(inner, only_contains_is_defined) {
                    EvaluatedResult::AlwaysTrue => EvaluatedResult::AlwaysFalse,
                    EvaluatedResult::AlwaysFalse => EvaluatedResult::AlwaysTrue,
                    EvaluatedResult::Unknown(expr) => EvaluatedResult::Unknown(
                        WithSpan::new_with_full(Box::new(Expr::Unary("!", expr)), span),
                    ),
                }
            }
            Expr::Unary(_, _) => EvaluatedResult::Unknown(WithSpan::new_with_full(expr, span)),
            Expr::BinOp(v) if v.op == "&&" => {
                let lhs = match self.evaluate_condition(v.lhs, only_contains_is_defined) {
                    EvaluatedResult::AlwaysTrue => {
                        // The left side of the `&&` can be omitted.
                        return self.evaluate_condition(v.rhs, only_contains_is_defined);
                    }
                    EvaluatedResult::AlwaysFalse => {
                        // The right side of the `&&` won't be evaluated, no need to go any further.
                        return EvaluatedResult::AlwaysFalse;
                    }
                    EvaluatedResult::Unknown(lhs) => lhs,
                };
                match self.evaluate_condition(v.rhs, only_contains_is_defined) {
                    EvaluatedResult::AlwaysTrue => {
                        // The right side of the `&&` can be omitted.
                        EvaluatedResult::Unknown(lhs)
                    }
                    EvaluatedResult::AlwaysFalse => {
                        // Keep the side effect.
                        let rhs = WithSpan::new_without_span(Box::new(Expr::BoolLit(false)));
                        EvaluatedResult::Unknown(bin_op(span, v.op, lhs, rhs))
                    }
                    EvaluatedResult::Unknown(rhs) => {
                        EvaluatedResult::Unknown(bin_op(span, v.op, lhs, rhs))
                    }
                }
            }
            Expr::BinOp(v) if v.op == "||" => {
                let lhs = match self.evaluate_condition(v.lhs, only_contains_is_defined) {
                    EvaluatedResult::AlwaysTrue => {
                        // The right side of the `||` won't be evaluated, no need to go any further.
                        return EvaluatedResult::AlwaysTrue;
                    }
                    EvaluatedResult::AlwaysFalse => {
                        // The left side of the `||` can be omitted.
                        return self.evaluate_condition(v.rhs, only_contains_is_defined);
                    }
                    EvaluatedResult::Unknown(lhs) => lhs,
                };
                match self.evaluate_condition(v.rhs, only_contains_is_defined) {
                    EvaluatedResult::AlwaysTrue => {
                        // Keep the side effect.
                        let rhs = WithSpan::new_without_span(Box::new(Expr::BoolLit(true)));
                        EvaluatedResult::Unknown(bin_op(span, v.op, lhs, rhs))
                    }
                    EvaluatedResult::AlwaysFalse => {
                        // The right side of the `||` can be omitted.
                        EvaluatedResult::Unknown(lhs)
                    }
                    EvaluatedResult::Unknown(rhs) => {
                        EvaluatedResult::Unknown(bin_op(span, v.op, lhs, rhs))
                    }
                }
            }
            Expr::BinOp(_) => {
                *only_contains_is_defined = false;
                EvaluatedResult::Unknown(WithSpan::new_with_full(expr, span))
            }
            Expr::Group(inner) => match self.evaluate_condition(inner, only_contains_is_defined) {
                EvaluatedResult::Unknown(expr) => EvaluatedResult::Unknown(
                    WithSpan::new_with_full(Box::new(Expr::Group(expr)), span),
                ),
                known => known,
            },
            Expr::IsDefined(left) => {
                // Variable is defined so we want to keep the condition.
                if self.is_var_defined(left) {
                    EvaluatedResult::AlwaysTrue
                } else {
                    EvaluatedResult::AlwaysFalse
                }
            }
            Expr::IsNotDefined(left) => {
                // Variable is defined so we don't want to keep the condition.
                if self.is_var_defined(left) {
                    EvaluatedResult::AlwaysFalse
                } else {
                    EvaluatedResult::AlwaysTrue
                }
            }
        }
    }

    fn write_if(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        if_: &'a If<'_>,
    ) -> Result<usize, CompileError> {
        let mut flushed = 0;
        let mut arm_sizes = Vec::new();
        let mut has_else = false;

        let conds = Conds::compute_branches(self, if_);

        if let Some(ws_before) = conds.ws_before {
            self.handle_ws(ws_before);
        }

        let mut iter = conds.conds.iter().enumerate().peekable();
        while let Some((pos, cond_info)) = iter.next() {
            let cond = cond_info.cond;

            if pos == 0 {
                self.handle_ws(cond.ws);
                flushed += self.write_buf_writable(ctx, buf)?;
            }

            self.push_locals(|this| {
                let mut has_cond = true;

                if let Some(CondTest { target, expr, .. }) = &cond.cond {
                    let expr = cond_info.cond_expr.as_ref().unwrap_or(expr);
                    let span = ctx.span_for_node(expr.span());

                    if pos == 0 {
                        if cond_info.generate_condition {
                            buf.write_token(Token![if], ctx.template_span);
                        } else {
                            has_cond = false;
                        }
                        // Otherwise it means it will be the only condition generated,
                        // so nothing to be added here.
                    } else if cond_info.generate_condition {
                        quote_into!(buf, ctx.template_span, { else if });
                    } else {
                        buf.write_token(Token![else], ctx.template_span);
                        has_else = true;
                    }

                    if let Some(target) = target {
                        let mut expr_buf = Buffer::new();
                        buf.write_token(Token![let], ctx.template_span);
                        // If this is a chain condition, then we need to declare the variable after the
                        // left expression has been handled but before the right expression is handled
                        // but this one should have access to the let-bound variable.
                        match &***expr {
                            Expr::BinOp(v) if matches!(v.op, "||" | "&&") => {
                                let display_wrap =
                                    this.visit_expr_first(ctx, &mut expr_buf, &v.lhs)?;
                                this.visit_target(ctx, buf, true, true, target, span);
                                this.visit_expr_not_first(
                                    ctx,
                                    &mut expr_buf,
                                    &v.lhs,
                                    display_wrap,
                                )?;
                                let op = logic_op(v.op, span);
                                quote_into!(buf, span, { = &#expr_buf #op });
                                this.visit_condition(ctx, buf, &v.rhs)?;
                            }
                            _ => {
                                let display_wrap =
                                    this.visit_expr_first(ctx, &mut expr_buf, expr)?;
                                this.visit_target(ctx, buf, true, true, target, span);
                                this.visit_expr_not_first(ctx, &mut expr_buf, expr, display_wrap)?;
                                quote_into!(buf, ctx.template_span, { = &#expr_buf });
                            }
                        }
                    } else if cond_info.generate_condition {
                        this.visit_condition(ctx, buf, expr)?;
                    }
                } else if pos != 0 {
                    // FIXME: Should have a span.
                    buf.write_token(Token![else], ctx.template_span);
                    has_else = true;
                } else {
                    has_cond = false;
                }

                let mut block_buf = Buffer::new();
                if cond_info.generate_content {
                    arm_sizes.push(this.handle(
                        ctx,
                        &cond.nodes,
                        &mut block_buf,
                        AstLevel::Nested,
                    )?);
                }

                if let Some((_, cond_info)) = iter.peek() {
                    let cond = cond_info.cond;

                    this.handle_ws(cond.ws);
                    flushed += this.write_buf_writable(ctx, &mut block_buf)?;
                } else {
                    if let Some(ws_after) = conds.ws_after {
                        this.handle_ws(ws_after);
                    }
                    this.handle_ws(if_.ws);
                    flushed += this.write_buf_writable(ctx, &mut block_buf)?;
                }
                if has_cond {
                    let block_buf = block_buf.into_token_stream();
                    // FIXME Should have a span.
                    quote_into!(buf, ctx.template_span, { { #block_buf } });
                } else {
                    buf.write_buf(block_buf);
                }
                Ok(0)
            })?;
        }

        if !has_else && !conds.conds.is_empty() {
            arm_sizes.push(0);
        }
        Ok(flushed + median(&mut arm_sizes))
    }

    #[allow(clippy::too_many_arguments)]
    fn write_match(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        m: &'a Match<'a>,
    ) -> Result<usize, CompileError> {
        let Match {
            ws1,
            ref expr,
            ref arms,
            ws2,
        } = *m;

        self.flush_ws(ws1);
        let flushed = self.write_buf_writable(ctx, buf)?;
        let mut arm_sizes = Vec::new();

        let expr_code = self.visit_expr_root(ctx, expr)?;
        let span = ctx.span_for_node(expr.span());

        let mut arm_size = 0;
        let mut iter = arms.iter().enumerate().peekable();
        let mut arms = Buffer::new();
        while let Some((i, arm)) = iter.next() {
            if i == 0 {
                self.handle_ws(arm.ws);
            }

            // FIXME: When `Target` is wrapped in `WithSpan`, update the spans.
            self.push_locals(|this| {
                let mut targets_buf = Buffer::new();
                for (index, target) in arm.target.iter().enumerate() {
                    if index != 0 {
                        targets_buf.write_token(Token![|], span);
                    }
                    this.visit_target(ctx, &mut targets_buf, true, true, target, span);
                }

                let mut arm_buf = Buffer::new();
                arm_size = this.handle(ctx, &arm.nodes, &mut arm_buf, AstLevel::Nested)?;

                if let Some((_, arm)) = iter.peek() {
                    this.handle_ws(arm.ws);
                    arm_sizes.push(arm_size + this.write_buf_writable(ctx, &mut arm_buf)?);
                } else {
                    this.handle_ws(ws2);
                    arm_sizes.push(arm_size + this.write_buf_writable(ctx, &mut arm_buf)?);
                }
                let targets_buf = targets_buf.into_token_stream();
                let arm_buf = arm_buf.into_token_stream();
                quote_into!(&mut arms, span, { #targets_buf => { #arm_buf } });
                Ok(0)
            })?;
        }

        let arms = arms.into_token_stream();
        quote_into!(buf, span, { match &#expr_code { #arms } });

        Ok(flushed + median(&mut arm_sizes))
    }

    fn write_loop(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        loop_block: &'a WithSpan<'a, Loop<'_>>,
    ) -> Result<usize, CompileError> {
        self.handle_ws(loop_block.ws1);
        let span = ctx.span_for_node(loop_block.span());
        self.push_locals(|this| {
            let has_else_nodes = !loop_block.else_nodes.is_empty();

            let var_did_loop = crate::var_did_loop();
            let var_item = crate::var_item();
            let var_iter = crate::var_iter();

            let flushed = this.write_buf_writable(ctx, buf)?;
            let mut loop_buf = Buffer::new();
            if has_else_nodes {
                quote_into!(&mut loop_buf, span, { let mut #var_did_loop = false; });
            }

            quote_into!(&mut loop_buf, span, { let #var_iter = });
            this.visit_loop_iter(ctx, &mut loop_buf, &loop_block.iter)?;
            loop_buf.write_token(Token![;], span);
            if let Some(cond) = &loop_block.cond {
                this.push_locals(|this| {
                    let mut target_buf = Buffer::new();
                    this.visit_target(ctx, &mut target_buf, true, true, &loop_block.var, span);
                    let target_buf = target_buf.into_token_stream();
                    let mut expr_buf = Buffer::new();
                    this.visit_expr(ctx, &mut expr_buf, cond)?;
                    let expr_buf = expr_buf.into_token_stream();
                    quote_into!(
                        &mut loop_buf,
                        span,
                        {
                            let #var_iter = #var_iter.filter(
                                |#target_buf| -> askama::helpers::core::primitive::bool {
                                    #expr_buf
                                }
                            );
                        }
                    );
                    Ok(0)
                })?;
            }

            let size_hint1 = this.push_locals(|this| {
                let mut target_buf = Buffer::new();
                this.visit_target(ctx, &mut target_buf, true, true, &loop_block.var, span);
                let target_buf = target_buf.into_token_stream();

                let mut loop_body_buf = Buffer::new();
                if has_else_nodes {
                    quote_into!(&mut loop_body_buf, span, { #var_did_loop = true; });
                }
                let mut size_hint1 =
                    this.handle(ctx, &loop_block.body, &mut loop_body_buf, AstLevel::Nested)?;
                this.handle_ws(loop_block.ws2);
                size_hint1 += this.write_buf_writable(ctx, &mut loop_body_buf)?;
                let loop_body_buf = loop_body_buf.into_token_stream();
                quote_into!(&mut loop_buf, span, {
                    for (#target_buf, #var_item) in askama::helpers::TemplateLoop::new(#var_iter) {
                        #loop_body_buf
                    }
                });
                Ok(size_hint1)
            })?;

            let size_hint2;
            if has_else_nodes {
                let mut cond_buf = Buffer::new();
                size_hint2 = this.push_locals(|this| {
                    let mut size_hint =
                        this.handle(ctx, &loop_block.else_nodes, &mut cond_buf, AstLevel::Nested)?;
                    this.handle_ws(loop_block.ws3);
                    size_hint += this.write_buf_writable(ctx, &mut cond_buf)?;
                    Ok(size_hint)
                })?;
                let cond_buf = cond_buf.into_token_stream();
                loop_buf.write_tokens(quote_spanned!(span=> if !#var_did_loop {
                    #cond_buf
                }));
            } else {
                this.handle_ws(loop_block.ws3);
                size_hint2 = this.write_buf_writable(ctx, &mut loop_buf)?;
            }

            buf.write_tokens(loop_buf.into_token_stream());

            Ok(flushed + ((size_hint1 * 3) + size_hint2) / 2)
        })
    }

    fn write_call(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        call: &'a WithSpan<'a, Call<'_>>,
    ) -> Result<usize, CompileError> {
        let Call {
            ws1,
            scope,
            name,
            ref args,
            ws2,
            ..
        } = **call;

        let (def, own_ctx) = if let Some(s) = scope {
            let path = ctx.imports.get(s).ok_or_else(|| {
                ctx.generate_error(format_args!("no import found for scope {s:?}"), call.span())
            })?;
            let mctx = self.contexts.get(path).ok_or_else(|| {
                ctx.generate_error(format_args!("context for {path:?} not found"), call.span())
            })?;
            let def = mctx.macros.get(name).ok_or_else(|| {
                ctx.generate_error(
                    format_args!("macro {name:?} not found in scope {s:?}"),
                    call.span(),
                )
            })?;
            (*def, mctx)
        } else {
            let def = ctx.macros.get(name).ok_or_else(|| {
                ctx.generate_error(format_args!("macro {name:?} not found"), call.span())
            })?;
            (*def, ctx)
        };

        // whitespaces for the invocation is constructed from
        // - call-block's outer (start)
        // - endcall-block's outer (end)
        helpers::MacroInvocation {
            callsite_ctx: ctx,
            callsite_span: call.span(),
            call: Some(call),
            callsite_ws: Ws(ws1.0, ws2.1),
            call_args: args,
            macro_def: def,
            macro_ctx: own_ctx,
        }
        .write(buf, self)
    }

    fn write_filter_block(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        filter: &'a WithSpan<'a, FilterBlock<'_>>,
    ) -> Result<usize, CompileError> {
        let var_filter_source = crate::var_filter_source();

        self.write_buf_writable(ctx, buf)?;
        self.flush_ws(filter.ws1);
        self.is_in_filter_block += 1;
        self.write_buf_writable(ctx, buf)?;
        let span = ctx.span_for_node(filter.span());

        // build `FmtCell` that contains the inner block
        let mut filter_def_buf = Buffer::new();
        let size_hint = self.push_locals(|this| {
            this.prepare_ws(filter.ws1);
            let size_hint =
                this.handle(ctx, &filter.nodes, &mut filter_def_buf, AstLevel::Nested)?;
            this.flush_ws(filter.ws2);
            this.write_buf_writable(ctx, &mut filter_def_buf)?;
            Ok(size_hint)
        })?;
        let filter_def_buf = filter_def_buf.into_token_stream();
        let var_writer = crate::var_writer();
        let filter_def_buf = quote_spanned!(span=>
            let #var_filter_source = askama::helpers::FmtCell::new(
                |#var_writer: &mut askama::helpers::core::fmt::Formatter<'_>| -> askama::Result<()> {
                    #filter_def_buf
                    askama::Result::Ok(())
                }
            );
        );

        // display the `FmtCell`
        let mut filter_buf = Buffer::new();
        let display_wrap = self.visit_filter(
            ctx,
            &mut filter_buf,
            &filter.filters.name,
            &filter.filters.arguments,
            filter.span(),
        )?;
        let filter_buf = filter_buf.into_token_stream();
        let filter_buf = match display_wrap {
            DisplayWrap::Wrapped => filter_buf,
            DisplayWrap::Unwrapped => {
                let escaper = TokenStream::from_str(self.input.escaper).unwrap();
                quote_spanned!(span=>
                    (&&askama::filters::AutoEscaper::new(
                        &(#filter_buf), #escaper
                    )).askama_auto_escape()?
                )
            }
        };
        quote_into!(buf, span, { {
            #filter_def_buf
            if askama::helpers::core::write!(#var_writer, "{}", #filter_buf).is_err() {
                return #var_filter_source.take_err();
            }
        } });

        self.is_in_filter_block -= 1;
        self.prepare_ws(filter.ws2);
        Ok(size_hint)
    }

    fn handle_include(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        i: &'a WithSpan<'a, Include<'_>>,
    ) -> Result<usize, CompileError> {
        self.flush_ws(i.ws);
        self.write_buf_writable(ctx, buf)?;
        let file_info = ctx
            .path
            .map(|path| FileInfo::of(i.span(), path, ctx.parsed));
        let path = self.input.config.find_template(
            i.path,
            Some(&self.input.path),
            file_info,
            Some(ctx.span_for_node(i.span())),
        )?;

        // We clone the context of the child in order to preserve their macros and imports.
        // But also add all the imports and macros from this template that don't override the
        // child's ones to preserve this template's context.
        let child_ctx = &mut self.contexts[&path].clone();
        for (name, mac) in &ctx.macros {
            child_ctx.macros.entry(name).or_insert(mac);
        }
        for (name, import) in &ctx.imports {
            child_ctx
                .imports
                .entry(name)
                .or_insert_with(|| import.clone());
        }

        // Create a new generator for the child, and call it like in `impl_template` as if it were
        // a full template, while preserving the context.
        let heritage = if !child_ctx.blocks.is_empty() || child_ctx.extends.is_some() {
            Some(Heritage::new(child_ctx, self.contexts))
        } else {
            None
        };

        let handle_ctx = match &heritage {
            Some(heritage) => heritage.root,
            None => child_ctx,
        };

        let size_hint = self.with_child(heritage.as_ref(), |child| {
            let mut size_hint = 0;
            size_hint += child.handle(handle_ctx, handle_ctx.nodes, buf, AstLevel::Top)?;
            size_hint += child.write_buf_writable(handle_ctx, buf)?;
            Ok(size_hint)
        })?;

        self.prepare_ws(i.ws);

        Ok(size_hint)
    }

    fn is_shadowing_variable(
        &self,
        ctx: &Context<'_>,
        var: &Target<'a>,
        l: Span<'_>,
    ) -> Result<bool, CompileError> {
        match var {
            Target::Name(name) => {
                match self.locals.get(name) {
                    // declares a new variable
                    None => Ok(false),
                    // an initialized variable gets shadowed
                    Some(meta) if meta.initialized => Ok(true),
                    // initializes a variable that was introduced in a LetDecl before
                    _ => Ok(false),
                }
            }
            Target::Placeholder(_) => Ok(false),
            Target::Rest(var_name) => {
                if let Some(var_name) = **var_name {
                    match self.is_shadowing_variable(ctx, &Target::Name(var_name), l) {
                        Ok(false) => {}
                        outcome => return outcome,
                    }
                }
                Ok(false)
            }
            Target::Tuple(_, targets) => {
                for target in targets {
                    match self.is_shadowing_variable(ctx, target, l) {
                        Ok(false) => continue,
                        outcome => return outcome,
                    }
                }
                Ok(false)
            }
            Target::Struct(_, named_targets) => {
                for (_, target) in named_targets {
                    match self.is_shadowing_variable(ctx, target, l) {
                        Ok(false) => continue,
                        outcome => return outcome,
                    }
                }
                Ok(false)
            }
            _ => Err(ctx.generate_error(
                "literals are not allowed on the left-hand side of an assignment",
                l,
            )),
        }
    }

    fn write_let(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        l: &'a WithSpan<'a, Let<'_>>,
    ) -> Result<(), CompileError> {
        self.handle_ws(l.ws);
        let span = ctx.span_for_node(l.span());

        let Some(val) = &l.val else {
            self.write_buf_writable(ctx, buf)?;
            buf.write_token(Token![let], span);
            if l.is_mutable {
                buf.write_token(Token![mut], span);
            }
            self.visit_target(ctx, buf, false, true, &l.var, span);
            buf.write_token(Token![;], span);
            return Ok(());
        };

        // Handle when this statement creates a new alias of a caller variable (or of another alias),
        if let Target::Name(dstvar) = l.var
            && let Expr::Var(srcvar) = ***val
            && let Some(caller_alias) = self.locals.get_caller(srcvar)
        {
            self.locals
                .insert(dstvar.into(), LocalMeta::CallerAlias(caller_alias.clone()));
            return Ok(());
        }

        let mut expr_buf = Buffer::new();
        self.visit_expr(ctx, &mut expr_buf, val)?;

        let shadowed = self.is_shadowing_variable(ctx, &l.var, l.span())?;
        if shadowed {
            // Need to flush the buffer if the variable is being shadowed,
            // to ensure the old variable is used.
            self.write_buf_writable(ctx, buf)?;
        }
        if shadowed
            || !matches!(l.var, Target::Name(_))
            || matches!(&l.var, Target::Name(name) if self.locals.get(name).is_none())
        {
            buf.write_token(Token![let], span);
            if l.is_mutable {
                buf.write_token(Token![mut], span);
            }
        }

        self.visit_target(ctx, buf, true, true, &l.var, span);
        // If it's not taking the ownership of a local variable or copyable, then we need to add
        // a reference.
        let borrow = !matches!(***val, Expr::Try(..))
            && !matches!(***val, Expr::Var(name) if self.locals.get(name).is_some())
            && !is_copyable(val);
        buf.write_tokens(if borrow {
            quote_spanned! { span => = &(#expr_buf); }
        } else {
            quote_spanned! { span => = #expr_buf; }
        });
        Ok(())
    }

    // If `name` is `Some`, this is a call to a block definition, and we have to find
    // the first block for that name from the ancestry chain. If name is `None`, this
    // is from a `super()` call, and we can get the name from `self.super_block`.
    fn write_block(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        name: Option<&'a str>,
        outer: Ws,
        node: Span<'_>,
    ) -> Result<usize, CompileError> {
        if self.is_in_filter_block > 0 {
            return Err(ctx.generate_error("cannot have a block inside a filter block", node));
        }
        // Flush preceding whitespace according to the outer WS spec
        self.flush_ws(outer);

        let cur = match (name, self.super_block) {
            // The top-level context contains a block definition
            (Some(cur_name), None) => (cur_name, 0),
            // A block definition contains a block definition of the same name
            (Some(cur_name), Some((prev_name, _))) if cur_name == prev_name => {
                return Err(ctx.generate_error(
                    format_args!("cannot define recursive blocks ({cur_name})"),
                    node,
                ));
            }
            // A block definition contains a definition of another block
            (Some(cur_name), Some((_, _))) => (cur_name, 0),
            // `super()` was called inside a block
            (None, Some((prev_name, r#gen))) => (prev_name, r#gen + 1),
            // `super()` is called from outside a block
            (None, None) => {
                return Err(ctx.generate_error("cannot call 'super()' outside block", node));
            }
        };

        self.write_buf_writable(ctx, buf)?;

        let block_fragment_write =
            self.input.block.map(|(block, _)| block) == name && self.buf_writable.discard;
        // Allow writing to the buffer if we're in the block fragment
        if block_fragment_write {
            self.buf_writable.discard = false;
        }
        let prev_buf_discard = buf.is_discard();
        buf.set_discard(self.buf_writable.discard);

        // Get the block definition from the heritage chain
        let heritage = self
            .heritage
            .ok_or_else(|| ctx.generate_error("no block ancestors available", node))?;
        let (child_ctx, def) = *heritage.blocks[cur.0].get(cur.1).ok_or_else(|| {
            ctx.generate_error(
                match name {
                    None => fmt_left!("no super() block found for block '{}'", cur.0),
                    Some(name) => fmt_right!(move "no block found for name '{name}'"),
                },
                node,
            )
        })?;

        // We clone the context of the child in order to preserve their macros and imports.
        // But also add all the imports and macros from this template that don't override the
        // child's ones to preserve this template's context.
        let mut child_ctx = child_ctx.clone();
        for (name, mac) in &ctx.macros {
            child_ctx.macros.entry(name).or_insert(mac);
        }
        for (name, import) in &ctx.imports {
            child_ctx
                .imports
                .entry(name)
                .or_insert_with(|| import.clone());
        }

        let size_hint = self.with_child(Some(heritage), |child| {
            // Handle inner whitespace suppression spec and process block nodes
            child.prepare_ws(def.ws1);

            child.super_block = Some(cur);
            let size_hint = child.handle(&child_ctx, &def.nodes, buf, AstLevel::Block)?;

            if !child.locals.is_current_empty() {
                // Need to flush the buffer before popping the variable stack
                child.write_buf_writable(ctx, buf)?;
            }

            child.flush_ws(def.ws2);
            Ok(size_hint)
        })?;

        // Restore original block context and set whitespace suppression for
        // succeeding whitespace according to the outer WS spec
        self.prepare_ws(outer);

        // If we are rendering a specific block and the discard changed, it means that we're done
        // with the block we want to render and that from this point, everything will be discarded.
        //
        // To get this block content rendered as well, we need to write to the buffer before then.
        if buf.is_discard() != prev_buf_discard {
            self.write_buf_writable(ctx, buf)?;
        }
        // Restore the original buffer discarding state
        if block_fragment_write {
            self.buf_writable.discard = true;
        }
        buf.set_discard(prev_buf_discard);

        Ok(size_hint)
    }

    fn write_expr(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        ws: Ws,
        mut expr: &'a WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<usize, CompileError> {
        while let Expr::Group(inner) = &***expr {
            expr = inner;
        }

        if let Expr::Call(call) = &***expr
            && let ControlFlow::Break(size_hint) =
                self.write_expr_call(ctx, buf, ws, expr.span(), call)?
        {
            return Ok(size_hint);
        }

        self.handle_ws(ws);
        self.write_expr_item(expr);
        Ok(0)
    }

    fn write_expr_item(&mut self, expr: &'a WithSpan<'a, Box<Expr<'a>>>) {
        match &***expr {
            Expr::Group(expr) => self.write_expr_item(expr),
            Expr::Concat(items) => {
                for expr in items {
                    self.write_expr_item(expr);
                }
            }
            _ => {
                self.buf_writable.push(
                    compile_time_escape(expr, self.input.escaper).unwrap_or(Writable::Expr(expr)),
                );
            }
        }
    }

    fn write_expr_call(
        &mut self,
        ctx: &Context<'a>,
        buf: &mut Buffer,
        ws: Ws,
        span: Span<'a>,
        call: &'a parser::expr::Call<'a>,
    ) -> Result<ControlFlow<usize>, CompileError> {
        fn check_num_args<'a>(
            span: Span<'a>,
            ctx: &Context<'a>,
            expected: usize,
            found: usize,
            name: &str,
        ) -> Result<(), CompileError> {
            if expected != found {
                Err(ctx.generate_error(
                    format!(
                        "expected {expected} argument{} in `{name}`, found {found}",
                        if expected != 1 { "s" } else { "" }
                    ),
                    span,
                ))
            } else {
                Ok(())
            }
        }

        // handle some special cases for call-expressions
        if let Expr::Var(var_name) = **call.path {
            let caller_alias = self.locals.get_caller(var_name);

            // use of special keyword `super`:
            if var_name == "super" {
                check_num_args(span, ctx, 0, call.args.len(), "super")?;
                return self
                    .write_block(ctx, buf, None, ws, span)
                    .map(ControlFlow::Break);
            }

            // attempted to use keyword `caller` - but no caller is currently in scope
            if var_name == "caller" && caller_alias.is_none() {
                return Err(ctx.generate_error("block is not defined for `caller`", span));
            }

            // short call-expression for macro invocations, like `{{ macro_name() }}`.
            if let Some(macro_def) = ctx.macros.get(var_name) {
                return helpers::MacroInvocation {
                    callsite_ctx: ctx,
                    callsite_span: span,
                    call: None,
                    callsite_ws: ws,
                    call_args: &call.args,
                    macro_def,
                    macro_ctx: ctx,
                }
                .write(buf, self)
                .map(ControlFlow::Break);
            }

            // the called variable is an alias to some macro's `caller()`.
            // This is either `caller()` itself, or an alias created by  `{% set alias = caller %}`.
            if let Some(LocalCallerMeta { call_ctx, def }) = caller_alias.cloned() {
                self.handle_ws(ws);
                let span_span = ctx.span_for_node(span);
                let size_hint = self.push_locals(|this| {
                    // Block-out the special caller() variable from this scope onward until it is defined by a
                    // new call-block again. This prohibits a caller from calling itself.
                    this.locals.insert("caller".into(), LocalMeta::Negative);

                    this.write_buf_writable(&call_ctx, buf)?;
                    this.prepare_ws(def.ws1);
                    let mut value = Buffer::new();
                    let mut variable_buf = Buffer::new();
                    check_num_args(
                        span,
                        &call_ctx,
                        def.caller_args.len(),
                        call.args.len(),
                        "caller",
                    )?;
                    for (index, arg) in def.caller_args.iter().enumerate() {
                        match call.args.get(index) {
                            Some(expr) => {
                                value.clear();
                                match &***expr {
                                    // If `expr` is already a form of variable then
                                    // don't reintroduce a new variable. This is
                                    // to avoid moving non-copyable values.
                                    &Expr::Var(name) if name != "self" => {
                                        let var = this.locals.resolve_or_self(name);
                                        this.locals.insert(
                                            Cow::Borrowed(arg),
                                            LocalMeta::var_with_ref(var),
                                        );
                                    }
                                    Expr::AssociatedItem(obj, associated_item) => {
                                        let mut associated_item_buf = Buffer::new();
                                        this.visit_associated_item(
                                            &call_ctx,
                                            &mut associated_item_buf,
                                            obj,
                                            associated_item,
                                        )?;

                                        // FIXME: Too many steps to get a string. Also,
                                        // `visit_associated_item` returns stuff like `x.y`, how
                                        // is this supposed to match a variable? O.o
                                        let associated_item = associated_item_buf.to_string();
                                        let var = this
                                            .locals
                                            .resolve(&associated_item)
                                            .unwrap_or(associated_item);
                                        this.locals.insert(
                                            Cow::Borrowed(arg),
                                            LocalMeta::var_with_ref(var),
                                        );
                                    }
                                    // Everything else still needs to become variables,
                                    // to avoid having the same logic be executed
                                    // multiple times, e.g. in the case of macro
                                    // parameters being used multiple times.
                                    _ => {
                                        value.write(
                                            this.visit_expr_root(&call_ctx, expr)?,
                                            span_span,
                                        );
                                        // We need to normalize the arg to write it, thus we need to add it to
                                        // locals in the normalized manner
                                        let id = field_new(arg, span_span);
                                        variable_buf.write_tokens(if !is_copyable(expr) {
                                            quote_spanned! { span_span => let #id = &(#value); }
                                        } else {
                                            quote_spanned! { span_span => let #id = #value; }
                                        });
                                        this.locals.insert_with_default(Cow::Borrowed(arg));
                                    }
                                }
                            }
                            None => {
                                return Err(call_ctx.generate_error(
                                    format_args!("missing `{arg}` argument in `caller`"),
                                    span,
                                ));
                            }
                        }
                    }
                    value.clear();
                    let mut size_hint =
                        this.handle(&call_ctx, &def.nodes, &mut value, AstLevel::Nested)?;

                    this.flush_ws(def.ws2);
                    size_hint += this.write_buf_writable(&call_ctx, &mut value)?;
                    let value = value.into_token_stream();
                    let variable_buf = variable_buf.into_token_stream();
                    quote_into!(buf, span_span, { #variable_buf #value });
                    Ok(size_hint)
                })?;
                return Ok(ControlFlow::Break(size_hint));
            }
        }

        // short call-expression for scoped macro invocations, like `{{ scope::macro_name() }}`.
        if let Expr::Path(path_components) = &**call.path
            && let [scope, macro_name] = path_components.as_slice()
            && scope.generics.is_empty()
            && macro_name.generics.is_empty()
            && let Some(scope) = ctx.imports.get(&scope.name)
            && let Some(macro_ctx) = self.contexts.get(scope)
            && let Some(macro_def) = macro_ctx.macros.get(&macro_name.name)
        {
            return helpers::MacroInvocation {
                callsite_ctx: ctx,
                callsite_span: span,
                call: None,
                callsite_ws: ws,
                call_args: &call.args,
                macro_def,
                macro_ctx,
            }
            .write(buf, self)
            .map(ControlFlow::Break);
        }

        if let Expr::Path(path_components) = &**call.path
            && let [scope, macro_name] = path_components.as_slice()
            && scope.generics.is_empty()
            && macro_name.generics.is_empty()
            && let Some(scope) = ctx.imports.get(&scope.name)
            && let Some(macro_ctx) = self.contexts.get(scope)
            && let Some(macro_def) = macro_ctx.macros.get(&macro_name.name)
        {
            return helpers::MacroInvocation {
                callsite_ctx: ctx,
                callsite_span: span,
                call: None,
                callsite_ws: ws,
                call_args: &call.args,
                macro_def,
                macro_ctx,
            }
            .write(buf, self)
            .map(ControlFlow::Break);
        }

        Ok(ControlFlow::Continue(()))
    }

    // Write expression buffer and empty
    pub(crate) fn write_buf_writable(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
    ) -> Result<usize, CompileError> {
        let mut size_hint = 0;
        let items = mem::take(&mut self.buf_writable.buf);
        let mut it = items.iter().enumerate().peekable();

        if let Some((_, Writable::Lit(lit))) = it.peek() {
            let mut literal = String::new();

            while let Some((_, Writable::Lit(s))) = it.peek() {
                size_hint += s.len();
                string_escape(&mut literal, s);
                it.next();
            }
            let span = ctx.span_for_node(lit.span());
            buf.write_str_lit(literal, span);
        }
        if it.peek().is_none() {
            return Ok(size_hint);
        }

        let mut targets = Buffer::new();
        let mut lines = Buffer::new();
        let mut expr_cache = HashMap::with_capacity(self.buf_writable.len());
        // the `last_line` contains any sequence of trailing simple `writer.write_str()` calls
        let mut trailing_simple_lines = Vec::new();

        let mut matched_expr_buf = Buffer::new();
        while let Some((idx, s)) = it.next() {
            match s {
                Writable::Lit(s) => {
                    let mut items = vec![s];
                    while let Some((_, Writable::Lit(s))) = it.peek() {
                        items.push(s);
                        it.next();
                    }
                    if it.peek().is_some() {
                        let mut literal = String::new();
                        let span = ctx.span_for_node(items[0].span());
                        for s in items {
                            size_hint += s.len();
                            string_escape(&mut literal, s);
                        }
                        lines.write_str_lit(literal, span);
                    } else {
                        trailing_simple_lines = items;
                        break;
                    }
                }
                Writable::Expr(s) => {
                    size_hint += 3;

                    let mut expr_buf = Buffer::new();
                    let span = ctx.span_for_node(s.span());
                    let expr = match self.visit_expr(ctx, &mut expr_buf, s)? {
                        DisplayWrap::Wrapped => expr_buf.into_token_stream(),
                        DisplayWrap::Unwrapped => {
                            let escaper = TokenStream::from_str(self.input.escaper).unwrap();
                            let expr_buf = expr_buf.into_token_stream();
                            quote_spanned!(span=>
                                (&&askama::filters::AutoEscaper::new(&(#expr_buf), #escaper)).
                                    askama_auto_escape()?
                            )
                        }
                    };

                    let (id, entry);
                    let id = if is_cacheable(s) {
                        match expr_cache.entry(expr.to_string()) {
                            Entry::Occupied(e) => {
                                entry = e;
                                entry.get()
                            }
                            Entry::Vacant(entry) => {
                                let id = &*entry.insert(crate::var_expr_n(idx, span));
                                quote_into!(&mut matched_expr_buf, span, { &(#expr), });
                                quote_into!(&mut targets, span, { #id, });
                                id
                            }
                        }
                    } else {
                        quote_into!(&mut matched_expr_buf, span, { &(#expr), });
                        id = crate::var_expr_n(idx, span);
                        quote_into!(&mut targets, span, { #id, });
                        &id
                    };

                    let var_writer = crate::var_writer();
                    let var_values = crate::var_values();
                    quote_into!(&mut lines, span, {
                        (&&&askama::filters::Writable(#id)).askama_write(#var_writer, #var_values)?;
                    });
                }
            }
        }
        quote_into!(
            buf,
            ctx.template_span,
            {
                match (#matched_expr_buf) {
                    (#targets) => {
                        #lines
                    }
                }
            }
        );

        if !trailing_simple_lines.is_empty() {
            let mut literal = String::new();
            let span = ctx.span_for_node(trailing_simple_lines[0].span());
            for s in trailing_simple_lines {
                size_hint += s.len();
                string_escape(&mut literal, s);
            }
            buf.write_str_lit(literal, span);
        }

        Ok(size_hint)
    }

    fn write_comment(&mut self, comment: &'a WithSpan<'a, Comment<'_>>) {
        self.handle_ws(comment.ws);
    }

    fn write_lit(&mut self, lit: &'a WithSpan<'_, Lit<'_>>) {
        assert!(self.next_ws.is_none());
        let Lit { lws, val, rws } = **lit;
        if !lws.is_empty() {
            match self.skip_ws {
                Whitespace::Suppress => {}
                _ if val.is_empty() => {
                    assert!(rws.is_empty());
                    self.next_ws = Some(lws);
                }
                Whitespace::Preserve => {
                    self.buf_writable
                        .push(Writable::Lit(WithSpan::new_with_full(
                            Cow::Borrowed(lws),
                            lit.span(),
                        )));
                }
                Whitespace::Minimize => {
                    self.buf_writable
                        .push(Writable::Lit(WithSpan::new_with_full(
                            Cow::Borrowed(match lws.contains('\n') {
                                true => "\n",
                                false => " ",
                            }),
                            lit.span(),
                        )));
                }
            }
        }

        if !val.is_empty() {
            self.skip_ws = Whitespace::Preserve;
            self.buf_writable
                .push(Writable::Lit(WithSpan::new_with_full(
                    Cow::Borrowed(val),
                    lit.span(),
                )));
        }

        if !rws.is_empty() {
            self.next_ws = Some(rws);
        }
    }

    // Helper methods for dealing with whitespace nodes

    // Combines `flush_ws()` and `prepare_ws()` to handle both trailing whitespace from the
    // preceding literal and leading whitespace from the succeeding literal.
    pub(crate) fn handle_ws(&mut self, ws: Ws) {
        self.flush_ws(ws);
        self.prepare_ws(ws);
    }

    fn should_trim_ws(&self, ws: Option<Whitespace>) -> Whitespace {
        ws.unwrap_or(self.input.config.whitespace)
    }

    // If the previous literal left some trailing whitespace in `next_ws` and the
    // prefix whitespace suppressor from the given argument, flush that whitespace.
    // In either case, `next_ws` is reset to `None` (no trailing whitespace).
    pub(crate) fn flush_ws(&mut self, ws: Ws) {
        if self.next_ws.is_none() {
            return;
        }

        // If `whitespace` is set to `suppress`, we keep the whitespace characters only if there is
        // a `+` character.
        match self.should_trim_ws(ws.0) {
            Whitespace::Preserve => {
                let val = self.next_ws.unwrap();
                if !val.is_empty() {
                    self.buf_writable
                        .push(Writable::Lit(WithSpan::new_with_full(
                            Cow::Borrowed(val),
                            val,
                        )));
                }
            }
            Whitespace::Minimize => {
                let val = self.next_ws.unwrap();
                if !val.is_empty() {
                    self.buf_writable
                        .push(Writable::Lit(WithSpan::new_with_full(
                            Cow::Borrowed(match val.contains('\n') {
                                true => "\n",
                                false => " ",
                            }),
                            val,
                        )));
                }
            }
            Whitespace::Suppress => {}
        }
        self.next_ws = None;
    }

    // Sets `skip_ws` to match the suffix whitespace suppressor from the given
    // argument, to determine whether to suppress leading whitespace from the
    // next literal.
    pub(crate) fn prepare_ws(&mut self, ws: Ws) {
        self.skip_ws = self.should_trim_ws(ws.1);
    }
}

fn bin_op<'a>(
    span: impl Into<Span<'a>>,
    op: &'a str,
    lhs: WithSpan<'a, Box<Expr<'a>>>,
    rhs: WithSpan<'a, Box<Expr<'a>>>,
) -> WithSpan<'a, Box<Expr<'a>>> {
    WithSpan::new_with_full(Box::new(Expr::BinOp(BinOp { op, lhs, rhs })), span)
}

struct CondInfo<'a> {
    cond: &'a WithSpan<'a, Cond<'a>>,
    cond_expr: Option<WithSpan<'a, Box<Expr<'a>>>>,
    generate_condition: bool,
    generate_content: bool,
}

struct Conds<'a> {
    conds: Vec<CondInfo<'a>>,
    ws_before: Option<Ws>,
    ws_after: Option<Ws>,
}

#[derive(Debug, Clone, PartialEq)]
enum EvaluatedResult<'a> {
    AlwaysTrue,
    AlwaysFalse,
    Unknown(WithSpan<'a, Box<Expr<'a>>>),
}

impl<'a> Conds<'a> {
    fn compute_branches(generator: &Generator<'a, '_>, i: &'a If<'a>) -> Self {
        let mut conds = Vec::with_capacity(i.branches.len());
        let mut ws_before = None;
        let mut ws_after = None;
        let mut stop_loop = false;

        for cond in &i.branches {
            if stop_loop {
                ws_after = Some(cond.ws);
                break;
            }
            if let Some(CondTest {
                expr,
                contains_bool_lit_or_is_defined,
                ..
            }) = &cond.cond
            {
                let mut only_contains_is_defined = true;

                let span = expr.span();
                let evaluated_result = if *contains_bool_lit_or_is_defined {
                    Some(generator.evaluate_condition(expr.clone(), &mut only_contains_is_defined))
                } else {
                    None
                };

                match evaluated_result {
                    // We generate the condition in case some calls are changing a variable, but
                    // no need to generate the condition body since it will never be called.
                    //
                    // However, if the condition only contains "is (not) defined" checks, then we
                    // can completely skip it.
                    Some(EvaluatedResult::AlwaysFalse) => {
                        if only_contains_is_defined {
                            if conds.is_empty() && ws_before.is_none() {
                                // If this is the first `if` and it's skipped, we definitely don't
                                // want its whitespace control to be lost.
                                ws_before = Some(cond.ws);
                            }
                            continue;
                        }
                        conds.push(CondInfo {
                            cond,
                            cond_expr: Some(WithSpan::new_with_full(
                                Box::new(Expr::BoolLit(false)),
                                span,
                            )),
                            generate_condition: true,
                            generate_content: false,
                        });
                    }
                    // This case is more interesting: it means that we will always enter this
                    // condition, meaning that any following should not be generated. Another
                    // thing to take into account: if there are no if branches before this one,
                    // no need to generate an `else`.
                    Some(EvaluatedResult::AlwaysTrue) => {
                        let generate_condition = !only_contains_is_defined;
                        conds.push(CondInfo {
                            cond,
                            cond_expr: Some(WithSpan::new_with_full(
                                Box::new(Expr::BoolLit(true)),
                                span,
                            )),
                            generate_condition,
                            generate_content: true,
                        });
                        // Since it's always true, we can stop here.
                        stop_loop = true;
                    }
                    Some(EvaluatedResult::Unknown(cond_expr)) => {
                        conds.push(CondInfo {
                            cond,
                            cond_expr: Some(cond_expr),
                            generate_condition: true,
                            generate_content: true,
                        });
                    }
                    None => {
                        conds.push(CondInfo {
                            cond,
                            cond_expr: None,
                            generate_condition: true,
                            generate_content: true,
                        });
                    }
                }
            } else {
                let generate_condition = !conds.is_empty();
                conds.push(CondInfo {
                    cond,
                    cond_expr: None,
                    generate_condition,
                    generate_content: true,
                });
            }
        }
        Self {
            conds,
            ws_before,
            ws_after,
        }
    }
}

fn median(sizes: &mut [usize]) -> usize {
    if sizes.is_empty() {
        return 0;
    }
    sizes.sort_unstable();
    if sizes.len() % 2 == 1 {
        sizes[sizes.len() / 2]
    } else {
        (sizes[sizes.len() / 2 - 1] + sizes[sizes.len() / 2]) / 2
    }
}

#[derive(Clone, Copy, PartialEq)]
pub(crate) enum AstLevel {
    Top,
    Block,
    Nested,
}

/// Returns `true` if the outcome of this expression may be used multiple times in the same
/// `write!()` call, without evaluating the expression again, i.e. the expression should be
/// side-effect free.
fn is_cacheable(expr: &WithSpan<'_, Box<Expr<'_>>>) -> bool {
    match &***expr {
        // Literals are the definition of pure:
        Expr::BoolLit(_) => true,
        Expr::NumLit(_, _) => true,
        Expr::StrLit(_) => true,
        Expr::CharLit(_) => true,
        // fmt::Display should have no effects:
        Expr::Var(_) => true,
        Expr::Path(_) => true,
        // Check recursively:
        Expr::Array(args) => args.iter().all(is_cacheable),
        Expr::AssociatedItem(lhs, _) => is_cacheable(lhs),
        Expr::Index(lhs, rhs) => is_cacheable(lhs) && is_cacheable(rhs),
        Expr::Filter(v) => v.arguments.iter().all(is_cacheable),
        Expr::Unary(_, arg) => is_cacheable(arg),
        Expr::BinOp(v) => is_cacheable(&v.lhs) && is_cacheable(&v.rhs),
        Expr::IsDefined(_) | Expr::IsNotDefined(_) => true,
        Expr::Range(v) => {
            v.lhs.as_ref().is_none_or(is_cacheable) && v.rhs.as_ref().is_none_or(is_cacheable)
        }
        Expr::Group(arg) => is_cacheable(arg),
        Expr::Tuple(args) => args.iter().all(is_cacheable),
        Expr::NamedArgument(_, expr) => is_cacheable(expr),
        Expr::As(expr, _) => is_cacheable(expr),
        Expr::Try(expr) => is_cacheable(expr),
        Expr::Concat(args) => args.iter().all(is_cacheable),
        // Doesn't make sense in this context.
        Expr::LetCond(_) => false,
        // We have too little information to tell if the expression is pure:
        Expr::Call { .. } => false,
        Expr::RustMacro(_, _) => false,
        // Should never be encountered:
        Expr::FilterSource => unreachable!("FilterSource in expression?"),
        Expr::ArgumentPlaceholder => unreachable!("ExpressionPlaceholder in expression?"),
    }
}
