use core::fmt;
use std::borrow::Cow;
use std::fmt::Write;
use std::mem;
use std::str::FromStr;

use parser::node::{Call, Macro, Node, Ws};
use parser::{Expr, Span, TyGenerics, WithSpan};
use proc_macro2::TokenStream;
use quote::quote_spanned;

use crate::generator::node::AstLevel;
use crate::generator::{BlockInfo, Generator, LocalMeta, MapChain, RenderFor, is_copyable};
use crate::heritage::Context;
use crate::integration::Buffer;
use crate::{CompileError, HashMap, SizeHint, field_new, quote_into};

/// Helper to generate the code for macro invocations
pub(crate) struct MacroInvocation<'a, 'b> {
    pub callsite_ctx: &'b Context<'a>,
    pub callsite_span: Span,
    pub callsite_ws: Ws,
    pub call_args: &'b [WithSpan<Box<Expr<'a>>>],
    pub call: Option<&'a WithSpan<Call<'a>>>,
    pub macro_def: &'a Macro<'a>,
    pub macro_ctx: &'b Context<'a>,
}

impl<'a, 'b> MacroInvocation<'a, 'b> {
    // FIXME: add missing spans
    pub(crate) fn write<'h>(
        &self,
        buf: &'b mut Buffer,
        generator: &mut Generator<'a, 'h>,
        render_for: RenderFor,
    ) -> Result<SizeHint, CompileError> {
        if generator
            .seen_callers
            .iter()
            .any(|(s, _)| std::ptr::eq(*s, self.macro_def))
        {
            if let Some(reason) = self.why_not_a_function() {
                let mut message = format!("Found recursion in macro calls. {reason}:");
                for (m, f) in &generator.seen_callers {
                    if let Some(f) = f {
                        write!(message, "{f}").unwrap();
                    } else {
                        write!(message, "\n`{}`", m.name.escape_debug()).unwrap();
                    }
                }
                return Err(self
                    .callsite_ctx
                    .generate_error(message, self.callsite_span));
            }
            return self.write_function_call(buf, generator);
        } else {
            generator.seen_callers.push((
                self.macro_def,
                self.callsite_ctx.file_info_of(self.callsite_span),
            ));
        }

        generator.push_locals(|this| {
            if let Some(call) = self.call {
                this.locals.insert(
                    "caller".into(),
                    LocalMeta::caller(call, self.callsite_ctx.clone()),
                );
            }

            self.ensure_arg_count()?;

            this.flush_ws(self.callsite_ws); // Cannot handle_ws() here: whitespace from macro definition comes first
            let mut content = Buffer::new();
            let mut size_hint = this.write_buf_writable(self.callsite_ctx, &mut content)?;

            this.prepare_ws(self.macro_def.ws1);

            self.write_preamble(&mut content, this)?;

            size_hint += this.handle(
                self.macro_ctx,
                &self.macro_def.nodes,
                &mut content,
                AstLevel::Nested,
                render_for,
            )?;

            this.flush_ws(self.macro_def.ws2);
            size_hint += this.write_buf_writable(self.callsite_ctx, &mut content)?;
            let content = content.into_token_stream();
            quote_into!(buf, self.callsite_ctx.span_for_node(self.callsite_span), {{ #content }});

            this.prepare_ws(self.callsite_ws);
            this.seen_callers.pop();
            Ok(size_hint)
        })
    }

    /// A recursive call is written as a call to a function generated for the macro, see
    /// [`Generator::write_macro_functions()`]. Returns why this call cannot be one.
    fn why_not_a_function(&self) -> Option<String> {
        let name = self.macro_def.name.escape_debug();
        if let Some(arg) = self.macro_def.args.iter().find(|arg| arg.ty.is_none()) {
            return Some(format!(
                "A macro can only call itself if all its arguments have a type, \
                 but argument `{}` of macro `{name}` has none",
                arg.name.escape_debug(),
            ));
        }
        // The function cannot see the caller's body, so only an empty one is allowed.
        if let Some(call) = self.call
            && (!call.caller_args.is_empty()
                || call.nodes.iter().any(|node| match &**node {
                    Node::Lit(lit) => !lit.val.is_empty(),
                    Node::Comment(_) => false,
                    _ => true,
                }))
        {
            return Some(format!(
                "A macro can only call itself without a `caller` body, \
                 but this call of macro `{name}` has one",
            ));
        }
        None
    }

    fn write_function_call<'h>(
        &self,
        buf: &'b mut Buffer,
        generator: &mut Generator<'a, 'h>,
    ) -> Result<SizeHint, CompileError> {
        self.ensure_arg_count()?;
        let function = generator.macro_function(self.macro_def, self.macro_ctx);
        let span = self.callsite_ctx.span_for_node(self.callsite_span);

        generator.push_locals(|this| {
            this.flush_ws(self.callsite_ws);
            let mut content = Buffer::new();
            let size_hint = this.write_buf_writable(self.callsite_ctx, &mut content)?;
            // Every argument has a type, so the preamble binds each one to a variable of its name.
            self.write_preamble(&mut content, this)?;
            let args = self
                .macro_def
                .args
                .iter()
                .map(|arg| field_new(&arg.name, span));
            let var_writer = crate::var_writer();
            let var_values = crate::var_values();
            quote_into!(&mut content, span, {
                self.#function(#var_writer, #var_values, #(#args),*)?;
            });
            let content = content.into_token_stream();
            quote_into!(buf, span, {{ #content }});

            this.prepare_ws(self.callsite_ws);
            Ok(size_hint)
        })
    }

    fn write_preamble<'h>(
        &self,
        buf: &'b mut Buffer,
        generator: &mut Generator<'a, 'h>,
    ) -> Result<(), CompileError> {
        let mut named_arguments = HashMap::default();
        if let Some(Expr::NamedArgument(_, _)) = self.call_args.last().map(|expr| &***expr) {
            // First we check that all named arguments actually exist in the called item.
            for arg in self.call_args.iter().rev() {
                let &Expr::NamedArgument(arg_name, _) = &***arg else {
                    break;
                };
                let Some(index) = self
                    .macro_def
                    .args
                    .iter()
                    .position(|arg| arg.name == arg_name)
                else {
                    return Err(self.callsite_ctx.generate_error(
                        format_args!(
                            "no argument named `{}` in macro `{}`",
                            arg_name.escape_debug(),
                            self.macro_def.name.escape_debug(),
                        ),
                        self.callsite_span,
                    ));
                };
                named_arguments.insert(&**arg_name, (index, arg));
            }
        }
        let mut used_args = vec![None; self.macro_def.args.len()];

        for (index, call_arg) in self.call_args.iter().enumerate() {
            // No need to check if named arguments are before unnamed arguments since it's
            // already checked in `askama_parser`.
            let (index, expr) = match &***call_arg {
                Expr::NamedArgument(arg_name, _) => {
                    // We already looked for invalid named args when generating `named_arguments`.
                    let Some((index, expr)) = named_arguments.get(&**arg_name) else {
                        unreachable!()
                    };
                    (*index, *expr)
                }
                _ => (index, call_arg),
            };
            used_args[index] = Some(expr);
        }

        let span = self.callsite_ctx.span_for_node(self.callsite_span);
        let mut args = ArgBindings::default();
        for (arg, expr) in self.macro_def.args.iter().zip(&used_args) {
            if let Some(expr) = expr {
                let span = self.callsite_ctx.span_for_node(arg.name.span());
                args.add(
                    generator,
                    self.callsite_ctx,
                    &arg.name,
                    arg.ty.as_ref(),
                    expr,
                    span,
                )?;
            }
        }
        args.write(buf, generator, span);

        // Default values can use the arguments before them, so they are bound one by one.
        for (arg, expr) in self.macro_def.args.iter().zip(&used_args) {
            if expr.is_some() {
                continue;
            }
            let Some(default_value) = &arg.default else {
                return Err(self.callsite_ctx.generate_error(
                    format_args!("missing `{}` argument", arg.name.escape_debug()),
                    self.callsite_span,
                ));
            };
            let span = self.callsite_ctx.span_for_node(arg.name.span());
            let mut args = ArgBindings::default();
            args.add(
                generator,
                self.callsite_ctx,
                &arg.name,
                arg.ty.as_ref(),
                default_value,
                span,
            )?;
            args.write(buf, generator, span);
        }

        Ok(())
    }

    fn ensure_arg_count(&self) -> Result<(), CompileError> {
        if self.call_args.len() > self.macro_def.args.len() {
            return Err(self.callsite_ctx.generate_error(
                format_args!(
                    "macro `{}` expected {} argument{}, found {}",
                    self.macro_def.name.escape_debug(),
                    self.macro_def.args.len(),
                    if self.macro_def.args.len() > 1 {
                        "s"
                    } else {
                        ""
                    },
                    self.call_args.len(),
                ),
                self.callsite_span,
            ));
        }

        // First we list of arguments position, then we remove every argument with a value.
        let mut args: Vec<_> = self
            .macro_def
            .args
            .iter()
            .map(|arg| Some(arg.name))
            .collect();
        for (pos, arg) in self.call_args.iter().enumerate() {
            let pos = match ***arg {
                Expr::NamedArgument(name, ..) => {
                    self.macro_def.args.iter().position(|arg| arg.name == name)
                }
                _ => Some(pos),
            };
            if let Some(pos) = pos
                && mem::take(&mut args[pos]).is_none()
            {
                // This argument was already passed, so error.
                return Err(self.callsite_ctx.generate_error(
                    format_args!(
                        "argument `{}` was passed more than once when calling macro `{}`",
                        self.macro_def.args[pos].name.escape_debug(),
                        self.macro_def.name.escape_debug(),
                    ),
                    arg.span(),
                ));
            }
        }

        // Now we can check off arguments with a default value, too.
        for (pos, arg) in self.macro_def.args.iter().enumerate() {
            if arg.default.is_some() {
                args[pos] = None;
            }
        }

        // Now that we have a needed information, we can print an error message (if needed).
        struct FmtMissing<'a, I> {
            count: usize,
            missing: I,
            name: WithSpan<&'a str>,
        }

        impl<'a, I: Iterator<Item = WithSpan<&'a str>> + Clone> fmt::Display for FmtMissing<'a, I> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let mut iter = self.missing.clone();
                if self.count == 1 {
                    let a = iter.next().unwrap();
                    write!(
                        f,
                        "missing argument when calling macro `{}`: `{}`",
                        self.name.escape_debug(),
                        a.escape_debug(),
                    )
                } else {
                    write!(
                        f,
                        "missing arguments when calling macro `{}`: ",
                        self.name.escape_debug(),
                    )?;
                    for (idx, a) in iter.enumerate() {
                        if idx == self.count - 1 {
                            write!(f, " and ")?;
                        } else if idx > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "`{}`", a.escape_debug())?;
                    }
                    Ok(())
                }
            }
        }

        let missing = args.iter().filter_map(|o| *o);
        let count = missing.clone().count();
        if count == 0 {
            return Ok(());
        }

        let fmt_missing = FmtMissing {
            count,
            missing,
            name: self.macro_def.name,
        };
        Err(self
            .callsite_ctx
            .generate_error(fmt_missing, self.callsite_span))
    }
}

/// Arguments of a macro or `caller()` call. They are evaluated in the call-site scope, then bound
/// all at once, so an argument can't see a parameter that has the same name as one of its variables.
#[derive(Default)]
pub(crate) struct ArgBindings<'a> {
    ids: Vec<TokenStream>,
    tys: Vec<TokenStream>,
    values: Vec<TokenStream>,
    locals: Vec<(&'a str, LocalMeta<'a>)>,
}

impl<'a> ArgBindings<'a> {
    pub(crate) fn add(
        &mut self,
        generator: &mut Generator<'a, '_>,
        ctx: &Context<'_>,
        name: &'a str,
        ty: Option<&WithSpan<TyGenerics<'a>>>,
        expr: &WithSpan<Box<Expr<'a>>>,
        span: proc_macro2::Span,
    ) -> Result<(), CompileError> {
        let var = match &***expr {
            // If `expr` is already a form of variable then
            // don't reintroduce a new variable. This is
            // to avoid moving non-copyable values.
            &Expr::Var(name) if name != "self" => Some(generator.locals.resolve_or_self(name)),
            Expr::AssociatedItem(obj, associated_item) => {
                let mut associated_item_buf = Buffer::new();
                generator.visit_associated_item(
                    ctx,
                    &mut associated_item_buf,
                    obj,
                    associated_item,
                )?;

                // FIXME: Too many steps to get a string. Also, `visit_associated_item` returns
                // stuff like `x.y`, how is this supposed to match a variable? O.o
                let associated_item = associated_item_buf.into_token_stream().to_string();
                Some(
                    generator
                        .locals
                        .resolve(&associated_item)
                        .unwrap_or(associated_item),
                )
            }
            _ => None,
        };

        let value = match var {
            Some(var) if ty.is_none() => {
                self.locals.push((name, LocalMeta::var_with_ref(var)));
                return Ok(());
            }
            Some(var) => {
                let var = TokenStream::from_str(&var).expect("invalid variable name");
                quote_spanned! { span => &#var }
            }
            // Everything else still needs to become variables,
            // to avoid having the same logic be executed
            // multiple times, e.g. in the case of macro
            // parameters being used multiple times.
            None => {
                let value = generator.visit_expr_root(ctx, expr)?;
                if !is_copyable(expr) || ty.is_some() {
                    quote_spanned! { span => &(#value) }
                } else {
                    value
                }
            }
        };
        self.tys.push(match ty {
            Some(ty) => {
                // To prevent moving the value/variable, we take a reference of it.
                let mut ty_buf = Buffer::new();
                ty_buf.write_token(syn::Token![&], span);
                generator.visit_ty_generic(ctx, &mut ty_buf, ty, span);
                ty_buf.into_token_stream()
            }
            None => quote_spanned! { span => _ },
        });
        self.ids.push(field_new(name, span));
        self.values.push(value);
        self.locals.push((name, LocalMeta::var_decl()));
        Ok(())
    }

    pub(crate) fn write(
        self,
        buf: &mut Buffer,
        generator: &mut Generator<'a, '_>,
        span: proc_macro2::Span,
    ) {
        let Self {
            ids,
            tys,
            values,
            locals,
        } = self;
        if !ids.is_empty() {
            buf.write_tokens(quote_spanned! { span =>
                let (#(#ids,)*): (#(#tys,)*) = (#(#values,)*);
            });
        }
        for (name, meta) in locals {
            generator.locals.insert(Cow::Borrowed(name), meta);
        }
    }
}

impl<'a> Generator<'a, '_> {
    /// The name of the function generated for a macro that calls itself.
    pub(crate) fn macro_function(
        &mut self,
        macro_def: &'a Macro<'a>,
        macro_ctx: &Context<'a>,
    ) -> syn::Ident {
        let index = match self
            .macro_functions
            .iter()
            .position(|(def, _)| std::ptr::eq(*def, macro_def))
        {
            Some(index) => index,
            None => {
                self.macro_functions.push((macro_def, macro_ctx.clone()));
                self.macro_functions.len() - 1
            }
        };
        // Each block fragment generates its own copy, in an `impl` of the same type.
        let name = match self.input.block {
            Some((block, _)) => format!("__askama_macro_{index}_{block}"),
            None => format!("__askama_macro_{index}"),
        };
        syn::Ident::new(&name, proc_macro2::Span::call_site())
    }

    /// Writes an `impl` block with a method for each macro that calls itself (directly or
    /// indirectly). The outermost call is inlined as usual; the recursive calls call the method.
    /// Like a Rust function, the method only sees its arguments and the template's fields.
    pub(crate) fn write_macro_functions(&mut self, buf: &mut Buffer) -> Result<(), CompileError> {
        let span = proc_macro2::Span::call_site();
        let var_writer = crate::var_writer();
        let var_values = crate::var_values();
        let mut functions = Buffer::new();
        // A body can call further recursive macros, which adds them to the list.
        let mut index = 0;
        while let Some((macro_def, macro_ctx)) = self.macro_functions.get(index).cloned() {
            let function = self.macro_function(macro_def, &macro_ctx);
            let mut generator = Generator::new(
                self.input,
                self.contexts,
                self.heritage,
                MapChain::default(),
                false,
                BlockInfo::new(),
            );
            generator.macro_functions = mem::take(&mut self.macro_functions);
            generator.seen_callers.push((macro_def, None));

            let mut params = Buffer::new();
            for arg in &macro_def.args {
                let Some(ty) = &arg.ty else {
                    unreachable!("checked by `why_not_a_function()`")
                };
                let name = field_new(&arg.name, span);
                let mut ty_buf = Buffer::new();
                generator.visit_ty_generic(&macro_ctx, &mut ty_buf, ty, span);
                let ty = ty_buf.into_token_stream();
                quote_into!(&mut params, span, { #name: &#ty, });
                generator
                    .locals
                    .insert(Cow::Borrowed(*arg.name), LocalMeta::var_decl());
            }
            let params = params.into_token_stream();

            let mut body = Buffer::new();
            generator.prepare_ws(macro_def.ws1);
            let _: SizeHint = generator.handle(
                &macro_ctx,
                &macro_def.nodes,
                &mut body,
                AstLevel::Nested,
                RenderFor::Template,
            )?;
            generator.flush_ws(macro_def.ws2);
            let _: SizeHint = generator.write_buf_writable(&macro_ctx, &mut body)?;
            let body = body.into_token_stream();
            self.macro_functions = generator.macro_functions;

            quote_into!(&mut functions, span, {
                #[allow(clippy::too_many_arguments)]
                fn #function(
                    &self,
                    #var_writer: &mut dyn askama::helpers::core::fmt::Write,
                    #var_values: &dyn askama::Values,
                    #params
                ) -> askama::Result<()> {
                    #[allow(unused_imports)]
                    use askama::{
                        filters::{AutoEscape as _, WriteWritable as _},
                        helpers::{ResultConverter as _, core::fmt::Write as _},
                    };

                    #body
                    askama::Result::Ok(())
                }
            });
            index += 1;
        }
        if index > 0 {
            let functions = functions.into_token_stream();
            let ident = &self.input.ast.ident;
            let (impl_generics, ty_generics, where_clause) =
                self.input.ast.generics.split_for_impl();
            quote_into!(buf, span, {
                impl #impl_generics #ident #ty_generics #where_clause {
                    #functions
                }
            });
        }
        Ok(())
    }
}
