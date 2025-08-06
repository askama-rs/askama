use core::fmt;
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::Write;
use std::mem;

use parser::node::{Call, Macro, Ws};
use parser::{Expr, Span, WithSpan};
use quote::quote_spanned;
use rustc_hash::FxBuildHasher;

use crate::generator::node::AstLevel;
use crate::generator::{Generator, LocalMeta, is_copyable};
use crate::heritage::Context;
use crate::integration::Buffer;
use crate::{CompileError, field_new};

/// Helper to generate the code for macro invocations
pub(crate) struct MacroInvocation<'a, 'b> {
    pub callsite_ctx: &'b Context<'a>,
    pub callsite_span: Span<'a>,
    pub callsite_ws: Ws,
    pub call_args: &'b Vec<WithSpan<'a, Box<Expr<'a>>>>,
    pub call: Option<&'a WithSpan<'a, Call<'a>>>,
    pub macro_def: &'a Macro<'a>,
    pub macro_ctx: &'b Context<'a>,
}

impl<'a, 'b> MacroInvocation<'a, 'b> {
    // FIXME: add missing spans
    pub(crate) fn write<'h>(
        &self,
        buf: &'b mut Buffer,
        generator: &mut Generator<'a, 'h>,
    ) -> Result<usize, CompileError> {
        if generator
            .seen_callers
            .iter()
            .any(|(s, _)| std::ptr::eq(*s, self.macro_def))
        {
            let mut message = "Found recursion in macro calls:".to_owned();
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
            this.write_buf_writable(self.callsite_ctx, &mut content)?;

            this.prepare_ws(self.macro_def.ws1);

            self.write_preamble(&mut content, this)?;

            let mut size_hint = this.handle(
                self.macro_ctx,
                &self.macro_def.nodes,
                &mut content,
                AstLevel::Nested,
            )?;

            this.flush_ws(self.macro_def.ws2);
            size_hint += this.write_buf_writable(self.callsite_ctx, &mut content)?;
            let content = content.into_token_stream();
            quote_into!(buf, self.callsite_ctx.template_span, {{ #content }});

            this.prepare_ws(self.callsite_ws);
            this.seen_callers.pop();
            Ok(size_hint)
        })
    }

    fn write_preamble<'h>(
        &self,
        buf: &'b mut Buffer,
        generator: &mut Generator<'a, 'h>,
    ) -> Result<(), CompileError> {
        let mut named_arguments: HashMap<&str, _, FxBuildHasher> = HashMap::default();
        if let Some(Expr::NamedArgument(_, _)) = self.call_args.last().map(|expr| &***expr) {
            // First we check that all named arguments actually exist in the called item.
            for (index, arg) in self.call_args.iter().enumerate().rev() {
                let Expr::NamedArgument(arg_name, _) = &***arg else {
                    break;
                };
                if !self.macro_def.args.iter().any(|(arg, _)| arg == arg_name) {
                    return Err(self.callsite_ctx.generate_error(
                        format_args!(
                            "no argument named `{arg_name}` in macro {}",
                            self.macro_def.name
                        ),
                        self.callsite_span,
                    ));
                }
                named_arguments.insert(arg_name, (index, arg));
            }
        }
        let mut value = Buffer::new();
        let mut allow_positional = true;
        let mut used_named_args = vec![false; self.call_args.len()];

        for (index, (arg, default_value)) in self.macro_def.args.iter().enumerate() {
            let expr = if let Some((index, expr)) = named_arguments.get(arg) {
                used_named_args[*index] = true;
                allow_positional = false;
                expr
            } else {
                match self.call_args.get(index) {
                    Some(arg_expr) if !matches!(***arg_expr, Expr::NamedArgument(_, _)) => {
                        // If there is already at least one named argument, then it's not allowed
                        // to use unnamed ones at this point anymore.
                        if !allow_positional {
                            return Err(self.callsite_ctx.generate_error(
                                format_args!(
                                    "cannot have unnamed argument (`{arg}`) after named argument \
                                        in call to macro {}",
                                    self.macro_def.name
                                ),
                                self.callsite_span,
                            ));
                        }
                        arg_expr
                    }
                    Some(arg_expr) if used_named_args[index] => {
                        let Expr::NamedArgument(name, _) = ***arg_expr else {
                            unreachable!()
                        };
                        return Err(self.callsite_ctx.generate_error(
                            format_args!("`{name}` is passed more than once"),
                            self.callsite_span,
                        ));
                    }
                    _ => {
                        if let Some(default_value) = default_value {
                            default_value
                        } else {
                            return Err(self.callsite_ctx.generate_error(
                                format_args!("missing `{arg}` argument"),
                                self.callsite_span,
                            ));
                        }
                    }
                }
            };
            match &***expr {
                // If `expr` is already a form of variable then
                // don't reintroduce a new variable. This is
                // to avoid moving non-copyable values.
                &Expr::Var(name) if name != "self" => {
                    let var = generator.locals.resolve_or_self(name);
                    generator
                        .locals
                        .insert(Cow::Borrowed(arg), LocalMeta::var_with_ref(var));
                }
                Expr::AssociatedItem(obj, associated_item) => {
                    let mut associated_item_buf = Buffer::new();
                    generator.visit_associated_item(
                        self.callsite_ctx,
                        &mut associated_item_buf,
                        obj,
                        associated_item,
                    )?;

                    // FIXME: Too many steps to get a string. Also, `visit_associated_item` returns
                    // stuff like `x.y`, how is this supposed to match a variable? O.o
                    let associated_item = associated_item_buf.into_token_stream().to_string();
                    let var = generator
                        .locals
                        .resolve(&associated_item)
                        .unwrap_or(associated_item);
                    generator
                        .locals
                        .insert(Cow::Borrowed(arg), LocalMeta::var_with_ref(var));
                }
                // Everything else still needs to become variables,
                // to avoid having the same logic be executed
                // multiple times, e.g. in the case of macro
                // parameters being used multiple times.
                _ => {
                    value.clear();
                    value.write_tokens(generator.visit_expr_root(self.callsite_ctx, expr)?);
                    let span = self.callsite_ctx.template_span;
                    let id = field_new(arg, span);
                    buf.write_tokens(if !is_copyable(expr) {
                        quote_spanned! { span => let #id = &(#value); }
                    } else {
                        quote_spanned! { span => let #id = #value; }
                    });

                    generator.locals.insert_with_default(Cow::Borrowed(arg));
                }
            }
        }

        Ok(())
    }

    fn ensure_arg_count(&self) -> Result<(), CompileError> {
        if self.call_args.len() > self.macro_def.args.len() {
            return Err(self.callsite_ctx.generate_error(
                format_args!(
                    "macro `{}` expected {} argument{}, found {}",
                    self.macro_def.name,
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
            .map(|&(name, _)| Some(name))
            .collect();
        for (pos, arg) in self.call_args.iter().enumerate() {
            let pos = match ***arg {
                Expr::NamedArgument(name, ..) => self
                    .macro_def
                    .args
                    .iter()
                    .position(|(arg_name, _)| *arg_name == name),
                _ => Some(pos),
            };
            if let Some(pos) = pos
                && mem::take(&mut args[pos]).is_none()
            {
                // This argument was already passed, so error.
                return Err(self.callsite_ctx.generate_error(
                    format_args!(
                        "argument `{}` was passed more than once when calling macro `{}`",
                        self.macro_def.args[pos].0, self.macro_def.name,
                    ),
                    self.callsite_span,
                ));
            }
        }

        // Now we can check off arguments with a default value, too.
        for (pos, (_, dflt)) in self.macro_def.args.iter().enumerate() {
            if dflt.is_some() {
                args[pos] = None;
            }
        }

        // Now that we have a needed information, we can print an error message (if needed).
        struct FmtMissing<'a, I> {
            count: usize,
            missing: I,
            name: &'a str,
        }

        impl<'a, I: Iterator<Item = &'a str> + Clone> fmt::Display for FmtMissing<'a, I> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                if self.count == 1 {
                    let a = self.missing.clone().next().unwrap();
                    write!(
                        f,
                        "missing argument when calling macro `{}`: `{a}`",
                        self.name
                    )
                } else {
                    write!(f, "missing arguments when calling macro `{}`: ", self.name)?;
                    for (idx, a) in self.missing.clone().enumerate() {
                        if idx == self.count - 1 {
                            write!(f, " and ")?;
                        } else if idx > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "`{a}`")?;
                    }
                    Ok(())
                }
            }
        }

        let missing = args.iter().filter_map(Option::as_deref);
        let fmt_missing = FmtMissing {
            count: missing.clone().count(),
            missing,
            name: self.macro_def.name,
        };
        if fmt_missing.count == 0 {
            Ok(())
        } else {
            Err(self
                .callsite_ctx
                .generate_error(fmt_missing, self.callsite_span))
        }
    }
}
