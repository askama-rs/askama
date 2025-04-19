use std::borrow::Cow;

use parser::{Expr, IntKind, Num, Span, StrLit, StrPrefix, TyGenerics, WithSpan};

use super::{DisplayWrap, Generator, TargetIsize, TargetUsize};
use crate::heritage::Context;
use crate::integration::Buffer;
use crate::{CompileError, MsgValidEscapers};

impl<'a> Generator<'a, '_> {
    pub(super) fn visit_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Expr<'a>>],
        generics: &[WithSpan<'a, TyGenerics<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let filter = match name {
            "center" => Self::visit_center_filter,
            "deref" => Self::visit_deref_filter,
            "escape" | "e" => Self::visit_escape_filter,
            "filesizeformat" => Self::visit_humansize,
            "fmt" => Self::visit_fmt_filter,
            "format" => Self::visit_format_filter,
            "indent" => Self::visit_indent_filter,
            "join" => Self::visit_join_filter,
            "json" | "tojson" => Self::visit_json_filter,
            "linebreaks" => Self::visit_linebreaks_filter,
            "linebreaksbr" => Self::visit_linebreaksbr_filter,
            "paragraphbreaks" => Self::visit_paragraphbreaks_filter,
            "pluralize" => Self::visit_pluralize_filter,
            "ref" => Self::visit_ref_filter,
            "safe" => Self::visit_safe_filter,
            "truncate" => Self::visit_truncate_filter,
            "urlencode" => Self::visit_urlencode_filter,
            "urlencode_strict" => Self::visit_urlencode_strict_filter,
            "value" => return self.visit_value(ctx, buf, args, generics, node, "`value` filter"),
            "wordcount" => Self::visit_wordcount_filter,
            name => {
                let filter = match () {
                    _ if BUILTIN_FILTERS.contains(&name) => Self::visit_builtin_filter,
                    _ if BUILTIN_FILTERS_ALLOC.contains(&name) => Self::visit_builtin_filter_alloc,
                    _ if BUILTIN_FILTERS_STD.contains(&name) => Self::visit_builtin_filter_std,
                    _ => Self::visit_custom_filter,
                };
                return filter(self, ctx, buf, name, args, generics, node);
            }
        };

        ensure_no_generics(ctx, name, node, generics)?;
        filter(self, ctx, buf, args, node)
    }

    fn visit_custom_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Expr<'a>>],
        generics: &[WithSpan<'a, TyGenerics<'a>>],
        _node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        buf.write(format_args!("filters::{name}"));
        self.visit_call_generics(buf, generics);
        buf.write('(');
        self.visit_arg(ctx, buf, &args[0])?;
        buf.write(",__askama_values");
        if args.len() > 1 {
            buf.write(',');
            self.visit_args(ctx, buf, &args[1..])?;
        }
        buf.write(")?");
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_builtin_filter_alloc(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Expr<'a>>],
        generics: &[WithSpan<'a, TyGenerics<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, name, node)?;
        self.visit_builtin_filter(ctx, buf, name, args, generics, node)
    }

    fn visit_builtin_filter_std(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Expr<'a>>],
        generics: &[WithSpan<'a, TyGenerics<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_std(ctx, name, node)?;
        self.visit_builtin_filter(ctx, buf, name, args, generics, node)
    }

    fn visit_builtin_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Expr<'a>>],
        generics: &[WithSpan<'a, TyGenerics<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_no_generics(ctx, name, node, generics)?;
        buf.write(format_args!("askama::filters::{name}"));
        self.visit_call_generics(buf, generics);
        buf.write('(');
        self.visit_args(ctx, buf, args)?;
        buf.write(")?");
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_urlencode_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_urlencode_filter_inner(ctx, buf, "urlencode", args, node)
    }

    fn visit_urlencode_strict_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_urlencode_filter_inner(ctx, buf, "urlencode_strict", args, node)
    }

    fn visit_urlencode_filter_inner(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        if cfg!(not(feature = "urlencode")) {
            return Err(ctx.generate_error(
                format_args!("the `{name}` filter requires the `urlencode` feature to be enabled"),
                node,
            ));
        }

        // Both filters return HTML-safe strings.
        buf.write(format_args!(
            "askama::filters::HtmlSafeOutput(askama::filters::{name}(",
        ));
        self.visit_args(ctx, buf, args)?;
        buf.write(")?)");
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_wordcount_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, "wordcount", node)?;
        if args.len() != 1 {
            return Err(ctx.generate_error(
                format_args!("unexpected argument(s) in `wordcount` filter"),
                node,
            ));
        }

        buf.write("match askama::filters::wordcount(&(");
        self.visit_args(ctx, buf, args)?;
        buf.write(
            ")) {\
                expr0 => {\
                    (&&&askama::filters::Writable(&expr0)).\
                        askama_write(&mut askama::helpers::Empty, __askama_values)?;\
                    expr0.into_count()\
                }\
            }\
        ",
        );

        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_humansize(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        _node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        // All filters return numbers, and any default formatted number is HTML safe.
        buf.write(format_args!(
            "askama::filters::HtmlSafeOutput(askama::filters::filesizeformat(\
                 askama::helpers::get_primitive_value(&("
        ));
        self.visit_args(ctx, buf, args)?;
        buf.write(")) as askama::helpers::core::primitive::f32)?)");
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_pluralize_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const SINGULAR: &WithSpan<'static, Expr<'static>> =
            &WithSpan::new_without_span(Expr::StrLit(StrLit {
                prefix: None,
                content: "",
            }));
        const PLURAL: &WithSpan<'static, Expr<'static>> =
            &WithSpan::new_without_span(Expr::StrLit(StrLit {
                prefix: None,
                content: "s",
            }));

        let (count, sg, pl) = match args {
            [count] => (count, SINGULAR, PLURAL),
            [count, sg] => (count, sg, PLURAL),
            [count, sg, pl] => (count, sg, pl),
            _ => {
                return Err(
                    ctx.generate_error("unexpected argument(s) in `pluralize` filter", node)
                );
            }
        };
        if let Some(is_singular) = expr_is_int_lit_plus_minus_one(count) {
            let value = if is_singular { sg } else { pl };
            self.visit_auto_escaped_arg(ctx, buf, value)?;
        } else {
            buf.write("askama::filters::pluralize(");
            self.visit_arg(ctx, buf, count)?;
            for value in [sg, pl] {
                buf.write(',');
                self.visit_auto_escaped_arg(ctx, buf, value)?;
            }
            buf.write(")?");
        }
        Ok(DisplayWrap::Wrapped)
    }

    fn visit_paragraphbreaks_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_linebreaks_filters(ctx, buf, "paragraphbreaks", args, node)
    }

    fn visit_linebreaksbr_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_linebreaks_filters(ctx, buf, "linebreaksbr", args, node)
    }

    fn visit_linebreaks_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_linebreaks_filters(ctx, buf, "linebreaks", args, node)
    }

    fn visit_linebreaks_filters(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, name, node)?;
        if args.len() != 1 {
            return Err(ctx.generate_error(
                format_args!("unexpected argument(s) in `{name}` filter"),
                node,
            ));
        }
        buf.write(format_args!(
            "askama::filters::{name}(&(&&askama::filters::AutoEscaper::new(&(",
        ));
        self.visit_args(ctx, buf, args)?;
        // The input is always HTML escaped, regardless of the selected escaper:
        buf.write("), askama::filters::Html)).askama_auto_escape()?)?");
        // The output is marked as HTML safe, not safe in all contexts:
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_ref_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let arg = match args {
            [arg] => arg,
            _ => return Err(ctx.generate_error("unexpected argument(s) in `as_ref` filter", node)),
        };
        buf.write('&');
        self.visit_expr(ctx, buf, arg)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_deref_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let arg = match args {
            [arg] => arg,
            _ => return Err(ctx.generate_error("unexpected argument(s) in `deref` filter", node)),
        };
        buf.write('*');
        self.visit_expr(ctx, buf, arg)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_json_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        if cfg!(not(feature = "serde_json")) {
            return Err(ctx.generate_error(
                "the `json` filter requires the `serde_json` feature to be enabled",
                node,
            ));
        }

        let filter = match args.len() {
            1 => "json",
            2 => "json_pretty",
            _ => return Err(ctx.generate_error("unexpected argument(s) in `json` filter", node)),
        };
        buf.write(format_args!("askama::filters::{filter}("));
        self.visit_args(ctx, buf, args)?;
        buf.write(")?");
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_indent_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const FALSE: &WithSpan<'static, Expr<'static>> =
            &WithSpan::new_without_span(Expr::BoolLit(false));

        ensure_filter_has_feature_alloc(ctx, "indent", node)?;
        let (source, indent, first, blank) =
            match args {
                [source, indent] => (source, indent, FALSE, FALSE),
                [source, indent, first] => (source, indent, first, FALSE),
                [source, indent, first, blank] => (source, indent, first, blank),
                _ => return Err(ctx.generate_error(
                    "filter `indent` needs a `width` argument, and can have two optional arguments",
                    node,
                )),
            };
        buf.write("askama::filters::indent(");
        self.visit_arg(ctx, buf, source)?;
        buf.write(",");
        self.visit_arg(ctx, buf, indent)?;
        buf.write(", askama::helpers::as_bool(&(");
        self.visit_arg(ctx, buf, first)?;
        buf.write(")), askama::helpers::as_bool(&(");
        self.visit_arg(ctx, buf, blank)?;
        buf.write(")))?");
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_safe_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        if args.len() != 1 {
            return Err(ctx.generate_error("unexpected argument(s) in `safe` filter", node));
        }
        buf.write("askama::filters::safe(");
        self.visit_args(ctx, buf, args)?;
        buf.write(format_args!(", {})?", self.input.escaper));
        Ok(DisplayWrap::Wrapped)
    }

    fn visit_escape_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        if args.len() > 2 {
            return Err(ctx.generate_error("only two arguments allowed to escape filter", node));
        }
        let opt_escaper = match args.get(1).map(|expr| &**expr) {
            Some(Expr::StrLit(StrLit { prefix, content })) => {
                if let Some(prefix) = prefix {
                    let kind = if *prefix == StrPrefix::Binary {
                        "slice"
                    } else {
                        "CStr"
                    };
                    return Err(ctx.generate_error(
                        format_args!(
                            "invalid escaper `b{content:?}`. Expected a string, found a {kind}"
                        ),
                        args[1].span(),
                    ));
                }
                Some(content)
            }
            Some(_) => {
                return Err(ctx.generate_error("invalid escaper type for escape filter", node));
            }
            None => None,
        };
        let escaper = match opt_escaper {
            Some(name) => self
                .input
                .config
                .escapers
                .iter()
                .find_map(|(extensions, path)| {
                    extensions
                        .contains(&Cow::Borrowed(name))
                        .then_some(path.as_ref())
                })
                .ok_or_else(|| {
                    ctx.generate_error(
                        format_args!(
                            "invalid escaper '{name}' for `escape` filter. {}",
                            MsgValidEscapers(&self.input.config.escapers),
                        ),
                        node,
                    )
                })?,
            None => self.input.escaper,
        };
        buf.write("askama::filters::escape(");
        self.visit_args(ctx, buf, &args[..1])?;
        buf.write(format_args!(", {escaper})?"));
        Ok(DisplayWrap::Wrapped)
    }

    fn visit_format_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, "format", node)?;
        if !args.is_empty() {
            if let Expr::StrLit(ref fmt) = *args[0] {
                buf.write("askama::helpers::alloc::format!(");
                self.visit_str_lit(buf, fmt);
                if args.len() > 1 {
                    buf.write(',');
                    self.visit_args(ctx, buf, &args[1..])?;
                }
                buf.write(')');
                return Ok(DisplayWrap::Unwrapped);
            }
        }
        Err(ctx.generate_error(r#"use filter format like `"a={} b={}"|format(a, b)`"#, node))
    }

    fn visit_fmt_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, "fmt", node)?;
        if let [_, arg2] = args {
            if let Expr::StrLit(ref fmt) = **arg2 {
                buf.write("askama::helpers::alloc::format!(");
                self.visit_str_lit(buf, fmt);
                buf.write(',');
                self.visit_args(ctx, buf, &args[..1])?;
                buf.write(')');
                return Ok(DisplayWrap::Unwrapped);
            }
        }
        Err(ctx.generate_error(r#"use filter fmt like `value|fmt("{:?}")`"#, node))
    }

    // Force type coercion on first argument to `join` filter (see #39).
    fn visit_join_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        _node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        buf.write("askama::filters::join((&");
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                buf.write(", &");
            }
            self.visit_expr(ctx, buf, arg)?;
            if i == 0 {
                buf.write(").into_iter()");
            }
        }
        buf.write(")?");
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_center_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_center_truncate_filter(ctx, buf, args, node, "center")
    }

    fn visit_truncate_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_center_truncate_filter(ctx, buf, args, node, "truncate")
    }

    fn visit_center_truncate_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Expr<'a>>],
        node: Span<'_>,
        name: &str,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, name, node)?;
        let [arg, length] = args else {
            return Err(ctx.generate_error(
                format_args!("`{name}` filter needs one argument, the `length`"),
                node,
            ));
        };

        buf.write(format_args!("askama::filters::{name}("));
        self.visit_arg(ctx, buf, arg)?;
        buf.write(
            "\
                ,\
                askama::helpers::core::primitive::usize::try_from(\
                    askama::helpers::get_primitive_value(&(",
        );
        self.visit_arg(ctx, buf, length)?;
        buf.write(
            "\
                    ))\
                ).map_err(|_| askama::Error::Fmt)?\
            )?",
        );
        Ok(DisplayWrap::Unwrapped)
    }
}

fn ensure_filter_has_feature_alloc(
    ctx: &Context<'_>,
    name: &str,
    node: Span<'_>,
) -> Result<(), CompileError> {
    if !cfg!(feature = "alloc") {
        return Err(ctx.generate_error(
            format_args!("the `{name}` filter requires the `alloc` feature to be enabled"),
            node,
        ));
    }
    Ok(())
}

fn ensure_filter_has_feature_std(
    ctx: &Context<'_>,
    name: &str,
    node: Span<'_>,
) -> Result<(), CompileError> {
    if !cfg!(feature = "alloc") {
        return Err(ctx.generate_error(
            format_args!("the `{name}` filter requires the `std` feature to be enabled"),
            node,
        ));
    }
    Ok(())
}

fn ensure_no_generics(
    ctx: &Context<'_>,
    name: &str,
    node: Span<'_>,
    generics: &[WithSpan<'_, TyGenerics<'_>>],
) -> Result<(), CompileError> {
    if !generics.is_empty() {
        return Err(
            ctx.generate_error(format_args!("unexpected generics on filter `{name}`"), node)
        );
    }
    Ok(())
}

fn expr_is_int_lit_plus_minus_one(expr: &WithSpan<'_, Expr<'_>>) -> Option<bool> {
    fn is_signed_singular<T: Eq + Default, E>(
        from_str_radix: impl Fn(&str, u32) -> Result<T, E>,
        value: &str,
        plus_one: T,
        minus_one: T,
    ) -> Option<bool> {
        Some([plus_one, minus_one].contains(&from_str_radix(value, 10).ok()?))
    }

    fn is_unsigned_singular<T: Eq + Default, E>(
        from_str_radix: impl Fn(&str, u32) -> Result<T, E>,
        value: &str,
        plus_one: T,
    ) -> Option<bool> {
        Some(from_str_radix(value, 10).ok()? == plus_one)
    }

    macro_rules! impl_match {
        (
            $kind:ident $value:ident;
            $($svar:ident => $sty:ident),*;
            $($uvar:ident => $uty:ident),*;
        ) => {
            match $kind {
                $(
                    Some(IntKind::$svar) => is_signed_singular($sty::from_str_radix, $value, 1, -1),
                )*
                $(
                    Some(IntKind::$uvar) => is_unsigned_singular($uty::from_str_radix, $value, 1),
                )*
                None => match $value.starts_with('-') {
                    true => is_signed_singular(i128::from_str_radix, $value, 1, -1),
                    false => is_unsigned_singular(u128::from_str_radix, $value, 1),
                },
            }
        };
    }

    let Expr::NumLit(_, Num::Int(value, kind)) = **expr else {
        return None;
    };
    impl_match! {
        kind value;
        I8 => i8,
        I16 => i16,
        I32 => i32,
        I64 => i64,
        I128 => i128,
        Isize => TargetIsize;
        U8 => u8,
        U16 => u16,
        U32 => u32,
        U64 => u64,
        U128 => u128,
        Usize => TargetUsize;
    }
}

// These built-in filters take no arguments, no generics, and are not feature gated.
const BUILTIN_FILTERS: &[&str] = &[];

// These built-in filters take no arguments, no generics, and need `features = ["alloc"]`.
const BUILTIN_FILTERS_ALLOC: &[&str] = &[
    "capitalize",
    "lower",
    "lowercase",
    "title",
    "trim",
    "upper",
    "uppercase",
];

// These built-in filters take no arguments, no generics, and need `features = ["std"]`.
const BUILTIN_FILTERS_STD: &[&str] = &[];
