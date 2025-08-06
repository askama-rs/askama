use std::borrow::Cow;
use std::fmt::{self, Write};
use std::mem::replace;
use std::ptr;
use std::str::FromStr;

use parser::{
    Expr, IntKind, Num, PathComponent, PathOrIdentifier, Span, StrLit, StrPrefix, TyGenerics,
    WithSpan,
};
use proc_macro2::TokenStream;
use syn::Token;

use super::{DisplayWrap, Generator, TargetIsize, TargetUsize};
use crate::heritage::Context;
use crate::integration::Buffer;
use crate::{CompileError, MsgValidEscapers, field_new, fmt_left, fmt_right};

impl<'a> Generator<'a, '_> {
    pub(super) fn visit_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &PathOrIdentifier<'a>,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let (name, generics): (&str, &[WithSpan<'_, TyGenerics<'_>>]) = match name {
            PathOrIdentifier::Path(path) => match path.as_slice() {
                [arg] => (arg.name, arg.generics.as_slice()),
                _ => return self.visit_custom_filter_with_path(ctx, buf, path, args, node),
            },
            PathOrIdentifier::Identifier(name) => (*name, &[]),
        };
        let filter = match name {
            "assigned_or" => Self::visit_assigned_or,
            "center" => Self::visit_center_filter,
            "default" => Self::visit_default_filter,
            "defined_or" => Self::visit_defined_or,
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
            "reject" => Self::visit_reject_filter,
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

    fn visit_custom_filter_with_path(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        path: &[WithSpan<'a, PathComponent<'a>>],
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_no_named_arguments(ctx, path.last().unwrap().name, args, node)?;
        self.visit_path(ctx, buf, path);
        let span = ctx.span_for_node(node);

        let mut tmp = Buffer::new();
        tmp.write_tokens(self.visit_arg(ctx, &args[0], ctx.span_for_node(args[0].span()))?);
        let var_values = crate::var_values();
        quote_into!(&mut tmp, span, { ,#var_values });
        if args.len() > 1 {
            tmp.write_token(Token![,], span);
            self.visit_args(ctx, &mut tmp, &args[1..])?;
        }
        let tmp = tmp.into_token_stream();
        buf.write_tokens(spanned!(span=> (#tmp)?));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_custom_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &'a str,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        _: &[WithSpan<'a, TyGenerics<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_custom_filter_with_path(
            ctx,
            buf,
            &[
                WithSpan::new_without_span(PathComponent::new_with_name("filters")),
                WithSpan::new_without_span(PathComponent::new_with_name(name)),
            ],
            args,
            node,
        )
    }

    fn visit_builtin_filter_alloc(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &'a str,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
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
        name: &'a str,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
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
        name: &'a str,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        generics: &[WithSpan<'a, TyGenerics<'a>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_no_generics(ctx, name, node, generics)?;
        let span = ctx.span_for_node(node);

        let arg = no_arguments(ctx, name, args)?;
        let name = field_new(name, span);
        quote_into!(buf, span, { askama::filters::#name });
        self.visit_call_generics(ctx, buf, generics);
        let arg = self.visit_arg(ctx, arg, span)?;
        buf.write_tokens(spanned!(span=> (#arg)?));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_urlencode_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_urlencode_filter_inner(ctx, buf, "urlencode", args, node)
    }

    fn visit_urlencode_strict_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_urlencode_filter_inner(ctx, buf, "urlencode_strict", args, node)
    }

    fn visit_urlencode_filter_inner(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        if cfg!(not(feature = "urlencode")) {
            return Err(ctx.generate_error(
                format_args!("the `{name}` filter requires the `urlencode` feature to be enabled"),
                node,
            ));
        }

        let arg = no_arguments(ctx, name, args)?;
        let span = ctx.span_for_node(node);
        let arg = self.visit_arg(ctx, arg, span)?;

        let name = quote::format_ident!("{name}");
        // Both filters return HTML-safe strings.
        buf.write_tokens(
            spanned!(span=> askama::filters::HtmlSafeOutput(askama::filters::#name(#arg)?)),
        );
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_wordcount_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, "wordcount", node)?;

        let arg = no_arguments(ctx, "wordcount", args)?;
        let span = ctx.span_for_node(node);
        let arg = self.visit_arg(ctx, arg, span)?;

        let var_values = crate::var_values();
        buf.write_tokens(spanned!(span=> match askama::filters::wordcount(&(#arg)) {
            expr0 => {
                (&&&askama::filters::Writable(&expr0)).
                    askama_write(&mut askama::helpers::Empty, #var_values)?;
                expr0.into_count()
            }
        }));

        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_humansize(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let arg = no_arguments(ctx, "humansize", args)?;
        let span = ctx.span_for_node(node);
        let arg = self.visit_arg(ctx, arg, span)?;

        // All filters return numbers, and any default formatted number is HTML safe.
        buf.write_tokens(
            spanned!(span=> askama::filters::HtmlSafeOutput(
                askama::filters::filesizeformat(
                    askama::helpers::get_primitive_value(&(#arg)) as askama::helpers::core::primitive::f32
                )?
            )),
        );
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_reject_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "filter",
                default_value: None,
            },
        ];
        let [input, filter] = collect_filter_args(ctx, "reject", node, args, ARGUMENTS)?;
        let span = ctx.span_for_node(node);

        let mut tmp = Buffer::new();
        if matches!(&***filter, Expr::Path(_)) {
            self.visit_loop_iter(ctx, &mut tmp, input)?;
            let arg = self.visit_arg(ctx, filter, ctx.span_for_node(filter.span()))?;

            let tmp = tmp.into_token_stream();
            buf.write_tokens(spanned!(span=> askama::filters::reject_with(#tmp, #arg)?));
        } else {
            self.visit_loop_iter(ctx, &mut tmp, input)?;
            let arg = self.visit_arg(ctx, filter, ctx.span_for_node(filter.span()))?;

            let tmp = tmp.into_token_stream();
            buf.write_tokens(spanned!(span=> askama::filters::reject(
                #tmp,
                // coerce [T, &T, &&T...] to &T
                (&&&(#arg))
                as &_)?
            ));
        }

        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_pluralize_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const SINGULAR: &WithSpan<'_, &Expr<'_>> =
            &WithSpan::new_without_span(&Expr::StrLit(StrLit {
                prefix: None,
                content: "",
                contains_null: false,
                contains_unicode_character: false,
                contains_unicode_escape: false,
                contains_high_ascii: false,
            }));
        const PLURAL: &WithSpan<'_, &Expr<'_>> =
            &WithSpan::new_without_span(&Expr::StrLit(StrLit {
                prefix: None,
                content: "s",
                contains_null: false,
                contains_unicode_character: false,
                contains_unicode_escape: false,
                contains_high_ascii: false,
            }));
        const ARGUMENTS: &[&FilterArgument; 3] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "singular",
                default_value: Some(SINGULAR),
            },
            &FilterArgument {
                name: "plural",
                default_value: Some(PLURAL),
            },
        ];

        let [count, sg, pl] = collect_filter_args(ctx, "pluralize", node, args, ARGUMENTS)?;

        if let Some(is_singular) = expr_is_int_lit_plus_minus_one(count) {
            let value = if is_singular { sg } else { pl };
            self.visit_auto_escaped_arg(ctx, buf, value)?;
        } else {
            let span = ctx.span_for_node(node);
            let arg = self.visit_arg(ctx, count, ctx.span_for_node(count.span()))?;
            let mut sg_buf = Buffer::new();
            self.visit_auto_escaped_arg(ctx, &mut sg_buf, sg)?;
            let mut pl_buf = Buffer::new();
            self.visit_auto_escaped_arg(ctx, &mut pl_buf, pl)?;
            let sg = sg_buf.into_token_stream();
            let pl = pl_buf.into_token_stream();
            quote_into!(buf, span, { askama::filters::pluralize(#arg, #sg, #pl)? });
        }
        Ok(DisplayWrap::Wrapped)
    }

    fn visit_paragraphbreaks_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_linebreaks_filters(ctx, buf, "paragraphbreaks", args, node)
    }

    fn visit_linebreaksbr_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_linebreaks_filters(ctx, buf, "linebreaksbr", args, node)
    }

    fn visit_linebreaks_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_linebreaks_filters(ctx, buf, "linebreaks", args, node)
    }

    fn visit_linebreaks_filters(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        name: &str,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let arg = no_arguments(ctx, name, args)?;
        let arg = self.visit_arg(ctx, arg, ctx.span_for_node(arg.span()))?;
        let span = ctx.span_for_node(node);

        let name = quote::format_ident!("{name}");
        buf.write_tokens(spanned!(span=> askama::filters::#name(
            &(&&askama::filters::AutoEscaper::new(&(
                #arg
            // The input is always HTML escaped, regardless of the selected escaper:
            ), askama::filters::Html)).askama_auto_escape()?)?
        ));
        // The output is marked as HTML safe, not safe in all contexts:
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_ref_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let arg = no_arguments(ctx, "ref", args)?;
        buf.write_token(Token![&], ctx.span_for_node(node));
        self.visit_expr(ctx, buf, arg)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_deref_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let arg = no_arguments(ctx, "deref", args)?;
        buf.write_token(Token![*], ctx.span_for_node(node));
        self.visit_expr(ctx, buf, arg)?;
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_json_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "indent",
                default_value: Some(ARGUMENT_PLACEHOLDER),
            },
        ];

        if cfg!(not(feature = "serde_json")) {
            return Err(ctx.generate_error(
                "the `json` filter requires the `serde_json` feature to be enabled",
                node,
            ));
        }

        let [value, indent] = collect_filter_args(ctx, "json", node, args, ARGUMENTS)?;
        let span = ctx.span_for_node(node);
        if is_argument_placeholder(indent) {
            let arg = self.visit_arg(ctx, value, ctx.span_for_node(value.span()))?;
            buf.write_tokens(spanned!(span=> askama::filters::json(#arg)?));
        } else {
            let value = self.visit_arg(ctx, value, ctx.span_for_node(value.span()))?;
            let indent = self.visit_arg(ctx, indent, ctx.span_for_node(indent.span()))?;
            buf.write_tokens(spanned!(span=> askama::filters::json_pretty(#value, #indent)?));
        }
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_indent_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 4] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "width",
                default_value: None,
            },
            &FilterArgument {
                name: "first",
                default_value: Some(FALSE),
            },
            &FilterArgument {
                name: "blank",
                default_value: Some(FALSE),
            },
        ];

        ensure_filter_has_feature_alloc(ctx, "indent", node)?;
        let [source, indent, first, blank] =
            collect_filter_args(ctx, "indent", node, args, ARGUMENTS)?;
        let source = self.visit_arg(ctx, source, ctx.span_for_node(source.span()))?;
        let indent = self.visit_arg(ctx, indent, ctx.span_for_node(indent.span()))?;
        let first = self.visit_arg(ctx, first, ctx.span_for_node(first.span()))?;
        let blank = self.visit_arg(ctx, blank, ctx.span_for_node(blank.span()))?;

        let span = ctx.span_for_node(node);
        buf.write_tokens(spanned!(span=>
            askama::filters::indent(
                #source,
                #indent,
                askama::helpers::as_bool(&(#first)),
                askama::helpers::as_bool(&(#blank))
            )?
        ));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_safe_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        let arg = no_arguments(ctx, "safe", args)?;
        let arg = self.visit_arg(ctx, arg, ctx.span_for_node(node))?;

        let span = ctx.span_for_node(node);
        let escaper = TokenStream::from_str(self.input.escaper).unwrap();
        buf.write_tokens(spanned!(span=> askama::filters::safe(#arg, #escaper)?));
        Ok(DisplayWrap::Wrapped)
    }

    fn visit_escape_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "escaper",
                default_value: Some(ARGUMENT_PLACEHOLDER),
            },
        ];

        let [source, opt_escaper] = collect_filter_args(ctx, "escape", node, args, ARGUMENTS)?;
        let opt_escaper = if !is_argument_placeholder(opt_escaper) {
            let Expr::StrLit(StrLit {
                prefix, content, ..
            }) = ***opt_escaper
            else {
                return Err(ctx.generate_error("invalid escaper type for escape filter", node));
            };
            if let Some(prefix) = prefix {
                let kind = if prefix == StrPrefix::Binary {
                    "slice"
                } else {
                    "CStr"
                };
                return Err(ctx.generate_error(
                    format_args!(
                        "invalid escaper `b{content:?}`. Expected a string, found a {kind}"
                    ),
                    opt_escaper.span(),
                ));
            }
            Some(content)
        } else {
            None
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
                            "invalid escaper `{}` for `escape` filter. {}",
                            name.escape_debug(),
                            MsgValidEscapers(&self.input.config.escapers),
                        ),
                        node,
                    )
                })?,
            None => self.input.escaper,
        };
        let source = self.visit_arg(ctx, source, ctx.span_for_node(source.span()))?;
        let span = ctx.span_for_node(node);
        let escaper = TokenStream::from_str(escaper).unwrap();
        buf.write_tokens(spanned!(span=> askama::filters::escape(#source, #escaper)?));
        Ok(DisplayWrap::Wrapped)
    }

    fn visit_format_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        ensure_filter_has_feature_alloc(ctx, "format", node)?;
        ensure_no_named_arguments(ctx, "format", args, node)?;
        if let [head, tail @ ..] = args
            && let Expr::StrLit(ref fmt) = ***head
        {
            let span = ctx.span_for_node(node);
            let mut filter = Buffer::new();
            self.visit_str_lit(&mut filter, fmt, span);
            if !tail.is_empty() {
                filter.write_token(Token![,], ctx.span_for_node(node));
                self.visit_args(ctx, &mut filter, tail)?;
            }
            let filter = filter.into_token_stream();
            buf.write_tokens(spanned!(span=> askama::helpers::alloc::format!(#filter)));
            return Ok(DisplayWrap::Unwrapped);
        }
        Err(ctx.generate_error(
            r#"use `format` filter like `"a={} b={}"|format(a, b)`"#,
            node,
        ))
    }

    fn visit_fmt_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "format",
                default_value: None,
            },
        ];

        ensure_filter_has_feature_alloc(ctx, "fmt", node)?;
        let [source, fmt] = collect_filter_args(ctx, "fmt", node, args, ARGUMENTS)?;
        let Expr::StrLit(ref fmt) = ***fmt else {
            return Err(ctx.generate_error(r#"use `fmt` filter like `value|fmt("{:?}")`"#, node));
        };
        let span = ctx.span_for_node(node);
        let mut filter = Buffer::new();
        self.visit_str_lit(&mut filter, fmt, span);
        let source = self.visit_arg(ctx, source, ctx.span_for_node(source.span()))?;
        let filter = filter.into_token_stream();
        buf.write_tokens(spanned!(span=>
            askama::helpers::alloc::format!(#filter, #source)
        ));
        Ok(DisplayWrap::Unwrapped)
    }

    // Force type coercion on first argument to `join` filter (see #39).
    fn visit_join_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "separator",
                default_value: None,
            },
        ];

        let [iterable, separator] = collect_filter_args(ctx, "join", node, args, ARGUMENTS)?;
        let iterable = self.visit_arg(ctx, iterable, ctx.span_for_node(iterable.span()))?;
        let separator = self.visit_arg(ctx, separator, ctx.span_for_node(separator.span()))?;
        let span = ctx.span_for_node(node);
        buf.write_tokens(spanned!(span=> askama::filters::join(
                (&(#iterable)).into_iter(),
                #separator
            )?));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_center_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_center_truncate_filter(ctx, buf, args, node, "center")
    }

    fn visit_truncate_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        self.visit_center_truncate_filter(ctx, buf, args, node, "truncate")
    }

    fn visit_center_truncate_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
        name: &str,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "length",
                default_value: None,
            },
        ];

        ensure_filter_has_feature_alloc(ctx, name, node)?;
        let [arg, length] = collect_filter_args(ctx, name, node, args, ARGUMENTS)?;
        let arg = self.visit_arg(ctx, arg, ctx.span_for_node(arg.span()))?;
        let length = self.visit_arg(ctx, length, ctx.span_for_node(length.span()))?;
        let span = ctx.span_for_node(node);
        let name = quote::format_ident!("{name}");
        buf.write_tokens(spanned!(span=> askama::filters::#name(
                #arg,
                askama::helpers::core::primitive::usize::try_from(
                    askama::helpers::get_primitive_value(&(#length))
                ).map_err(|_| askama::Error::Fmt)?
            )?));
        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_default_filter(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 3] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "default_value",
                default_value: None,
            },
            &FilterArgument {
                name: "boolean",
                default_value: Some(FALSE),
            },
        ];

        let [value, fallback, is_assigned] =
            collect_filter_args(ctx, "default", node, args, ARGUMENTS)?;
        let Expr::BoolLit(is_assigned) = ***is_assigned else {
            return Err(ctx.generate_error(
                "the `default` filter takes a boolean literal as its optional second argument",
                is_assigned.span(),
            ));
        };
        if is_assigned {
            self.visit_assigned_or_impl(ctx, buf, node, value, fallback)
        } else {
            self.visit_defined_or_impl(ctx, buf, node, value, fallback, "default")
        }
    }

    fn visit_assigned_or(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "fallback",
                default_value: None,
            },
        ];

        let [value, fallback] = collect_filter_args(ctx, "assigned_or", node, args, ARGUMENTS)?;
        self.visit_assigned_or_impl(ctx, buf, node, value, fallback)
    }

    fn visit_assigned_or_impl(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        node: Span<'_>,
        value: &WithSpan<'a, Box<Expr<'a>>>,
        fallback: &WithSpan<'a, Box<Expr<'a>>>,
    ) -> Result<DisplayWrap, CompileError> {
        if let Expr::Var(var_name) = ***value
            && !self.is_var_assigned(var_name)
        {
            self.visit_expr(ctx, buf, fallback)?;
            return Ok(DisplayWrap::Unwrapped);
        }

        let mut value_buf = Buffer::new();
        value_buf.write_tokens(self.visit_arg(ctx, value, ctx.span_for_node(value.span()))?);
        let value_buf = value_buf.into_token_stream();
        let mut fallback_buf = Buffer::new();
        fallback_buf.write_tokens(self.visit_arg(
            ctx,
            fallback,
            ctx.span_for_node(fallback.span()),
        )?);
        let fallback_buf = fallback_buf.into_token_stream();

        let span = ctx.span_for_node(node);
        buf.write_tokens(
            spanned!(span=> askama::filters::assigned_or(&(#value_buf), #fallback_buf)?),
        );

        Ok(DisplayWrap::Unwrapped)
    }

    fn visit_defined_or(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        args: &[WithSpan<'a, Box<Expr<'a>>>],
        node: Span<'_>,
    ) -> Result<DisplayWrap, CompileError> {
        const ARGUMENTS: &[&FilterArgument; 2] = &[
            FILTER_SOURCE,
            &FilterArgument {
                name: "fallback",
                default_value: None,
            },
        ];

        let [value, fallback] = collect_filter_args(ctx, "defined_or", node, args, ARGUMENTS)?;
        self.visit_defined_or_impl(ctx, buf, node, value, fallback, "defined_or")
    }

    fn visit_defined_or_impl(
        &mut self,
        ctx: &Context<'_>,
        buf: &mut Buffer,
        node: Span<'_>,
        value: &WithSpan<'a, Box<Expr<'a>>>,
        fallback: &WithSpan<'a, Box<Expr<'a>>>,
        name: &str,
    ) -> Result<DisplayWrap, CompileError> {
        let Expr::Var(var_name) = ***value else {
            return Err(ctx.generate_error(
                format!("the `{name}` filter requires a variable name on its left-hand side"),
                node,
            ));
        };

        let expr = match self.is_var_assigned(var_name) {
            true => value,
            false => fallback,
        };
        self.visit_expr(ctx, buf, expr)?;

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

const FALSE: &WithSpan<'static, &Expr<'static>> =
    &WithSpan::new_without_span(&Expr::BoolLit(false));

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

fn expr_is_int_lit_plus_minus_one(expr: &WithSpan<'_, Box<Expr<'_>>>) -> Option<bool> {
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

    let Expr::NumLit(_, Num::Int(value, kind)) = ***expr else {
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

#[repr(C)] // rationale: needs to have the same layout as `StaticBoxFilterArgument`
struct FilterArgument {
    name: &'static str,
    /// If set to `None`, then a value is needed.
    /// If set to `Some(ARGUMENT_PLACEHOLDER)`, then no value has to be assigned.
    /// If set to `Some(&WithSpan...)`, then this value will be used if no argument was supplied.
    default_value: Option<&'static WithSpan<'static, &'static Expr<'static>>>,
}

#[repr(C)] // rationale: needs to have the same layout as `FilterArgument`
struct StaticBoxFilterArgument {
    name: &'static str,
    default_value: Option<&'static WithSpan<'static, Box<Expr<'static>>>>,
}

/// Must be the first entry to `collect_filter_args()`'s argument `filter_args`.
const FILTER_SOURCE: &FilterArgument = &FilterArgument {
    name: "",
    default_value: None,
};

const ARGUMENT_PLACEHOLDER: &WithSpan<'_, &Expr<'_>> =
    &WithSpan::new_without_span(&Expr::ArgumentPlaceholder);

#[inline]
fn is_argument_placeholder(arg: &WithSpan<'_, Box<Expr<'_>>>) -> bool {
    matches!(***arg, Expr::ArgumentPlaceholder)
}

fn no_arguments<'a, 'b>(
    ctx: &Context<'_>,
    name: &str,
    args: &'b [WithSpan<'a, Box<Expr<'a>>>],
) -> Result<&'b WithSpan<'a, Box<Expr<'a>>>, CompileError> {
    match args {
        [arg] => Ok(arg),
        [_, arg, ..] => Err(ctx.generate_error(
            format_args!("`{name}` filter does not have any arguments"),
            arg.span(),
        )),
        _ => unreachable!(),
    }
}

#[inline]
fn collect_filter_args<'a, 'b, const N: usize>(
    ctx: &Context<'_>,
    name: &str,
    node: Span<'_>,
    input_args: &'b [WithSpan<'a, Box<Expr<'a>>>],
    filter_args: &'static [&'static FilterArgument; N],
) -> Result<[&'b WithSpan<'a, Box<Expr<'a>>>; N], CompileError> {
    // The transmutations are needed, because you cannot build a `Box` in a `const` context,
    // not even `&Box`.

    // Cannot use `transmute() to transmute dependently sized types: `[_; N]`
    // SAFETY: `&WithSpan<'_, &Expr<'_>>` has the same layout as `&WithSpan<'_, Box<Expr<'_>>>`.
    //         `WithSpan` is `repr(C)`, and `Box<T>` has the same layout as `&T`.
    //         Since we work with `&WithSpan<'_, Box<_>>`, there is no need to use `ManuallyDrop`.
    let mut collected_args: [&WithSpan<'_, Box<Expr<'_>>>; N] = unsafe {
        let collected_args: [&WithSpan<'_, &Expr<'_>>; N] = [ARGUMENT_PLACEHOLDER; N];
        ptr::read(ptr::addr_of!(collected_args).cast())
    };

    // SAFETY: `StaticBoxFilterArgument` has the same layout as `FilterArgument`.
    //         It contains a `&WithSpan<'_, Box<Expr<'_>>>` instead of `&WithSpan<'_, &Expr<'_>>`.
    //         See the comments for `collected_args` for further explanations.
    let filter_args: &[&StaticBoxFilterArgument; N] = unsafe { std::mem::transmute(filter_args) };

    // rationale: less code duplication by implementing the bulk of the function non-generic
    collect_filter_args_inner(
        ctx,
        name,
        node,
        input_args,
        filter_args,
        &mut collected_args,
    )?;
    Ok(collected_args)
}

fn collect_filter_args_inner<'a, 'b>(
    ctx: &Context<'_>,
    name: &str,
    node: Span<'_>,
    input_args: &'b [WithSpan<'a, Box<Expr<'a>>>],
    filter_args: &'static [&'static StaticBoxFilterArgument],
    collected_args: &mut [&'b WithSpan<'a, Box<Expr<'a>>>],
) -> Result<(), CompileError> {
    // invariant: the parser ensures that named arguments come after positional arguments
    let mut arg_idx = 0;
    for arg in input_args {
        let (idx, value) = if let Expr::NamedArgument(arg_name, ref value) = ***arg {
            let Some(idx) = filter_args
                .iter()
                .enumerate()
                .find_map(|(idx, arg)| (arg.name == arg_name).then_some(idx))
            else {
                return Err(ctx.generate_error(
                    match filter_args.len() {
                        1 => fmt_left!("`{name}` filter does not have any arguments"),
                        _ => fmt_right!(
                            "`{name}` filter does not have an argument `{}`{}",
                            arg_name.escape_debug(),
                            ItsArgumentsAre(filter_args),
                        ),
                    },
                    arg.span(),
                ));
            };
            (idx, value)
        } else {
            let idx = arg_idx;
            arg_idx += 1;
            (idx, arg)
        };

        let Some(collected_arg) = collected_args.get_mut(idx) else {
            return Err(ctx.generate_error(
                format_args!(
                    "`{name}` filter accepts at most {} argument{}{}",
                    filter_args.len() - 1,
                    if filter_args.len() != 2 { "s" } else { "" },
                    ItsArgumentsAre(filter_args),
                ),
                arg.span(),
            ));
        };
        if !is_argument_placeholder(replace(collected_arg, value)) {
            return Err(ctx.generate_error(
                format_args!(
                    "`{}` argument to `{}` filter was already set{}",
                    filter_args[idx].name.escape_debug(),
                    name.escape_debug(),
                    ItsArgumentsAre(filter_args),
                ),
                arg.span(),
            ));
        }
    }

    for (&arg, collected) in filter_args.iter().zip(collected_args) {
        if !is_argument_placeholder(collected) {
            continue;
        } else if let Some(default) = arg.default_value {
            *collected = default;
        } else {
            return Err(ctx.generate_error(
                format_args!(
                    "`{}` argument is missing when calling `{name}` filter{}",
                    arg.name.escape_debug(),
                    ItsArgumentsAre(filter_args),
                ),
                node,
            ));
        }
    }

    Ok(())
}

struct ItsArgumentsAre(&'static [&'static StaticBoxFilterArgument]);

impl fmt::Display for ItsArgumentsAre {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("; its arguments are: (")?;
        for (idx, arg) in self.0.iter().enumerate() {
            match idx {
                0 => continue,
                1 => {}
                _ => f.write_str(", ")?,
            }
            if arg.default_value.is_some() {
                write!(f, "[{}]", arg.name)?;
            } else {
                f.write_str(arg.name)?;
            }
        }
        f.write_char(')')
    }
}

fn ensure_no_named_arguments(
    ctx: &Context<'_>,
    name: &str,
    args: &[WithSpan<'_, Box<Expr<'_>>>],
    node: Span<'_>,
) -> Result<(), CompileError> {
    for arg in args {
        if let Expr::NamedArgument(..) = &***arg {
            return Err(ctx.generate_error(
                format_args!(
                    "`{}` filter cannot accept named arguments",
                    name.escape_debug()
                ),
                node,
            ));
        }
    }
    Ok(())
}

// These built-in filters take no arguments, no generics, and are not feature gated.
const BUILTIN_FILTERS: &[&str] = &[];

// These built-in filters take no arguments, no generics, and need `features = ["alloc"]`.
const BUILTIN_FILTERS_ALLOC: &[&str] = &[
    "capitalize",
    "lower",
    "lowercase",
    "title",
    "titlecase",
    "trim",
    "upper",
    "uppercase",
];

// These built-in filters take no arguments, no generics, and need `features = ["std"]`.
const BUILTIN_FILTERS_STD: &[&str] = &["unique"];
