use std::fmt::Display;
use std::mem::take;
use std::str::FromStr;

use parser::PathComponent;
use proc_macro2::{Literal, Span, TokenStream, TokenTree};
use quote::{ToTokens, quote_spanned};
use syn::spanned::Spanned;
use syn::{
    Data, DeriveInput, Fields, GenericParam, Generics, Ident, Lifetime, LifetimeParam, LitStr,
    Token, Type, Variant, parse_quote,
};

use crate::generator::TmplKind;
use crate::input::{PartialTemplateArgs, TemplateArgs};
use crate::{CompileError, Context, Print, build_template_item, field_new, quote_into};

/// Implement every integration for the given item
pub(crate) fn impl_everything(ast: &DeriveInput, buf: &mut Buffer) {
    impl_display(ast, buf);
    impl_fast_writable(ast, buf);
}

/// Writes header for the `impl` for `TraitFromPathName` or `Template` for the given item
pub(crate) fn write_header(ast: &DeriveInput, buf: &mut Buffer, target: TokenStream) {
    let (impl_generics, orig_ty_generics, where_clause) = ast.generics.split_for_impl();

    let ident = &ast.ident;
    let span = Span::call_site();
    quote_into!(buf, span, {
        #[automatically_derived]
        impl #impl_generics #target for #ident #orig_ty_generics #where_clause
    });
}

/// Implement `Display` for the given item.
fn impl_display(ast: &DeriveInput, buf: &mut Buffer) {
    let ident = &ast.ident;
    let span = Span::call_site();
    let msg =
        // format!(" Implement the [`Display`][core::fmt::Display] trait for [`{ident}`]");
        format!(" Implement the [`format!()`][askama::helpers::std::format] trait for [`{ident}`]");
    quote_into!(buf, span, {
        #[doc = #msg]
        ///
        /// Please be aware of the rendering performance notice in the [`Template`][askama::Template] trait.
    });
    write_header(
        ast,
        buf,
        quote_spanned!(span => askama::helpers::core::fmt::Display),
    );
    quote_into!(buf, span, {
        {
            #[inline]
            fn fmt(
                &self,
                f: &mut askama::helpers::core::fmt::Formatter<'_>,
            ) -> askama::helpers::core::fmt::Result {
                askama::Template::render_into(self, f)
                    .map_err(|_| askama::helpers::core::fmt::Error)
            }
        }
    });
}

/// Implement `FastWritable` for the given item.
fn impl_fast_writable(ast: &DeriveInput, buf: &mut Buffer) {
    let span = Span::call_site();
    write_header(ast, buf, quote_spanned!(span => askama::FastWritable));
    quote_into!(buf, span, {
        {
            #[inline]
            fn write_into<AskamaW>(
                &self,
                dest: &mut AskamaW,
                values: &dyn askama::Values,
            ) -> askama::Result<()>
            where
                AskamaW: askama::helpers::core::fmt::Write + ?askama::helpers::core::marker::Sized,
            {
                askama::Template::render_into_with_values(self, dest, values)
            }
        }
    });
}

#[derive(Debug)]
pub(crate) struct Buffer {
    // The buffer to generate the code into
    buf: TokenStream,
    discard: bool,
    string_literals: Vec<(String, proc_macro2::Span)>,
}

impl Display for Buffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.buf.to_string().as_str())
    }
}

impl ToTokens for Buffer {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.buf.to_tokens(tokens);
    }

    #[inline]
    fn to_token_stream(&self) -> TokenStream {
        self.buf.clone()
    }

    #[inline]
    fn into_token_stream(self) -> TokenStream {
        self.buf
    }
}

impl IntoIterator for Buffer {
    type Item = <TokenStream as IntoIterator>::Item;
    type IntoIter = <TokenStream as IntoIterator>::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.buf.into_iter()
    }
}

impl Buffer {
    pub(crate) fn new() -> Self {
        Self {
            buf: TokenStream::new(),
            discard: false,
            string_literals: Vec::new(),
        }
    }

    fn handle_str_lit(&mut self) {
        let Some((literal, span)) = take(&mut self.string_literals).into_iter().reduce(
            |(mut acc_lit, acc_span), (literal, span)| {
                acc_lit.push_str(&literal);
                (acc_lit, acc_span.join(span).unwrap_or(acc_span))
            },
        ) else {
            return;
        };

        let mut literal: Literal = format!(r#""{literal}""#).parse().unwrap();
        literal.set_span(span);
        let askama_writer = crate::var_writer();
        self.buf.extend(quote_spanned! {
            span =>
            #askama_writer.write_str(#literal)?;
        });
    }

    pub(crate) fn write_str_lit(&mut self, literal: String, span: proc_macro2::Span) {
        if self.discard || literal.is_empty() {
            return;
        }
        self.string_literals.push((literal, span));
    }

    #[inline]
    pub(crate) fn into_token_stream(mut self) -> TokenStream {
        self.handle_str_lit();
        self.buf
    }

    #[inline]
    pub(crate) fn is_discard(&self) -> bool {
        self.discard
    }

    #[inline]
    pub(crate) fn set_discard(&mut self, discard: bool) {
        self.discard = discard;
    }

    #[inline]
    pub(crate) fn write_tokens(&mut self, src: impl IntoIterator<Item = TokenTree>) {
        if self.discard {
            return;
        }
        self.handle_str_lit();
        self.buf.extend(src);
    }

    pub(crate) fn write_token<F, T>(&mut self, token: F, span: proc_macro2::Span)
    where
        F: Fn(proc_macro2::Span) -> T,
        T: syn::token::Token + ToTokens,
    {
        if self.discard {
            return;
        }
        self.handle_str_lit();
        token(span).to_tokens(&mut self.buf);
    }

    pub(crate) fn write_literal(&mut self, repr: &str, span: proc_macro2::Span) {
        if self.discard {
            return;
        }
        self.handle_str_lit();
        self._write_literal_repr(repr, span);
    }

    fn _write_literal_repr(&mut self, repr: &str, span: proc_macro2::Span) {
        let mut literal: Literal = repr.parse().unwrap();
        literal.set_span(span);
        literal.to_tokens(&mut self.buf);
    }

    pub(crate) fn write_field(&mut self, name: &str, span: proc_macro2::Span) {
        if self.discard {
            return;
        }
        self.handle_str_lit();
        self.buf.extend(field_new(name, span));
    }

    pub(crate) fn write_separated_path(&mut self, ctx: &Context<'_>, path: &[PathComponent<'_>]) {
        if self.discard {
            return;
        }

        self.handle_str_lit();
        for (idx, item) in path.iter().enumerate() {
            let span = ctx.span_for_node(item.name.span());
            if idx > 0 {
                Token![::](span).to_tokens(&mut self.buf);
            }
            if !item.name.is_empty() {
                Ident::new(*item.name, span).to_tokens(&mut self.buf);
            }
        }
    }

    pub(crate) fn write_escaped_str(&mut self, s: &str, span: proc_macro2::Span) {
        if self.discard {
            return;
        }
        self.handle_str_lit();
        LitStr::new(s, span).to_tokens(&mut self.buf);
    }

    pub(crate) fn clear(&mut self) {
        self.string_literals.clear();
        self.buf = TokenStream::new();
    }

    pub(crate) fn write_buf(
        &mut self,
        Buffer {
            buf,
            string_literals,
            ..
        }: Buffer,
    ) {
        if self.discard {
            return;
        }
        self.handle_str_lit();
        self.buf.extend(buf);
        self.string_literals.extend(string_literals);
    }
}

/// Similar to `write!(dest, "{src:?}")`, but only escapes the strictly needed characters,
/// and without the surrounding `"…"` quotation marks.
pub(crate) fn string_escape(dest: &mut String, src: &str) {
    // SAFETY: we will only push valid str slices
    let dest = unsafe { dest.as_mut_vec() };
    let src = src.as_bytes();
    let mut last = 0;

    // According to <https://doc.rust-lang.org/reference/tokens.html#string-literals>, every
    // character is valid except `" \ IsolatedCR`. We don't test if the `\r` is isolated or not,
    // but always escape it.
    for x in memchr::memchr3_iter(b'\\', b'"', b'\r', src) {
        dest.extend(&src[last..x]);
        dest.extend(match src[x] {
            b'\\' => br"\\",
            b'\"' => br#"\""#,
            _ => br"\r",
        });
        last = x + 1;
    }
    dest.extend(&src[last..]);
}

// FIXME: Add span
pub(crate) fn build_template_enum(
    buf: &mut Buffer,
    enum_ast: &DeriveInput,
    mut enum_args: Option<PartialTemplateArgs>,
    vars_args: Vec<Option<PartialTemplateArgs>>,
    has_default_impl: bool,
) -> Result<usize, CompileError> {
    let Data::Enum(enum_data) = &enum_ast.data else {
        unreachable!();
    };
    let span = enum_ast.span();

    impl_everything(enum_ast, buf);

    let enum_id = &enum_ast.ident;
    let enum_span = enum_id.span();
    let lifetime = Lifetime::new(&format!("'__Askama_{enum_id}"), enum_span);

    let mut generics = enum_ast.generics.clone();
    if generics.lt_token.is_none() {
        generics.lt_token = Some(Token![<](enum_span));
    }
    if generics.gt_token.is_none() {
        generics.gt_token = Some(Token![>](enum_span));
    }
    generics
        .params
        .insert(0, GenericParam::Lifetime(LifetimeParam::new(lifetime)));

    let mut biggest_size_hint = 0;
    let mut render_into_arms = TokenStream::new();
    let mut size_hint_arms = TokenStream::new();
    for (var, var_args) in enum_data.variants.iter().zip(vars_args) {
        let Some(mut var_args) = var_args else {
            continue;
        };

        let (var_ast, deref_impl) = type_for_enum_variant(enum_ast, &generics, var);
        quote_into!(buf, span, { #var_ast #deref_impl });

        // not inherited: template, meta_docs, block, print
        if let Some(enum_args) = &mut enum_args {
            set_default(&mut var_args, enum_args, |v| &mut v.source);
            set_default(&mut var_args, enum_args, |v| &mut v.escape);
            set_default(&mut var_args, enum_args, |v| &mut v.ext);
            set_default(&mut var_args, enum_args, |v| &mut v.syntax);
            set_default(&mut var_args, enum_args, |v| &mut v.config);
            set_default(&mut var_args, enum_args, |v| &mut v.whitespace);
        }
        let size_hint = biggest_size_hint.max(build_template_item(
            buf,
            &var_ast,
            Some(enum_ast),
            &TemplateArgs::from_partial(&var_ast, Some(var_args))?,
            TmplKind::Variant,
        )?);
        biggest_size_hint = biggest_size_hint.max(size_hint);

        variant_as_arm(
            &var_ast,
            var,
            size_hint,
            &mut render_into_arms,
            &mut size_hint_arms,
        );
    }
    let print_code = enum_args.as_ref().is_some_and(|args| {
        args.print
            .is_some_and(|print| print == Print::Code || print == Print::All)
    });

    if has_default_impl {
        let size_hint = build_template_item(
            buf,
            enum_ast,
            None,
            &TemplateArgs::from_partial(enum_ast, enum_args)?,
            TmplKind::Variant,
        )?;
        biggest_size_hint = biggest_size_hint.max(size_hint);

        let var_arg = crate::var_arg();
        let var_writer = crate::var_writer();
        let var_values = crate::var_values();
        render_into_arms.extend(quote_spanned! {
            span =>
            ref #var_arg => {
                <_ as askama::helpers::EnumVariantTemplate>::render_into_with_values(
                    #var_arg,
                    #var_writer,
                    #var_values,
                )
            }
        });
        size_hint_arms.extend(quote_spanned! {
            span =>
            _ => {
                #size_hint
            }
        });
    }

    let mut methods = TokenStream::new();
    let var_writer = crate::var_writer();
    let var_values = crate::var_values();
    methods.extend(quote_spanned!(span =>
        fn render_into_with_values<AskamaW>(
            &self,
            #var_writer: &mut AskamaW,
            #var_values: &dyn askama::Values,
        ) -> askama::Result<()>
        where
            AskamaW: askama::helpers::core::fmt::Write + ?askama::helpers::core::marker::Sized
        {
            match *self {
                #render_into_arms
            }
        }
    ));

    #[cfg(feature = "alloc")]
    methods.extend(quote_spanned!(
        span =>
        fn render_with_values(
            &self,
            #var_values: &dyn askama::Values,
        ) -> askama::Result<askama::helpers::alloc::string::String> {
            let size_hint = match self {
                #size_hint_arms
            };
            let mut buf = askama::helpers::alloc::string::String::new();
            let _ = buf.try_reserve(size_hint);
            self.render_into_with_values(&mut buf, #var_values)?;
            askama::Result::Ok(buf)
        }
    ));

    write_header(enum_ast, buf, quote_spanned!(span => askama::Template));
    quote_into!(buf, span, {
        {
            #methods
            const SIZE_HINT: askama::helpers::core::primitive::usize = #biggest_size_hint;
        }
    });
    if print_code {
        eprintln!("{buf}");
    }
    Ok(biggest_size_hint)
}

fn set_default<S, T, A>(dest: &mut S, parent: &mut S, mut access: A)
where
    T: Clone,
    A: FnMut(&mut S) -> &mut Option<T>,
{
    let dest = access(dest);
    if dest.is_none()
        && let Some(parent) = access(parent)
    {
        *dest = Some(parent.clone());
    }
}

/// Generates a `struct` to contain the data of an enum variant
fn type_for_enum_variant(
    enum_ast: &DeriveInput,
    enum_generics: &Generics,
    var: &Variant,
) -> (DeriveInput, TokenStream) {
    let enum_id = &enum_ast.ident;
    let lt = enum_generics.params.first().unwrap();
    let (_, ty_generics, _) = enum_ast.generics.split_for_impl();
    let mut generics = enum_ast.generics.clone();
    generics.params.insert(0, lt.clone());

    let id = &var.ident;
    let span = id.span();
    let id = Ident::new(&format!("__Askama__{enum_id}__{id}"), span);

    let field: Type = parse_quote! {
        &#lt #enum_id #ty_generics
    };
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let (fields, deref_impl) = match &var.fields {
        Fields::Named(fields) => {
            let mut fields = fields.clone();
            for f in fields.named.iter_mut() {
                let ty = &f.ty;
                f.ty = parse_quote!(&#lt #ty);
            }
            let field_name = Ident::new(&format!("__Askama__{enum_id}__phantom"), span);
            fields.named.push(parse_quote!(#field_name: #field));
            let deref_impl = quote_spanned! {
                span=>
                impl #impl_generics askama::helpers::core::ops::Deref for #id #ty_generics {
                    type Target = #field;

                    fn deref(&self) -> &Self::Target {
                        &self.#field_name
                    }
                }
            };
            (Fields::Named(fields), deref_impl)
        }
        Fields::Unnamed(fields) => {
            let mut fields = fields.clone();
            for f in fields.unnamed.iter_mut() {
                let ty = &f.ty;
                f.ty = parse_quote!(&#lt #ty);
            }
            fields.unnamed.push(parse_quote!(#field));
            let idx = TokenStream::from_str(&format!("self.{}", fields.unnamed.len() - 1)).unwrap();
            let deref_impl = quote_spanned! {
                span=>
                impl #impl_generics askama::helpers::core::ops::Deref for #id #ty_generics {
                    type Target = #field;

                    fn deref(&self) -> &Self::Target {
                        &#idx
                    }
                }
            };
            (Fields::Unnamed(fields), deref_impl)
        }
        Fields::Unit => {
            let fields = Fields::Unnamed(parse_quote!((#field)));
            let deref_impl = quote_spanned! {
                span=>
                impl #impl_generics askama::helpers::core::ops::Deref for #id #ty_generics {
                    type Target = #field;

                    fn deref(&self) -> &Self::Target {
                        &self.0
                    }
                }
            };
            (fields, deref_impl)
        }
    };
    let semicolon = match &var.fields {
        Fields::Named(_) => None,
        _ => Some(Token![;](span)),
    };

    let span = enum_ast.span().resolved_at(proc_macro2::Span::call_site());
    (
        syn::parse_quote_spanned! {
            span=>
            #[askama::helpers::core::prelude::rust_2021::derive(
                askama::helpers::core::prelude::rust_2021::Clone,
                askama::helpers::core::prelude::rust_2021::Copy,
            )]
            struct #id #enum_generics #fields #semicolon
        },
        deref_impl,
    )
}

/// Generates a `match` arm for an `enum` variant, that calls `<_ as EnumVariantTemplate>::render_into()`
/// for that type and data
fn variant_as_arm(
    var_ast: &DeriveInput,
    var: &Variant,
    size_hint: usize,
    render_into_arms: &mut TokenStream,
    size_hint_arms: &mut TokenStream,
) {
    let var_id = &var_ast.ident;
    let ident = &var.ident;
    let span = ident.span();

    let generics = var_ast.generics.clone();
    let (_, ty_generics, _) = generics.split_for_impl();
    let ty_generics: TokenStream = ty_generics
        .as_turbofish()
        .to_token_stream()
        .into_iter()
        .enumerate()
        .map(|(idx, token)| match idx {
            // 0 1 2 3 4   =>   : : < ' __Askama_Foo
            4 => TokenTree::Ident(Ident::new("_", span)),
            _ => token,
        })
        .collect();

    let Data::Struct(ast_data) = &var_ast.data else {
        unreachable!();
    };
    let mut src = TokenStream::new();
    let mut this = TokenStream::new();
    match &var.fields {
        Fields::Named(fields) => {
            for (idx, field) in fields.named.iter().enumerate() {
                let arg = Ident::new(&format!("__askama_arg_{idx}"), field.span());
                let id = field.ident.as_ref().unwrap();
                src.extend(quote_spanned!(span => #id: ref #arg,));
                this.extend(quote_spanned!(span => #id: #arg,));
            }

            let phantom = match &ast_data.fields {
                Fields::Named(fields) => fields
                    .named
                    .iter()
                    .next_back()
                    .unwrap()
                    .ident
                    .as_ref()
                    .unwrap(),
                Fields::Unnamed(_) | Fields::Unit => unreachable!(),
            };
            this.extend(quote_spanned!(
                span => #phantom: &self,
            ));
        }

        Fields::Unnamed(fields) => {
            for (idx, field) in fields.unnamed.iter().enumerate() {
                let span = field.ident.span();
                let arg = Ident::new(&format!("__askama_arg_{idx}"), span);
                let idx = syn::LitInt::new(&format!("{idx}"), span);
                src.extend(quote_spanned!(span => #idx: ref #arg,));
                this.extend(quote_spanned!(span => #idx: #arg,));
            }
            let idx = syn::LitInt::new(&format!("{}", fields.unnamed.len()), span);
            this.extend(quote_spanned!(span => #idx: &self,));
        }

        Fields::Unit => {
            this.extend(quote_spanned!(span => 0: &self,));
        }
    };
    let var_writer = crate::var_writer();
    let var_values = crate::var_values();
    render_into_arms.extend(quote_spanned! {
        span =>
        Self :: #ident { #src } => {
            <_ as askama::helpers::EnumVariantTemplate>::render_into_with_values(
                & #var_id #ty_generics { #this },
                #var_writer,
                #var_values,
            )
        }
    });
    size_hint_arms.extend(quote_spanned! {
        span =>
        Self :: #ident { .. } => {
            #size_hint
        }
    });
}
