//! askama::filter_fn - Proc macro implementation
//! This parses an annotated freestanding function annotated with the `filter_fn` attribute
//! into an internal intermediate representation (the `FilterSignature` struct).
//! Then, the output code is generated from said struct.

use std::ops::ControlFlow;

use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote, quote_spanned};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Mut;
use syn::{
    Block, Expr, FnArg, GenericParam, ItemFn, Lifetime, Pat, PatType, ReturnType, Signature, Token,
    Type, TypeParamBound, Visibility,
};

use crate::{CompileError, HashMap, HashSet, parse_ts_or_compile_error};

pub fn derive_filter_fn(
    attr: TokenStream,
    item: TokenStream,
    import_askama: fn() -> TokenStream,
) -> TokenStream {
    let ffn: ItemFn = match parse_ts_or_compile_error(item, import_askama) {
        ControlFlow::Continue(ffn) => ffn,
        ControlFlow::Break(err) => return err,
    };
    match filter_fn_impl(attr, &ffn) {
        Ok(tt) => tt,
        Err(CompileError { msg, span }) => {
            let import_askama = import_askama();
            quote_spanned! {
                span.unwrap_or_else(|| ffn.sig.ident.span()) =>
                const _: () = {
                    #import_askama
                    askama::helpers::core::compile_error!(#msg);
                };
            }
        }
    }
}

/// Helper macro to produce proc macro compiler error messages with a given span
/// if a given condition is not met.
macro_rules! p_assert {
    ($cond:expr, $span:expr => $msg:literal $(,)?) => {
        match $cond {
            true => Ok(()),
            false => p_err!($span => $msg)
        }
    };
}

macro_rules! p_err {
    ($span:expr => $msg:literal $(,)?) => {
        Err(CompileError::new_with_span_stable($msg, None, Some($span)))
    };
}

// ##############################################################################################

/// Internal representation for custom required filter arguments
struct FilterArgumentRequired {
    idx: usize,
    ident: Ident,
    mutability: Option<Mut>,
    ty: Type,
    generics: HashSet<Ident>,
}

/// Internal representation for custom optional filter arguments.
/// These are arguments for which an optional value was supplied using `#[optional(...)]`
struct FilterArgumentOptional {
    idx: usize,
    ident: Ident,
    mutability: Option<Mut>,
    ty: Type,
    default: Expr,
}

/// Internal representation for a filter function's lifetime.
#[derive(Clone)]
struct FilterLifetime {
    lifetime: Lifetime,
    bounds: Punctuated<Lifetime, Token![+]>,
    used_by_extra_args: bool,
}

/// Internal representation for a filter function's generic argument.
#[derive(Clone)]
struct FilterArgumentGeneric {
    ident: Ident,
    bounds: Punctuated<TypeParamBound, Token![+]>,
}

fn get_lifetimes(stream: TokenStream, lifetimes: &mut HashSet<Ident>) {
    let mut iterator = stream.into_iter().peekable();
    while let Some(token) = iterator.next() {
        match token {
            TokenTree::Group(g) => get_lifetimes(g.stream(), lifetimes),
            TokenTree::Punct(p) if p.as_char() == '\'' => {
                // Lifetimes are represented as `[Punct('), Ident("a")]` in the `TokenStream`.
                if let Some(TokenTree::Ident(i)) = iterator.peek() {
                    lifetimes.insert(i.clone());
                }
            }
            TokenTree::Punct(_) | TokenTree::Ident(_) | TokenTree::Literal(_) => continue,
        }
    }
}

/// A freestanding method annotated with `askama::filter_fn` is parsed into an instance of this
/// struct, and then the resulting code is generated from there.
/// This struct serves as an intermediate representation after some preprocessing on the raw AST.
struct FilterSignature {
    /// Name of the annotated freestanding filter function
    ident: Ident,
    /// Lifetime bounds.
    lifetimes: Vec<FilterLifetime>,
    /// Name of the input variable
    arg_input: FilterArgumentRequired,
    /// Name of the askama environment variable
    arg_env: FilterArgumentRequired,
    /// Generic parameters required for the filter's input argument
    arg_input_generics: Vec<FilterArgumentGeneric>,
    /// Required filter arguments
    args_required: Vec<FilterArgumentRequired>,
    /// Optional filter arguments - each of which has a default value
    args_optional: Vec<FilterArgumentOptional>,
    /// Generic parameters in use by the required filter arguments
    args_required_generics: HashMap<Ident, FilterArgumentGeneric>,
    /// Filter function result type
    result_ty: ReturnType,
}

// ##############################################################################################
// parsing
// ##############################################################################################
impl FilterSignature {
    /// Parse the annotated function's signature and do some preprocessing to produce an instance
    /// of the `FilterSignature` struct.
    fn try_from_signature(sig: &Signature) -> Result<FilterSignature, CompileError> {
        // preliminary validation
        p_assert!(!sig.inputs.is_empty(), sig.paren_token.span.open() =>
            "Filter function missing required input and environment arguments. Example: \
            `fn filter0(_: &dyn std::fmt::Display, _: &dyn askama::Values) -> askama::Result<String>`"
        )?;
        p_assert!(sig.inputs.len() >= 2, sig.paren_token.span.open() =>
            "Filter function missing required environment argument. Example: \
            `fn filter0(_: &dyn std::fmt::Display, _: &dyn askama::Values) -> askama::Result<String>`"
        )?;
        if let Some(gc_arg) = sig.generics.const_params().next() {
            p_err!(gc_arg.span() => "Const generics are currently not supported for filters")?;
        }
        p_assert!(
            matches!(sig.output, ReturnType::Type(_, _)),
            sig.paren_token.span.close() => "Filter function is missing return type"
        )?;

        // ########################################
        // generics
        let mut generics = HashMap::default();
        for gp in sig.generics.type_params() {
            p_assert!(gp.default.is_none(), gp.default.span() => "Filter functions don't support generic parameter defaults")?;

            let ident = gp.ident.clone();
            let bounds = gp.bounds.clone();
            generics.insert(ident.clone(), FilterArgumentGeneric { ident, bounds });
        }

        // ########################################
        // fixed arguments (input & env)
        let arg_input = Self::try_get_fixed_arg(&sig.inputs[0], &generics)?;
        let arg_input_generics: Vec<_> = arg_input
            .generics
            .iter()
            .map(|i| generics[i].clone())
            .collect();
        let arg_env = Self::try_get_fixed_arg(&sig.inputs[1], &generics)?;

        // ########################################
        // user arguments
        let mut args_required = vec![];
        let mut args_optional = vec![];
        let mut args_required_generics = HashMap::default();
        let mut lifetimes_used_in_non_required = HashSet::default();
        for (arg_idx, arg) in sig.inputs.iter().skip(2).enumerate() {
            let FnArg::Typed(arg) = arg else {
                continue;
            };
            let Pat::Ident(arg_pat) = &*arg.pat else {
                p_err!(arg.pat.span() => "Only conventional function arguments are supported")?
            };
            p_assert!(
                !matches!(*arg.ty, Type::ImplTrait(_)),
                arg.ty.span() => "Impl generics are currently not supported for filters"
            )?;
            get_lifetimes(arg.to_token_stream(), &mut lifetimes_used_in_non_required);

            // reference-parameters without explicit lifetime, inherit the 'filter lifetime
            let arg_type = patch_ref_with_lifetime(&arg.ty, &format_ident!("filter"));

            match Self::get_optional_arg_attr(arg)? {
                // required argument (= has no default value)
                None => {
                    // required argument
                    p_assert!(args_optional.is_empty(), arg.span() => "All required arguments must appear before any optional ones")?;
                    // determine all generic parameters used by this argument
                    let used_generics: HashSet<_> = generics
                        .keys()
                        .filter(|i| type_contains_ident(&arg.ty, i).is_some())
                        .cloned()
                        .collect();
                    // mark the used generic parameters
                    used_generics.iter().map(|i| &generics[i]).for_each(|g| {
                        args_required_generics.insert(g.ident.clone(), g.clone());
                    });
                    args_required.push(FilterArgumentRequired {
                        idx: arg_idx,
                        ident: arg_pat.ident.clone(),
                        mutability: arg_pat.mutability,
                        ty: arg_type,
                        generics: used_generics,
                    });
                }
                // optional argument (= has default value)
                Some(default) => {
                    // check if the argument uses any generics (which is not allowed for optional arguments)
                    if let Some(span) = generics
                        .keys()
                        .filter_map(|i| type_contains_ident(&arg.ty, i))
                        .next()
                    {
                        p_err!(span => "Optional arguments must not use generic parameters")?;
                    }

                    args_optional.push(FilterArgumentOptional {
                        idx: arg_idx,
                        ident: arg_pat.ident.clone(),
                        mutability: arg_pat.mutability,
                        ty: arg_type,
                        default,
                    });
                }
            }
        }
        // lifetimes
        let lifetimes = sig
            .generics
            .lifetimes()
            .map(|lt| {
                let lifetime = lt.lifetime.clone();
                let bounds = lt.bounds.clone();
                let used_by_extra_args = lifetimes_used_in_non_required.contains(&lifetime.ident);
                FilterLifetime {
                    lifetime,
                    bounds,
                    used_by_extra_args,
                }
            })
            .collect::<Vec<_>>();

        // ########################################

        Ok(FilterSignature {
            ident: sig.ident.clone(),
            lifetimes,
            arg_input,
            arg_input_generics,
            arg_env,
            args_required,
            args_optional,
            args_required_generics,
            result_ty: sig.output.clone(),
        })
    }

    /// Parse one of the fixed filter arguments (value and env)
    fn try_get_fixed_arg(
        arg: &FnArg,
        generics: &HashMap<Ident, FilterArgumentGeneric>,
    ) -> Result<FilterArgumentRequired, CompileError> {
        let FnArg::Typed(arg) = arg else {
            p_err!(arg.span() => "Illegal or unsupported type of argument for filter function")?
        };
        let (arg_ident, mutability) = match &*arg.pat {
            Pat::Ident(pat_ident) => (pat_ident.ident.clone(), pat_ident.mutability),
            Pat::Wild(pat) => (Ident::new("_", pat.span()), None), // little hack
            _ => p_err!(arg.pat.span() => "Only conventional function arguments are supported")?,
        };

        Ok(FilterArgumentRequired {
            idx: 0,
            ident: arg_ident,
            ty: *arg.ty.clone(),
            mutability,
            generics: generics
                .keys()
                .filter(|i| type_contains_ident(&arg.ty, i).is_some())
                .cloned()
                .collect(),
        })
    }

    /// Parse the `#[optional(<default_expr>)]` attribute found on filter function arguments.
    /// For optional arguments, this is mandatory.
    fn get_optional_arg_attr(arg: &PatType) -> Result<Option<Expr>, CompileError> {
        for attr in &arg.attrs {
            if let Some(ident) = attr.meta.path().get_ident()
                && ident == "optional"
            {
                let default: Expr = match attr.parse_args() {
                    Ok(default) => default,
                    Err(_) => p_err!(attr.span() => "Default argument not a valid expression")?,
                };
                return Ok(Some(default));
            }
        }
        Ok(None)
    }
}

// ##############################################################################################
// code generation
// ##############################################################################################
impl FilterSignature {
    /// Returns a tuple containing two items:
    ///
    /// 1. The list of lifetimes with their bounds.
    /// 2. The list of lifetimes without their bounds.
    fn lifetimes_bounds<F: Fn(&FilterLifetime) -> bool>(
        &self,
        filter: F,
    ) -> (Vec<TokenStream>, Vec<&Lifetime>) {
        let mut lifetimes = Vec::with_capacity(self.lifetimes.len());
        let mut lifetimes_no_bounds = Vec::with_capacity(self.lifetimes.len());
        for lt in &self.lifetimes {
            if !filter(lt) {
                continue;
            }
            let name = &lt.lifetime;
            let bounds = &lt.bounds;
            lifetimes.push(quote! { #name: #bounds });
            lifetimes_no_bounds.push(name);
        }
        (lifetimes, lifetimes_no_bounds)
    }

    fn lifetimes_fillers<F: Fn(&FilterLifetime) -> bool>(&self, filter: F) -> Vec<TokenStream> {
        self.lifetimes
            .iter()
            .filter(|l| filter(l))
            .map(|_| quote! { '_ })
            .collect()
    }

    /// Generates a struct named after the filter function.
    /// This struct will contain all the filter's arguments (except input and env).
    /// The struct is basically a builder pattern for the custom filter arguments.
    /// It is structured like this:
    /// - All required arguments (no default value supplied) are contained in an `Option`
    /// - All optional arguments (default value supplied via attr) are contained as is
    /// - The struct adopts all the generic parameters which are in use by custom args
    /// - The struct always has a 'filter lifetime. This is the default lifetime relating
    ///   to the struct instance itself. It is patched onto reference arguments without
    ///   own explicit lifetime.
    /// - The struct has one const generic bool parameter for each required argument, tracking
    ///   whether the required argument was supplied.
    ///
    /// For every user argument to the filter, we implement the trait:
    /// `askama::filters::ValidArgIdx<const IDX: usize>` on the generated struct (where IDX = arg.idx).
    /// During code generation, the line: `const _: bool = askama::filters::ValidArgIdx<n>::VALID`
    /// can then check at compile-time whether there is an argument with the given index.
    fn gen_struct_definition(&self, vis: &Visibility) -> TokenStream {
        let ident = &self.ident;
        // struct generic parameters
        let struct_generics = self
            .args_required_generics
            .values()
            .map(|g| g.ident.clone());
        let required_flags = self
            .args_required
            .iter()
            .map(|a| format_ident!("REQUIRED_ARG_FLAG_{}", a.idx));
        // struct field definitions
        let required_fields = self.args_required.iter().map(|arg| {
            let (name, ty) = (&arg.ident, &arg.ty);
            quote! { #name: Option<#ty> }
        });
        let optional_fields = self.args_optional.iter().map(|arg| {
            let (name, ty) = (&arg.ident, &arg.ty);
            quote! { #name: #ty }
        });
        // introspection (better compile error messages on misuse)
        let required_arg_cnt = self.args_required.len();
        let optional_arg_cnt = self.args_optional.len();
        let arg_cnt = required_arg_cnt + optional_arg_cnt;
        let lifetimes_fillers = self.lifetimes_fillers(|l| l.used_by_extra_args);
        let valid_arg_impls = (0..arg_cnt).map(|idx| {
            quote! {
                #[diagnostic::do_not_recommend]
                impl askama::filters::ValidArgIdx<#idx> for #ident<'_, #(#lifetimes_fillers,)*> {}
            }
        });

        let (_, lifetimes) = self.lifetimes_bounds(|l| l.used_by_extra_args);
        quote! {
            #[allow(non_camel_case_types)]
            #vis struct #ident<'filter, #(#lifetimes,)* #(#struct_generics = (),)* #(const #required_flags : bool = false,)*> {
                _lifetime: std::marker::PhantomData<&'filter ()>,
                /* required fields */
                #(#required_fields,)*
                /* optional fields */
                #(#optional_fields,)*
            }

            #(#valid_arg_impls)*
        }
    }

    /// Generate the entry-point for the filter builder struct.
    /// This fills all required arguments (`Option<Ty>`) as `None`, and all the optional
    /// arguments with the default value supplied in the `#[optional(..)]` attribute.
    ///
    /// This entry point starts with a type of `()` for all the generic parameter
    /// used by required arguments. They are only filled with the correct type
    /// as soon as the argument is supplied into the corresponding setter.
    fn gen_default_impl(&self) -> TokenStream {
        let ident = &self.ident;
        // initial field values
        let required_defaults = self
            .args_required
            .iter()
            .map(|a| &a.ident)
            .map(|i| quote! { #i: None });
        let optional_defaults = self.args_optional.iter().map(|a| {
            let ident = &a.ident;
            let value = &a.default;
            quote! { #ident: #value }
        });
        let lifetimes_fillers = self.lifetimes_fillers(|l| l.used_by_extra_args);

        quote! {
            impl std::default::Default for #ident<'_, #(#lifetimes_fillers,)*> {
                fn default() -> Self {
                    Self {
                        _lifetime: std::marker::PhantomData::default(),
                        #(#required_defaults,)*
                        #(#optional_defaults,)*
                    }
                }
            }
        }
    }

    /// Generate the builder-style setter methods. Each argument gets two methods.
    /// - with_{arg_name}() for when an argument is passed as named arg
    /// - with_{arg_idx}() for when an argument is passed as positional arg
    ///
    /// Positional setters are always implemented by calling their named counterparts.
    ///
    /// Since optional arguments don't support generic arguments and their presence
    /// does not need to be checked, they simply change the field's value in the struct.
    /// Whereas required arguments construct a new struct instance, because they need to
    /// - Patch generic arguments (that started out with `()`)
    /// - Change the const generic bool parameter that tracks their presence to `true`
    fn gen_setters(&self) -> TokenStream {
        let optional_setters = self.gen_setters_optional();
        let required_setters = self
            .args_required
            .iter()
            .map(|arg| self.gen_required_setter(arg));

        quote! {
            #optional_setters
            #(#required_setters)*
        }
    }

    /// This generates setters for required arguments - which is much more complex than
    /// optional arguments. Each setter for a required argument:
    /// - constructs a new instance of the builder struct.
    /// - patches the required arguments' tracking const bool flag to `true`
    /// - fills the required argument's corresponding generic type arguments
    ///
    /// So setters for required arguments do not just return a copy of the builder struct,
    /// they also change its type signature (due to differing generic arguments).
    fn gen_required_setter(&self, arg: &FilterArgumentRequired) -> TokenStream {
        let ident = &self.ident;
        let cur_arg_ident = &arg.ident;
        let cur_arg_ty = &arg.ty;
        // setter idents
        let named_ident = format_ident!("with_{}", arg.ident);
        let positional_ident = format_ident!("with_{}", arg.idx);
        // impl generics
        let required_generics_impl: Vec<_> = self
            .args_required_generics
            .keys()
            .map(|i| format_ident!("{}__OLD", i))
            .collect();
        let required_flags: Vec<_> = self
            .args_required
            .iter()
            .map(|a| format_ident!("REQUIRED_ARG_FLAG_{}", a.idx))
            .collect();
        // function generics
        let required_generics_fn: Vec<_> = arg
            .generics
            .iter()
            .map(|i| &self.args_required_generics[i])
            .map(|g| {
                let ident = &g.ident;
                let bounds = &g.bounds;
                quote! { #ident: #bounds }
            })
            .collect();
        let (_, lifetimes_no_bounds) = self.lifetimes_bounds(|l| l.used_by_extra_args);
        // return type
        let fn_return_ty = {
            let required_generics_result =
                self.args_required_generics
                    .keys()
                    .map(|i| match arg.generics.contains(i) {
                        true => i.clone(),
                        false => format_ident!("{}__OLD", i),
                    });
            let required_flags_result = self.args_required.iter().map(|a| {
                match a.idx == arg.idx {
                    true => quote!(true), // current arg
                    false => format_ident!("REQUIRED_ARG_FLAG_{}", a.idx).to_token_stream(),
                }
            });
            quote! { #ident<'filter, #(#lifetimes_no_bounds,)* #(#required_generics_result,)* #(#required_flags_result,)*> }
        };
        // struct fields - (all fields, except that of current argument)
        let other_required_fields = self
            .args_required
            .iter()
            .filter(|a| a.idx != arg.idx)
            .map(|a| &a.ident)
            .map(|i| quote! { #i: self.#i });
        let optional_fields = self.args_optional.iter().map(|a| &a.ident);

        quote! {
            #[allow(non_camel_case_types)]
            impl<'filter, #(#lifetimes_no_bounds,)* #(#required_generics_impl,)* #(const #required_flags: bool,)*>
            #ident<'filter, #(#lifetimes_no_bounds,)* #(#required_generics_impl,)* #(#required_flags,)*> {
                // named setter
                #[inline(always)]
                pub fn #named_ident<#(#required_generics_fn,)*>(self, new_value: #cur_arg_ty) -> #fn_return_ty {
                    // construct new instance of filter builder struct, by copying over all current values.
                    // But replace the value of the setter's corresponding field with `Some(new_value)`.
                    #ident {
                        _lifetime: self._lifetime,
                        // copy previous field values (all except field of current setter)
                        #(#other_required_fields,)*
                        #(#optional_fields: self.#optional_fields,)*
                        // patch field of current argument to new value
                        #cur_arg_ident: Some(new_value)
                    }
                }

                // positional setter
                #[inline(always)]
                pub fn #positional_ident<#(#required_generics_fn,)*>(self, new_value: #cur_arg_ty) -> #fn_return_ty {
                    self.#named_ident(new_value)
                }
            }
        }
    }

    /// Generate setters for optional arguments
    /// Compared to required arguments, they don't need to create a new struct instance,
    /// because they don't need to change the struct's generic parameters.
    /// Each getter just overwrites its corresponding field with the new value.
    fn gen_setters_optional(&self) -> TokenStream {
        let ident = &self.ident;
        // generics (use stupid enumeration instead of named arguments for simplicity)
        let required_generics: Vec<_> = (0..self.args_required_generics.len())
            .map(|i| format_ident!("T{}", i))
            .collect();
        let required_flags: Vec<_> = (0..self.args_required.len())
            .map(|i| format_ident!("F{}", i))
            .collect();

        let optional_setters = self.args_optional.iter().map(|arg| {
            let arg_ident = &arg.ident;
            let named_ident = format_ident!("with_{arg_ident}");
            let positioned_ident = format_ident!("with_{}", arg.idx);
            let arg_ty = &arg.ty;

            quote! {
                // named setter
                #[inline(always)]
                pub fn #named_ident(mut self, value: #arg_ty) -> Self {
                    self.#arg_ident = value;
                    self
                }
                // positional setter
                #[inline(always)]
                pub fn #positioned_ident(self, value: #arg_ty) -> Self {
                    self.#named_ident(value)
                }
            }
        });

        let (_, lifetimes_no_bounds) = self.lifetimes_bounds(|l| l.used_by_extra_args);
        quote! {
            #[allow(non_camel_case_types)]
            impl<'filter, #(#lifetimes_no_bounds,)* #(#required_generics,)* #(const #required_flags: bool,)*>
            #ident<'filter, #(#lifetimes_no_bounds,)* #(#required_generics,)* #(#required_flags,)*> {
                #(#optional_setters)*
            }
        }
    }

    /// Generate the `execute(input, env)` method that does the filter's actual work.
    /// This method only takes the filter's input (before the pipe), as well as the askama values
    /// environment variable as arguments.
    /// The method is contained in an `impl{}` block that guards against missing required arguments
    /// by requiring the value `true` for all argument-tracking const generic bool parameters.
    ///
    /// The method's body contains an internal "preamble" that first maps all of the struct's
    /// fields into the local context by consuming them. Required arguments are unwrapped from
    /// their `Option<>` container, and optional arguments are moved as is.
    /// Then, the actual filter code is inserted after.
    fn gen_exec_impl(&self, sig: &Signature, filter_impl: &Block) -> TokenStream {
        let ident = &self.ident;
        // input variable
        // method generics (only the parameters not already present on struct)
        let input_ident = &self.arg_input.ident;
        let input_mutability = &self.arg_input.mutability;
        let input_ty = &self.arg_input.ty;
        let input_bounds = self
            .arg_input_generics
            .iter()
            .filter(|g| !self.args_required_generics.contains_key(&g.ident))
            .map(|g| {
                let ident = &g.ident;
                let bounds = &g.bounds;
                quote! { #ident: #bounds }
            });
        let (all_lifetimes, _) = self.lifetimes_bounds(|_| true);
        let (_, type_lifetimes) = self.lifetimes_bounds(|l| l.used_by_extra_args);

        // env variable
        let env_ident = &self.arg_env.ident;
        let env_ty = &self.arg_env.ty;

        // struct generics
        let required_generics: Vec<_> = self
            .args_required_generics
            .values()
            .map(|g| &g.ident)
            .collect();
        let required_generic_bounds = self.args_required_generics.values().map(|g| &g.bounds);
        let required_flags = std::iter::repeat_n(quote!(true), self.args_required.len());

        // filter result
        let result_ty = &self.result_ty;

        // variables
        let required_args = self.args_required.iter().map(|a| {
            let mutability = a.mutability;
            let ident = &a.ident;
            quote! {
                let #mutability #ident = unsafe { self.#ident.unwrap_unchecked() };
            }
        });
        let optional_args = self.args_optional.iter().map(|a| {
            let mutability = a.mutability;
            let ident = &a.ident;
            quote! {
                let #mutability #ident = unsafe { self.#ident };
            }
        });

        let fn_token = &sig.fn_token;
        let impl_generics = quote! { #(#required_generics: #required_generic_bounds,)* };
        let impl_struct_generics = quote! { #(#required_generics,)* #(#required_flags,)* };
        let lifetimes_fillers = self.lifetimes_fillers(|l| l.used_by_extra_args);
        quote_spanned! {
            sig.paren_token.span =>
            // if all required arguments have been supplied (P0 == true, P1 == true)
            // ... the execute() method is "unlocked":
            impl<#(#all_lifetimes,)* #impl_generics> #ident<'_, #(#type_lifetimes,)* #impl_struct_generics> {
                #[inline(always)]
                pub #fn_token execute< #(#input_bounds,)* >(
                    self,
                    #input_mutability #input_ident: #input_ty,
                    #env_ident: #env_ty
                ) #result_ty {
                    // map filter variables with original name into scope
                    #( #required_args )*
                    #( #optional_args )*
                    // insert actual filter function implementation
                    #filter_impl
                }
            }

            impl<#impl_generics> askama::filters::ValidFilterInvocation for #ident<'_, #(#lifetimes_fillers,)* #impl_struct_generics> {}
        }
    }
}

// ######################################################

fn filter_fn_impl(attr: TokenStream, ffn: &ItemFn) -> Result<TokenStream, CompileError> {
    p_assert!(
        attr.is_empty(),
        attr.span() => "`#[askama::filter_fn]` does not expect any attributes"
    )?;

    let fsig = FilterSignature::try_from_signature(&ffn.sig)?;

    for gp in &ffn.sig.generics.params {
        match gp {
            GenericParam::Type(_) | GenericParam::Lifetime(_) => {}
            GenericParam::Const(_) => {
                p_err!(gp.span() => "Const generic arguments are not supported for now")?;
            }
        }
    }

    let struct_def = fsig.gen_struct_definition(&ffn.vis);
    let default_impl = fsig.gen_default_impl();
    let setter_impl = fsig.gen_setters();
    let exec_impl = fsig.gen_exec_impl(&ffn.sig, &ffn.block);

    Ok(quote!(
        #struct_def
        #default_impl
        #setter_impl
        #exec_impl
    ))
}

/// Recursively check if a type contains one of the given Idents
fn type_contains_ident(ty: &Type, ident: &Ident) -> Option<Span> {
    match ty {
        Type::Path(type_path) => {
            for segment in &type_path.path.segments {
                // Check if the segment ident matches
                if &segment.ident == ident {
                    return Some(segment.ident.span());
                }

                // Check generic arguments recursively
                if let syn::PathArguments::AngleBracketed(ref args) = segment.arguments {
                    for arg in &args.args {
                        match arg {
                            syn::GenericArgument::Type(inner_ty) => {
                                if let Some(span) = type_contains_ident(inner_ty, ident) {
                                    return Some(span);
                                }
                            }
                            syn::GenericArgument::AssocType(assoc) => {
                                if let Some(span) = type_contains_ident(&assoc.ty, ident) {
                                    return Some(span);
                                }
                            }
                            _ => {} // Not types -> skip
                        }
                    }
                }
            }
            None
        }
        Type::Reference(type_ref) => type_contains_ident(&type_ref.elem, ident),
        Type::Slice(type_slice) => type_contains_ident(&type_slice.elem, ident),
        Type::Array(type_array) => type_contains_ident(&type_array.elem, ident),
        Type::Tuple(type_tuple) => type_tuple
            .elems
            .iter()
            .filter_map(|elem_ty| type_contains_ident(elem_ty, ident))
            .next(),
        Type::Paren(type_paren) => type_contains_ident(&type_paren.elem, ident),
        Type::Group(type_group) => type_contains_ident(&type_group.elem, ident),
        _ => None, // covers everything else
    }
}

fn patch_ref_with_lifetime(ty: &Type, lifetime: &Ident) -> Type {
    match ty {
        Type::Reference(type_ref) => {
            let mut new_type_ref = type_ref.clone();

            // Inject the lifetime if it's missing
            if new_type_ref.lifetime.is_none() {
                new_type_ref.lifetime = Some(Lifetime {
                    apostrophe: Span::call_site(),
                    ident: lifetime.clone(),
                });
            }

            Type::Reference(new_type_ref)
        }
        _ => ty.clone(), // Only patch reference types; others remain unchanged
    }
}
