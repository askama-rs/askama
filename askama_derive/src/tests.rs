//! Files containing tests for generated code.

use std::fmt;
use std::path::Path;

use console::style;
use prettyplease::unparse;
use proc_macro2::TokenStream;
use quote::quote;
use similar::{Algorithm, ChangeTag, TextDiffConfig};
use syn::parse_quote;

use crate::integration::Buffer;
use crate::{AnyTemplateArgs, derive_template};

#[track_caller]
fn build_template(ast: &syn::DeriveInput) -> Result<TokenStream, crate::CompileError> {
    let mut buf = Buffer::new();
    let args = AnyTemplateArgs::new(ast)?;
    crate::build_template(&mut buf, ast, args)?;
    Ok(buf.into_token_stream())
}

fn import_askama() -> TokenStream {
    quote! {
        extern crate askama;
    }
}

// This function makes it much easier to compare expected code by adding the wrapping around
// the code we want to check.
#[track_caller]
fn compare(jinja: &str, expected: &str, fields: &[(&str, &str)], size_hint: usize) {
    compare_ex(jinja, expected, fields, size_hint, "")
}

#[track_caller]
fn compare_ex(
    jinja: &str,
    expected: &str,
    fields: &[(&str, &str)],
    size_hint: usize,
    prefix: &str,
) {
    let generated = jinja_to_rust(jinja, fields, prefix);

    let expected: TokenStream = expected
        .parse()
        .expect("`TokenStream` failed to parse input");
    let expected: syn::File = syn::parse_quote! {
        #[automatically_derived]
        impl askama::Template for Foo {
            fn render_into_with_values<AskamaW>(
                &self,
                __askama_writer: &mut AskamaW,
                __askama_values: &dyn askama::Values,
            ) -> askama::Result<()>
            where
                AskamaW: askama::helpers::core::fmt::Write + ?askama::helpers::core::marker::Sized,
            {
                #[allow(unused_imports)]
                use askama::{
                    filters::{AutoEscape as _, WriteWritable as _},
                    helpers::{ResultConverter as _, core::fmt::Write as _},
                };
                #expected
                askama::Result::Ok(())
            }
            const SIZE_HINT: askama::helpers::core::primitive::usize = #size_hint;
        }

        /// Implement the [`format!()`][askama::helpers::std::format] trait for [`Foo`]
        ///
        /// Please be aware of the rendering performance notice in the [`Template`][askama::Template] trait.
        #[automatically_derived]
        impl askama::helpers::core::fmt::Display for Foo {
            #[inline]
            fn fmt(&self, f: &mut askama::helpers::core::fmt::Formatter<'_>) -> askama::helpers::core::fmt::Result {
                askama::Template::render_into(self, f).map_err(|_| askama::helpers::core::fmt::Error)
            }
        }

        #[automatically_derived]
        impl askama::FastWritable for Foo {
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
    };

    let expected = unparse(&expected);
    let generated = unparse(&generated);
    if expected != generated {
        struct Diff<'a>(&'a str, &'a str);

        impl fmt::Display for Diff<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let diff = TextDiffConfig::default()
                    .algorithm(Algorithm::Patience)
                    .diff_lines(self.0, self.1);
                for change in diff.iter_all_changes() {
                    let (change, line) = match change.tag() {
                        ChangeTag::Equal => (
                            style(" ").dim().bold(),
                            style(change.to_string_lossy()).dim(),
                        ),
                        ChangeTag::Delete => (
                            style("-").red().bold(),
                            style(change.to_string_lossy()).red(),
                        ),
                        ChangeTag::Insert => (
                            style("+").green().bold(),
                            style(change.to_string_lossy()).green(),
                        ),
                    };
                    write!(f, "{change}{line}")?;
                }
                Ok(())
            }
        }

        panic!(
            "\n\
            === Expected ===\n\
            \n\
            {expected}\n\
            \n\
            === Generated ===\n\
            \n\
            {generated}\n\
            \n\
            === Diff ===\n\
            \n\
            {diff}\n\
            \n\
            === FAILURE ===",
            expected = style(&expected).red(),
            generated = style(&generated).green(),
            diff = Diff(&expected, &generated),
        );
    }
}

fn jinja_to_rust(jinja: &str, fields: &[(&str, &str)], prefix: &str) -> syn::File {
    let jinja = format!(
        r##"#[template(source = {jinja:?}, ext = "txt")]
{prefix}
struct Foo {{ {} }}"##,
        fields
            .iter()
            .map(|(name, type_)| format!("{name}: {type_}"))
            .collect::<Vec<_>>()
            .join(","),
    );

    let generated = build_template(
        &syn::parse_str::<syn::DeriveInput>(&jinja).expect("`syn` failed to parse code"),
    )
    .expect("`build_template` failed");
    match syn::parse2(generated.clone()) {
        Ok(generated) => generated,
        Err(err) => panic!(
            "\n\
            === Invalid code generated ===\n\
            \n\
            {generated}\n\
            \n\
            === Error ===\n\
            \n\
            {err}"
        ),
    }
}

#[test]
fn check_if_let() {
    // In this test, we ensure that `query` never is `self.query`.
    compare(
        "{% if let Some(query) = s && !query.is_empty() %}{{query}}{% endif %}",
        r"if let Some(query,) = &self.s && !askama::helpers::as_bool(&(query.is_empty())) {
    match (
        &((&&askama::filters::AutoEscaper::new(&(query), askama::filters::Text)).askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}",
        &[],
        3,
    );

    // In this test, we ensure that `s` is `self.s` only in the first `if let Some(s) = self.s`
    // condition.
    compare(
        "{% if let Some(s) = s %}{{ s }}{% endif %}",
        r"if let Some(s,) = &self.s {
    match (
        &((&&askama::filters::AutoEscaper::new(&(s), askama::filters::Text)).askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}",
        &[],
        3,
    );

    // In this test, we ensure that `s` is `self.s` only in the first `if let Some(s) = self.s`
    // condition.
    compare(
        "{% if let Some(s) = s && !s.is_empty() %}{{s}}{% endif %}",
        r"if let Some(s,) = &self.s && !askama::helpers::as_bool(&(s.is_empty())) {
    match (
        &((&&askama::filters::AutoEscaper::new(&(s), askama::filters::Text)).askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}",
        &[],
        3,
    );
}

// Since this feature is not stable yet, we can't add a "normal" test for it so instead we check
// the generated code.
#[test]
fn check_if_let_chain() {
    // Both `bla` and `blob` variables must exist in this `if`.
    compare(
        "{% if let Some(bla) = y && x && let Some(blob) = y %}{{bla}} {{blob}}{% endif %}",
        r#"if let Some(bla) = &self.y && askama::helpers::as_bool(&(self.x)) && let Some(blob) = &self.y {
    match (
        &((&&askama::filters::AutoEscaper::new(&(bla), askama::filters::Text))
            .askama_auto_escape()?),
        &((&&askama::filters::AutoEscaper::new(&(blob), askama::filters::Text))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0, __askama_expr2) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            __askama_writer.write_str(" ")?;
            (&&&askama::filters::Writable(__askama_expr2)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}"#,
        &[],
        7,
    );

    compare(
        r#"{% if let Some(bla) = y
            && bla == "x"
            && let Some(blob) = z
            && blob == "z" %}{{bla}} {{blob}}{% endif %}"#,
        r#"if let Some(bla) = &self.y && askama::helpers::as_bool(&(bla == "x"))
             && let Some(blob) = &self.z && askama::helpers::as_bool(&(blob == "z"))
{
    match (
        &((&&askama::filters::AutoEscaper::new(&(bla), askama::filters::Text))
            .askama_auto_escape()?),
        &((&&askama::filters::AutoEscaper::new(&(blob), askama::filters::Text))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0, __askama_expr2) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            __askama_writer.write_str(" ")?;
            (&&&askama::filters::Writable(__askama_expr2)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}"#,
        &[],
        7,
    );

    // Bindings variables with the same name as the bound variable should be declared in the right
    // order.
    compare(
        r#"{% if let Some(y) = y
            && y == "x"
            && w
            && let Some(z) = z
            && z == "z" %}{{y}} {{z}}{% endif %}"#,
        r#"if let Some(y) = &self.y && self.y == "x"
    && askama::helpers::as_bool(&(self.w)) && let Some(z) = &self.z
    && askama::helpers::as_bool(&(z == "z"))
{
    match (
        &((&&askama::filters::AutoEscaper::new(&(y), askama::filters::Text))
            .askama_auto_escape()?),
        &((&&askama::filters::AutoEscaper::new(&(z), askama::filters::Text))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0, __askama_expr2) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            __askama_writer.write_str(" ")?;
            (&&&askama::filters::Writable(__askama_expr2)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}"#,
        &[],
        7,
    );

    compare(
        r#"{% if w
            && let Some(y) = y
            && y == "x"
            && let Some(z) = z
            && z == "z" %}{{y}} {{z}}{% endif %}"#,
        r#"if askama::helpers::as_bool(&(self.w)) && let Some(y) = &self.y
    && self.y == "x" && let Some(z) = &self.z
    && askama::helpers::as_bool(&(z == "z"))
{
    match (
        &((&&askama::filters::AutoEscaper::new(&(y), askama::filters::Text))
            .askama_auto_escape()?),
        &((&&askama::filters::AutoEscaper::new(&(z), askama::filters::Text))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0, __askama_expr2) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            __askama_writer.write_str(" ")?;
            (&&&askama::filters::Writable(__askama_expr2)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}"#,
        &[],
        7,
    );
}

#[test]
fn check_includes_only_once() {
    // In this test we make sure that every used template gets referenced exactly once.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("templates");
    let path1 = path.join("include1.html").canonicalize().unwrap();
    let path2 = path.join("include2.html").canonicalize().unwrap();
    let path3 = path.join("include3.html").canonicalize().unwrap();
    compare(
        r#"{% include "include1.html" %}"#,
        &format!(
            r#"const _: &[askama::helpers::core::primitive::u8] = askama::helpers::core::include_bytes!({path1:#?});
            const _: &[askama::helpers::core::primitive::u8] = askama::helpers::core::include_bytes!({path2:#?});
            const _: &[askama::helpers::core::primitive::u8] = askama::helpers::core::include_bytes!({path3:#?});
            __askama_writer.write_str("3333")?;"#
        ),
        &[],
        4,
    );
}

#[test]
fn check_is_defined() {
    // Checks that it removes conditions if we know at compile-time that they always return false.
    //
    // We're forced to add `bla` otherwise `compare` assert fails in weird ways...
    compare(
        "{% if y is defined %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if x is not defined %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[("x", "u32")],
        3,
    );
    compare(
        "{% if y is defined && x is not defined %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[("x", "u32")],
        3,
    );

    // Same with declared variables.
    compare(
        "{% set y = 12 %}
         {%- if y is not defined %}{{query}}{% endif %}bla",
        r#"let y = 12;
__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% set y = 12 %}
         {%- if y is not defined && x is defined %}{{query}}{% endif %}bla",
        r#"let y = 12;
__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );

    // Checks that if the condition is always `true` at compile-time, then we keep the code but
    // remove the condition.
    compare(
        "{% if y is defined %}bla{% endif %}",
        r#"__askama_writer.write_str("bla")?;"#,
        &[("y", "u32")],
        3,
    );
    compare(
        "{% if x is not defined %}bla{% endif %}",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    // Same with declared variables.
    compare(
        "{% set y = 12 %}
         {%- if y is defined %}bla{% endif %}",
        r#"let y = 12;
__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );

    // If the always `true` condition is followed by more `else if`/`else`, check that they are
    // removed as well.
    compare(
        "{% if x is defined %}bli
         {%- else if x == 12 %}12{% endif %}bla",
        r#"__askama_writer.write_str("blibla")?;"#,
        &[("x", "u32")],
        6,
    );
    compare(
        "{% if x is defined %}bli
         {%- else if x == 12 %}12
         {%- else %}nope{% endif %}bla",
        r#"__askama_writer.write_str("blibla")?;"#,
        &[("x", "u32")],
        6,
    );
    // If it's not the first one.
    compare(
        "{% if x == 12 %}bli
         {%- else if x is defined %}12
         {%- else %}nope{% endif %}",
        r#"if askama::helpers::as_bool(&(self.x == 12)) {
__askama_writer.write_str("bli")?;
} else {
__askama_writer.write_str("12")?;
}"#,
        &[("x", "u32")],
        5,
    );

    // Checking that it doesn't remove the condition if other non-"if (not) defined" checks
    // are present.
    compare(
        "{% if y is defined || x == 12 %}{{x}}{% endif %}",
        r"if askama::helpers::as_bool(&(self.x == 12)) {
    match (
        &((&&askama::filters::AutoEscaper::new(&(self.x), askama::filters::Text)).askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}
",
        &[("x", "u32")],
        3,
    );
    compare(
        "{% if y is defined || x == 12 %}{{x}}{% endif %}",
        r"match (
    &((&&askama::filters::AutoEscaper::new(&(self.x), askama::filters::Text)).askama_auto_escape()?),
) {
    (__askama_expr0,) => {
        (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
    }
}
",
        &[("y", "u32"), ("x", "u32")],
        3,
    );
    compare(
        "{% if y is defined && y == 12 %}{{x}}{% endif %}",
        r"",
        &[],
        0,
    );
    compare(
        "{% if y is defined && y == 12 %}{{y}}{% else %}bli{% endif %}",
        r#"__askama_writer.write_str("bli")?;"#,
        &[],
        3,
    );
    compare(
        "{% if y is defined && y == 12 %}{{y}}{% else %}bli{% endif %}",
        r#"
if askama::helpers::as_bool(&(self.y == 12)) {
    match (
        &((&&askama::filters::AutoEscaper::new(
            &(self.y),
            askama::filters::Text,
        ))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
} else {
    __askama_writer.write_str("bli")?;
}
"#,
        &[("y", "u32")],
        6,
    );
    // Since the first `if` is always `true`, the `else` should not be generated.
    compare(
        "{% if y is defined %}{{y}}{% else %}bli{% endif %}",
        r"
match (
    &((&&askama::filters::AutoEscaper::new(
        &(self.y),
        askama::filters::Text,
    ))
        .askama_auto_escape()?),
) {
    (__askama_expr0,) => {
        (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
    }
}
",
        &[("y", "u32")],
        3,
    );

    // Checking some funny cases.

    // This one is a bit useless because you can use `is not defined` but I suppose it's possible
    // to encounter cases like that in the wild so better have a check.
    compare(
        "{% if !(y is defined) %}bla{% endif %}",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if !(y is not defined) %}bli{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if !(y is defined) %}bli{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[("y", "u32")],
        3,
    );
    compare(
        "{% if !(y is not defined) %}bla{% endif %}",
        r#"__askama_writer.write_str("bla")?;"#,
        &[("y", "u32")],
        3,
    );

    // Ensure that the `!` is kept .
    compare(
        "{% if y is defined && !y %}bla{% endif %}",
        r#"if !askama::helpers::as_bool(&(self.y)) {
    __askama_writer.write_str("bla")?;
}"#,
        &[("y", "bool")],
        3,
    );
    compare(
        "{% if y is defined && !(y) %}bla{% endif %}",
        r#"if !(askama::helpers::as_bool(&(self.y))) {
    __askama_writer.write_str("bla")?;
}"#,
        &[("y", "bool")],
        3,
    );
    compare(
        "{% if y is not defined || !y %}bla{% endif %}",
        r#"if !askama::helpers::as_bool(&(self.y)) {
    __askama_writer.write_str("bla")?;
}"#,
        &[("y", "bool")],
        3,
    );
    compare(
        "{% if y is not defined || !(y) %}bla{% endif %}",
        r#"if !(askama::helpers::as_bool(&(self.y))) {
    __askama_writer.write_str("bla")?;
}"#,
        &[("y", "bool")],
        3,
    );
}

#[test]
fn check_bool_conditions() {
    // Checks that it removes conditions if we know at compile-time that they always return false.
    //
    // We're forced to add `bla` otherwise `compare` assert fails in weird ways...
    compare(
        "{% if false %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if false && false %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if false && true %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if true && false %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if false || true %}bli{% endif %}bla",
        r#"__askama_writer.write_str("blibla")?;"#,
        &[],
        6,
    );
    compare(
        "{% if true || false %}bli{% endif %}bla",
        r#"__askama_writer.write_str("blibla")?;"#,
        &[],
        6,
    );

    compare(
        "{% if true || x == 12 %}{{x}}{% endif %}",
        r"match (
    &((&&askama::filters::AutoEscaper::new(&(self.x), askama::filters::Text)).askama_auto_escape()?),
) {
    (__askama_expr0,) => {
        (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
    }
}
",
        &[("x", "u32")],
        3,
    );
    compare(
        "{% if false || x == 12 %}{{x}}{% endif %}",
        r"if askama::helpers::as_bool(&(self.x == 12)) {
    match (
        &((&&askama::filters::AutoEscaper::new(
            &(self.x),
            askama::filters::Text,
        ))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}
",
        &[("x", "u32")],
        3,
    );

    // Checking that it also works with sub conditions.

    // It's important here that the `(true || x == 12)` part remains since it's not first in the
    // condition.
    compare(
        "{% if y == 3 || (true || x == 12) %}{{x}}{% endif %}",
        r"if askama::helpers::as_bool(&(self.y == 3)) || true {
    match (
        &((&&askama::filters::AutoEscaper::new(
            &(self.x),
            askama::filters::Text,
        ))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}
",
        &[],
        3,
    );
    // However in this case, since `(true || x == 12)` is evaluated to `true`, `y == 3` will never
    // be evaluated so the whole code is removed.
    compare(
        "{% if (true || x == 12) || y == 3 %}{{x}}{% endif %}",
        r"match (
    &((&&askama::filters::AutoEscaper::new(
        &(self.x),
        askama::filters::Text,
    ))
        .askama_auto_escape()?),
) {
    (__askama_expr0,) => {
        (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
    }
}
",
        &[],
        3,
    );
    compare(
        "{% if y == 3 || (x == 12 || true) %}{{x}}{% endif %}",
        r"
if askama::helpers::as_bool(&(self.y == 3))
    || (askama::helpers::as_bool(&(self.x == 12)) || true)
{
    match (
        &((&&askama::filters::AutoEscaper::new(
            &(self.x),
            askama::filters::Text,
        ))
            .askama_auto_escape()?),
    ) {
        (__askama_expr0,) => {
            (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
        }
    }
}
",
        &[],
        3,
    );

    // Some funny cases.
    compare(
        "{% if !(false) %}bla{% endif %}",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );
    compare(
        "{% if !(true) %}{{query}}{% endif %}bla",
        r#"__askama_writer.write_str("bla")?;"#,
        &[],
        3,
    );

    // Complex condition
    compare(
        "{% if (a || !b) && !(c || !d) %}x{% endif %}",
        r#"
            if (
                askama::helpers::as_bool(&(self.a))
                || !askama::helpers::as_bool(&(self.b))
            ) && !(
                askama::helpers::as_bool(&(self.c))
                || !askama::helpers::as_bool(&(self.d))
            ) {
                __askama_writer.write_str("x")?;
            }"#,
        &[("a", "i32"), ("b", "i32"), ("c", "i32"), ("d", "i32")],
        1,
    );
}

#[test]
fn check_escaping_at_compile_time() {
    compare(
        r#"The card is
        {%- match suit %}
            {%- when Suit::Clubs or Suit::Spades -%}
                {{ " black" }}
            {%- when Suit::Diamonds or Suit::Hearts -%}
                {{ " red" }}
        {%- endmatch %}"#,
        r#"__askama_writer.write_str("The card is")?;
        match &self.suit {
            Suit::Clubs {} | Suit::Spades {} => {
                __askama_writer.write_str(" black")?;
            }
            Suit::Diamonds {} | Suit::Hearts {} => {
                __askama_writer.write_str(" red")?;
            }
        }"#,
        &[("suit", "Suit")],
        16,
    );

    compare(
        r#"{{ '\x41' }}{{ '\n' }}{{ '\r' }}{{ '\t' }}{{ '\\' }}{{ '\u{2665}' }}{{ '\'' }}{{ '\"' }}{{ '"' }}
{{ "\x41\n\r\t\\\u{2665}\'\"'" }}"#,
        r#"__askama_writer.write_str("A
\r	\\♥'\"\"
A
\r	\\♥'\"'")?;"#,
        &[],
        23,
    );

    compare(
        r"{{ 1_2_3_4 }} {{ 4e3 }} {{ false }} {{0x1_1}} {{0o10}} {{0b11}}",
        r#"__askama_writer.write_str("1234 4000 false 17 8 3")?;"#,
        &[],
        22,
    );
}

#[cfg(feature = "code-in-doc")]
#[test]
fn test_code_in_comment() {
    let ts = r#"
        #[template(ext = "txt", in_doc = true)]
        /// ```askama
        /// Hello world!
        /// ```
        struct Tmpl;
    "#;
    let ast = syn::parse_str(ts).unwrap();
    let generated = build_template(&ast).unwrap().to_string();
    assert!(generated.contains("Hello world!"));
    assert!(!generated.contains("compile_error"));

    let ts = r#"
        #[template(ext = "txt", in_doc = true)]
        /// ```askama
        /// Hello
        /// world!
        /// ```
        struct Tmpl;
    "#;
    let ast = syn::parse_str(ts).unwrap();
    let generated = build_template(&ast).unwrap().to_string();
    assert!(generated.contains("Hello\nworld!"));
    assert!(!generated.contains("compile_error"));

    let ts = r#"
        /// ```askama
        /// Hello
        #[template(ext = "txt", in_doc = true)]
        /// world!
        /// ```
        struct Tmpl;
    "#;
    let ast = syn::parse_str(ts).unwrap();
    let generated = build_template(&ast).unwrap().to_string();
    assert!(generated.contains("Hello\nworld!"));
    assert!(!generated.contains("compile_error"));

    let ts = r#"
        /// This template greets the whole world
        ///
        /// ```askama
        /// Hello
        #[template(ext = "txt", in_doc = true)]
        /// world!
        /// ```
        ///
        /// Some more text.
        struct Tmpl;
    "#;
    let ast = syn::parse_str(ts).unwrap();
    let generated = build_template(&ast).unwrap().to_string();
    assert!(generated.contains("Hello\nworld!"));
    assert!(!generated.contains("compile_error"));

    let ts = "
        #[template(ext = \"txt\", in_doc = true)]
        #[doc = \"```askama\nHello\nworld!\n```\"]
        struct Tmpl;
    ";
    let ast = syn::parse_str(ts).unwrap();
    let generated = build_template(&ast).unwrap().to_string();
    assert!(generated.contains("Hello\nworld!"));
    assert!(!generated.contains("compile_error"));

    let ts = "
        #[template(ext = \"txt\", in_doc = true)]
        /// `````
        /// ```askama
        /// {{bla}}
        /// ```
        /// `````
        struct BlockOnBlock;
    ";
    let ast = syn::parse_str(ts).unwrap();
    let err = build_template(&ast).unwrap_err();
    assert_eq!(
        err.to_string(),
        "when using `in_doc` with the value `true`, the struct's documentation needs a `askama` \
         code block"
    );

    let ts = "
        #[template(ext = \"txt\", in_doc = true)]
        /// ```askama
        /// `````
        /// {{bla}}
        /// `````
        /// ```
        struct BlockOnBlock;
    ";
    let ast = syn::parse_str(ts).unwrap();
    let generated = build_template(&ast).unwrap().to_string();
    assert!(!generated.contains("compile_error"));
}

#[test]
fn test_pluralize() {
    compare(
        r"{{dogs}} dog{{dogs|pluralize}}",
        r#"
        match (
            &((&&askama::filters::AutoEscaper::new(
                &(self.dogs),
                askama::filters::Text,
            ))
                .askama_auto_escape()?),
            &(askama::filters::pluralize(
                &(self.dogs),
                askama::helpers::Empty,
                askama::filters::Safe("s"),
            )?),
        ) {
            (__askama_expr0, __askama_expr3) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
                __askama_writer.write_str(" dog")?;
                (&&&askama::filters::Writable(__askama_expr3)).askama_write(__askama_writer, __askama_values)?;
            }
        }"#,
        &[("dogs", "i8")],
        10,
    );
    compare(
        r#"{{dogs}} dog{{dogs|pluralize("go")}}"#,
        r#"
        match (
            &((&&askama::filters::AutoEscaper::new(
                &(self.dogs),
                askama::filters::Text,
            ))
                .askama_auto_escape()?),
            &(askama::filters::pluralize(
                &(self.dogs),
                askama::filters::Safe("go"),
                askama::filters::Safe("s"),
            )?),
        ) {
            (__askama_expr0, __askama_expr3) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
                __askama_writer.write_str(" dog")?;
                (&&&askama::filters::Writable(__askama_expr3)).askama_write(__askama_writer, __askama_values)?;
            }
        }"#,
        &[("dogs", "i8")],
        10,
    );
    compare(
        r#"{{mice}} {{mice|pluralize("mouse", "mice")}}"#,
        r#"
        match (
            &((&&askama::filters::AutoEscaper::new(
                &(self.mice),
                askama::filters::Text,
            ))
                .askama_auto_escape()?),
            &(askama::filters::pluralize(
                &(self.mice),
                askama::filters::Safe("mouse"),
                askama::filters::Safe("mice"),
            )?),
        ) {
            (__askama_expr0, __askama_expr2) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
                __askama_writer.write_str(" ")?;
                (&&&askama::filters::Writable(__askama_expr2)).askama_write(__askama_writer, __askama_values)?;
            }
        }"#,
        &[("dogs", "i8")],
        7,
    );

    compare(
        r"{{count|pluralize(one, count)}}",
        r"
        match (
            &(askama::filters::pluralize(
                &(self.count),
                (&&askama::filters::AutoEscaper::new(
                    &(self.one),
                    askama::filters::Text,
                ))
                    .askama_auto_escape()?,
                (&&askama::filters::AutoEscaper::new(
                    &(self.count),
                    askama::filters::Text,
                ))
                    .askama_auto_escape()?,
            )?),
        ) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            }
        }
        ",
        &[("count", "i8"), ("one", "&'static str")],
        3,
    );

    compare(
        r"{{0|pluralize(sg, pl)}}",
        r"
        match (
            &((&&askama::filters::AutoEscaper::new(&(self.pl), askama::filters::Text))
                .askama_auto_escape()?),
        ) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            }
        }
        ",
        &[("sg", "&'static str"), ("pl", "&'static str")],
        3,
    );
    compare(
        r"{{1|pluralize(sg, pl)}}",
        r"
        match (
            &((&&askama::filters::AutoEscaper::new(&(self.sg), askama::filters::Text))
                .askama_auto_escape()?),
        ) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            }
        }
        ",
        &[("sg", "&'static str"), ("pl", "&'static str")],
        3,
    );

    compare(
        r#"{{0|pluralize("sg", "pl")}}"#,
        r#"
        match (&(askama::filters::Safe("pl")),) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            }
        }
        "#,
        &[],
        3,
    );
    compare(
        r#"{{1|pluralize("sg", "pl")}}"#,
        r#"
        match (&(askama::filters::Safe("sg")),) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            }
        }
        "#,
        &[],
        3,
    );

    compare(
        r"{{0|pluralize}}",
        r#"
        match (&(askama::filters::Safe("s")),) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            }
        }
        "#,
        &[],
        3,
    );
    compare(
        r"{{1|pluralize}}",
        r"
        match (&(askama::helpers::Empty),) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
            }
        }
        ",
        &[],
        3,
    );
}

#[test]
fn test_concat() {
    compare(
        r#"{{ "<" ~ a ~ "|" ~ b ~ '>' }}"#,
        r#"
            __askama_writer.write_str("<")?;
            match (
                &((&&askama::filters::AutoEscaper::new(&(self.a), askama::filters::Text))
                    .askama_auto_escape()?),
                &((&&askama::filters::AutoEscaper::new(&(self.b), askama::filters::Text))
                    .askama_auto_escape()?),
            ) {
                (__askama_expr1, __askama_expr3) => {
                    (&&&askama::filters::Writable(__askama_expr1)).askama_write(__askama_writer, __askama_values)?;
                    __askama_writer.write_str("|")?;
                    (&&&askama::filters::Writable(__askama_expr3)).askama_write(__askama_writer, __askama_values)?;
                }
            }
            __askama_writer.write_str(">")?;
        "#,
        &[("a", "&'static str"), ("b", "u32")],
        9,
    );

    compare(
        r#"{{ ("a=" ~ a ~ " b=" ~ b)|upper }}"#,
        r#"
            match (
                &((&&askama::filters::AutoEscaper::new(
                    &(askama::filters::upper(
                        &((askama::helpers::Concat(
                            &(askama::helpers::Concat(&("a="), &(self.a))),
                            &(askama::helpers::Concat(&(" b="), &(self.b))),
                        ))),
                    )?),
                    askama::filters::Text,
                ))
                    .askama_auto_escape()?),
            ) {
                (__askama_expr0,) => {
                    (&&&askama::filters::Writable(__askama_expr0)).askama_write(__askama_writer, __askama_values)?;
                }
            }
        "#,
        &[("a", "&'static str"), ("b", "u32")],
        3,
    );
}

#[test]
fn extends_with_whitespace_control() {
    const CONTROL: &[&str] = &["", "\t", "-", "+", "~"];

    let expected = jinja_to_rust(r#"{% extends "a.html" %} back"#, &[], "");
    let expected = unparse(&expected);
    for front in CONTROL {
        for back in CONTROL {
            let src = format!(r#"{{%{front} extends "a.html" {back}%}} back"#);
            let actual = jinja_to_rust(&src, &[], "");
            let actual = unparse(&actual);
            assert_eq!(expected, actual, "source: {src:?}");
        }
    }
}

#[test]
fn test_with_config() {
    // In this test we make sure that the config path is tracked.
    compare_ex(
        r#""#,
        &format!(
            "const _: &[askama::helpers::core::primitive::u8] = \
            askama::helpers::core::include_bytes!({:#?});",
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("empty_test_config.toml")
                .canonicalize()
                .unwrap(),
        ),
        &[],
        0,
        r#"#[template(config = "empty_test_config.toml")]"#,
    );
}

#[test]
fn test_generated_with_error() {
    // Ensure that the generated code on errors can still be parsed by syn.
    let ts = quote! {
        #[derive(Template)]
        #[template(ext = "txt", source = "test {#")]
        struct HelloWorld;
    };
    let ts = derive_template(ts, import_askama);
    let _: syn::File = syn::parse2(ts).unwrap();
}

#[test]
fn test_filter_with_path() {
    compare(
        r"{{ a | b::c::d }}",
        r#"
        match (
            &((&&askama::filters::AutoEscaper::new(
                &({
                    askama::filters::ValidFilterInvocation::wrap(b::c::d::default())
                        .execute(&(self.a), __askama_values)?
                }),
                askama::filters::Text,
            ))
                .askama_auto_escape()?),
        ) {
            (__askama_expr0,) => {
                (&&&askama::filters::Writable(__askama_expr0))
                    .askama_write(__askama_writer, __askama_values)?;
            }
        }"#,
        &[("a", "i8")],
        3,
    );
}

#[test]
fn fuzzed_0b85() -> Result<(), syn::Error> {
    let input = quote! {
        #[template(
            ext = "",
            source = "\u{c}{{vSelf&&h<6-0b85%04540736.66609.500804540736.660<c7~}}2/3\0{w66hi%e<a}}"
        )]
        struct a {}
    };
    let output = derive_template(input, import_askama);
    let _: syn::File = syn::parse2(output)?;
    Ok(())
}

#[test]
fn fuzzed_comparator_chain() -> Result<(), syn::Error> {
    let input = quote! {
        #[template(
            ext = "",
            source = "\u{c}{{vu7218/63e3666663-666/3330e633/63e3666663666/3333<c\"}\u{1}2}\0\"<c7}}2\"\"\"\"\0\0\0\0"
        )]
        enum fff {}
    };
    let output = derive_template(input, import_askama);
    let _: syn::File = syn::parse2(output)?;
    Ok(())
}

#[test]
fn test_macro_names_that_need_escaping() {
    // Cannot be raw identifiers: ["crate", "self", "Self", "super"]
    // Never parsed as identifiers: ["false", "true"]

    const KEYWORDS: &[&str] = &[
        "abstract", "as", "async", "await", "become", "box", "break", "const", "continue", "do",
        "dyn", "else", "enum", "extern", "final", "fn", "for", "gen", "if", "impl", "in", "let",
        "loop", "macro", "match", "mod", "move", "mut", "override", "priv", "pub", "ref", "return",
        "static", "struct", "trait", "try", "type", "typeof", "unsafe", "unsized", "use",
        "virtual", "where", "while", "yield",
    ];

    for keyword in KEYWORDS {
        compare(
            &format!(r"{{{{ {keyword}!() }}}}"),
            &format!(
                "
                match (
                    &((&&askama::filters::AutoEscaper::new(
                        &(r#{keyword}!()),
                        askama::filters::Text,
                    ))
                        .askama_auto_escape()?),
                ) {{
                    (__askama_expr0,) => {{
                        (&&&askama::filters::Writable(__askama_expr0))
                            .askama_write(__askama_writer, __askama_values)?;
                    }}
                }}"
            ),
            &[],
            3,
        );
    }
}

#[test]
fn test_macro_calls_need_proper_tokens() -> Result<(), syn::Error> {
    // Regression test for fuzzed error <https://github.com/askama-rs/askama/issues/459>.
    // Macro calls can contains any valid tokens, but only valid tokens.
    // Invalid tokens will be rejected by rust, so we must not emit them.

    #[rustfmt::skip] // FIXME: rustfmt bug <https://github.com/rust-lang/rustfmt/issues/5489>
    let input = quote! {
        #[template(
            ext = "",
            source = "\u{c}awtraitaitA{{override\u{c}!  \u{c} (\u{1f}  \u{c}\u{c})\u{c}}}"
//                                      ^^^^^^^^               ^^^^^^
//                                      illegal identifier     illegal token
        )]
        struct f {}
    };
    let output = derive_template(input, import_askama);
    assert!(
        output
            .to_string()
            .contains("expected valid tokens in macro call")
    );
    let _: syn::File = syn::parse2(output)?;
    Ok(())
}

#[test]
fn test_macro_call_raw_prefix_without_data() -> Result<(), syn::Error> {
    // Regression test for <https://github.com/askama-rs/askama/issues/475>.
    // The parser must reject wrong usage of raw prefixes.
    let input = quote! {
        #[template(ext = "", source = "{{ z!{r#} }}")]
        enum q {}
    };
    let output = derive_template(input, import_askama);
    assert!(
        output
            .to_string()
            .contains("prefix `r#` is only allowed with raw identifiers and raw strings")
    );
    let _: syn::File = syn::parse2(output)?;
    Ok(())
}

#[test]
fn test_macro_call_reserved_prefix() -> Result<(), syn::Error> {
    // The parser must reject reserved prefixes.
    let input = quote! {
        #[template(ext = "", source = "{{ z!{hello#world} }}")]
        enum q {}
    };
    let output = derive_template(input, import_askama);
    assert!(output.to_string().contains("reserved prefix `hello#`"));
    let _: syn::File = syn::parse2(output)?;
    Ok(())
}

#[test]
fn test_macro_call_valid_raw_cstring() -> Result<(), syn::Error> {
    // Regression test for <https://github.com/askama-rs/askama/issues/478>.
    // CString literals must not contain NULs.

    #[rustfmt::skip] // FIXME: rustfmt bug <https://github.com/rust-lang/rustfmt/issues/5489>
    let input = quote! {
        #[template(ext = "", source = "{{ c\"\0\" }}")]
//                                           ^^ NUL is not allowed in cstring literals
        enum l {}
    };
    let output = derive_template(input, import_askama);
    assert!(
        output
            .to_string()
            .contains("null characters in C string literals are not supported")
    );
    let _: syn::File = syn::parse2(output)?;
    Ok(())
}

#[test]
fn test_bare_cr_doc_comment() -> Result<(), syn::Error> {
    // Regression test for <https://issues.oss-fuzz.com/issues/431448399>.
    // Doc comment `///` must not contain bare CRs, except a CRLF to end the comment.

    #[rustfmt::skip] // FIXME: rustfmt bug <https://github.com/rust-lang/rustfmt/issues/5489>
    let input = quote! {
        #[template(ext = "", source = "{{ e!(/// \r \n) }}")]
//                                               ^^ CR not directly followed by LF
        enum l {}
    };
    let output = derive_template(input, import_askama);
    assert!(
        output
            .to_string()
            .contains("bare CR not allowed in doc comment")
    );
    let _: syn::File = syn::parse2(output)?;

    #[rustfmt::skip] // FIXME: rustfmt bug <https://github.com/rust-lang/rustfmt/issues/5489>
    let input = quote! {
        #[template(ext = "", source = "{{ e!(/** \r */) }}")]
//                                               ^^ CR not directly followed by LF
        enum l {}
    };
    let output = derive_template(input, import_askama);
    assert!(
        output
            .to_string()
            .contains("bare CR not allowed in doc comment")
    );
    let _: syn::File = syn::parse2(output)?;

    #[rustfmt::skip] // FIXME: rustfmt bug <https://github.com/rust-lang/rustfmt/issues/5489>
    let input = quote! {
        #[template(ext = "", source = "{{ e!(/// \r\n) }}")]
//                                               ^^^^ CR is directly followed by LF
        enum l {}
    };
    let output = derive_template(input, import_askama);
    assert!(!output.to_string().contains("compile_error"));
    let _: syn::File = syn::parse2(output)?;

    #[rustfmt::skip] // FIXME: rustfmt bug <https://github.com/rust-lang/rustfmt/issues/5489>
    let input = quote! {
        #[template(ext = "", source = "{{ e!(/** \r\n */) }}")]
//                                               ^^^^ CR is directly followed by LF
        enum l {}
    };
    let output = derive_template(input, import_askama);
    assert!(!output.to_string().contains("compile_error"));
    let _: syn::File = syn::parse2(output)?;

    Ok(())
}

#[test]
fn check_expr_ungrouping() {
    // In this test we ensure that superfluous parentheses around expressions are stripped before
    // handling the expression.

    compare(
        r#"{{ ("hello") }}"#,
        r#"__askama_writer.write_str("hello")?;"#,
        &[],
        5,
    );
    compare(
        r#"{{ ("hello") ~ " " ~ ("world") }}"#,
        r#"__askama_writer.write_str("hello world")?;"#,
        &[],
        11,
    );
    compare(
        r#"{{ ("hello") ~ (" " ~ ("world")) }}"#,
        r#"__askama_writer.write_str("hello world")?;"#,
        &[],
        11,
    );
    compare(
        r#"{{ ((((((((((("hello") ~ " ")))) ~ ((("world"))))))))) }}"#,
        r#"__askama_writer.write_str("hello world")?;"#,
        &[],
        11,
    );
}

#[test]
fn regression_tests_span_change() {
    // This test contains regression test for errors occurred during the big refactoring:
    // "Add a nightly feature which allows to manipulate spans to underline which part of the
    // template is failing compilation" <https://github.com/askama-rs/askama/issues/420>

    // Custom filters with and without generics.
    compare(
        "Hello, {{ user | cased }}!",
        r#"
            __askama_writer.write_str("Hello, ")?;
            match (
                &((&&askama::filters::AutoEscaper::new(
                &({
                    askama::filters::ValidFilterInvocation::wrap(
                            filters::cased::default(),
                        )
                        .execute(&(self.user), __askama_values)?
                }),
                    askama::filters::Text,
                ))
                    .askama_auto_escape()?),
            ) {
                (__askama_expr2,) => {
                    (&&&askama::filters::Writable(__askama_expr2))
                        .askama_write(__askama_writer, __askama_values)?;
                }
            }
            __askama_writer.write_str("!")?;
        "#,
        &[],
        11,
    );
    compare(
        "Hello, {{ user | cased::<> }}!",
        r#"
            __askama_writer.write_str("Hello, ")?;
            match (
                &((&&askama::filters::AutoEscaper::new(
                &({
                    askama::filters::ValidFilterInvocation::wrap(
                            filters::cased::default(),
                        )
                        .execute(&(self.user), __askama_values)?
                }),
                    askama::filters::Text,
                ))
                    .askama_auto_escape()?),
            ) {
                (__askama_expr2,) => {
                    (&&&askama::filters::Writable(__askama_expr2))
                        .askama_write(__askama_writer, __askama_values)?;
                }
            }
            __askama_writer.write_str("!")?;
        "#,
        &[],
        11,
    );

    let _ = build_template(&parse_quote! {
        #[template(source = "{{ \"x\" | ΔxΔyΔ }}", ext = "txt")]
        struct Foo;
    });
    let _ = build_template(&parse_quote! {
        #[template(source = r"{{ "x" | ΔxΔyΔ }}", ext = "txt")]
        struct Foo;
    });
    let _ = build_template(&parse_quote! {
        #[template(source = r#"{{ "x" | ΔxΔyΔ }}"#, ext = "txt")]
        struct Foo;
    });

    let _ = build_template(&parse_quote! {
        #[template(source = "{{ \"ΔxΔyΔ\" | x }}", ext = "txt")]
        struct Foo;
    });
    let _ = build_template(&parse_quote! {
        #[template(source = r"{{ "ΔxΔyΔ" | x }}", ext = "txt")]
        struct Foo;
    });
    let _ = build_template(&parse_quote! {
        #[template(source = r#"{{ "ΔxΔyΔ" | x }}"#, ext = "txt")]
        struct Foo;
    });
}

#[test]
fn test_compound_assignment() {
    for op in [
        "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
    ] {
        let jinja = r#"
            {%- let mut prefixsum = 0 -%}
            {%- for i in 0..limit -%}
                {%- mut prefixsum @= i -%}
                {{ prefixsum }}.
            {%- endfor -%}
        "#
        .replace("@=", op);

        let expected = r#"
            let mut prefixsum = 0;
            let __askama_iter = 0..self.limit;
            for (i, __askama_item) in askama::helpers::TemplateLoop::new(__askama_iter) {
                prefixsum @= i;
                match (
                    &((&&askama::filters::AutoEscaper::new(&(prefixsum), askama::filters::Text))
                        .askama_auto_escape()?),
                ) {
                    (__askama_expr0,) => {
                        (&&&askama::filters::Writable(__askama_expr0))
                            .askama_write(__askama_writer, __askama_values)?;
                    }
                }
                __askama_writer.write_str(".")?;
            }
        "#
        .replace("@=", op);

        compare(&jinja, &expected, &[("limit", "u32")], 6);
    }
}

#[test]
fn check_size_hint() {
    compare(
        r#"{% for _ in .. %} Hello {% break %} {% endfor %}"#,
        r#"
            let __askama_iter = ..;
            for (_, __askama_item) in askama::helpers::TemplateLoop::new(__askama_iter) {
                __askama_writer.write_str(" Hello ")?;
                break;
                __askama_writer.write_str(" ")?;
            }
        "#,
        &[],
        1,
    );
    compare(
        r#"{% for _ in .. %} Hello {% continue %} {% endfor %}"#,
        r#"
            let __askama_iter = ..;
            for (_, __askama_item) in askama::helpers::TemplateLoop::new(__askama_iter) {
                __askama_writer.write_str(" Hello ")?;
                continue;
                __askama_writer.write_str(" ")?;
            }
        "#,
        &[],
        1,
    );
}
