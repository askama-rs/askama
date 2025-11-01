//! Module for built-in filter functions
//!
//! Contains all the built-in filter functions for use in templates.
//! You can define your own filters, as well.
//!
//! ## Note
//!
//! All **result types of any filter function** in this module is **subject to change** at any
//! point, and is **not indicated by as semver breaking** version bump.
//! The traits [`AutoEscape`] and [`WriteWritable`] are used by [`askama_macros`]'s generated code
//! to work with all compatible types.

#[cfg(feature = "alloc")]
mod alloc;
mod core;
mod default;
mod escape;
mod humansize;
mod indent;
#[cfg(feature = "serde_json")]
mod json;
#[cfg(feature = "std")]
mod std;
#[cfg(feature = "urlencode")]
mod urlencode;

#[cfg(feature = "alloc")]
pub use self::alloc::{
    capitalize, fmt, format, lower, lowercase, title, titlecase, trim, upper, uppercase,
};
pub use self::core::{
    Either, PluralizeCount, center, join, linebreaks, linebreaksbr, paragraphbreaks, pluralize,
    reject, reject_with, truncate, wordcount,
};
pub use self::default::{DefaultFilterable, assigned_or};
pub use self::escape::{
    AutoEscape, AutoEscaper, Escaper, Html, HtmlSafe, HtmlSafeOutput, MaybeSafe, Safe, Text,
    Unsafe, Writable, WriteWritable, e, escape, safe,
};
pub use self::humansize::filesizeformat;
pub use self::indent::{AsIndent, indent};
#[cfg(feature = "serde_json")]
pub use self::json::{json, json_pretty};
#[cfg(feature = "std")]
pub use self::std::unique;
#[cfg(feature = "urlencode")]
pub use self::urlencode::{urlencode, urlencode_strict};

// MAX_LEN is maximum allowed length for filters.
const MAX_LEN: usize = 10_000;

/// Internal trait that is used by the `filter_fn` proc-macro to produce nicer error messages when
/// too many arguments were passed to a filter invocation.
#[doc(hidden)]
#[diagnostic::on_unimplemented(
    message = "Argument at position {IDX} is invalid on filter {Self}. Too many arguments supplied?",
    label = "Filter function"
)]
pub trait ValidArgIdx<const IDX: usize> {
    const VALID: bool = true;
}

/// Internal marker trait that is used by the `filter_fn` proc-macro to produce nicer error messages
/// too few arguments were passed to a filter invocation.
#[doc(hidden)]
#[diagnostic::on_unimplemented(
    message = "Invalid filter function invocation. Not all required arguments were supplied.",
    label = "Filter function"
)]
pub trait ValidFilterInvocation: Sized {
    #[inline(always)]
    fn wrap(self) -> Self {
        self
    }
}
