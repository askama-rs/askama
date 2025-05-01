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
    DefaultFilterable, Either, PluralizeCount, assigned_or, center, join, linebreaks, linebreaksbr,
    paragraphbreaks, pluralize, reject, reject_with, truncate, wordcount,
};
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
