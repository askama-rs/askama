// The content of this file was copied and adapted from the project [`rustc-literal-escaper`] in
// revision [`425ca35`]. Please find the full list of contributors in [their revision history].
//
// License: Apache-2.0 OR MIT
// Authors: The Rust Project Developers, Guillaume Gomez, Marijn Schouten
//
// [`rustc-literal-escaper`]: <https://github.com/rust-lang/literal-escaper>
// [`425ca35`]: <https://github.com/rust-lang/literal-escaper/blob/425ca35a89d4ccb301bba7e2e59c5831bad0c303/src/lib.rs>
// [their revision history]: <https://github.com/rust-lang/literal-escaper/commits/425ca35a89d4ccb301bba7e2e59c5831bad0c303/src/lib.rs>

//! Utilities for validating (raw) string, char, and byte literals and
//! turning escape sequences into the values they represent.

use std::ops::Range;
use std::str::Chars;

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct EscapeError;

/// Unescape the first unit of a string (double quoted syntax)
fn unescape_1(chars: &mut Chars<'_>) -> Result<char, EscapeError> {
    // Previous character was '\\', unescape what follows.
    let c = chars.next().ok_or(EscapeError)?;
    if c == '0' {
        Ok('\0')
    } else {
        simple_escape(c).or_else(|c| match c {
            'x' => hex2unit(hex_escape(chars)?),
            'u' => {
                let value = unicode_escape(chars)?;
                if value > char::MAX as u32 {
                    Err(EscapeError)
                } else {
                    char::from_u32(value).ok_or(EscapeError)
                }
            }
            _ => Err(EscapeError),
        })
    }
}

/// Unescape a string literal
///
/// Takes the contents of a raw string literal (without quotes)
/// and produces a sequence of `Result<char, EscapeError>`
/// which are returned via `callback`.
pub(crate) fn unescape(
    src: &str,
    mut callback: impl FnMut(Range<usize>, char),
) -> Result<(), EscapeError> {
    let mut chars = src.chars();
    while let Some(c) = chars.next() {
        let start = src.len() - chars.as_str().len() - c.len_utf8();
        let res = match c {
            '\\' => {
                if let Some(b'\n') = chars.as_str().as_bytes().first() {
                    let _ = chars.next();
                    // skip whitespace for backslash newline, see [Rust language reference]
                    // (https://doc.rust-lang.org/reference/tokens.html#string-literals).
                    skip_ascii_whitespace(&mut chars)?;
                    continue;
                } else {
                    unescape_1(&mut chars)?
                }
            }
            '"' => return Err(EscapeError),
            '\r' => return Err(EscapeError),
            c => c,
        };
        let end = src.len() - chars.as_str().len();
        callback(start..end, res);
    }
    Ok(())
}

/// Interpret a non-nul ASCII escape
///
/// Parses the character of an ASCII escape (except nul) without the leading backslash.
#[inline] // single use in Unescape::unescape_1
fn simple_escape(c: char) -> Result<char, char> {
    // Previous character was '\\', unescape what follows.
    match c {
        '"' => Ok('"'),
        'n' => Ok('\n'),
        'r' => Ok('\r'),
        't' => Ok('\t'),
        '\\' => Ok('\\'),
        '\'' => Ok('\''),
        _ => Err(c),
    }
}

/// Interpret a hexadecimal escape
///
/// Parses the two hexadecimal characters of a hexadecimal escape without the leading r"\x".
#[inline] // single use in Unescape::unescape_1
fn hex_escape(chars: &mut impl Iterator<Item = char>) -> Result<u8, EscapeError> {
    let hi = chars.next().ok_or(EscapeError)?;
    let hi = hi.to_digit(16).ok_or(EscapeError)?;

    let lo = chars.next().ok_or(EscapeError)?;
    let lo = lo.to_digit(16).ok_or(EscapeError)?;

    Ok((hi * 16 + lo) as u8)
}

/// Interpret a unicode escape
///
/// Parse the braces with hexadecimal characters (and underscores) part of a unicode escape.
/// This r"{...}" normally comes after r"\u" and cannot start with an underscore.
#[inline] // single use in Unescape::unescape_1
fn unicode_escape(chars: &mut impl Iterator<Item = char>) -> Result<u32, EscapeError> {
    if chars.next() != Some('{') {
        return Err(EscapeError);
    }

    // First character must be a hexadecimal digit.
    let mut value: u32 = match chars.next().ok_or(EscapeError)? {
        '_' => return Err(EscapeError),
        '}' => return Err(EscapeError),
        c => c.to_digit(16).ok_or(EscapeError)?,
    };

    // First character is valid, now parse the rest of the number
    // and closing brace.
    let mut n_digits = 1;
    loop {
        match chars.next() {
            None => return Err(EscapeError),
            Some('_') => continue,
            Some('}') => {
                // Incorrect syntax has higher priority for error reporting
                // than unallowed value for a literal.
                return if n_digits > 6 {
                    Err(EscapeError)
                } else {
                    Ok(value)
                };
            }
            Some(c) => {
                let digit: u32 = c.to_digit(16).ok_or(EscapeError)?;
                n_digits += 1;
                if n_digits > 6 {
                    // Stop updating value since we're sure that it's incorrect already.
                    continue;
                }
                value = value * 16 + digit;
            }
        };
    }
}

/// Interpret a string continuation escape (https://doc.rust-lang.org/reference/expressions/literal-expr.html#string-continuation-escapes)
///
/// Skip ASCII whitespace, except for the formfeed character
/// (see [this issue](https://github.com/rust-lang/rust/issues/136600)).
/// Warns on unescaped newline and following non-ASCII whitespace.
#[inline] // single use in Unescape::unescape
fn skip_ascii_whitespace(chars: &mut Chars<'_>) -> Result<(), EscapeError> {
    let rest = chars.as_str();
    let first_non_space = rest
        .bytes()
        .position(|b| b != b' ' && b != b'\t' && b != b'\n' && b != b'\r')
        .unwrap_or(rest.len());
    let (space, rest) = rest.split_at(first_non_space);
    if space.contains('\n') {
        return Err(EscapeError);
    }
    *chars = rest.chars();
    if let Some(c) = chars.clone().next()
        && c.is_whitespace()
    {
        return Err(EscapeError);
    }
    Ok(())
}

#[inline]
fn hex2unit(b: u8) -> Result<char, EscapeError> {
    if b.is_ascii() {
        Ok(b as char)
    } else {
        Err(EscapeError)
    }
}
