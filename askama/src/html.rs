// The file is shared across many crates, not all have this feature.
// If they don't then the tests won't be compiled in, but that's OK, because they are executed at
// least in the crate `askama`. There's no need to run the test multiple times.
#![allow(unexpected_cfgs)]

use core::{fmt, str};

use crate::ascii_str::{AsciiChar, AsciiStr};

#[allow(unused)]
pub(crate) fn write_escaped_str(mut dest: impl fmt::Write, src: &str) -> fmt::Result {
    let mut escaped_buf = ESCAPED_BUF_INIT;
    let mut last = 0;
    let mut escape_byte = |index: usize, byte: u8| -> fmt::Result {
        if let Some(escaped) = get_escaped(byte) {
            [escaped_buf[2], escaped_buf[3]] = escaped;
            write_str_if_nonempty(&mut dest, &src[last..index])?;
            dest.write_str(AsciiStr::from_slice(&escaped_buf[..ESCAPED_BUF_LEN]))?;
            last = index + 1;
        }
        Ok(())
    };

    // Most text needs no escaping at all, so a whole word is tested at a time for as long as
    // there is one, and only the few bytes that are left after it one by one.
    let (words, tail) = src.as_bytes().as_chunks();
    for (word_index, word) in words.iter().enumerate() {
        let mut found = find_escaped(u64::from_le_bytes(*word));
        while found != 0 {
            let index = found.trailing_zeros() as usize / 8;
            escape_byte(word_index * WORD_LEN + index, word[index])?;
            found &= found - 1;
        }
    }
    for (index, &byte) in (words.len() * WORD_LEN..).zip(tail) {
        escape_byte(index, byte)?;
    }
    write_str_if_nonempty(&mut dest, &src[last..])
}

const WORD_LEN: usize = size_of::<u64>();

/// Sets the highest bit of every byte in `word` that needs HTML escaping.
#[inline]
fn find_escaped(word: u64) -> u64 {
    const LOW: u64 = u64::from_ne_bytes([0x7f; WORD_LEN]);
    const HIGH: u64 = u64::from_ne_bytes([0x80; WORD_LEN]);

    let mut found = 0;
    let mut i = 0;
    while i < CHARS.len() {
        // A byte in `diff` is zero iff it is `CHARS[i]` in `word`. Adding `0x7f` to its lower
        // seven bits cannot carry into the next byte, and leaves the highest bit unset only if
        // they were all zero.
        let diff = word ^ u64::from_ne_bytes([CHARS[i]; WORD_LEN]);
        found |= !(((diff & LOW) + LOW) | diff);
        i += 1;
    }
    found & HIGH
}

#[allow(unused)]
pub(crate) fn write_escaped_char(mut dest: impl fmt::Write, c: char) -> fmt::Result {
    if !c.is_ascii() {
        dest.write_char(c)
    } else if let Some(escaped) = get_escaped(c as u8) {
        let mut escaped_buf = ESCAPED_BUF_INIT;
        [escaped_buf[2], escaped_buf[3]] = escaped;
        dest.write_str(AsciiStr::from_slice(&escaped_buf[..ESCAPED_BUF_LEN]))
    } else {
        // RATIONALE: `write_char(c)` gets optimized if it is known that `c.is_ascii()`
        dest.write_char(c)
    }
}

/// Returns the decimal representation of the codepoint if the character needs HTML escaping.
#[inline]
fn get_escaped(byte: u8) -> Option<[AsciiChar; 2]> {
    if let MIN_CHAR..=MAX_CHAR = byte {
        let entry = TABLE.0[(byte - MIN_CHAR) as usize];
        (entry != UNESCAPED).then_some(entry)
    } else {
        None
    }
}

#[inline(always)]
fn write_str_if_nonempty(output: &mut impl fmt::Write, input: &str) -> fmt::Result {
    if !input.is_empty() {
        output.write_str(input)
    } else {
        Ok(())
    }
}

/// List of characters that need HTML escaping, not necessarily in ordinal order.
const CHARS: &[u8] = br#""&'<>"#;

/// The character with the lowest codepoint that needs HTML escaping.
const MIN_CHAR: u8 = {
    let mut v = u8::MAX;
    let mut i = 0;
    while i < CHARS.len() {
        if v > CHARS[i] {
            v = CHARS[i];
        }
        i += 1;
    }
    v
};

/// The character with the highest codepoint that needs HTML escaping.
const MAX_CHAR: u8 = {
    let mut v = u8::MIN;
    let mut i = 0;
    while i < CHARS.len() {
        if v < CHARS[i] {
            v = CHARS[i];
        }
        i += 1;
    }
    v
};

/// Number of codepoints between the lowest and highest character that needs escaping, incl.
const CHAR_RANGE: usize = (MAX_CHAR - MIN_CHAR + 1) as usize;

#[repr(align(64))]
struct Table([[AsciiChar; 2]; CHAR_RANGE]);

/// For characters that need HTML escaping, the codepoint is formatted as decimal digits,
/// otherwise `b"\0\0"`. Starting at [`MIN_CHAR`].
const TABLE: &Table = &{
    let mut table = Table([UNESCAPED; CHAR_RANGE]);
    let mut i = 0;
    while i < CHARS.len() {
        let c = CHARS[i];
        table.0[c as u32 as usize - MIN_CHAR as usize] = AsciiChar::two_digits(c as u32);
        i += 1;
    }
    table
};

const UNESCAPED: [AsciiChar; 2] = AsciiStr::new_sized("");

const ESCAPED_BUF_INIT_UNPADDED: &str = "&#__;";
// RATIONALE: llvm generates better code if the buffer is register sized
const ESCAPED_BUF_INIT: [AsciiChar; 8] = AsciiStr::new_sized(ESCAPED_BUF_INIT_UNPADDED);
const ESCAPED_BUF_LEN: usize = ESCAPED_BUF_INIT_UNPADDED.len();

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use super::*;

    #[test]
    #[cfg(feature = "alloc")]
    fn test_simple_html_string_escaping() {
        extern crate alloc;

        let mut buf = alloc::string::String::new();
        write_escaped_str(&mut buf, "<script>").unwrap();
        assert_eq!(buf, "&#60;script&#62;");

        buf.clear();
        write_escaped_str(&mut buf, "s<crip>t").unwrap();
        assert_eq!(buf, "s&#60;crip&#62;t");

        buf.clear();
        write_escaped_str(&mut buf, "s<cripcripcripcripcripcripcripcripcripcrip>t").unwrap();
        assert_eq!(buf, "s&#60;cripcripcripcripcripcripcripcripcripcrip&#62;t");
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_html_string_escaping_at_every_offset() {
        extern crate alloc;

        use alloc::string::String;
        use alloc::vec::Vec;

        struct Chunks(Vec<String>);

        impl fmt::Write for Chunks {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                self.0.push(s.into());
                Ok(())
            }
        }

        // One chunk for every run of text that needs no escaping, and one for every escaped char.
        fn expected(src: &str) -> Vec<String> {
            let mut chunks = Vec::new();
            let mut run = String::new();
            for c in src.chars() {
                if CHARS.contains(&(c as u32).try_into().unwrap_or(0)) {
                    if !run.is_empty() {
                        chunks.push(core::mem::take(&mut run));
                    }
                    chunks.push(alloc::format!("&#{};", c as u32));
                } else {
                    run.push(c);
                }
            }
            if !run.is_empty() {
                chunks.push(run);
            }
            chunks
        }

        // The chars to escape, their neighbors, and chars that contain the same bytes but for
        // the highest bit: `'\u{a2}'` is `[0xc2, b'"' | 0x80]`.
        const ALPHABET: &[char] = &[
            '"', '&', '\'', '<', '>', '!', '#', '%', '(', ';', '=', '?', '\0', '\u{7f}', '\u{a2}',
            '\u{a6}', '\u{bc}', '\u{be}', '€', '🦀',
        ];

        for len in 0..=2 * WORD_LEN + 1 {
            for first in 0..len {
                for second in first..len {
                    for &a in ALPHABET {
                        for &b in ALPHABET {
                            let src: String = (0..len)
                                .map(|i| match i {
                                    _ if i == second => b,
                                    _ if i == first => a,
                                    _ => 'x',
                                })
                                .collect();
                            let mut chunks = Chunks(Vec::new());
                            write_escaped_str(&mut chunks, &src).unwrap();
                            assert_eq!(chunks.0, expected(&src), "{src:?}");
                        }
                    }
                }
            }
        }
    }
}
