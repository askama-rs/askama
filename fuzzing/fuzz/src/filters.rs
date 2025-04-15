use std::fmt;

use arbitrary::{Arbitrary, Unstructured};
use askama::filters::{self, AsIndent};

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Scenario<'a> {
    Text(Text<'a>),
}

impl<'a> super::Scenario<'a> for Scenario<'a> {
    type RunError = askama::Error;

    fn new(data: &'a [u8]) -> Result<Self, arbitrary::Error> {
        Self::arbitrary_take_rest(Unstructured::new(data))
    }

    fn run(&self) -> Result<(), Self::RunError> {
        match *self {
            Self::Text(text) => run_text(text),
        }
    }
}

fn run_text(filter: Text<'_>) -> Result<(), askama::Error> {
    let Text { input, filter } = filter;
    let _ = match filter {
        TextFilter::Capitalize => filters::capitalize(input)?.to_string(),
        TextFilter::Center(a) => filters::center(input, a)?.to_string(),
        TextFilter::Indent {
            prefix,
            first,
            blank,
        } => filters::indent(input, prefix, first, blank)?.to_string(),
        TextFilter::Linebreaks => filters::linebreaks(input)?.to_string(),
        TextFilter::LinebreaksBr => filters::linebreaksbr(input)?.to_string(),
        TextFilter::Lowercase => filters::lowercase(input)?.to_string(),
        TextFilter::ParagraphBreaks => filters::paragraphbreaks(input)?.to_string(),
        TextFilter::Safe(e) => match e {
            Escaper::Html => filters::safe(input, filters::Html)?.to_string(),
            Escaper::Text => filters::safe(input, filters::Text)?.to_string(),
        },
        TextFilter::Title => filters::title(input)?.to_string(),
        TextFilter::Trim => filters::trim(input)?.to_string(),
        TextFilter::Truncate(a) => filters::truncate(input, a)?.to_string(),
        TextFilter::Uppercase => filters::uppercase(input)?.to_string(),
        TextFilter::Urlencode => filters::urlencode(input)?.to_string(),
        TextFilter::UrlencodeStrict => filters::urlencode_strict(input)?.to_string(),
    };
    Ok(())
}

impl fmt::Display for Scenario<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Scenario::Text(Text { input, filter }) = self;
        let text = match filter {
            TextFilter::Capitalize => format!("capitalize({input:?})"),
            TextFilter::Center(a) => format!("center({input:?}, {a:?})"),
            TextFilter::Indent {
                prefix,
                first,
                blank,
            } => {
                format!("indent({input:?}, {prefix}, {first:?}, {blank:?})")
            }
            TextFilter::Linebreaks => format!("linebreaks({input:?})"),
            TextFilter::LinebreaksBr => format!("linebreaksbr({input:?})"),
            TextFilter::Lowercase => format!("lowercase({input:?})"),
            TextFilter::ParagraphBreaks => format!("paragraphbreaks({input:?})"),
            TextFilter::Safe(e) => match e {
                Escaper::Html => format!("safe({input:?}, filters::Html)"),
                Escaper::Text => format!("safe({input:?}, filters::Text)"),
            },
            TextFilter::Title => format!("title({input:?})"),
            TextFilter::Trim => format!("trim({input:?})"),
            TextFilter::Truncate(a) => format!("truncate({input:?}, {a:?})"),
            TextFilter::Uppercase => format!("uppercase({input:?})"),
            TextFilter::Urlencode => format!("urlencode({input:?})"),
            TextFilter::UrlencodeStrict => format!("urlencode_strict({input:?})"),
        };
        write!(
            f,
            "\
use askama::filters;

#[test]
fn test() {{
    let _: String = filters::{text}?.to_string();
}}\
            ",
        )
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub struct Text<'a> {
    input: &'a str,
    filter: TextFilter<'a>,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum TextFilter<'a> {
    Capitalize,
    Center(usize),
    Indent {
        prefix: Prefix<'a>,
        first: bool,
        blank: bool,
    },
    Linebreaks,
    LinebreaksBr,
    Lowercase,
    ParagraphBreaks,
    Safe(Escaper),
    Title,
    Trim,
    Truncate(usize),
    Uppercase,
    Urlencode,
    UrlencodeStrict,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum Prefix<'a> {
    Width(usize),
    Prefix(&'a str),
}

impl std::fmt::Display for Prefix<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prefix::Width(v) => write!(f, "{v:?}"),
            Prefix::Prefix(v) => write!(f, "{v:?}"),
        }
    }
}

impl AsIndent for Prefix<'_> {
    fn as_indent(&self) -> &str {
        match self {
            Prefix::Width(v) => v.as_indent(),
            Prefix::Prefix(v) => v.as_indent(),
        }
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum Escaper {
    Html,
    Text,
}

// TODO:
// abs
// escape,
// filesizeformat
// fmt
// format
// into_f64
// into_isize
// join
// json
// json_pretty
// wordcount
