// This example contains a custom filter `|cased`.
// Depending on the runtime value `"case"`, the input is either turned
// into lower case, upper case, or left alone, if the runtime value is undefined.

use std::any::Any;

use askama::{Template, Values};

mod filters {
    use super::*;

    #[askama::filter_fn]
    pub fn cased(value: impl ToString, values: &dyn Values) -> askama::Result<String> {
        let value = value.to_string();
        let case = askama::get_value(values, "case").ok();
        Ok(match case {
            Some(Case::Lower) => value.to_lowercase(),
            Some(Case::Upper) => value.to_uppercase(),
            None => value,
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Case {
    Lower,
    Upper,
}

#[test]
fn test_runtime_values_in_custom_filters() {
    #[derive(Template)]
    #[template(ext = "txt", source = "Hello, {{ user | cased }}!")]
    struct MyStruct<'a> {
        user: &'a str,
    }

    // The filter source ("wOrLd") should be written in lower case.
    let values: (&str, &dyn Any) = ("case", &Case::Lower);
    assert_eq!(
        MyStruct { user: "wOrLd" }
            .render_with_values(&values)
            .unwrap(),
        "Hello, world!"
    );

    // The filter source ("wOrLd") should be written in upper case.
    let values: (&str, &dyn Any) = ("case", &Case::Upper);
    assert_eq!(
        MyStruct { user: "wOrLd" }
            .render_with_values(&values)
            .unwrap(),
        "Hello, WORLD!"
    );

    // The filter source ("wOrLd") should be written as is.
    assert_eq!(
        MyStruct { user: "wOrLd" }.render().unwrap(),
        "Hello, wOrLd!"
    );
}
