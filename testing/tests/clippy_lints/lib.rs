#![deny(clippy::elidable_lifetime_names)]
#![deny(clippy::all)]

// FIXME: This is expected, however the span is wrong.
// #![deny(clippy::unnecessary_wraps)]

// https://github.com/askama-rs/askama/issues/651
// // Checks that `clippy:unnecessary_wraps` is not triggered.
// pub mod unnecessary_wraps {
//     mod filters {
//         use std::fmt::Display;

//         #[askama::filter_fn]
//         pub fn simple(value: impl Display, _env: &dyn askama::Values) -> askama::Result<String> {
//             Ok(value.to_string())
//         }
//     }

//     #[derive(askama::Template)]
//     #[template(source = r#"{{ "foo" | simple }}"#, ext = "txt")]
//     struct Foo<'a> {
//         _bar: &'a (),
//     }
// }

// Checks that `clippy::elidable_lifetime_names` is not triggered.
pub mod elidable_lifetime_names {
    #[derive(Debug, askama::Template)]
    #[template(source = "", ext = "txt")]
    struct Test<'a> {
        _data: &'a (),
    }
}
