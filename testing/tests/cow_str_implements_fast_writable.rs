use std::borrow::Cow;
use std::fmt::Display;

use askama::{FastWritable, Template};

// This tests, that Cow<'_, str> implements FastWritable.
// If it didn't, compiling the tests would fail.
const _: () = {
    #[derive(Template)]
    #[template(source = "{{content|safe}}", ext = "txt")]
    pub struct Test<T: FastWritable + Display> {
        pub content: T,
    }

    Test {
        content: Cow::Borrowed(""),
    };
};
