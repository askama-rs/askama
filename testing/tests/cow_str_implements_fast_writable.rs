use std::borrow::Cow;
use askama::{FastWritable, Template};

//This tests, that Cow<'_, str> implements FastWritable.
//If it didn't, compiling the tests would fail.
//
//Since this test fails at compile-time, there isn't actually any need to run it.
#[allow(dead_code)]
fn cow_str_fast_writable(){
    #[derive(Template)]
    #[template(source = "{{content|safe}}", ext="txt")]
    //Todo: need to explicitly mark content as |safe?
    //error[E0599]: the method `askama_auto_escape` exists for reference `&&AutoEscaper<'_, T, Text>`, but its trait bounds were not satisfied
    //  --> testing/tests/cow_str_implements_fast_writable.rs:9:14
    //   |
    // 9 |     #[derive(Template)]
    //   |              ^^^^^^^^ method cannot be called on `&&AutoEscaper<'_, T, Text>` due to unsatisfied trait bounds
    //   |
    //   = note: the following trait bounds were not satisfied:
    //           `T: std::fmt::Display`
    //           which is required by `&&AutoEscaper<'_, T, Text>: AutoEscape`
    //   = note: this error originates in the derive macro `Template` (in Nightly builds, run with -Z macro-backtrace for more info)
    pub struct Test<T: FastWritable> {
        pub content: T,
    }

    Test{
        content: Cow::Borrowed("")
    }.render()
        .unwrap();
}
