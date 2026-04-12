// This test (coupled with `testing/tests/print.rs`) ensures that `print = "..."`
// works as expected.

use askama::Template;

#[derive(Template)]
#[template(source = r#"{% let x = 12 %}{{x}}"#, ext = "txt", print = "all")]
struct PrintAll;

#[derive(Template)]
#[template(source = r#"{% let x = 12 %}{{x}}"#, ext = "txt", print = "ast")]
struct PrintAst;

#[derive(Template)]
#[template(source = r#"{% let x = 12 %}{{x}}"#, ext = "txt", print = "code")]
struct PrintCode;
