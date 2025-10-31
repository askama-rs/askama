// Test file specifically for parser bugs uncovered with fuzzing.

use askama::Template;

#[derive(Template)]
#[template(
    source = r#"{{..{Ւ{"#,
    ext = "html",
)]
struct T;

fn main() {}
