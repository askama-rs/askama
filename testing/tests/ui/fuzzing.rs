// Test file specifically for parser bugs uncovered with fuzzing.

use askama::Template;

#[test]
fn test_fuzz_1() {
    #[derive(Template)]
    #[template(
        source = r#"{{..{Ւ{"#,
        ext = "html",
    )]
    struct T;
}
