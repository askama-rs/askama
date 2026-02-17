use askama::Template;

#[derive(Template)]
#[template(source = r#"{% let my_arr = [;] %}"#, ext = "txt")]
struct Empty;

#[derive(Template)]
#[template(source = r#"{% let my_arr = [;0] %}"#, ext = "txt")]
struct EmptyElement;

#[derive(Template)]
#[template(source = r#"{% let my_arr = ["";] %}"#, ext = "txt")]
struct EmptyCount;

#[derive(Template)]
#[template(source = r#"{% let my_arr = [,;] %}"#, ext = "txt")]
struct StrayElementComma;

#[derive(Template)]
#[template(source = r#"{% let my_arr = [; 10, 10] %}"#, ext = "txt")]
struct StrayCountComma;

#[derive(Template)]
#[template(source = r#"{% let my_arr = [,;,] %}"#, ext = "txt")]
struct StrayCommas;

#[derive(Template)]
#[template(source = r#"{% let my_arr = ["";10;10] %}"#, ext = "txt")]
struct MultipleSemicolons;

#[derive(Template)]
#[template(
    source = r#"{{ [[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[ }}"#,
    ext = "txt"
)]
struct RecursionLimit;

// This one ensures that the parser isn't taking forever to fail.
#[derive(Template)]
#[template(
    source = r#"{{[[[[[[[[[[[[[[[[[[[[[(D,_);2];2];2];2];2];2];2];2];2];2];2];2];2];2];2];2];2];2];X];N]"#,
    ext = "txt"
)]
struct FromFuzz;

fn main() {}
