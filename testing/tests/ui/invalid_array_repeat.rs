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

fn main() {}
