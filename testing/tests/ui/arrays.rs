use askama::Template;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b %}"#, ext = "html")]
struct MissingClosing1;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b, %}"#, ext = "html")]
struct MissingClosing2;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b @ %}"#, ext = "html")]
struct MissingClosing3;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b, @ %}"#, ext = "html")]
struct MissingClosing4;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b; c] %}"#, ext = "html")]
struct TooManyExprs1;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b, ; c] %}"#, ext = "html")]
struct TooManyExprs2;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b, c; d] %}"#, ext = "html")]
struct TooManyExprs3;

#[derive(Template)]
#[template(source = r#"{% let x = [,] %}"#, ext = "html")]
struct StayComma1;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b,,] %}"#, ext = "html")]
struct StayComma2;

#[derive(Template)]
#[template(source = r#"{% let x = [a, ; b] %}"#, ext = "html")]
struct StayComma3;

#[derive(Template)]
#[template(source = r#"{% let x = [a; b,] %}"#, ext = "html")]
struct StayComma4;

#[derive(Template)]
#[template(source = r#"{% let x = [a; b, c] %}"#, ext = "html")]
struct MultiDimensional1;

#[derive(Template)]
#[template(source = r#"{% let x = [a; b; c] %}"#, ext = "html")]
struct MultiDimensional2;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b) %}"#, ext = "html")]
struct WrongClosing1;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b} %}"#, ext = "html")]
struct WrongClosing2;

#[derive(Template)]
#[template(source = r#"{% let x = [a, b> %}"#, ext = "html")]
struct WrongClosing3;

#[derive(Template)]
#[template(source = r#"{% let x = [a; b) %}"#, ext = "html")]
struct WrongClosing4;

#[derive(Template)]
#[template(source = r#"{% let x = [a; b} %}"#, ext = "html")]
struct WrongClosing5;

#[derive(Template)]
#[template(source = r#"{% let x = [a; b> %}"#, ext = "html")]
struct WrongClosing6;

fn main() {}
