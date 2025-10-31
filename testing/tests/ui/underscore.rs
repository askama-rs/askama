use askama::Template;

#[derive(Template)]
#[template(source = r#"{% let x = [_] %}"#, ext = "html")]
struct UnderscoreErr1;

#[derive(Template)]
#[template(source = r#"{% if (_ + 12) != 0 %}{% endif %}"#, ext = "html")]
struct UnderscoreErr2;

#[derive(Template)]
#[template(source = r#"{% if 12 == _ %}{% endif %}"#, ext = "html")]
struct UnderscoreErr3;

#[derive(Template)]
#[template(source = r#"{% match _ %}{% endmatch %}"#, ext = "html")]
struct UnderscoreErr4;

#[derive(Template)]
#[template(source = r#"{% let _ %}"#, ext = "html")]
struct UnderscoreErr5;

#[derive(Template)]
#[template(source = r#"{% decl _ %}"#, ext = "html")]
struct UnderscoreErr6;

#[derive(Template)]
#[template(source = r#"{% declare _ %}"#, ext = "html")]
struct UnderscoreErr7;

fn main() {}
