// Check that `mut` can only be used with a variable name (not destructuring).

use askama::Template;

#[derive(Template)]
#[template(source = r#"
{% let mut (a, b) = (1, 2) %}
"#, ext = "html")]
struct Var1;

#[derive(Template)]
#[template(source = r#"
{% let mut [a, b] = [1, 2] %}
"#, ext = "html")]
struct Var2;

#[derive(Template)]
#[template(source = r#"
{% let mut Some(a) = Some("a") %}
"#, ext = "html")]
struct Var3;

fn main() {}
