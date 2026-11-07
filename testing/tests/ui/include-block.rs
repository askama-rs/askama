use askama::Template;

#[derive(Template)]
#[template(
    ext = "html",
    source = r#"{% include "fragment-simple.html" block missing %}"#
)]
struct UnknownBlock;

#[derive(Template)]
#[template(ext = "html", source = r#"{% include "included.html" block a %}"#)]
struct NoBlocks;

#[derive(Template)]
#[template(
    ext = "html",
    source = r#"{% include "include-block-nested.html" block list %}"#
)]
struct NestedInIf;

fn main() {
}
