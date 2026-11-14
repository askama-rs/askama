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
    source = r#"{% include "include-block-loop.html" block item %}"#
)]
struct NestedInFor;

#[derive(Template)]
#[template(
    ext = "html",
    source = r#"{% include "include-block-loop-child.html" block inner %}"#
)]
struct ParentNestedInFor;

fn main() {
}
