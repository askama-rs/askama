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

// The child's block is at its top level, but the parent places it inside an `if`.
#[derive(Template)]
#[template(
    ext = "html",
    source = r#"{% include "include-block-nested-child.html" block list %}"#
)]
struct NestedInParentIf;

fn main() {
}
