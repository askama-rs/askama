use askama::Template;

#[derive(Template)]
#[template(
    source = r#"{% for v in values %}{{ loop.cycle([]) }}{{ v }},{% endfor %}"#,
    ext = "txt"
)]
struct ForCycleEmpty;

#[derive(Template)]
#[template(
    source = r#"{% for v in values %}{{ loop.cycle::<u8>([]) }}{{ v }},{% endfor %}"#,
    ext = "txt"
)]
struct ForCycleGenerics;

fn main() {
}
