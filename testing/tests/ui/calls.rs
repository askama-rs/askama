use askama::Template;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call( }}"#)]
struct UnclosedCall1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(a }}"#)]
struct UnclosedCall2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(a, }}"#)]
struct UnclosedCall3;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(a, b }}"#)]
struct UnclosedCall4;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(a, b, }}"#)]
struct UnclosedCall5;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(,) }}"#)]
struct CommaWithoutAnyArguments1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(, a) }}"#)]
struct CommaWithoutAnyArguments2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(, a,) }}"#)]
struct CommaWithoutAnyArguments3;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(, a, }}"#)]
struct CommaWithoutAnyArguments4;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(a,,) }}"#)]
struct MultipleCommas1;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(a,, b,) }}"#)]
struct MultipleCommas2;

#[derive(Template)]
#[template(ext = "txt", source = r#"{{ call(a, b,,) }}"#)]
struct MultipleCommas3;

fn main() {}
