use std::sync::Mutex;

use askama::Template;

#[derive(Template)]
#[template(ext = "html", source = "{{ (1 + 1) | default(2) }}")]
struct LhsExpr;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default }}")]
struct NoDefaultValue;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default(boolean = true) }}")]
struct NoDefaultValue2;

#[derive(Template)]
#[template(ext = "html", source = "{{ value | default(2, true) }}")]
struct NotUnwrappable {
    value: Mutex<u32>,
}

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default(1, 2) }}")]
struct NotABool;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default(1, boolean = 2) }}")]
struct NotABool2;

fn main() {
}
