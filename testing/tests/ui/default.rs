use std::sync::Mutex;

use askama::Template;

#[derive(Template)]
#[template(ext = "html", source = "{{ (1 + 1) | default(2) }}")]
struct DefaultLhsExpr;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default }}")]
struct DefaultNoDefaultValue;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default(boolean = true) }}")]
struct DefaultNoDefaultValue2;

#[derive(Template)]
#[template(ext = "html", source = "{{ value | default(2, true) }}")]
struct DefaultNotUnwrappable {
    value: Mutex<u32>,
}

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default(1, 2) }}")]
struct DefaultNotABool;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | default(1, boolean = 2) }}")]
struct DefaultNotABool2;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | assigned_or }}")]
struct AssignedOrNoDefaultValue;

#[derive(Template)]
#[template(ext = "html", source = "{{ (1 + 1) | defined_or(2) }}")]
struct DefinedOrLhsExpr;

#[derive(Template)]
#[template(ext = "html", source = "{{ var | defined_or }}")]
struct DefinedOrNoDefaultValue;

fn main() {}
