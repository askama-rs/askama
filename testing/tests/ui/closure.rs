use askama::Template;

#[derive(Template)]
#[template(source = "{{ value|apply(|| 1) }}", ext = "txt")]
pub struct NoParameter {
    value: u32,
}

#[derive(Template)]
#[template(source = "{{ value|apply(|a|) }}", ext = "txt")]
pub struct NoBody {
    value: u32,
}

#[derive(Template)]
#[template(source = "{{ value|apply(|Self| 1) }}", ext = "txt")]
pub struct ReservedParameter {
    value: u32,
}

#[derive(Template)]
#[template(source = "{{ value|apply(|a| a|lower) }}", ext = "txt")]
pub struct FilterInBody {
    value: u32,
}

#[derive(Template)]
#[template(source = "{{ value|apply(|a| a.parse()?) }}", ext = "txt")]
pub struct TryInBody {
    value: u32,
}

fn main() {}
