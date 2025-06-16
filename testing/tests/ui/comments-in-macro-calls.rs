use askama::Template;

// Regression test for <https://issues.oss-fuzz.com/issues/425145246>.

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(// hello) }}")]
struct LineComment;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(// hello)\n}}")]
struct LineComment2;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(/* hello) }}")]
struct BlockComment;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(/// hello) }}")]
struct OuterLineDoc;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(/// hello)\n}}")]
struct OuterLineDoc2;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(/** hello) }}")]
struct OuterBlockDoc;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(//! hello) }}")]
struct InnerLineDoc;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(//! hello)\n}}")]
struct InnerLineDoc2;

#[derive(Template)]
#[template(ext = "html", source = "{{ e!(/*! hello) }}")]
struct InnerBlockDoc;

fn main() {}
