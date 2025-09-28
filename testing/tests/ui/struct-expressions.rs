#![allow(unused_variables)]

use askama::Template;

#[derive(Default)]
pub struct InnerCell {
    pub number: u32,
    pub other: u32,
}
impl std::fmt::Display for InnerCell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Hello, {} and {}!", self.number, self.other)
    }
}

#[derive(Template)]
#[template(
    source = r#"{{ InnerCell { ..Default::default(), other: 24 } }}"#,
    ext = "txt"
)]
struct OuterTemplate1;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { }}thing"#, ext = "txt")]
struct OuterTemplate2;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo }}thing"#, ext = "txt")]
struct OuterTemplate3;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo: }}thing"#, ext = "txt")]
struct OuterTemplate4;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo: 32 }}thing"#, ext = "txt")]
struct OuterTemplate5;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo: 32, }}thing"#, ext = "txt")]
struct OuterTemplate6;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo: 32, .. }}thing"#, ext = "txt")]
struct OuterTemplate7;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo: 32, ..Default::Default }}thing"#, ext = "txt")]
struct OuterTemplate8;

fn main() {}
