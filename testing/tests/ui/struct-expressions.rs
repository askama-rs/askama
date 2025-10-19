#![allow(unused_variables)]

use askama::Template;

#[derive(Template)]
#[template(
    source = r#"{{ InnerCell { ..Default::default(), other: 24 } }}"#,
    ext = "txt"
)]
struct OuterTemplate1;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { }}"#, ext = "txt")]
struct OuterTemplate2;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo: } }}"#, ext = "txt")]
struct OuterTemplate3;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { foo: 32, .. } }}"#, ext = "txt")]
struct OuterTemplate4;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { . } }}"#, ext = "txt")]
struct OuterTemplate5;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { , } }}"#, ext = "txt")]
struct OuterTemplate6;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { ..Default::default(): 32 } }}"#, ext = "txt")]
struct OuterTemplate7;

#[derive(Template)]
#[template(source = r#"some{{ InnerCell { ..Default::default(), a: 12 } }}"#, ext = "txt")]
struct OuterTemplate8;

fn main() {}
