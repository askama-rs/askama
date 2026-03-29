use askama::Template;

#[derive(Template)]
#[template(source = "{{ f::<&[u32 }}", ext = "txt")]
struct Array1;

#[derive(Template)]
#[template(source = "{{ f::<&[u32> }}", ext = "txt")]
struct Array2;

#[derive(Template)]
#[template(source = "{{ f::<&[u32,]> }}", ext = "txt")]
struct Array3;

#[derive(Template)]
#[template(source = "{{ f::<&[u32;]> }}", ext = "txt")]
struct Array4;

#[derive(Template)]
#[template(source = "{{ f::<&[u32; 'c']> }}", ext = "txt")]
struct Array5;

#[derive(Template)]
#[template(source = "{{ f::<&[u32; 1.2]> }}", ext = "txt")]
struct Array6;

#[derive(Template)]
#[template(source = "{{ f::<&[u32; 1u8]> }}", ext = "txt")]
struct Array7;

#[derive(Template)]
#[template(source = "{{ f::<( }}", ext = "txt")]
struct Tuple1;

#[derive(Template)]
#[template(source = "{{ f::<(> }}", ext = "txt")]
struct Tuple2;

#[derive(Template)]
#[template(source = "{{ f::<(,> }}", ext = "txt")]
struct Tuple3;

#[derive(Template)]
#[template(source = "{{ f::<({},)> }}", ext = "txt")]
struct Tuple4;

fn main() {
}
