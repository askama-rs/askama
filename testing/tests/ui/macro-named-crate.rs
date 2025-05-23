// The names `crate`, `self`, `Self` and `super` cannot be raw identifiers, so they can never
// be valid macro names.

#[derive(askama::Template)]
#[template(source = "{{ crate!() }}", ext = "txt")]
struct MacroCrate;

#[derive(askama::Template)]
#[template(source = "{{ self!() }}", ext = "txt")]
struct MacroSelf;

#[derive(askama::Template)]
#[template(source = "{{ Self!() }}", ext = "txt")]
struct MacroSelfType;

#[derive(askama::Template)]
#[template(source = "{{ super!() }}", ext = "txt")]
struct MacroSuper;

#[derive(askama::Template)]
#[template(source = "{{ some::path::crate!() }}", ext = "txt")]
struct MacroPathCrate;

#[derive(askama::Template)]
#[template(source = "{{ some::path::self!() }}", ext = "txt")]
struct MacroPathSelf;

#[derive(askama::Template)]
#[template(source = "{{ some::path::Self!() }}", ext = "txt")]
struct MacroPathSelfType;

#[derive(askama::Template)]
#[template(source = "{{ some::path::super!() }}", ext = "txt")]
struct MacroPathSuper;

fn main() {
}
