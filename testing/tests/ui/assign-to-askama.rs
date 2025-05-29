use askama::Template;

#[derive(Template)]
#[template(source = r#"{% let __askama_var %}"#, ext = "html")]
struct Define;

#[derive(Template)]
#[template(source = r#"{% let __askama_var = "var" %}"#, ext = "html")]
struct Assign;

macro_rules! test_kw {
    ($name:tt $source:literal) => {
        #[derive(Template)]
        #[template(source = $source, ext = "html")]
        struct $name;
    };
}

test_kw!(Abstract "{% let abstract %}");
test_kw!(As "{% let as %}");
test_kw!(Async "{% let async %}");
test_kw!(Await "{% let await %}");
test_kw!(Become "{% let become %}");
test_kw!(Box "{% let box %}");
test_kw!(Break "{% let break %}");
test_kw!(Const "{% let const %}");
test_kw!(Continue "{% let continue %}");
test_kw!(Crate "{% let crate %}");
test_kw!(Do "{% let do %}");
test_kw!(Dyn "{% let dyn %}");
test_kw!(Else "{% let else %}");
test_kw!(Enum "{% let enum %}");
test_kw!(Extern "{% let extern %}");
test_kw!(False "{% let false %}");
test_kw!(Final "{% let final %}");
test_kw!(Fn "{% let fn %}");
test_kw!(For "{% let for %}");
test_kw!(Gen "{% let gen %}");
test_kw!(If "{% let if %}");
test_kw!(Impl "{% let impl %}");
test_kw!(In "{% let in %}");
test_kw!(Let "{% let let %}");
test_kw!(Loop "{% let loop %}");
test_kw!(Macro "{% let macro %}");
test_kw!(Match "{% let match %}");
test_kw!(Mod "{% let mod %}");
test_kw!(Move "{% let move %}");
test_kw!(Mut "{% let mut mut %}");
test_kw!(Override "{% let override %}");
test_kw!(Priv "{% let priv %}");
test_kw!(Pub "{% let pub %}");
test_kw!(Ref "{% let ref %}");
test_kw!(Return "{% let return %}");
test_kw!(LowerSelf "{% let self %}");
test_kw!(UpperSelf "{% let Self %}");
test_kw!(Static "{% let static %}");
test_kw!(Struct "{% let struct %}");
test_kw!(Super "{% let super %}");
test_kw!(Trait "{% let trait %}");
test_kw!(True "{% let true %}");
test_kw!(Try "{% let try %}");
test_kw!(Type "{% let type %}");
test_kw!(Typeof "{% let typeof %}");
test_kw!(Union "{% let union %}");
test_kw!(Unsafe "{% let unsafe %}");
test_kw!(Unsized "{% let unsized %}");
test_kw!(Use "{% let use %}");
test_kw!(Virtual "{% let virtual %}");
test_kw!(Where "{% let where %}");
test_kw!(While "{% let while %}");
test_kw!(Yield "{% let yield %}");

fn main() {
}
