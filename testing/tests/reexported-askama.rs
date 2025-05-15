#[doc(hidden)]
pub use askama as __askama;

#[rustfmt::skip] // FIXME: upstream bug <https://github.com/rust-lang/rust/issues/141053>
#[macro_export]
macro_rules! new_greeter {
    ($name:ident) => {
        #[derive(Debug, $crate::__askama::Template)]
        #[template(
            ext = "txt",
            source = "Hello, world!",
            askama = $crate::__askama
        )]
        struct $name;
    };
}

#[test]
fn test_reexported_askama() {
    // This test is the an example of `askama::Template`'s doc.
    // It cannot be executed in there.
    // We show how an re-exported `askama` can be used in a macro.

    new_greeter!(HelloWorld);
    assert_eq!(HelloWorld.to_string(), "Hello, world!");
}
