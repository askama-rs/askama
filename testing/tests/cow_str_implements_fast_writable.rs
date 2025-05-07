use std::borrow::Cow;
use std::fmt::Display;

use askama::{FastWritable, Template};

#[test]
fn test_cows() {
    // This test ensures that Cow is FastWritable.
    // Every expression needs to implement fmt::Display, even if the FastWritable path
    // is going to be used.

    #[derive(Template)]
    #[template(source = "{{ bull }} + {{ cow }} = {{ calf }}", ext = "txt")]
    struct Cattle<A, B, C>
    where
        A: FastWritable + Display,
        B: FastWritable + Display,
        C: FastWritable + Display,
    {
        bull: A,
        cow: B,
        calf: C,
    }

    let calf = "calf".to_owned();
    let t = Cattle {
        bull: Cow::Borrowed("bull"),
        cow: Cow::<str>::Owned("cow".to_owned()),
        calf: Cow::Borrowed(&calf),
    };
    assert_eq!(t.render().unwrap(), "bull + cow = calf");
}
