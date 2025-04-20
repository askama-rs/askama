use std::fmt::{self, Write};

use askama::{FastWritable, NO_VALUES};

// In a real application, please have a look at
// https://github.com/kdeldycke/awesome-falsehood/blob/690a070/readme.md#human-identity
struct Name<'a> {
    forename: &'a str,
    surname: &'a str,
}

impl fmt::Display for Name<'_> {
    // Because the method simply forwards the call, it should be `inline`.
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `fmt::Write` has no access to runtime values,
        // so simply pass `NO_VALUES`.
        self.write_into(f, NO_VALUES)?;
        Ok(())
    }
}

impl FastWritable for Name<'_> {
    fn write_into<W: fmt::Write + ?Sized>(
        &self,
        dest: &mut W,
        _values: &dyn askama::Values,
    ) -> askama::Result<()> {
        dest.write_str(self.surname)?;
        dest.write_str(", ")?;
        dest.write_str(self.forename)?;
        Ok(())
    }
}

#[test]
fn both_implementations_should_render_the_same_text() {
    let person = Name {
        forename: "Max",
        surname: "Mustermann",
    };

    let mut buf_fmt = String::new();
    write!(buf_fmt, "{person}").unwrap();

    let mut buf_fast = String::new();
    person.write_into(&mut buf_fast, NO_VALUES).unwrap();

    assert_eq!(buf_fmt, buf_fast);
    assert_eq!(buf_fmt, "Mustermann, Max");
}
