use std::fmt::Display;

use askama::Template;

#[test]
fn test_blocks() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "
            {%- block first -%} first=<{{first}}> {%- endblock -%}
            {%- block second -%} second=<{{second}}> {%- endblock -%}
            {%- block third -%} third=<{{third}}> {%- endblock -%}
            {%- block fail -%} better luck next time {%- endblock -%}
        ",
        block = "fail",
        blocks = ["first", "second", "third"]
    )]
    struct WithBlocks<'a, S: Display, T>
    where
        T: Display,
    {
        first: &'a str,
        second: S,
        third: &'a T,
    }

    let tmpl = WithBlocks {
        first: "number one",
        second: 2,
        third: &"bronze",
    };

    assert_eq!(tmpl.as_first().render().unwrap(), "first=<number one>");
    assert_eq!(tmpl.as_second().render().unwrap(), "second=<2>");
    assert_eq!(tmpl.as_third().render().unwrap(), "third=<bronze>");
    assert_eq!(tmpl.render().unwrap(), "better luck next time");
}
