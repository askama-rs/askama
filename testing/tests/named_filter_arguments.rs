use askama::Template;

#[test]
fn test_pluralize_two_positional_args() {
    #[derive(Template)]
    #[template(
        source = r#"I have {{ count }} butterfl{{ count | pluralize("y", "ies") }}."#,
        ext = "txt"
    )]
    struct CountButterflies {
        count: usize,
    }

    assert_eq!(
        CountButterflies { count: 0 }.render().unwrap(),
        "I have 0 butterflies."
    );
    assert_eq!(
        CountButterflies { count: 1 }.render().unwrap(),
        "I have 1 butterfly."
    );
    assert_eq!(
        CountButterflies { count: 2 }.render().unwrap(),
        "I have 2 butterflies."
    );
}

#[test]
fn test_pluralize_positional_and_named() {
    #[derive(Template)]
    #[template(
        source = r#"I have {{ count }} butterfl{{ count | pluralize("y", pl = "ies") }}."#,
        ext = "txt"
    )]
    struct CountButterflies {
        count: usize,
    }

    assert_eq!(
        CountButterflies { count: 0 }.render().unwrap(),
        "I have 0 butterflies."
    );
    assert_eq!(
        CountButterflies { count: 1 }.render().unwrap(),
        "I have 1 butterfly."
    );
    assert_eq!(
        CountButterflies { count: 2 }.render().unwrap(),
        "I have 2 butterflies."
    );
}

#[test]
fn test_pluralize_named_reordered() {
    #[derive(Template)]
    #[template(
        source = r#"I have {{ count }} butterfl{{ count | pluralize(pl = "ies", sg = "y") }}."#,
        ext = "txt"
    )]
    struct CountButterflies {
        count: usize,
    }

    assert_eq!(
        CountButterflies { count: 0 }.render().unwrap(),
        "I have 0 butterflies."
    );
    assert_eq!(
        CountButterflies { count: 1 }.render().unwrap(),
        "I have 1 butterfly."
    );
    assert_eq!(
        CountButterflies { count: 2 }.render().unwrap(),
        "I have 2 butterflies."
    );
}

#[test]
fn test_pluralize_defaulted_and_named() {
    #[derive(Template)]
    #[template(
        source = r#"I have {{ count }} potato{{ count | pluralize(pl = "es") }}."#,
        ext = "txt"
    )]
    struct CountPotatoes {
        count: usize,
    }

    assert_eq!(
        CountPotatoes { count: 0 }.render().unwrap(),
        "I have 0 potatoes."
    );
    assert_eq!(
        CountPotatoes { count: 1 }.render().unwrap(),
        "I have 1 potato."
    );
    assert_eq!(
        CountPotatoes { count: 2 }.render().unwrap(),
        "I have 2 potatoes."
    );
}

#[test]
fn test_ident() {
    const TEXT: &str = "\
        Lorem Ipsum has been the industry's\n\
        \n\
        standard dummy text ever since the 1500s";

    #[derive(Template)]
    #[template(source = r#"<{{ text | indent("$$",  blank = true) }}>"#, ext = "txt")]
    struct IdentBlank<'a> {
        text: &'a str,
    }

    assert_eq!(
        IdentBlank { text: TEXT }.render().unwrap(),
        "\
            <Lorem Ipsum has been the industry's\n\
            $$\n\
            $$standard dummy text ever since the 1500s>"
    );

    #[derive(Template)]
    #[template(source = r#"<{{ text | indent("$$",  first = true) }}>"#, ext = "txt")]
    struct IdentFirst<'a> {
        text: &'a str,
    }

    assert_eq!(
        IdentFirst { text: TEXT }.render().unwrap(),
        "\
            <$$Lorem Ipsum has been the industry's\n\
            \n\
            $$standard dummy text ever since the 1500s>"
    );

    #[derive(Template)]
    #[template(
        source = r#"<{{ text | indent("$$", blank = true, first = true) }}>"#,
        ext = "txt"
    )]
    struct IdentBoth<'a> {
        text: &'a str,
    }

    assert_eq!(
        IdentBoth { text: TEXT }.render().unwrap(),
        "\
            <$$Lorem Ipsum has been the industry's\n\
            $$\n\
            $$standard dummy text ever since the 1500s>"
    );

    #[derive(Template)]
    #[template(
        source = r#"<{{ text | indent("$$", first = true, blank = true) }}>"#,
        ext = "txt"
    )]
    struct IdentBoth2<'a> {
        text: &'a str,
    }

    assert_eq!(
        IdentBoth2 { text: TEXT }.render().unwrap(),
        "\
            <$$Lorem Ipsum has been the industry's\n\
            $$\n\
            $$standard dummy text ever since the 1500s>"
    );

    #[derive(Template)]
    #[template(
        source = r#"<{{ text | indent(first = true, width = "$$", blank = true) }}>"#,
        ext = "txt"
    )]
    struct IdentBoth3<'a> {
        text: &'a str,
    }

    assert_eq!(
        IdentBoth3 { text: TEXT }.render().unwrap(),
        "\
            <$$Lorem Ipsum has been the industry's\n\
            $$\n\
            $$standard dummy text ever since the 1500s>"
    );
}
