use askama::Template;

// This test ensures that the compiler doesn't fail because of type recursion.
// This is a regression test for <https://github.com/askama-rs/askama/issues/393>.
#[test]
fn test_recursive_template_struct() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{{name}}<{% for child in children %}{{ child }},{% endfor %}>"
    )]
    struct Person<'a> {
        name: &'a str,
        children: &'a [Person<'a>],
    }

    let a = Person {
        name: "a",
        children: &[],
    };
    let b = Person {
        name: "b",
        children: &[a],
    };
    assert_eq!(
        Person {
            name: "c",
            children: &[b]
        }
        .render()
        .unwrap(),
        "c<b<a<>,>,>"
    );
}

// Same test but on enums.
#[test]
fn test_recursive_template_enum() {
    #[derive(Template)]
    enum HelloWorld<'a> {
        #[template(source = r#"Hello, <strong>{{user}}</strong>!"#, ext = "txt")]
        Primary { user: &'a str },
        #[template(source = r#"{{subitem}}"#, ext = "txt")]
        Secondary { subitem: &'a HelloWorld<'a> },
    }

    let primary = HelloWorld::Primary { user: "georgia" };
    assert_eq!(
        HelloWorld::Secondary { subitem: &primary }
            .render()
            .unwrap(),
        "Hello, <strong>georgia</strong>!"
    );
}
