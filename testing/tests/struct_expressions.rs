use askama::Template;

#[test]
fn test_struct_expressions() {
    struct InnerCell {
        number: u32,
    }
    impl std::fmt::Display for InnerCell {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Hello, {}!", self.number)
        }
    }

    #[derive(Template)]
    #[template(source = r#"{{ InnerCell { number: 42 } }}"#, ext = "txt")]
    struct OuterTemplate;
    let template = OuterTemplate;
    assert_eq!(template.render().unwrap(), "Hello, 42!");

    #[derive(Template)]
    #[template(source = r#"{{ InnerCell { number: *my_number } }}"#, ext = "txt")]
    struct OuterTemplate2 {
        my_number: u32,
    }
    let template = OuterTemplate2 { my_number: 42 };
    assert_eq!(template.render().unwrap(), "Hello, 42!");

    // With trailing comma.
    #[derive(Template)]
    #[template(source = r#"{{ InnerCell { number: 42, } }}"#, ext = "txt")]
    struct OuterTemplate3;
    assert_eq!(OuterTemplate3.render().unwrap(), "Hello, 42!");
}

#[test]
fn test_struct_expressions_in_mod() {
    #[derive(Template)]
    #[template(source = r#"{{ inner::InnerCell { number: 42 } }}"#, ext = "txt")]
    struct OuterTemplate;
    mod inner {
        pub struct InnerCell {
            pub number: u32,
        }
        impl std::fmt::Display for InnerCell {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "Hello, {}!", self.number)
            }
        }
    }
    let template = OuterTemplate;
    assert_eq!(template.render().unwrap(), "Hello, 42!");
}

#[test]
fn test_struct_expressions_default() {
    #[derive(Default)]
    struct InnerCell {
        number: u32,
        other: u32,
    }
    impl std::fmt::Display for InnerCell {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Hello, {} and {}!", self.number, self.other)
        }
    }

    #[derive(Template)]
    #[template(
        source = r#"{{ InnerCell { number: 42, ..Default::default() } }}"#,
        ext = "txt"
    )]
    struct OuterTemplate;
    assert_eq!(OuterTemplate.render().unwrap(), "Hello, 42 and 0!");

    #[derive(Template)]
    #[template(source = r#"{{ InnerCell { ..Default::default() } }}"#, ext = "txt")]
    struct OuterTemplate2;
    assert_eq!(OuterTemplate2.render().unwrap(), "Hello, 0 and 0!");

    // With trailing comma.
    #[derive(Template)]
    #[template(source = r#"{{ InnerCell { ..Default::default(), } }}"#, ext = "txt")]
    struct OuterTemplate3;
    assert_eq!(OuterTemplate3.render().unwrap(), "Hello, 0 and 0!");
}

#[test]
fn test_struct_expressions_tuple() {
    #[derive(Template)]
    #[template(source = r#"{{ InnerCell { 0: 42, 1: 43 } }}"#, ext = "txt")]
    struct OuterTemplate;
    struct InnerCell(u32, u32);
    impl std::fmt::Display for InnerCell {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Hello, {} and {}!", self.0, self.1)
        }
    }
    let template = OuterTemplate;
    assert_eq!(template.render().unwrap(), "Hello, 42 and 43!");
}

#[test]
fn test_struct_expressions_nested() {
    #[derive(Template)]
    #[template(
        source = r#"{{ InnerCell { 0: InnerCell { 0: InnerCell { 0: "Hi" } } } }}"#,
        ext = "txt"
    )]
    struct OuterTemplate;
    struct InnerCell<T>(T);
    impl<T: std::fmt::Display> std::fmt::Display for InnerCell<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}!", self.0)
        }
    }
    let template = OuterTemplate;
    assert_eq!(template.render().unwrap(), "Hi!!!");
}

#[test]
fn test_struct_expressions_generic() {
    #[derive(Template)]
    #[template(source = r#"{{ InnerCell::<u64> { 0: 84 } }}"#, ext = "txt")]
    struct OuterTemplate;
    struct InnerCell<T>(T);
    impl<T: std::fmt::Display> std::fmt::Display for InnerCell<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}!", self.0)
        }
    }
    let template = OuterTemplate;
    assert_eq!(template.render().unwrap(), "84!");
}
