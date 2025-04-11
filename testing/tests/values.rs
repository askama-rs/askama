use std::any::Any;
use std::collections::HashMap;

use askama::Template;

#[test]
fn test_values() {
    #[derive(Template)]
    #[template(
        source = r#"{% if let Ok(bla) = "a" | value::<u32> %}{{bla}}{% endif %}"#,
        ext = "txt"
    )]
    struct V;

    let mut values: HashMap<String, Box<dyn Any>> = HashMap::default();
    assert_eq!(V.render_with_values(&values).unwrap(), "");
    values.insert("a".to_string(), Box::new(12u32));
    assert_eq!(V.render_with_values(&values).unwrap(), "12");
    values.insert("a".to_string(), Box::new(false));
    assert_eq!(V.render_with_values(&values).unwrap(), "");
}

#[test]
fn test_values2() {
    #[derive(Template)]
    #[template(
        source = r#"
            {%- if let Ok(bla) = "a" | value::<&str> %}{{bla}}{% endif -%}
            {%- if let Ok(bla) = "b" | value::<bool> %} {{bla}}{% endif -%}
        "#,
        ext = "txt"
    )]
    struct V;

    let mut values: HashMap<String, Box<dyn Any>> = HashMap::default();
    assert_eq!(V.render_with_values(&values).unwrap(), "");
    values.insert("a".to_string(), Box::new("hey"));
    assert_eq!(V.render_with_values(&values).unwrap(), "hey");
    values.insert("b".to_string(), Box::new(false));
    assert_eq!(V.render_with_values(&values).unwrap(), "hey false");
    values.remove("a");
    assert_eq!(V.render_with_values(&values).unwrap(), " false");
}

#[test]
fn test_values3() {
    #[derive(Template)]
    #[template(
        source = r#"
            {%- match "data" | value::<&str> -%}
                {%- when Ok(data) -%} ok={{ data }}
                {%- when Err(err) -%} err={{ err }}
            {%- endmatch -%}
        "#,
        ext = "txt"
    )]
    struct V;

    let mut values: HashMap<String, Box<dyn Any>> = HashMap::default();
    assert_eq!(
        V.render_with_values(&values).unwrap(),
        "err=key missing in values"
    );
    values.insert("data".to_string(), Box::new(false));
    assert_eq!(
        V.render_with_values(&values).unwrap(),
        "err=value has wrong type"
    );
    values.insert("data".to_string(), Box::new("hey"));
    assert_eq!(V.render_with_values(&values).unwrap(), "ok=hey");
    values.insert("data".to_string(), Box::new(Box::new("hey")));
    assert_eq!(V.render_with_values(&values).unwrap(), "ok=hey");
}

#[test]
fn test_value_function_getter() {
    #[derive(Template)]
    #[template(
        source = r#"{% if let Ok(bla) = askama::get_value::<u32>("a") %}{{bla}}{% endif %}"#,
        ext = "txt"
    )]
    struct V;

    let mut values: HashMap<String, Box<dyn Any>> = HashMap::default();
    assert_eq!(V.render_with_values(&values).unwrap(), "");
    values.insert("a".to_string(), Box::new(12u32));
    assert_eq!(V.render_with_values(&values).unwrap(), "12");
    values.insert("a".to_string(), Box::new(false));
    assert_eq!(V.render_with_values(&values).unwrap(), "");
}

#[test]
fn test_value_in_subtemplates() {
    #[derive(Template)]
    #[template(source = r#"{{ Child }}"#, ext = "html")]
    struct Parent;

    #[derive(Template)]
    #[template(
        source = r#"Hello, {{ askama::get_value::<String>("who")? }}!"#,
        ext = "html"
    )]
    struct Child;

    let values: (&str, &dyn Any) = ("who", &"<world>".to_owned());
    assert_eq!(
        Parent.render_with_values(&values).unwrap(),
        "Hello, &#38;#60;world&#38;#62;!", // sic: escaped twice
    );
}
