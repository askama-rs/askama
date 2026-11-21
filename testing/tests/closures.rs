use askama::Template;

// A closure passed to a method gets its parameter types inferred by rustc, like in Rust code.
#[test]
fn closure_in_method_call() {
    #[derive(Template)]
    #[template(
        source = "{% for n in numbers.iter().filter(|n| *n % 2 == 0) %}{{ n }},{% endfor %}",
        ext = "txt"
    )]
    struct Even {
        numbers: Vec<u32>,
    }

    assert_eq!(
        Even {
            numbers: vec![1, 2, 3, 4]
        }
        .render()
        .unwrap(),
        "2,4,"
    );
}

// A parameter shadows the field of the same name, other names still resolve to fields.
#[test]
fn closure_parameter_shadows_field() {
    #[derive(Template)]
    #[template(
        source = "{% for n in numbers.iter().map(|factor| factor * factor) %}{{ n }},{% endfor %}
{%- for n in numbers.iter().map(|n| n * factor) %}{{ n }},{% endfor %}",
        ext = "txt"
    )]
    struct Scaled {
        numbers: Vec<u32>,
        factor: u32,
    }

    assert_eq!(
        Scaled {
            numbers: vec![1, 2, 3],
            factor: 10
        }
        .render()
        .unwrap(),
        "1,4,9,10,20,30,"
    );
}

// A closure is passed to a custom filter as is, also as a named argument.
#[test]
fn closure_as_custom_filter_argument() {
    mod filters {
        #[askama::filter_fn]
        pub fn apply<F: Fn(u32) -> u32>(
            value: &u32,
            _: &dyn askama::Values,
            f: F,
        ) -> askama::Result<u32> {
            Ok(f(*value))
        }
    }

    #[derive(Template)]
    #[template(
        source = "{{ value|apply(|v| v + 1) }} {{ value|apply(f = |v| v * 2) }}",
        ext = "txt"
    )]
    struct Applied {
        value: u32,
    }

    assert_eq!(Applied { value: 5 }.render().unwrap(), "6 10");
}
