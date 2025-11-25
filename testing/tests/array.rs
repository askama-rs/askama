use askama::Template;

// # Array Repeat:      [<element>; <count>]
// ###################################################################################################

#[test]
fn test_array_repeat_in_macro_args() {
    #[derive(Template)]
    #[template(
        source = r#"
            {%- macro test_macro(title, my_arg = [""; 0]) -%}
                {{ title }}:
                {%- if !my_arg.is_empty() -%}
                    [
                    {%- for entry in my_arg -%}
                        {{ entry }},
                    {%- endfor -%}
                    ]
                {%- else -%}
                    []
                {%- endif -%}
            {%- endmacro -%}

            {{- test_macro("default") -}}
            {{- test_macro("set_empty", my_arg = [""; 0]) -}}
            {{- test_macro("set", my_arg = ["hello!"]) -}}
        "#,
        ext = "txt"
    )]
    struct ArrayRepeatInMacros;

    let t = ArrayRepeatInMacros;
    assert_eq!(t.render().unwrap(), "default:[]set_empty:[]set:[hello!,]");
}

#[test]
fn test_array_repeat_in_for() {
    #[derive(Template)]
    #[template(
        source = r#"[
            {%- for elem in [""; 0] -%}
                {{ elem }}
            {%- endfor -%}
        ]"#,
        ext = "txt"
    )]
    struct ArrayRepeatInForLoop;

    let t = ArrayRepeatInForLoop;
    assert_eq!(t.render().unwrap(), "[]");
}

#[test]
fn test_array_repeat_in_assignment() {
    #[derive(Template)]
    #[template(source = r#"{%- let my_arr = [""; 0] -%}"#, ext = "txt")]
    struct ArrayRepeatInAssignment;

    let t = ArrayRepeatInAssignment;
    t.render().unwrap();
}
