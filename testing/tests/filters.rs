use askama::Template;
use assert_matches::assert_matches;
#[cfg(feature = "serde_json")]
use serde_json::{Value, json};

#[test]
fn filter_escape() {
    #[derive(Template)]
    #[template(path = "filters.html")]
    struct TestTemplate {
        strvar: String,
    }

    let s = TestTemplate {
        strvar: "// my <html> is \"unsafe\" & should be 'escaped'".to_string(),
    };
    assert_eq!(
        s.render().unwrap(),
        "// my &#60;html&#62; is &#34;unsafe&#34; &#38; \
         should be &#39;escaped&#39;"
    );
}

#[test]
fn filter_opt_escaper_none() {
    #[derive(Template)]
    #[template(
        source = "{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\"|escape(\"none\") }}
{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\"|escape(\"html\") }}
{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\"|escape }}
{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\" }}
",
        ext = "txt",
        escape = "none"
    )]
    struct OptEscaperNoneTemplate;

    let t = OptEscaperNoneTemplate;
    assert_eq!(
        t.render().unwrap(),
        r#"<h1 class="title">Foo Bar</h1>
&#60;h1 class=&#34;title&#34;&#62;Foo Bar&#60;/h1&#62;
<h1 class="title">Foo Bar</h1>
<h1 class="title">Foo Bar</h1>
"#
    );
}

#[test]
fn filter_opt_escaper_html() {
    #[derive(Template)]
    #[template(
        source = "{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\"|escape(\"none\") }}
{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\"|escape(\"html\") }}
{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\"|escape }}
{{ \"<h1 class=\\\"title\\\">Foo Bar</h1>\" }}
",
        ext = "txt",
        escape = "html"
    )]
    struct OptEscaperHtmlTemplate;

    let t = OptEscaperHtmlTemplate;
    assert_eq!(
        t.render().unwrap(),
        r#"<h1 class="title">Foo Bar</h1>
&#60;h1 class=&#34;title&#34;&#62;Foo Bar&#60;/h1&#62;
&#60;h1 class=&#34;title&#34;&#62;Foo Bar&#60;/h1&#62;
&#60;h1 class=&#34;title&#34;&#62;Foo Bar&#60;/h1&#62;
"#
    );
}

#[test]
fn filter_format() {
    #[derive(Template)]
    #[template(path = "format.html", escape = "none")]
    struct FormatTemplate<'a> {
        var: &'a str,
    }

    let t = FormatTemplate { var: "formatted" };
    assert_eq!(t.render().unwrap(), "\"formatted\"");
}

#[test]
fn filter_fmt() {
    #[derive(Template)]
    #[template(source = "{{ var|fmt(\"{:?}\") }}", ext = "html", escape = "none")]
    struct FmtTemplate<'a> {
        var: &'a str,
    }

    let t = FmtTemplate { var: "formatted" };
    assert_eq!(t.render().unwrap(), "\"formatted\"");
}

mod filters {
    use askama::Values;

    #[askama::filter_fn]
    pub fn myfilter(s: &str, _: &dyn Values) -> ::askama::Result<String> {
        Ok(s.replace("oo", "aa"))
    }

    // for test_nested_filter_ref
    #[askama::filter_fn]
    pub fn mytrim(s: &dyn std::fmt::Display, _: &dyn Values) -> ::askama::Result<String> {
        Ok(s.to_string().trim().to_owned())
    }
}

#[test]
fn test_my_filter() {
    #[derive(Template)]
    #[template(source = "{{ s|myfilter }}", ext = "txt")]
    struct MyFilterTemplate<'a> {
        s: &'a str,
    }

    let t = MyFilterTemplate { s: "foo" };
    assert_eq!(t.render().unwrap(), "faa");
}

#[test]
fn test_join() {
    #[derive(Template)]
    #[template(path = "filters_join.html")]
    struct JoinTemplate<'a> {
        s: &'a [&'a str],
    }

    let t = JoinTemplate {
        s: &["foo", "bar", "bazz"],
    };
    assert_eq!(t.render().unwrap(), "foo, bar, bazz");
}

#[test]
fn test_vec_join() {
    #[derive(Template)]
    #[template(path = "filters_join.html")]
    struct VecJoinTemplate {
        s: Vec<String>,
    }

    let t = VecJoinTemplate {
        s: vec!["foo".into(), "bar".into(), "bazz".into()],
    };
    assert_eq!(t.render().unwrap(), "foo, bar, bazz");
}

#[cfg(feature = "serde_json")]
#[test]
fn test_json() {
    #[derive(Template)]
    #[template(
        source = r#"{
  "foo": "{{ foo }}",
  "bar": {{ bar|json|safe }}
}"#,
        ext = "txt"
    )]
    struct JsonTemplate<'a> {
        foo: &'a str,
        bar: &'a Value,
    }

    let val = json!({"arr": [ "one", 2, true, null ]});
    let t = JsonTemplate {
        foo: "a",
        bar: &val,
    };
    assert_eq!(
        t.render().unwrap(),
        r#"{
  "foo": "a",
  "bar": {"arr":["one",2,true,null]}
}"#
    );
}

#[cfg(feature = "serde_json")]
#[test]
fn test_pretty_json() {
    #[derive(Template)]
    #[template(
        source = r#"{
  "foo": "{{ foo }}",
  "bar": {{ bar|json(2)|safe }}
}"#,
        ext = "txt"
    )]
    struct PrettyJsonTemplate<'a> {
        foo: &'a str,
        bar: &'a Value,
    }

    let val = json!({"arr": [ "one", 2, true, null ]});
    let t = PrettyJsonTemplate {
        foo: "a",
        bar: &val,
    };
    // Note: the json filter lacks a way to specify initial indentation
    assert_eq!(
        t.render().unwrap(),
        r#"{
  "foo": "a",
  "bar": {
  "arr": [
    "one",
    2,
    true,
    null
  ]
}
}"#
    );
}

#[cfg(feature = "serde_json")]
#[test]
fn test_dynamic_json() {
    #[derive(Template)]
    #[template(source = r#"{{ bar|json(indent)|safe }}"#, ext = "txt")]
    struct DynamicJsonTemplate<'a> {
        bar: &'a Value,
        indent: &'a str,
    }

    let val = json!({"arr": ["one", 2]});
    let t = DynamicJsonTemplate {
        bar: &val,
        indent: "?",
    };
    assert_eq!(
        t.render().unwrap(),
        r#"{
?"arr": [
??"one",
??2
?]
}"#
    );
}

#[test]
fn test_nested_filter_ref() {
    #[derive(Template)]
    #[template(source = "{{ x|mytrim|safe }}", ext = "html")]
    struct NestedFilterTemplate {
        x: String,
    }

    let t = NestedFilterTemplate {
        x: " floo & bar".to_string(),
    };
    assert_eq!(t.render().unwrap(), "floo & bar");
}

#[test]
fn test_filter_let_filter() {
    #[derive(Template)]
    #[template(
        source = "{% let p = baz.print(foo.as_ref()) %}{{ p|upper }}",
        ext = "html"
    )]
    struct FilterLetFilterTemplate {
        foo: String,
        baz: Baz,
    }

    struct Baz {}

    impl Baz {
        fn print(&self, s: &str) -> String {
            s.trim().to_owned()
        }
    }

    let t = FilterLetFilterTemplate {
        foo: " bar ".to_owned(),
        baz: Baz {},
    };
    assert_eq!(t.render().unwrap(), "BAR");
}

#[test]
fn test_filter_truncate() {
    #[derive(Template)]
    #[template(source = "{{ foo|truncate(10) }}{{ foo|truncate(5) }}", ext = "txt")]
    struct TruncateFilter {
        foo: String,
    }

    let t = TruncateFilter {
        foo: "alpha bar".into(),
    };
    assert_eq!(t.render().unwrap(), "alpha baralpha...");

    #[derive(Template)]
    #[template(source = "{{ foo | truncate(length) }}", ext = "txt")]
    struct TruncateFilterLength<'a> {
        foo: String,
        length: &'a &'a &'a i32,
    }

    assert_eq!(
        TruncateFilterLength {
            foo: "alpha bar".into(),
            length: &&&5,
        }
        .render()
        .unwrap(),
        "alpha..."
    );
    assert_matches!(
        TruncateFilterLength {
            foo: "alpha bar".into(),
            length: &&&-5,
        }
        .render()
        .unwrap_err(),
        askama::Error::Fmt
    );
}

#[cfg(feature = "serde_json")]
#[test]
fn test_json_attribute() {
    #[derive(Template)]
    #[template(source = r#"<li data-name="{{name|json}}"></li>"#, ext = "html")]
    struct JsonAttributeTemplate<'a> {
        name: &'a str,
    }

    let t = JsonAttributeTemplate {
        name: r#""><button>Hacked!</button>"#,
    };
    assert_eq!(
        t.render().unwrap(),
        r#"<li data-name="&#34;\&#34;\u003e\u003cbutton\u003eHacked!\u003c/button\u003e&#34;"></li>"#
    );
}

#[cfg(feature = "serde_json")]
#[test]
fn test_json_attribute2() {
    #[derive(Template)]
    #[template(source = r#"<li data-name='{{name|json|safe}}'></li>"#, ext = "html")]
    struct JsonAttribute2Template<'a> {
        name: &'a str,
    }

    let t = JsonAttribute2Template {
        name: r"'><button>Hacked!</button>",
    };
    assert_eq!(
        t.render().unwrap(),
        r#"<li data-name='"\u0027\u003e\u003cbutton\u003eHacked!\u003c/button\u003e"'></li>"#
    );
}

#[cfg(feature = "serde_json")]
#[test]
fn test_json_script() {
    #[derive(Template)]
    #[template(
        source = r#"<script>var user = {{name|json|safe}}</script>"#,
        ext = "html"
    )]
    struct JsonScriptTemplate<'a> {
        name: &'a str,
    }

    let t = JsonScriptTemplate {
        name: r"</script><button>Hacked!</button>",
    };
    assert_eq!(
        t.render().unwrap(),
        r#"<script>var user = "\u003c/script\u003e\u003cbutton\u003eHacked!\u003c/button\u003e"</script>"#
    );
}

#[test]
fn test_let_borrow() {
    #[derive(askama::Template)]
    #[template(
        source = r#"{% let word = s|ref %}{{ word }}
{%- let hello = String::from("hello") %}
{%- if word|deref == hello %}1{% else %}2{% endif %}"#,
        ext = "html"
    )]
    struct LetBorrow {
        s: String,
    }

    let template = LetBorrow {
        s: "hello".to_owned(),
    };
    assert_eq!(template.render().unwrap(), "hello1");
}

#[test]
fn test_linebreaks() {
    let s = "<script>\nalert('Hello, world!')\n</script>";

    #[derive(Template)]
    #[template(source = r#"{{ s|linebreaks }}"#, ext = "html")]
    struct LineBreaks {
        s: &'static str,
    }

    assert_eq!(
        LineBreaks { s }.render().unwrap(),
        "<p>&#60;script&#62;<br/>alert(&#39;Hello, world!&#39;)<br/>&#60;/script&#62;</p>",
    );

    #[derive(Template)]
    #[template(source = r#"{{ s|escape|linebreaks }}"#, ext = "html")]
    struct LineBreaksExtraEscape {
        s: &'static str,
    }

    assert_eq!(
        LineBreaksExtraEscape { s }.render().unwrap(),
        "<p>&#60;script&#62;<br/>alert(&#39;Hello, world!&#39;)<br/>&#60;/script&#62;</p>",
    );

    #[derive(Template)]
    #[template(source = r#"{{ s|linebreaks|safe }}"#, ext = "html")]
    struct LineBreaksExtraSafe {
        s: &'static str,
    }

    assert_eq!(
        LineBreaksExtraSafe { s }.render().unwrap(),
        "<p>&#60;script&#62;<br/>alert(&#39;Hello, world!&#39;)<br/>&#60;/script&#62;</p>",
    );

    #[derive(Template)]
    #[template(source = r#"{{ s|escape|linebreaks|safe }}"#, ext = "html")]
    struct LineBreaksExtraBoth {
        s: &'static str,
    }

    assert_eq!(
        LineBreaksExtraBoth { s }.render().unwrap(),
        "<p>&#60;script&#62;<br/>alert(&#39;Hello, world!&#39;)<br/>&#60;/script&#62;</p>",
    );
}

// Regression tests for <https://github.com/askama-rs/askama/issues/215>.
#[test]
fn test_filesizeformat() {
    #[derive(Template)]
    #[template(
        source = r#"{% if let Some(x) = s %}{{ x | filesizeformat }}{% endif %}"#,
        ext = "html"
    )]
    struct S {
        s: Option<u32>,
    }

    assert_eq!(S { s: Some(12) }.render().unwrap(), "12 B");
}

#[test]
fn test_filesizeformat_with_precision() {
    #[derive(Template)]
    #[template(source = r#"{{ 1024 | filesizeformat(precision = 3) }}"#, ext = "html")]
    struct FileSizeFormatPrecision {}

    assert_eq!(FileSizeFormatPrecision {}.render().unwrap(), "1.024 kB");
}

#[test]
fn test_whitespace_around_filter_operator() {
    #[derive(Template)]
    #[template(
        source = r#"{{ 12 |safe }}
{{ 8| safe }}
{{ 4   |    safe }}"#,
        ext = "html"
    )]
    struct S;

    assert_eq!(S.render().unwrap(), "12\n8\n4");
}

#[askama::filter_fn]
pub(crate) fn minus(value: &str, _: &dyn askama::Values) -> askama::Result<i32> {
    Ok(-value.parse().map_err(askama::Error::custom)?)
}

#[test]
fn test_filter_with_path() {
    // ensure that filters can have a path

    pub(crate) mod b {
        pub(crate) mod c {
            pub(crate) mod d {
                pub(crate) use crate::minus;
            }
        }
    }

    pub(crate) mod filters {
        pub(crate) use crate::minus;
    }

    #[derive(Template)]
    #[template(source = r#"{{ value | b::c::d::minus }}"#, ext = "html")]
    struct NestedPath<'a> {
        value: &'a str,
    }

    assert_eq!(NestedPath { value: "42" }.render().unwrap(), "-42");

    #[derive(Template)]
    #[template(source = r#"{{ value | self::minus }}"#, ext = "html")]
    struct SelfPath<'a> {
        value: &'a str,
    }

    assert_eq!(SelfPath { value: "42" }.render().unwrap(), "-42");

    #[derive(Template)]
    #[template(source = r#"{{ value | crate::minus }}"#, ext = "html")]
    struct CratePath<'a> {
        value: &'a str,
    }

    assert_eq!(CratePath { value: "42" }.render().unwrap(), "-42");

    #[derive(Template)]
    #[template(source = r#"{{ value | filters::minus }}"#, ext = "html")]
    struct ExplicitPath<'a> {
        value: &'a str,
    }

    assert_eq!(ExplicitPath { value: "42" }.render().unwrap(), "-42");

    #[derive(Template)]
    #[template(source = r#"{{ value | minus }}"#, ext = "html")]
    struct ImplicitPath<'a> {
        value: &'a str,
    }

    assert_eq!(ImplicitPath { value: "42" }.render().unwrap(), "-42");
}

#[test]
fn test_custom_filter_constructs() {
    pub(crate) mod filters {
        use std::fmt::Display;

        #[askama::filter_fn]
        pub fn noargs<T: Display>(value: T, _env: &dyn askama::Values) -> askama::Result<String> {
            Ok(format!(r#""{value}" | noargs()"#))
        }

        #[askama::filter_fn]
        pub fn req1<T: Display, F: Display>(
            value: T,
            _env: &dyn askama::Values,
            req0: F,
        ) -> askama::Result<String> {
            Ok(format!(r#""{value}" | req1({req0})"#))
        }

        #[askama::filter_fn]
        pub fn opt1<T: Display>(
            value: T,
            _env: &dyn askama::Values,
            #[optional("default")] opt0: &str,
        ) -> askama::Result<String> {
            Ok(format!(r#""{value}" | opt1({opt0})"#))
        }

        #[askama::filter_fn]
        pub fn req1_opt1<T: Display, F: Display>(
            value: T,
            _env: &dyn askama::Values,
            req0: F,
            #[optional("default")] opt0: &str,
        ) -> askama::Result<String> {
            Ok(format!(r#""{value}" | req1_opt1({req0}, {opt0})"#))
        }

        #[askama::filter_fn]
        pub fn shared_generic<T: Display>(
            value: T,
            _env: &dyn askama::Values,
            req0: T,
        ) -> askama::Result<String> {
            Ok(format!(r#""{value}" | shared_generic({req0})"#))
        }

        #[askama::filter_fn]
        pub fn impl_trait_input(
            value: impl Display,
            _env: &dyn askama::Values,
        ) -> askama::Result<String> {
            Ok(format!(r#""{value}" | impl_trait_input"#))
        }
    }

    #[derive(Template)]
    #[template(
        source = r#"
{{- test() | noargs | safe }}

{{ test() | req1("lol") | safe }}

{{ test() | opt1 | safe }}
{{ test() | opt1("nodefault") | safe }}
{{ test() | opt1(opt0 = "nodefault") | safe }}

{{ test() | req1_opt1("req") | safe }}
{{ test() | req1_opt1("req", "supplied") | safe }}
{{ test() | req1_opt1("req", opt0 = "supplied") | safe }}

{{ test() | shared_generic("blub") | safe }}
{{ test() | impl_trait_input | safe -}}
        "#,
        ext = "html"
    )]
    struct CustomFilterConstructs {}
    impl CustomFilterConstructs {
        pub fn test(&self) -> &'static str {
            "this is a test"
        }
    }

    let should = r#"
"this is a test" | noargs()

"this is a test" | req1(lol)

"this is a test" | opt1(default)
"this is a test" | opt1(nodefault)
"this is a test" | opt1(nodefault)

"this is a test" | req1_opt1(req, default)
"this is a test" | req1_opt1(req, supplied)
"this is a test" | req1_opt1(req, supplied)

"this is a test" | shared_generic(blub)
"this is a test" | impl_trait_input
    "#
    .trim();

    let actual = CustomFilterConstructs {}.render().unwrap();
    assert_eq!(actual, should);
}
