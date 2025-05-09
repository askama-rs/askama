#![allow(clippy::disallowed_names)] // For the use of `foo` in test cases

use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::fmt;
use std::pin::Pin;
use std::sync::{Arc, Mutex, MutexGuard};

use askama::Template;
use askama::filters::HtmlSafe;
use either::Either;

#[test]
fn test_variables() {
    #[derive(Template)]
    #[template(path = "simple.html")]
    struct VariablesTemplate<'a> {
        strvar: &'a str,
        num: i64,
        i18n: String,
    }

    let s = VariablesTemplate {
        strvar: "foo",
        num: 42,
        i18n: "Iñtërnâtiônàlizætiøn".to_string(),
    };
    assert_eq!(
        s.render().unwrap(),
        "\nhello world, foo\n\
         with number: 42\n\
         Iñtërnâtiônàlizætiøn is important\n\
         in vars too: Iñtërnâtiônàlizætiøn"
    );
}

#[test]
fn test_escape() {
    #[derive(Template)]
    #[template(path = "hello.html")]
    struct EscapeTemplate<'a> {
        name: &'a str,
    }

    let s = EscapeTemplate { name: "<>&\"'" };

    assert_eq!(s.render().unwrap(), "Hello, &#60;&#62;&#38;&#34;&#39;!");
}

#[test]
fn test_variables_no_escape() {
    #[derive(Template)]
    #[template(path = "simple-no-escape.txt")]
    struct VariablesTemplateNoEscape<'a> {
        strvar: &'a str,
        num: i64,
        i18n: String,
    }

    let s = VariablesTemplateNoEscape {
        strvar: "foo",
        num: 42,
        i18n: "Iñtërnâtiônàlizætiøn".to_string(),
    };
    assert_eq!(
        s.render().unwrap(),
        "\nhello world, foo\n\
         with number: 42\n\
         Iñtërnâtiônàlizætiøn is important\n\
         in vars too: Iñtërnâtiônàlizætiøn"
    );
}

mod test_constants {
    use askama::Template;

    const FOO: &str = "FOO";
    const FOO_BAR: &str = "FOO BAR";

    #[derive(Template)]
    #[template(
        source = "{{ foo }} {{ foo_bar }} {{ FOO }} {{ FOO_BAR }} {{ self::FOO }} {{ self::FOO_BAR }} {{ Self::BAR }} {{ Self::BAR_BAZ }}",
        ext = "txt"
    )]
    struct ConstTemplate {
        foo: &'static str,
        foo_bar: &'static str,
    }

    impl ConstTemplate {
        const BAR: &'static str = "BAR";
        const BAR_BAZ: &'static str = "BAR BAZ";
    }

    #[test]
    fn test_constants() {
        let t = ConstTemplate {
            foo: "foo",
            foo_bar: "foo bar",
        };
        assert_eq!(
            t.render().unwrap(),
            "foo foo bar FOO FOO BAR FOO FOO BAR BAR BAR BAZ"
        );
    }
}

#[test]
fn test_if() {
    #[derive(Template)]
    #[template(path = "if.html")]
    struct IfTemplate {
        cond: bool,
    }

    let s = IfTemplate { cond: true };
    assert_eq!(s.render().unwrap(), "true");
}

#[test]
fn test_else() {
    #[derive(Template)]
    #[template(path = "else.html")]
    struct ElseTemplate {
        cond: bool,
    }

    let s = ElseTemplate { cond: false };
    assert_eq!(s.render().unwrap(), "false");
}

#[test]
fn test_else_if() {
    #[derive(Template)]
    #[template(path = "else-if.html")]
    struct ElseIfTemplate {
        cond: bool,
        check: bool,
    }

    let s = ElseIfTemplate {
        cond: false,
        check: true,
    };
    assert_eq!(s.render().unwrap(), "checked");
}

#[test]
fn test_literals() {
    #[derive(Template)]
    #[template(path = "literals.html")]
    struct LiteralsTemplate {}

    let s = LiteralsTemplate {};
    assert_eq!(s.render().unwrap(), "a\na\ntrue\nfalse");
}

#[test]
fn test_literals_escape() {
    #[derive(Template)]
    #[template(path = "literals-escape.html")]
    struct LiteralsEscapeTemplate {}

    let s = LiteralsEscapeTemplate {};
    assert_eq!(
        s.render().unwrap(),
        "A\n\r\t\\\0♥&#39;&#34;&#34;\nA\n\r\t\\\0♥&#39;&#34;&#39;"
    );
}

#[test]
fn test_attr() {
    struct Holder {
        a: usize,
    }

    #[derive(Template)]
    #[template(path = "attr.html")]
    struct AttrTemplate {
        inner: Holder,
    }

    let t = AttrTemplate {
        inner: Holder { a: 5 },
    };
    assert_eq!(t.render().unwrap(), "5");
}

#[test]
fn test_tuple_attr() {
    #[derive(Template)]
    #[template(path = "tuple-attr.html")]
    struct TupleAttrTemplate<'a> {
        tuple: (&'a str, &'a str),
    }

    let t = TupleAttrTemplate {
        tuple: ("foo", "bar"),
    };
    assert_eq!(t.render().unwrap(), "foobar");
}

#[test]
fn test_nested_attr() {
    struct Holder {
        a: usize,
    }

    struct NestedHolder {
        holder: Holder,
    }

    #[derive(Template)]
    #[template(path = "nested-attr.html")]
    struct NestedAttrTemplate {
        inner: NestedHolder,
    }

    let t = NestedAttrTemplate {
        inner: NestedHolder {
            holder: Holder { a: 5 },
        },
    };
    assert_eq!(t.render().unwrap(), "5");
}

#[test]
fn test_option() {
    #[derive(Template)]
    #[template(path = "option.html")]
    struct OptionTemplate<'a> {
        var: Option<&'a str>,
    }

    let some = OptionTemplate { var: Some("foo") };
    assert_eq!(some.render().unwrap(), "some: foo");
    let none = OptionTemplate { var: None };
    assert_eq!(none.render().unwrap(), "none");
}

#[test]
fn test_option_none_some() {
    #[derive(Template)]
    #[template(source = "{{ Self::foo(None) }} {{ Self::foo(Some(1)) }}", ext = "txt")]
    struct OptionNoneSomeTemplate;

    impl OptionNoneSomeTemplate {
        fn foo(x: Option<i32>) -> i32 {
            x.unwrap_or_default()
        }
    }

    let t = OptionNoneSomeTemplate;
    assert_eq!(t.render().unwrap(), "0 1");
}

#[test]
fn test_generics() {
    #[derive(Template)]
    #[template(path = "generics.html")]
    struct GenericsTemplate<T, U = u8>
    where
        T: std::fmt::Display,
        U: std::fmt::Display,
    {
        t: T,
        u: U,
    }

    let t = GenericsTemplate { t: "a", u: 42 };
    assert_eq!(t.render().unwrap(), "a42");
}

#[test]
fn test_composition() {
    #[derive(Template)]
    #[template(path = "if.html")]
    struct IfTemplate {
        cond: bool,
    }

    #[derive(Template)]
    #[template(path = "composition.html")]
    struct CompositionTemplate {
        foo: IfTemplate,
    }

    let t = CompositionTemplate {
        foo: IfTemplate { cond: true },
    };
    assert_eq!(t.render().unwrap(), "composed: true");
}

#[test]
fn test_path_compare() {
    #[derive(PartialEq, Eq)]
    enum Alphabet {
        Alpha,
    }

    #[derive(Template)]
    #[template(source = "{% if x == Alphabet::Alpha %}true{% endif %}", ext = "txt")]
    struct PathCompareTemplate {
        x: Alphabet,
    }

    let t = PathCompareTemplate { x: Alphabet::Alpha };
    assert_eq!(t.render().unwrap(), "true");
}

#[test]
fn test_slice_literal() {
    #[derive(Template)]
    #[template(
        source = "{% for i in [\"a\", \"\"] %}{{ i }}{% endfor %}",
        ext = "txt"
    )]
    struct ArrayTemplate {}

    let t = ArrayTemplate {};
    assert_eq!(t.render().unwrap(), "a");
}

#[test]
fn test_func_ref_call() {
    #[derive(Template)]
    #[template(source = "Hello, {{ world(\"123\", 4) }}!", ext = "txt")]
    struct FunctionRefTemplate;

    impl FunctionRefTemplate {
        fn world(&self, s: &str, v: u8) -> String {
            format!("world({s}, {v})")
        }
    }

    let t = FunctionRefTemplate;
    assert_eq!(t.render().unwrap(), "Hello, world(123, 4)!");
}

mod test_path_func_call {
    use askama::Template;

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn world2(s: &str, v: u8) -> String {
        format!("world{v}{s}")
    }

    #[derive(Template)]
    #[template(source = "Hello, {{ self::world2(\"123\", 4) }}!", ext = "txt")]
    struct PathFunctionTemplate;

    #[test]
    fn test_path_func_call() {
        assert_eq!(PathFunctionTemplate.render().unwrap(), "Hello, world4123!");
    }
}

#[test]
fn test_root_path_func_call() {
    #[derive(Template)]
    #[template(source = "{{ ::std::string::String::from(\"123\") }}", ext = "txt")]
    struct RootPathFunctionTemplate;

    assert_eq!(RootPathFunctionTemplate.render().unwrap(), "123");
}

#[test]
fn test_fn() {
    #[derive(Template)]
    #[template(source = "Hello, {{ Self::world3(self, \"123\", 4) }}!", ext = "txt")]
    struct FunctionTemplate;

    impl FunctionTemplate {
        #[allow(clippy::trivially_copy_pass_by_ref)]
        #[allow(dead_code)]
        fn world3(&self, s: &str, v: u8) -> String {
            format!("world{s}{v}")
        }
    }

    let t = FunctionTemplate;
    assert_eq!(t.render().unwrap(), "Hello, world1234!");
}

#[test]
fn test_comment() {
    #[derive(Template)]
    #[template(source = "  {# foo -#} ", ext = "txt")]
    struct CommentTemplate {}

    let t = CommentTemplate {};
    assert_eq!(t.render().unwrap(), "  ");
}

#[test]
fn test_negation() {
    #[derive(Template)]
    #[template(source = "{% if !foo %}Hello{% endif %}", ext = "txt")]
    struct NegationTemplate {
        foo: bool,
    }

    let t = NegationTemplate { foo: false };
    assert_eq!(t.render().unwrap(), "Hello");
}

#[test]
fn test_minus() {
    #[derive(Template)]
    #[template(source = "{% if foo > -2 %}Hello{% endif %}", ext = "txt")]
    struct MinusTemplate {
        foo: i8,
    }

    let t = MinusTemplate { foo: 1 };
    assert_eq!(t.render().unwrap(), "Hello");
}

#[test]
fn test_index() {
    #[derive(Template)]
    #[template(source = "{{ foo[\"bar\"] }}", ext = "txt")]
    struct IndexTemplate {
        foo: HashMap<String, String>,
    }

    let mut foo = HashMap::new();
    foo.insert("bar".into(), "baz".into());
    let t = IndexTemplate { foo };
    assert_eq!(t.render().unwrap(), "baz");
}

#[test]
fn test_empty() {
    #[derive(Template)]
    #[template(source = "foo", ext = "txt")]
    struct Empty;

    assert_eq!(Empty.render().unwrap(), "foo");
}

#[test]
fn test_raw_simple() {
    #[derive(Template)]
    #[template(path = "raw-simple.html")]
    struct RawTemplate;

    let template = RawTemplate;
    assert_eq!(template.render().unwrap(), "\n<span>{{ name }}</span>\n");
}

#[test]
fn test_raw_complex() {
    #[derive(Template)]
    #[template(path = "raw-complex.html")]
    struct RawTemplateComplex;

    let template = RawTemplateComplex;
    assert_eq!(
        template.render().unwrap(),
        "\n{% block name %}\n  <span>{{ name }}</span>\n{% endblock %}\n"
    );
}

#[test]
fn test_raw_ws() {
    #[derive(Template)]
    #[template(path = "raw-ws.html")]
    struct RawTemplateWs;

    let template = RawTemplateWs;
    assert_eq!(template.render().unwrap(), "<{{hello}}>\n<{{bye}}>");
}

mod without_import_on_derive {
    #[derive(askama::Template)]
    #[template(source = "foo", ext = "txt")]
    struct WithoutImport;

    #[test]
    fn test_without_import() {
        use askama::Template;
        assert_eq!(WithoutImport.render().unwrap(), "foo");
    }
}

#[test]
fn test_define_string_var() {
    #[derive(askama::Template)]
    #[template(source = "{% let s = String::new() %}{{ s }}", ext = "txt")]
    struct DefineStringVar;

    let template = DefineStringVar;
    assert_eq!(template.render().unwrap(), "");
}

#[test]
fn test_simple_float() {
    #[derive(askama::Template)]
    #[template(source = "{% let x = 4.5 %}{{ x }}", ext = "html")]
    struct SimpleFloat;

    let template = SimpleFloat;
    assert_eq!(template.render().unwrap(), "4.5");
}

#[test]
fn test_num_literals() {
    #[derive(askama::Template)]
    #[template(path = "num-literals.html")]
    struct NumLiterals;

    let template = NumLiterals;
    assert_eq!(
        template.render().unwrap(),
        "[90, -90, 90, 2, 56, 240, 10.5, 10.5, 100000000000, 105000000000]\n1\n12",
    );
}

/// Test that we can use mixed case in variable names
///
/// We use some heuristics to distinguish paths (`std::str::String`) from
/// variable names (`foo`). Previously, this test would fail because any
/// name containing uppercase characters would be considered a path.
///
/// <https://github.com/askama-rs/askama/issues/924>
#[test]
fn test_mixed_case() {
    #[allow(non_snake_case)]
    #[derive(askama::Template)]
    #[template(source = "{{ xY }}", ext = "txt")]
    struct MixedCase {
        xY: &'static str,
    }

    let template = MixedCase { xY: "foo" };
    assert_eq!(template.render().unwrap(), "foo");
}

#[test]
#[allow(clippy::needless_borrows_for_generic_args)]
fn test_referenced() {
    #[allow(non_snake_case)]
    #[derive(askama::Template)]
    #[template(source = "Hello, {{ user }}!", ext = "txt")]
    struct Referenced {
        user: &'static str,
    }

    fn template_to_string(template: impl Template) -> String {
        template.to_string()
    }

    let template = Referenced { user: "person" };
    assert_eq!(template_to_string(&&template), "Hello, person!");
    assert_eq!(template_to_string(&template), "Hello, person!");
    assert_eq!(template_to_string(template), "Hello, person!");
}

#[test]
fn test_i16_to_u8() {
    #[derive(askama::Template)]
    #[template(
        source = "{{ input as u8 }} {{ &input as u8 }} {{ &&input as u8 }}",
        ext = "txt"
    )]
    struct TestI16ToU8 {
        input: i16,
    }

    assert_eq!(TestI16ToU8 { input: 0 }.to_string(), "0 0 0");
    assert_eq!(TestI16ToU8 { input: 0x7f00 }.to_string(), "0 0 0");
    assert_eq!(TestI16ToU8 { input: 255 }.to_string(), "255 255 255");
    assert_eq!(TestI16ToU8 { input: -12345 }.to_string(), "199 199 199");
}

#[test]
fn test_split_template_declaration() {
    #[derive(Template)]
    #[template(source = "🙂")]
    #[template(ext = "txt")]
    struct SplitTemplateDeclaration;

    assert_eq!(SplitTemplateDeclaration.to_string(), "🙂");
}

#[test]
fn test_ref_custom_type() {
    const TEXT: &str = "&this <is >not 'safe";

    struct MySafeType;

    impl HtmlSafe for MySafeType {}

    impl fmt::Display for MySafeType {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(TEXT)
        }
    }

    #[derive(Template)]
    #[template(ext = "html", source = "{{ data }}")]
    struct MyTemplate<'a, 'b, 'c> {
        data: &'a mut RefMut<'b, Pin<Arc<MutexGuard<'c, MySafeType>>>>,
    }

    let mutex = Mutex::new(MySafeType);
    let cell = RefCell::new(Arc::pin(mutex.try_lock().unwrap()));
    let tmpl = MyTemplate {
        data: &mut cell.try_borrow_mut().unwrap(),
    };
    assert_eq!(tmpl.render().unwrap(), TEXT);
}

#[test]
fn test_concat_outer() {
    #[derive(Template)]
    #[template(ext = "html", source = r#"{{ "<" ~ a ~ '>' }}"#)]
    struct ConcatOuter {
        a: &'static str,
    }

    assert_eq!(ConcatOuter { a: "'" }.to_string(), "&#60;&#39;&#62;");
}

#[test]
fn test_concat_inner() {
    #[derive(Template)]
    #[template(ext = "html", source = r#"{{ ("<" ~ a ~ '>')|urlencode }}"#)]
    struct ConcatInner {
        a: &'static str,
    }

    assert_eq!(ConcatInner { a: "'" }.to_string(), "%3C%27%3E");
}

#[test]
fn test_either() {
    #[derive(Template)]
    #[template(ext = "html", source = "Left")]
    struct Left;

    #[derive(Template)]
    #[template(ext = "html", source = "Right")]
    struct Right;

    type Direction = Either<Left, Right>;
    type OtherDirection = Either<Right, Left>;

    assert_eq!(Direction::Left(Left).to_string(), "Left");
    assert_eq!(Direction::Right(Right).to_string(), "Right");
    assert_eq!(OtherDirection::Left(Right).to_string(), "Right");
    assert_eq!(OtherDirection::Right(Left).to_string(), "Left");
}
