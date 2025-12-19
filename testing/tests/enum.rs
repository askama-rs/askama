use std::any::type_name_of_val;
use std::fmt::{Debug, Display};

use askama::Template;
use assert_matches::assert_matches;

#[test]
fn test_book_example() {
    #[derive(Template, Debug)]
    #[template(
        source = "
            {%- match self -%}
                {%- when Self::Square(side) -%}      {{side}}^2
                {%- when Self::Rectangle { a, b} -%} {{a}} * {{b}}
                {%- when Self::Circle { radius } -%} pi * {{radius}}^2
            {%- endmatch -%}
        ",
        ext = "txt"
    )]
    enum AreaWithMatch {
        #[template(source = "{{self.0}}^2", ext = "txt")]
        Square(f32),
        #[template(source = "{{a}} * {{b}}", ext = "txt")]
        Rectangle { a: f32, b: f32 },
        #[template(source = "pi * {{radius}}^2", ext = "txt")]
        Circle { radius: f32 },
    }

    assert_eq!(AreaWithMatch::Square(2.0).render().unwrap(), "2^2");
    assert_eq!(
        AreaWithMatch::Rectangle { a: 1.0, b: 2.0 }
            .render()
            .unwrap(),
        "1 * 2",
    );
    assert_eq!(
        AreaWithMatch::Circle { radius: 3.0 }.render().unwrap(),
        "pi * 3^2"
    );

    #[derive(Template, Debug)]
    enum AreaPerVariant {
        #[template(source = "{{self.0}}^2", ext = "txt")]
        Square(f32),
        #[template(source = "{{a}} * {{b}}", ext = "txt")]
        Rectangle { a: f32, b: f32 },
        #[template(source = "pi * {{radius}}^2", ext = "txt")]
        Circle { radius: f32 },
    }

    assert_eq!(AreaPerVariant::Square(2.0).render().unwrap(), "2^2");
    assert_eq!(
        AreaPerVariant::Rectangle { a: 1.0, b: 2.0 }
            .render()
            .unwrap(),
        "1 * 2",
    );
    assert_eq!(
        AreaPerVariant::Circle { radius: 3.0 }.render().unwrap(),
        "pi * 3^2"
    );

    #[derive(Template, Debug)]
    #[template(
        source = "
            {%- block square -%}
                {{self.0}}^2
            {%- endblock -%}
            {%- block rectangle -%}
                {{a}} * {{b}}
            {%- endblock -%}
            {%- block circle -%}
                pi * {{radius}}^2
            {%- endblock -%}
        ",
        ext = "txt"
    )]
    enum AreaWithBlocks {
        #[template(block = "square")]
        Square(f32),
        #[template(block = "rectangle")]
        Rectangle { a: f32, b: f32 },
        #[template(block = "circle")]
        Circle { radius: f32 },
    }

    assert_eq!(AreaWithBlocks::Square(2.0).render().unwrap(), "2^2");
    assert_eq!(
        AreaWithBlocks::Rectangle { a: 1.0, b: 2.0 }
            .render()
            .unwrap(),
        "1 * 2",
    );
    assert_eq!(
        AreaWithBlocks::Circle { radius: 3.0 }.render().unwrap(),
        "pi * 3^2"
    );
}

#[test]
fn test_simple_enum() {
    #[derive(Template, Debug)]
    #[template(
        ext = "txt",
        source = "{{ self::type_name_of_val(self) }} | {{ self.bar() }}"
    )]
    enum SimpleEnum<'a, B: Display + Debug> {
        #[template(source = "A")]
        A,
        #[template(source = "B()")]
        B(),
        #[template(source = "C({{self.0}}, {{self.1}})")]
        C(u32, u32),
        #[template(source = "D {}")]
        D {},
        #[template(source = "E { a: {{a}}, b: {{b}} }")]
        E {
            a: &'a str,
            b: B,
        },
        // uses default source with `SimpleEnum` as `Self`
        F,
        // uses default source with a synthetic type `__Askama__SimpleEnum__G` as `Self`
        #[template()]
        G,
    }

    impl<'a, B: Display + Debug> SimpleEnum<'a, B> {
        fn bar(&self) -> &str {
            match self {
                Self::F => "F",
                Self::G => "G",
                _ => "",
            }
        }
    }

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::A;
    assert_eq!(tmpl.render().unwrap(), "A");

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::B();
    assert_eq!(tmpl.render().unwrap(), "B()");

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::C(12, 34);
    assert_eq!(tmpl.render().unwrap(), "C(12, 34)");

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::C(12, 34);
    assert_eq!(tmpl.render().unwrap(), "C(12, 34)");

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::D {};
    assert_eq!(tmpl.render().unwrap(), "D {}");

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::E { a: "hello", b: X };
    assert_eq!(tmpl.render().unwrap(), "E { a: hello, b: X }");

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::F;
    assert_matches!(
        tmpl.render().unwrap().as_str(),
        "&enum::test_simple_enum::SimpleEnum<enum::X> | F"
        // output since rustc 1.91.0-nightly 2025-08-17
        | "&enum::test_simple_enum::SimpleEnum<'_, enum::X> | F"
    );

    let tmpl: SimpleEnum<'_, X> = SimpleEnum::G;
    assert_matches!(
        tmpl.render().unwrap().as_str(),
        "&enum::test_simple_enum::_::__Askama__SimpleEnum__G<enum::X> | G"
        // output since rustc 1.91.0-nightly 2025-08-17
        | "&enum::test_simple_enum::_::__Askama__SimpleEnum__G<'_, '_, enum::X> | G"
    );
}

#[test]
fn test_enum_blocks() {
    #[derive(Template, Debug)]
    #[template(
        ext = "txt",
        source = "\
            {% block a -%} <a = {{ a }}> {%- endblock %}
            {% block b -%} <b = {{ b }}> {%- endblock %}
            {% block c -%} <c = {{ c }}> {%- endblock %}
            {% block d -%} <d = {{ self::type_name_of_val(self) }}> {%- endblock %}
        "
    )]
    enum BlockEnum<'a, C: Display> {
        #[template(block = "a")]
        A { a: u32 },
        #[template(block = "b")]
        B { b: &'a str },
        #[template(block = "c")]
        C { c: C },
        #[template(block = "d")]
        D,
    }

    let tmpl: BlockEnum<'_, X> = BlockEnum::A { a: 42 };
    assert_eq!(tmpl.render().unwrap(), "<a = 42>");

    let tmpl: BlockEnum<'_, X> = BlockEnum::B { b: "second letter" };
    assert_eq!(tmpl.render().unwrap(), "<b = second letter>");

    let tmpl: BlockEnum<'_, X> = BlockEnum::C { c: X };
    assert_eq!(tmpl.render().unwrap(), "<c = X>");

    assert_matches!(
        BlockEnum::<'_, X>::D.render().unwrap().as_str(),
        "<d = &enum::test_enum_blocks::_::__Askama__BlockEnum__D<enum::X>>"
        // output since rustc 1.91.0-nightly 2025-08-17
        | "<d = &enum::test_enum_blocks::_::__Askama__BlockEnum__D<'_, '_, enum::X>>"
    );
}

#[test]
fn associated_constants() {
    #[derive(Template, Debug)]
    #[template(
        ext = "txt",
        source = "\
            {% block a -%} {{ Self::CONST_A }} {{ self.0 }} {%- endblock %}
            {% block b -%} {{ Self::CONST_B }} {{ self.0 }} {%- endblock %}
            {% block c -%} {{ Self::func_c(self.0) }} {{ self.0 }} {%- endblock %}
        "
    )]
    enum BlockEnum<'a, T: Display> {
        #[template(block = "a")]
        A(&'a str),
        #[template(block = "b")]
        B(T),
        #[template(block = "c")]
        C(&'a T),
    }

    impl<'a, T: Display> BlockEnum<'a, T> {
        const CONST_A: &'static str = "<A>";
        const CONST_B: &'static str = "<B>";

        fn func_c(_: &'a T) -> &'static str {
            "<C>"
        }
    }

    let tmpl: BlockEnum<'_, X> = BlockEnum::A("hello");
    assert_eq!(tmpl.render().unwrap(), "<A> hello");

    let tmpl: BlockEnum<'_, X> = BlockEnum::B(X);
    assert_eq!(tmpl.render().unwrap(), "<B> X");

    let tmpl: BlockEnum<'_, X> = BlockEnum::C(&X);
    assert_eq!(tmpl.render().unwrap(), "<C> X");
}

#[derive(Debug)]
struct X;

impl Display for X {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("X")
    }
}
