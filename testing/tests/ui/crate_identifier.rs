use askama::Template;

#[derive(Template)]
#[template(ext = "html", source = "{{ crate }}")]
struct Crate;

#[derive(Template)]
#[template(ext = "html", source = "{% if crate == 12 %}{% endif %}")]
struct Crate2;

#[derive(Template)]
#[template(ext = "html", source = "{% match crate %}{% endmatch %}")]
struct Crate3;

#[derive(Template)]
#[template(ext = "html", source = "{% let crate %}")]
struct Crate4;

#[derive(Template)]
#[template(ext = "html", source = "{% let crate = 12 %}")]
struct Crate5;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.a.crate }}")]
struct Crate6 {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{{ super }}")]
struct Super;

#[derive(Template)]
#[template(ext = "html", source = "{% if super == 12 %}{% endif %}")]
struct Super2;

#[derive(Template)]
#[template(ext = "html", source = "{% match super %}{% endmatch %}")]
struct Super3;

#[derive(Template)]
#[template(ext = "html", source = "{% let super %}")]
struct Super4;

#[derive(Template)]
#[template(ext = "html", source = "{% let super = 12 %}")]
struct Super5;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.a.super }}")]
struct Super6 {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{{ Self }}")]
struct Self1;

#[derive(Template)]
#[template(ext = "html", source = "{% if Self == 12 %}{% endif %}")]
struct Self2;

#[derive(Template)]
#[template(ext = "html", source = "{% match Self %}{% endmatch %}")]
struct Self3;

#[derive(Template)]
#[template(ext = "html", source = "{% let Self %}")]
struct Self4;

#[derive(Template)]
#[template(ext = "html", source = "{% let Self = 12 %}")]
struct Self5;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.a.Self }}")]
struct Self6 {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% let self %}")]
struct SmallSelf;

#[derive(Template)]
#[template(ext = "html", source = "{% let self = 12 %}")]
struct SmallSelf2;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.a.self }}")]
struct SmallSelf3 {
    a: u8,
}

// Regression test for <https://github.com/askama-rs/askama/issues/449>.
#[derive(Template)]
#[template(
    ext = "",
    source = "{{\u{c}KK3e331<c7}}61/63m3333u7<c0.}}\u{6}\0\u{c}\u{c}{{c/crate<338}}6unsafe/63a3ae\u{c}\u{c}\u{c}%et"
)]
struct Regression {}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when a::b::super %}{% endmatch %}")]
struct PathElemSuper {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when self::a::b::super %}{% endmatch %}")]
struct PathElemSuper2 {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when a::b::self %}{% endmatch %}")]
struct PathElemSelf {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when self::a::b::self %}{% endmatch %}")]
struct PathElemSelf2 {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when a::b::crate %}{% endmatch %}")]
struct PathElemCrate {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when self::a::b::crate %}{% endmatch %}")]
struct PathElemCrate2 {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when a::b::Self %}{% endmatch %}")]
struct PathElemSelfType {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{% match a %}{% when self::a::b::Self %}{% endmatch %}")]
struct PathElemSelfType2 {
    a: u8,
}

#[derive(Template)]
#[template(ext = "html", source = "{{ Self.4 }}")]
struct InvalidRawIdentifierSelfTyInAttr1;

#[derive(Template)]
#[template(ext = "html", source = "{{ super.4 }}")]
struct InvalidRawIdentifierSuperInAttr1;

#[derive(Template)]
#[template(ext = "html", source = "{{ crate.4 }}")]
struct InvalidRawIdentifierCrateInAttr1;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.Self.4 }}")]
struct InvalidRawIdentifierSelfTyInAttr2;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.super.4 }}")]
struct InvalidRawIdentifierSuperInAttr2;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.crate.4 }}")]
struct InvalidRawIdentifierCrateInAttr2;

#[derive(Template)]
#[template(ext = "html", source = "{{ self.self.4 }}")]
struct InvalidRawIdentifierSelfInAttr;

fn main() {}
