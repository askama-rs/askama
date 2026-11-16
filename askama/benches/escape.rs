use std::hint::black_box;

use askama::Template;
use askama::filters::{Html, escape};
use criterion::{Criterion, criterion_group, criterion_main};

criterion_main!(benches);
criterion_group!(benches, functions);

fn functions(c: &mut Criterion) {
    c.bench_function("Escaping", escaping);
    c.bench_function("Template short", |b| template(b, SHORT));
    c.bench_function("Template medium", |b| template(b, MEDIUM));
    c.bench_function("Template mixed", |b| template(b, MIXED));
    c.bench_function("Template strings.inc", |b| template(b, STRINGS));
}

fn escaping(b: &mut criterion::Bencher<'_>) {
    b.iter(|| {
        for &s in black_box(STRINGS) {
            let _ = black_box(format!("{}", escape(s, Html).unwrap()));
        }
    });
}

/// Writes every string through `&mut dyn fmt::Write`, as a generated template does.
fn template(b: &mut criterion::Bencher<'_>, strings: &'static [&'static str]) {
    #[derive(Template)]
    #[template(ext = "html", source = "{% for s in self.0 %}{{ s }}{% endfor %}")]
    struct Tmpl(&'static [&'static str]);

    let mut dest = String::new();
    b.iter(|| {
        dest.clear();
        Tmpl(black_box(strings)).render_into(&mut dest).unwrap();
        dest.len()
    });
}

const STRINGS: &[&str] = include!("strings.inc");

/// Nothing to escape, 0 to 16 bytes each.
const SHORT: &[&str] = &[
    "",
    "a",
    "foo",
    "Hello",
    "user_name",
    "0123456789",
    "Hello, World",
    "sixteen bytes ok",
];

/// Nothing to escape, 43 to 57 bytes each.
const MEDIUM: &[&str] = &[
    "The quick brown fox jumps over the lazy dog",
    "Lorem ipsum dolor sit amet, consectetur adipiscing elit",
    "Grüße aus Köln, Zürich und Århus, bis bald und danke",
];

/// 45 of the 94 bytes need escaping.
const MIXED: &[&str] = &[
    r#"<a href="/x?a=1&b=2">'q' & "r"</a>"#,
    r#"<<"a" & 'b'>> <i>&"c"&</i> <>"#,
    r#"<p class="x">&lt;&'&'&gt;</p>&&"#,
];
