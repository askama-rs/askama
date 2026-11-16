use std::hint::black_box;

use askama::Template;
use criterion::{Criterion, criterion_group, criterion_main};

criterion_main!(benches);
criterion_group!(benches, functions);

fn functions(c: &mut Criterion) {
    #[derive(Template)]
    #[template(ext = "txt", source = "{{ self.0|lower }}")]
    struct Lower<'a>(&'a str);

    #[derive(Template)]
    #[template(ext = "txt", source = "{{ self.0|upper }}")]
    struct Upper<'a>(&'a str);

    #[derive(Template)]
    #[template(ext = "txt", source = "{{ self.0|capitalize }}")]
    struct Capitalize<'a>(&'a str);

    #[derive(Template)]
    #[template(ext = "txt", source = "{{ self.0|title }}")]
    struct Title<'a>(&'a str);

    #[derive(Template)]
    #[template(ext = "txt", source = "{{ self.0|trim }}")]
    struct Trim<'a>(&'a str);

    macro_rules! bench {
        ($tmpl:ident, $name:literal, $input:expr) => {
            c.bench_function(concat!(stringify!($tmpl), " ", $name), |b| {
                let mut dest = String::new();
                b.iter(|| {
                    dest.clear();
                    $tmpl(black_box($input)).render_into(&mut dest).unwrap();
                    dest.len()
                })
            });
        };
    }

    bench!(Lower, "word", WORD);
    bench!(Lower, "short", SHORT);
    bench!(Lower, "words", WORDS);
    bench!(Lower, "lorem", LOREM);
    bench!(Lower, "last non-ascii", LAST_NON_ASCII);
    bench!(Lower, "umlauts", UMLAUTS);
    bench!(Upper, "word", WORD);
    bench!(Upper, "short", SHORT);
    bench!(Upper, "umlauts", UMLAUTS);
    bench!(Capitalize, "word", WORD);
    bench!(Capitalize, "short", SHORT);
    bench!(Capitalize, "umlauts", UMLAUTS);
    bench!(Title, "word", WORD);
    bench!(Title, "short", SHORT);
    bench!(Title, "words", WORDS);
    bench!(Title, "lorem", LOREM);
    bench!(Title, "umlauts", UMLAUTS);
    bench!(Trim, "short", PADDED);
    bench!(Trim, "lorem", LOREM);
}

const WORD: &str = "Hello";
const SHORT: &str = "Hello World";
const WORDS: &str = "the quick brown fox jumps over the lazy dog";
const PADDED: &str = "  Hello World  ";
const LAST_NON_ASCII: &str = "the quick brown fox jumps over the lazy dö";
const UMLAUTS: &str = "Grüße aus Köln, Zürich und Århus ÄÖÜ";
const LOREM: &str = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Mauris consequat \
    tellus sit amet ornare fermentum. Etiam nec erat ante. In at metus a orci mollis scelerisque. \
    Sed eget ultrices turpis, at sollicitudin erat. Integer hendrerit nec magna quis venenatis. \
    Vivamus non dolor hendrerit, vulputate velit sed, varius nunc. Quisque in pharetra mi. Sed \
    ullamcorper nibh malesuada commodo porttitor. Ut scelerisque sodales felis quis dignissim. \
    Morbi aliquam finibus justo, sit amet consectetur mauris efficitur sit amet. Donec posuere \
    turpis felis, eu lacinia magna accumsan quis. Fusce egestas lacus vel fermentum tincidunt. \
    Phasellus a nulla commodo, malesuada orci in, pellentesque sem. Duis id eros sed lectus \
    porttitor lobortis. Integer at lectus vel enim gravida venenatis. Mauris interdum magna \
    sit amet nulla pellentesque, ut porta mi elementum.";
