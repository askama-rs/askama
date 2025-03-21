use askama_escape::escape_html;
use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};

criterion_main!(benches);
criterion_group!(benches, functions);

fn functions(c: &mut Criterion) {
    c.bench_function("escape_html", escaping);
    let mut g = c.benchmark_group("all");
    let bytes = STRINGS.iter().map(|s| s.len() as u64).sum();
    g.throughput(Throughput::Bytes(bytes));
    g.bench_function("escape_html", escaping);
    g.finish();
}

fn escaping(b: &mut criterion::Bencher<'_>) {
    let mut dest = String::new();
    b.iter(|| {
        for &s in black_box(STRINGS) {
            dest.clear();
            black_box(escape_html(&mut dest, s)).unwrap();
        }
    });
}

const STRINGS: &[&str] = include!("strings.inc");
