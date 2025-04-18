use std::hint::black_box;
use std::iter::repeat_n;

use askama::Template;
use criterion::{Criterion, criterion_group, criterion_main};

criterion_main!(benches);
criterion_group!(benches, functions);

fn functions(c: &mut Criterion) {
    c.bench_function("Big table", big_table);
    c.bench_function("Big table (fmt)", big_table_fmt);
    c.bench_function("Big table (io)", big_table_io);

    c.bench_function("Teams", teams);
    c.bench_function("Teams (fmt)", teams_fmt);
    c.bench_function("Teams (io)", teams_io);
}

fn big_table(b: &mut criterion::Bencher) {
    let ctx = BigTable::default();
    b.iter(|| black_box(&ctx).render().unwrap());
}

fn big_table_fmt(b: &mut criterion::Bencher) {
    let ctx = BigTable::default();
    b.iter(|| black_box(&ctx).to_string());
}

fn big_table_io(b: &mut criterion::Bencher) {
    let ctx = BigTable::default();
    b.iter(|| {
        let mut vec = Vec::with_capacity(BigTable::SIZE_HINT);
        black_box(&ctx).write_into(&mut vec).unwrap();
        vec
    });
}

#[derive(Template)]
#[template(path = "big-table.html")]
struct BigTable {
    table: Vec<Vec<usize>>,
}

impl Default for BigTable {
    fn default() -> Self {
        const SIZE: usize = 100;

        BigTable {
            table: repeat_n((0..SIZE).collect(), SIZE).collect(),
        }
    }
}

fn teams(b: &mut criterion::Bencher) {
    let teams = Teams::default();
    b.iter(|| black_box(&teams).render().unwrap());
}

fn teams_fmt(b: &mut criterion::Bencher) {
    let teams = Teams::default();
    b.iter(|| black_box(&teams).to_string());
}

fn teams_io(b: &mut criterion::Bencher) {
    let teams = Teams::default();
    b.iter(|| {
        let mut vec = Vec::with_capacity(BigTable::SIZE_HINT);
        black_box(&teams).write_into(&mut vec).unwrap();
        vec
    });
}

#[derive(Template)]
#[template(path = "teams.html")]
struct Teams {
    year: u16,
    teams: Vec<Team>,
}

impl Default for Teams {
    fn default() -> Self {
        Teams {
            year: 2015,
            teams: vec![
                Team {
                    name: "Jiangsu".into(),
                    score: 43,
                },
                Team {
                    name: "Beijing".into(),
                    score: 27,
                },
                Team {
                    name: "Guangzhou".into(),
                    score: 22,
                },
                Team {
                    name: "Shandong".into(),
                    score: 12,
                },
            ],
        }
    }
}

struct Team {
    name: String,
    score: u8,
}
