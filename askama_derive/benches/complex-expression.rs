use std::fmt::Write;
use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use quote::quote;
use rand::SeedableRng;
use rand::seq::SliceRandom;
use rand_xoshiro::Xoroshiro64StarStar;

criterion_main!(benches);
criterion_group!(benches, binary_ops);

fn extern_crate_askama() -> proc_macro2::TokenStream {
    quote! {
        extern crate askama;
    }
}

fn binary_ops(c: &mut Criterion) {
    let mut rng = Xoroshiro64StarStar::seed_from_u64(PRIME64);
    for (group_name, ops) in [
        // way up in the operator precedence
        ("range ops", ["..", "..="].as_slice()),
        // way down in the operator precedence
        ("mult ops", ["*", "/", "%"].as_slice()),
        // all over the place in the operator precedence
        ("mixed ops", BINARY_OPS),
    ] {
        let mut ops = ops.to_owned();
        let mut iter = std::slice::Iter::default();

        let mut g = c.benchmark_group(group_name);
        for count in [1, 10, 100] {
            let mut source = format!("{group_name}: {{ v0");
            for i in 1..=count {
                let op = if let Some(&op) = iter.next() {
                    op
                } else {
                    ops.shuffle(&mut rng);
                    iter = ops.iter();
                    iter.next().unwrap()
                };
                write!(source, " {op} v{i}").unwrap();
            }
            source.push_str(" }}.");

            let ts = quote! {
                #[derive(Template)]
                #[template(source = #source, ext = "html")]
                struct Synthetic;
            };

            g.throughput(Throughput::ElementsAndBytes {
                elements: count as u64,
                bytes: source.len() as u64,
            });
            g.bench_function(format!("x{count}"), |b| {
                b.iter_batched(
                    || ts.clone(),
                    |ts| askama_derive::derive_template(black_box(ts), extern_crate_askama),
                    BatchSize::LargeInput,
                );
            });
        }
        g.finish();
    }
}

const BINARY_OPS: &[&str] = &[
    "..", "..=", "||", "&&", "bitor", "xor", "bitand", ">>", "<<", "+", "-", "~", "*", "/", "%",
];

const PRIME64: u64 = 0xaaaaaaaaaaaaaa3f; // biggest prime less than 0xaa..aa_u64 (alternating bits)
