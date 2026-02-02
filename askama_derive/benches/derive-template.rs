use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use quote::quote;

criterion_main!(benches);
criterion_group!(benches, hello_world, librustdoc);

fn extern_crate_askama() -> proc_macro2::TokenStream {
    quote! {
        extern crate askama;
    }
}

fn hello_world(c: &mut Criterion) {
    let source = "<html><body><h1>Hello, {{user}}!</h1></body></html>";
    let ts = quote! {
        #[derive(Template)]
        #[template(
            source = #source,
            ext = "html"
        )]
        struct Hello<'a> {
            user: &'a str,
        }
    };

    let mut g = c.benchmark_group("synthetic");
    g.throughput(Throughput::Bytes(source.len().try_into().unwrap()));
    g.bench_function("hello_world", |b| {
        b.iter_batched(
            || ts.clone(),
            |ts| askama_derive::derive_template(black_box(ts), extern_crate_askama),
            BatchSize::LargeInput,
        );
    });
    g.finish();
}

fn librustdoc(c: &mut Criterion) {
    let mut g = c.benchmark_group("librustdoc");

    macro_rules! benches {
        ($($name:expr => $struct:item)*) => { $({
            const SOURCE: &str =
                include_str!(concat!("../../askama_parser/benches/librustdoc/", $name));

            let ts = quote! {
                #[derive(Template)]
                #[template(source = #SOURCE, ext = "html")]
                $struct
            };
            g.throughput(Throughput::Bytes(SOURCE.len().try_into().unwrap()));
            g.bench_function($name, |b| {
                b.iter_batched(
                    || ts.clone(),
                    |input| askama_derive::derive_template(input, extern_crate_askama),
                    BatchSize::LargeInput,
                )
            });
        })* };
    }

    benches! {
        "item_info.html" =>
        struct ItemInfo {
            items: Vec<ShortItemInfo>,
        }

        "item_union.html" =>
        struct ItemUnion<'a, 'cx> {
            cx: RefCell<&'a mut Context<'cx>>,
            it: &'a clean::Item,
            s: &'a clean::Union,
        }

        "page.html" =>
        struct PageLayout<'a> {
            static_root_path: String,
            page: &'a Page<'a>,
            layout: &'a Layout,
            files: &'static StaticFiles,
            themes: Vec<String>,
            sidebar: String,
            content: String,
            rust_channel: &'static str,
            pub(crate) rustdoc_version: &'a str,
            display_krate: &'a str,
            display_krate_with_trailing_slash: String,
            display_krate_version_number: &'a str,
            display_krate_version_extra: &'a str,
        }

        "print_item.html" =>
        struct ItemVars<'a> {
            typ: &'a str,
            name: &'a str,
            item_type: &'a str,
            path_components: Vec<PathComponent>,
            stability_since_raw: &'a str,
            src_href: Option<&'a str>,
        }

        "short_item_info.html" =>
        enum ShortItemInfo {
            /// A message describing the deprecation of this item
            Deprecation {
                message: String,
            },
            /// The feature corresponding to an unstable item, and optionally
            /// a tracking issue URL and number.
            Unstable {
                feature: String,
                tracking: Option<(String, u32)>,
            },
            Portability {
                message: String,
            },
        }

        "sidebar.html" =>
        pub(super) struct Sidebar<'a> {
            pub(super) title_prefix: &'static str,
            pub(super) title: &'a str,
            pub(super) is_crate: bool,
            pub(super) is_mod: bool,
            pub(super) blocks: Vec<LinkBlock<'a>>,
            pub(super) path: String,
        }

        "source.html" =>
        struct Source<Code: std::fmt::Display> {
            embedded: bool,
            needs_expansion: bool,
            lines: RangeInclusive<usize>,
            code_html: Code,
        }

        "type_layout.html" =>
        struct TypeLayout<'cx> {
            variants: Vec<(Symbol, TypeLayoutSize)>,
            type_layout_size: Result<TypeLayoutSize, &'cx LayoutError<'cx>>,
        }

        "type_layout_size.html" =>
        struct TypeLayoutSize {
            is_unsized: bool,
            is_uninhabited: bool,
            size: u64,
        }
    }
    g.finish();
}
