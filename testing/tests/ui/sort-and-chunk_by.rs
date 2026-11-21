use askama::Template;

// `sort` takes one comparator, not a key and a comparator.
#[derive(Template)]
#[template(source = "{{ numbers|sort(|n| n, |a, b| a.cmp(b))|join(\",\") }}", ext = "txt")]
struct SortTwoArguments {
    numbers: Vec<u32>,
}

// `chunk_by` has no default key.
#[derive(Template)]
#[template(source = "{% for (n, ns) in numbers|chunk_by %}{% endfor %}", ext = "txt")]
struct ChunkByWithoutKey {
    numbers: Vec<u32>,
}

fn main() {}
