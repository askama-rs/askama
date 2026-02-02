use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Arguments;

use bitmaps::Bitmap;
use itertools::Itertools;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

fn main() {
    println!("// Generated using `scripts/make-buffer-write_token_str`.");
    println!("pub(crate) fn write_token_str(&mut self, op: &str, span: proc_macro2::Span) {{");
    println!("    type TokenFn = Option<fn(&mut TokenStream, proc_macro2::Span)>;");
    println!();
    println!("    #[allow(clippy::type_complexity)]");
    println!("    const OPERATORS: &[Option<(fn(&[u8]) -> u8, &[TokenFn])>] = &[");
    println!("        None,");
    println!("        Some((calc_op1, TABLE1)),");
    println!("        Some((calc_op2, TABLE2)),");
    println!("        Some((calc_op3, TABLE3)),");
    println!("        Some((calc_op4, TABLE4)),");
    println!("        Some((calc_op5, TABLE5)),");
    println!("        Some((calc_op6, TABLE6)),");
    println!("        Some((calc_op7, TABLE7)),");
    println!("        Some((calc_op8, TABLE8)),");
    println!("    ];");
    println!();

    calc_op1();
    calc_opn(2, "calc_op2");
    calc_opn(3, "calc_op3");
    calc_opn(4, "calc_op4");
    calc_opn(5, "calc_op5");
    calc_opn(6, "calc_op6");
    calc_opn(7, "calc_op7");
    calc_opn(8, "calc_op8");
    assert_eq!(OPERATORS.iter().map(|s| s.len()).max(), Some(8));

    println!("    if self.discard {{");
    println!("        return;");
    println!("    }}");
    println!("    self.handle_str_lit();");
    println!();
    println!("    if let Some(Some((calc, table))) = OPERATORS.get(op.len())");
    println!("        && let idx = calc(op.as_bytes())");
    println!("        && idx != u8::MAX");
    println!("        && let Some(Some(func)) = table.get(idx as usize)");
    println!("    {{");
    println!("        func(&mut self.buf, span);");
    println!("    }} else {{");
    println!(r#"        unreachable!("Unimplemented operator: `{{}}`", op.escape_debug());"#);
    println!("    }}");
    println!("}}");
}

fn calc_op1() {
    let ops: Vec<[u8; 1]> = OPERATORS
        .iter()
        .filter_map(|&s| s.as_bytes().as_array().copied())
        .collect_vec();

    let [factor, flip, rem, ..] = (0..256u32.pow(3))
        .into_par_iter()
        .filter_map(|idx| {
            let [factor, flip, rem, ..] = idx.to_le_bytes();
            if factor < 1 || (rem as usize) < ops.len() {
                return None;
            }

            let mut seen = Bitmap::<256>::new();
            let mut max_value = 0;
            for &[e] in ops.iter() {
                let value = (e.wrapping_mul(factor) ^ flip) % rem;
                if seen.set(value as usize, true) {
                    return None;
                }
                max_value = max_value.max(value);
            }

            Some((max_value, idx))
        })
        .min_by_key(|&(key, _)| key)
        .unwrap()
        .1
        .to_le_bytes();

    let mut map = BTreeMap::new();
    for op @ &[e] in ops.iter() {
        let value = (e.wrapping_mul(factor) ^ flip) % rem;
        assert_eq!(map.insert(value, str::from_utf8(op).unwrap()), None);
    }

    println!("    fn calc_op1(op: &[u8]) -> u8 {{");
    println!("        let &[op] = op else {{");
    println!("            return u8::MAX;");
    println!("        }};");
    print_calc_fn(
        &map,
        1,
        format_args!("(op.wrapping_mul({factor}) ^ {flip}) % {rem}"),
    );
}

fn calc_opn(n: u8, name: &str) {
    let (func, (_, key)) = [
        try_calc_front,
        try_calc_back,
        try_calc_skip,
        try_calc_extremes,
    ]
    .into_iter()
    .filter_map(|func| Some((func, func(n, name, 0)?)))
    .min_by_key(|&(_, (max_value, _))| max_value)
    .unwrap();
    func(n, name, key);
}

fn try_calc_front(n: u8, name: &str, key: u32) -> Option<(u8, u32)> {
    try_calc_impl(n, name, key, "[.., ea, ez]", |op| {
        if let &[.., a, z] = op {
            Some([a, z])
        } else {
            None
        }
    })
}

fn try_calc_back(n: u8, name: &str, key: u32) -> Option<(u8, u32)> {
    try_calc_impl(n, name, key, "[ea, ez, ..]", |op| {
        if let &[a, z, ..] = op {
            Some([a, z])
        } else {
            None
        }
    })
}

fn try_calc_extremes(n: u8, name: &str, key: u32) -> Option<(u8, u32)> {
    try_calc_impl(n, name, key, "[ea, .., ez]", |op| {
        if let &[a, .., z] = op {
            Some([a, z])
        } else {
            None
        }
    })
}

fn try_calc_skip(n: u8, name: &str, key: u32) -> Option<(u8, u32)> {
    try_calc_impl(n, name, key, "[ea, _, ez, ..]", |op| {
        if let &[a, _, z, ..] = op {
            Some([a, z])
        } else {
            None
        }
    })
}

fn try_calc_impl(
    n: u8,
    name: &str,
    key: u32,
    splat: &str,
    extract: fn(&[u8]) -> Option<[u8; 2]>,
) -> Option<(u8, u32)> {
    let ops: Vec<([u8; 2], &str)> = OPERATORS
        .iter()
        .filter_map(|&s| {
            if s.len() == n as usize
                && let Some(az) = extract(s.as_bytes())
            {
                Some((az, s))
            } else {
                None
            }
        })
        .collect_vec();
    if ops.iter().map(|&(op, _)| op).collect::<BTreeSet<_>>().len() != ops.len() {
        return None;
    }

    if key == 0 {
        return (0..256u32.pow(3))
            .into_par_iter()
            .filter_map(|idx| {
                let [fa, fz, rem, ..] = idx.to_le_bytes();
                if fa < 1 || fz < 1 || (rem as usize) < ops.len() {
                    return None;
                }

                let mut seen = Bitmap::<256>::new();
                let mut max_value = 0;
                for &([ea, ez], _) in ops.iter() {
                    let value = ea.wrapping_mul(fa).wrapping_add(ez.wrapping_mul(fz)) % rem;
                    if value == u8::MAX || seen.set(value as usize, true) {
                        return None;
                    }
                    max_value = max_value.max(value);
                }

                (max_value > 0).then_some((max_value, idx))
            })
            .min_by_key(|&(max_value, _)| max_value);
    }

    let [fa, fz, rem, ..] = key.to_le_bytes();

    let mut map = BTreeMap::new();
    for &([ea, ez], op) in ops.iter() {
        let value = ea.wrapping_mul(fa).wrapping_add(ez.wrapping_mul(fz)) % rem;
        if map.insert(value, op).is_some() {
            return None;
        }
    }

    println!("    fn {name}(op: &[u8]) -> u8 {{");

    let fa = if fa == 1 {
        "".to_owned()
    } else {
        format!(".wrapping_mul({fa})")
    };
    let fz = if fz == 1 {
        "".to_owned()
    } else {
        format!(".wrapping_mul({fz})")
    };

    if let 2 = n {
        println!("        let &[ea, ez] = op else {{")
    } else {
        println!("        let Ok(&{splat}): Result<&[u8; {n}], _> = op.try_into() else {{")
    }
    println!("            return u8::MAX;");
    println!("        }};");
    print_calc_fn(&map, n, format_args!("ea{fa}.wrapping_add(ez{fz}) % {rem}"));

    None
}

fn print_calc_fn(map: &BTreeMap<u8, &str>, n: u8, calc: Arguments<'_>) {
    println!("        {calc}");
    println!("    }}");
    println!();

    println!("    const TABLE{n}: &[TokenFn] = &[");
    for idx in 0..=*map.keys().last().unwrap() {
        if let Some(op) = map.get(&idx) {
            println!("        Some(|ts, span| Token![{op}](span).to_tokens(ts)),");
        } else {
            println!("        None,");
        }
    }
    println!("    ];");
    println!();
}

// per <https://docs.rs/syn/2.0.114/syn/macro.Token.html>
const OPERATORS: &[&str] = &[
    "abstract", "as", "async", "auto", "await", "become", "box", "break", "const", "continue",
    "crate", "default", "do", "dyn", "else", "enum", "extern", "final", "fn", "for", "if", "impl",
    "in", "let", "loop", "macro", "match", "mod", "move", "mut", "override", "priv", "pub", "raw",
    "ref", "return", "Self", "self", "static", "struct", "super", "trait", "try", "type", "typeof",
    "union", "unsafe", "unsized", "use", "virtual", "where", "while", "yield", "&", "&&", "&=",
    "@", "^", "^=", ":", ",", "$", ".", "..", "...", "..=", "=", "==", "=>", ">=", ">", "<-", "<=",
    "<", "-", "-=", "!=", "!", "|", "|=", "||", "::", "%", "%=", "+", "+=", "#", "?", "->", ";",
    "<<", "<<=", ">>", ">>=", "/", "/=", "*", "*=", "~", "_",
];
