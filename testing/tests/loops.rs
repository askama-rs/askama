#![allow(clippy::type_complexity)]

use std::fmt;
use std::ops::Range;

use askama::Template;

#[test]
fn test_for() {
    #[derive(Template)]
    #[template(path = "for.html")]
    struct ForTemplate<'a> {
        strings: Vec<&'a str>,
        tuple_strings: Vec<(&'a str, &'a str)>,
    }

    let s = ForTemplate {
        strings: vec!["A", "alfa", "1"],
        tuple_strings: vec![("B", "beta")],
    };
    assert_eq!(
        s.render().unwrap(),
        "0. A (first)\n1. alfa\n2. 1\n\n0. B,beta (first)\n"
    );
}

#[test]
fn test_nested_for() {
    #[derive(Template)]
    #[template(path = "nested-for.html")]
    struct NestedForTemplate<'a> {
        seqs: Vec<&'a [&'a str]>,
    }

    let alpha = vec!["a", "b", "c"];
    let numbers = vec!["one", "two"];
    let s = NestedForTemplate {
        seqs: vec![&alpha, &numbers],
    };
    assert_eq!(s.render().unwrap(), "1\n  0a1b2c2\n  0one1two");
}

#[test]
fn test_precedence_for() {
    #[derive(Template)]
    #[template(path = "precedence-for.html")]
    struct PrecedenceTemplate<'a> {
        strings: Vec<&'a str>,
    }

    let s = PrecedenceTemplate {
        strings: vec!["A", "alfa", "1"],
    };
    assert_eq!(
        s.render().unwrap(),
        "0. A2 (first)\n1. alfa4\n2. 16 (last)\n"
    );
}

#[test]
fn test_for_range() {
    #[derive(Template)]
    #[template(path = "for-range.html")]
    struct ForRangeTemplate {
        init: i32,
        end: i32,
    }

    let s = ForRangeTemplate { init: -1, end: 1 };
    assert_eq!(
        s.render().unwrap(),
        "foo (first)\nfoo (last)\nbar\nbar\nfoo\nbar\nbar\n"
    );
}

#[test]
fn test_for_array() {
    #[derive(Template)]
    #[template(source = "{% for i in [1, 2, 3] %}{{ i }}{% endfor %}", ext = "txt")]
    struct ForArrayTemplate;

    let t = ForArrayTemplate;
    assert_eq!(t.render().unwrap(), "123");
}

#[test]
fn test_for_method_call() {
    #[derive(Template)]
    #[template(
        source = "{% for i in [1, 2, 3].iter() %}{{ i }}{% endfor %}",
        ext = "txt"
    )]
    struct ForMethodCallTemplate;

    let t = ForMethodCallTemplate;
    assert_eq!(t.render().unwrap(), "123");
}

#[test]
fn test_for_path_call() {
    #[derive(Template)]
    #[template(
        source = "{% for i in ::std::iter::repeat(\"a\").take(5) %}{{ i }}{% endfor %}",
        ext = "txt"
    )]
    struct ForPathCallTemplate;

    assert_eq!(ForPathCallTemplate.render().unwrap(), "aaaaa");
}

#[test]
fn test_for_index() {
    #[derive(Template)]
    #[template(
        source = "{% for i in [1, 2, 3, 4, 5][3..] %}{{ i }}{% endfor %}",
        ext = "txt"
    )]
    struct ForIndexTemplate;

    let t = ForIndexTemplate;
    assert_eq!(t.render().unwrap(), "45");
}

#[test]
fn test_for_zip_ranges() {
    #[derive(Template)]
    #[template(
        source = "{% for (i, j) in (0..10).zip(10..20).zip(30..40) %}{{ i.0 }} {{ i.1 }} {{ j }} {% endfor %}",
        ext = "txt"
    )]
    struct ForZipRangesTemplate;

    let t = ForZipRangesTemplate;
    assert_eq!(
        t.render().unwrap(),
        "0 10 30 1 11 31 2 12 32 3 13 33 4 14 34 5 15 35 6 16 36 7 17 37 8 18 38 9 19 39 "
    );
}

#[test]
fn test_for_vec_attr_vec() {
    struct ForVecAttrVec {
        iterable: Vec<i32>,
    }

    #[derive(Template)]
    #[template(
        source = "{% for x in v %}{% for y in x.iterable %}{{ y }} {% endfor %}{% endfor %}",
        ext = "txt"
    )]
    struct ForVecAttrVecTemplate {
        v: Vec<ForVecAttrVec>,
    }

    let t = ForVecAttrVecTemplate {
        v: vec![
            ForVecAttrVec {
                iterable: vec![1, 2],
            },
            ForVecAttrVec {
                iterable: vec![3, 4],
            },
            ForVecAttrVec {
                iterable: vec![5, 6],
            },
        ],
    };
    assert_eq!(t.render().unwrap(), "1 2 3 4 5 6 ");
}

struct ForVecAttrSlice {
    iterable: &'static [i32],
}

#[test]
fn test_for_vec_attr_slice() {
    #[derive(Template)]
    #[template(
        source = "{% for x in v %}{% for y in x.iterable %}{{ y }} {% endfor %}{% endfor %}",
        ext = "txt"
    )]
    struct ForVecAttrSliceTemplate {
        v: Vec<ForVecAttrSlice>,
    }

    let t = ForVecAttrSliceTemplate {
        v: vec![
            ForVecAttrSlice { iterable: &[1, 2] },
            ForVecAttrSlice { iterable: &[3, 4] },
            ForVecAttrSlice { iterable: &[5, 6] },
        ],
    };
    assert_eq!(t.render().unwrap(), "1 2 3 4 5 6 ");
}

#[test]
fn test_for_vec_attr_range() {
    struct ForVecAttrRange {
        iterable: Range<usize>,
    }

    #[derive(Template)]
    #[template(
        source = "{% for x in v %}{% for y in x.iterable.clone() %}{{ y }} {% endfor %}{% endfor %}",
        ext = "txt"
    )]
    struct ForVecAttrRangeTemplate {
        v: Vec<ForVecAttrRange>,
    }

    let t = ForVecAttrRangeTemplate {
        v: vec![
            ForVecAttrRange { iterable: 1..3 },
            ForVecAttrRange { iterable: 3..5 },
            ForVecAttrRange { iterable: 5..7 },
        ],
    };
    assert_eq!(t.render().unwrap(), "1 2 3 4 5 6 ");
}

#[test]
fn test_for_vec_attr_slice_shadowing() {
    #[derive(Template)]
    #[template(
        source = "{% for v in v %}{% let v = v %}{% for v in v.iterable %}{% let v = v %}{{ v }} {% endfor %}{% endfor %}",
        ext = "txt"
    )]
    struct ForVecAttrSliceShadowingTemplate {
        v: Vec<ForVecAttrSlice>,
    }

    let t = ForVecAttrSliceShadowingTemplate {
        v: vec![
            ForVecAttrSlice { iterable: &[1, 2] },
            ForVecAttrSlice { iterable: &[3, 4] },
            ForVecAttrSlice { iterable: &[5, 6] },
        ],
    };
    assert_eq!(t.render().unwrap(), "1 2 3 4 5 6 ");
}

struct NotCloneable<T: fmt::Display>(T);

impl<T: fmt::Display> fmt::Display for NotCloneable<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

#[test]
fn test_for_destructoring_ref_tuple() {
    #[derive(Template)]
    #[template(
        source = "{% for (((a,), b), c) in v %}{{a}}{{b}}{{c}}-{% endfor %}",
        ext = "txt"
    )]
    struct ForDestructoringRefTupleTemplate<'a> {
        v: &'a [(((char,), NotCloneable<char>), &'a char)],
    }

    let v = [
        ((('a',), NotCloneable('b')), &'c'),
        ((('d',), NotCloneable('e')), &'f'),
        ((('g',), NotCloneable('h')), &'i'),
    ];
    let t = ForDestructoringRefTupleTemplate { v: &v };
    assert_eq!(t.render().unwrap(), "abc-def-ghi-");
}

#[test]
fn test_for_destructoring_tuple() {
    #[derive(Template)]
    #[template(
        source = "{% for (((a,), b), c) in v %}{{a}}{{b}}{{c}}-{% endfor %}",
        ext = "txt"
    )]
    struct ForDestructoringTupleTemplate<'a, const N: usize> {
        v: [(((char,), NotCloneable<char>), &'a char); N],
    }

    let t = ForDestructoringTupleTemplate {
        v: [
            ((('a',), NotCloneable('b')), &'c'),
            ((('d',), NotCloneable('e')), &'f'),
            ((('g',), NotCloneable('h')), &'i'),
        ],
    };
    assert_eq!(t.render().unwrap(), "abc-def-ghi-");
}

#[test]
fn test_for_enumerate() {
    #[derive(Template)]
    #[template(
        source = "{% for (i, msg) in messages.iter().enumerate() %}{{i}}={{msg}}-{% endfor %}",
        ext = "txt"
    )]
    struct ForEnumerateTemplate<'a> {
        messages: &'a [&'a str],
    }

    let t = ForEnumerateTemplate {
        messages: &["hello", "world", "!"],
    };
    assert_eq!(t.render().unwrap(), "0=hello-1=world-2=!-");
}

#[test]
fn test_loop_break() {
    #[derive(Template)]
    #[template(
        source = "{% for v in values.iter() %}x{{v}}{% if matches!(v, x if *x==3) %}{% break %}{% endif %}y{% endfor %}",
        ext = "txt"
    )]
    struct Break<'a> {
        values: &'a [i32],
    }

    let t = Break {
        values: &[1, 2, 3, 4, 5],
    };
    assert_eq!(t.render().unwrap(), "x1yx2yx3");

    let t = Break {
        values: &[1, 2, 4, 5],
    };
    assert_eq!(t.render().unwrap(), "x1yx2yx4yx5y");
}

#[test]
fn test_loop_continue() {
    #[derive(Template)]
    #[template(
        source = "{% for v in values %}x{{v}}{% if matches!(v, x if *x==3) %}{% continue %}{% endif %}y{% endfor %}",
        ext = "txt"
    )]
    struct Continue<'a> {
        values: &'a [i32],
    }

    let t = Continue {
        values: &[1, 2, 3, 4, 5],
    };
    assert_eq!(t.render().unwrap(), "x1yx2yx3x4yx5y");

    let t = Continue {
        values: &[1, 2, 4, 5],
    };
    assert_eq!(t.render().unwrap(), "x1yx2yx4yx5y");
}

#[test]
fn test_loop_break_continue() {
    #[derive(Template)]
    #[template(path = "for-break-continue.html")]
    struct BreakContinue<'a> {
        values: &'a [i32],
    }

    let t = BreakContinue {
        values: &[1, 2, 3, 4, 5],
    };
    assert_eq!(t.render().unwrap(), "x1yx2yx3yx4yx5y");

    let t = BreakContinue {
        values: &[1, 2, 3, 10, 4, 5],
    };
    assert_eq!(t.render().unwrap(), "x1yx2yx3yx10");

    let t = BreakContinue {
        values: &[1, 2, 3, 11, 4, 5],
    };
    assert_eq!(t.render().unwrap(), "x1yx2yx3yx11x4yx5y");
}

#[test]
fn test_for_cycle() {
    #[derive(Template)]
    #[template(
        source = r#"{% for v in values %}{{loop.cycle(["r", "g", "b"])}}{{v}},{% endfor %}"#,
        ext = "txt"
    )]
    struct ForCycle<'a> {
        values: &'a [u8],
    }

    let t = ForCycle {
        values: &[1, 2, 3, 4, 5, 6, 7, 8, 9],
    };
    assert_eq!(t.render().unwrap(), "r1,g2,b3,r4,g5,b6,r7,g8,b9,");
}

mod test_for_cycle {
    use askama::Template;

    #[derive(Template)]
    #[template(
        source = r#"{% for v in values %}{{loop.cycle(cycle)}}{{v}},{% endfor %}"#,
        ext = "txt"
    )]
    struct ForCycleDynamic<'a> {
        values: &'a [u8],
        cycle: &'a [char],
    }

    #[test]
    fn test_for_cycle_dynamic() {
        let t = ForCycleDynamic {
            values: &[1, 2, 3, 4, 5, 6, 7, 8, 9],
            cycle: &['a', 'b', 'c', 'd'],
        };
        assert_eq!(t.render().unwrap(), "a1,b2,c3,d4,a5,b6,c7,d8,a9,");
    }

    #[test]
    fn test_for_cycle_empty() {
        let t = ForCycleDynamic {
            values: &[1, 2, 3, 4, 5, 6, 7, 8, 9],
            cycle: &[],
        };
        assert!(t.render().is_err());
    }
}

#[test]
fn test_for_in_if() {
    #[derive(Template)]
    #[template(
        source = "{% for i in 0..limit if i % 2 == 1 %}{{i}}.{% else %}:({% endfor %}",
        ext = "txt"
    )]
    struct ForInIf {
        limit: usize,
    }

    let t = ForInIf { limit: 10 };
    assert_eq!(t.render().unwrap(), "1.3.5.7.9.");

    let t = ForInIf { limit: 1 };
    assert_eq!(t.render().unwrap(), ":(");
}

// This is a regression test for <https://github.com/askama-rs/askama/issues/150>.
// The loop didn't drop its locals context, creating a bug where a field could
// not be retrieved although it existed.
#[test]
fn test_loop_locals() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro mac(bla) -%}
{% for x in &[1] -%}
{% endfor -%}
{% endmacro -%}

{% call mac(bla=bla) %}{% endcall %}
{{- bla }}"#,
        ext = "txt"
    )]
    struct LoopLocalsContext {
        bla: u8,
    }

    let t = LoopLocalsContext { bla: 10 };
    assert_eq!(t.render().unwrap(), "10");
}

// This test ensures that the span used for generating askama idents
// is working correctly when derive happens with literals coming from
// another scope.
//
// Regression test for <https://github.com/askama-rs/askama/issues/564>.
#[test]
fn test_loop_span_scope() {
    macro_rules! looper {
        ($l:literal) => {
            #[derive(Template)]
            #[template(source = $l, ext = "txt")]
            pub struct X;
        };
    }

    looper!(
        r#"
{%- macro column(idx) -%}
    {{ idx }}
{%- endmacro -%}

{%- macro nested_arr(arr) -%}
    {% for e in arr -%}
        {{- loop.index0 }}
        {{~ column(loop.index0) -}}
    {% endfor -%}
{% endmacro -%}

{{ nested_arr([1, 2, 3]) }}"#
    );

    assert_eq!(X.render().unwrap(), "0\n01\n12\n2");
}
