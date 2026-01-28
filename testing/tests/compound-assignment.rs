use std::cell::Cell;

use askama::Template;

#[test]
fn test_prefixsum() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "
        {%- let mut prefixsum = 0 -%}
        {%- for i in 0..limit -%}
            {%- mut prefixsum += i -%}
            {{ prefixsum }}.
        {%- endfor -%}
    "
    )]
    struct PrefixSum {
        limit: u32,
    }

    assert_eq!(
        PrefixSum { limit: 10 }.render().unwrap(),
        "0.1.3.6.10.15.21.28.36.45."
    );
}

#[test]
fn test_expr_on_lhs() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "
        {%- let mut prefixsum = Cell::new(0u32) -%}
        {%- for i in 0..limit -%}
            {%- mut *prefixsum.get_mut() += i -%}
            {{ prefixsum.get() }}.
        {%- endfor -%}
    "
    )]
    struct PrefixSum {
        limit: u32,
    }

    assert_eq!(
        PrefixSum { limit: 10 }.render().unwrap(),
        "0.1.3.6.10.15.21.28.36.45."
    );
}

#[test]
fn test_add() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value += 2 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "11");
}

#[test]
fn test_sub() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value -= 2 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "7");
}

#[test]
fn test_mul() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value *= 2 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "18");
}

#[test]
fn test_div() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value /= 2 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "4");
}

#[test]
fn test_rem() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value %= 2 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "1");
}

#[test]
fn test_and() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value &= 3 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "1");
}

#[test]
fn test_or() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value |= 3 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "11");
}

#[test]
fn test_xor() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value ^= 3 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "10");
}

#[test]
fn test_shl() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value <<= 2 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "36");
}

#[test]
fn test_shr() {
    #[derive(Template)]
    #[template(
        ext = "txt",
        source = "{% let mut value = 9 %} {%- mut value >>= 2 -%} {{ value }}"
    )]
    struct Test;

    assert_eq!(Test.render().unwrap(), "2");
}
