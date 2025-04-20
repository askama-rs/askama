# Performance

## Rendering Performance

When rendering an askama template, you should prefer the methods

* [`.render()`] (to render the content into a new string),
* [`.render_into()`] (to render the content into an [`fmt::Write`] object, e.g. [`String`]) or
* [`.write_into()`] (to render the content into an [`io::Write`] object, e.g. [`Vec<u8>`])

over [`.to_string()`] or [`format!()`].
While `.to_string()` and `format!()` give you the same result, they generally perform much worse
than askama's own methods, because [`fmt::Write`] uses [dynamic methods calls] instead of
monomorphised code. On average, expect `.to_string()` to be 100% to 200% slower than `.render()`.

[dynamic methods calls]: <https://doc.rust-lang.org/stable/std/keyword.dyn.html>
[`.render()`]: <https://docs.rs/askama/latest/askama/trait.Template.html#method.render>
[`.render_into()`]: <https://docs.rs/askama/latest/askama/trait.Template.html#tymethod.render_into>
[`.write_into()`]: <https://docs.rs/askama/latest/askama/trait.Template.html#method.write_into>
[`fmt::Write`]: <https://doc.rust-lang.org/stable/std/fmt/trait.Write.html>
[`String`]: <https://doc.rust-lang.org/stable/std/string/struct.String.html>
[`io::Write`]: <https://doc.rust-lang.org/stable/std/io/trait.Write.html>
[`Vec<u8>`]: <https://doc.rust-lang.org/stable/std/vec/struct.Vec.html>
[`.to_string()`]: <https://doc.rust-lang.org/stable/std/string/trait.ToString.html#tymethod.to_string>
[`format!()`]: <https://doc.rust-lang.org/stable/std/fmt/fn.format.html>

## Faster Rendering of Custom Types

Every type that implements [`fmt::Display`] can be used in askama expressions: `{{ value }}`.
Rendering with `fmt::Display` can be slow, though, because it uses [dynamic methods calls] in its
[`fmt::Formatter`] argument. To speed up rendering (by a lot, actually),
askama adds the trait [`FastWritable`]. For any custom type you want to render,
it has to implement `fmt::Display`, but if it also implements `FastWritable`,
then – using [autoref-based specialization] – the latter implementation is automatically preferred.

To reduce the amount of code duplication, you can let your `fmt::Display` implementation call
your `FastWritable` implementation:

```rust
{{#include ../../testing/tests/book_example_performance_fmt_call_fast_writable.rs}}
```

[`fmt::Display`]: <https://doc.rust-lang.org/stable/std/fmt/trait.Display.html>
[`fmt::Formatter`]: <https://doc.rust-lang.org/stable/std/fmt/struct.Formatter.html>
[`FastWritable`]: <./doc/askama/trait.FastWritable.html>
[autoref-based specialization]: <https://lukaskalbertodt.github.io/2019/12/05/generalized-autoref-based-specialization.html>

## Slow Debug Recompilations

If you experience slow compile times when iterating with lots of templates,
you can compile Askama's derive macros with a higher optimization level.
This can speed up recompilation times dramatically.

Add the following to `Cargo.toml` or `.cargo/config.toml`:
```rust
[profile.dev.package.askama_derive]
opt-level = 3
```

This may affect clean compile times in debug mode, but incremental compiles
will be faster.
