# Performance

## Rendering Performance

When rendering a rinja template, you should prefer the methods

* [`.render()`] (to render the content into a new string),
* [`.render_into()`] (to render the content into an [`fmt::Write`] object, e.g. [`String`]) or
* [`.write_into()`] (to render the content into an [`io::Write`] object, e.g. [`Vec<u8>`])

over [`.to_string()`] or [`format!()`].
While `.to_string()` and `format!()` give you the same result, they generally perform much worse
than rinja's own methods, because [`fmt::Write`] uses [dynamic methods calls] instead of
monomorphised code. On average, expect `.to_string()` to be 100% to 200% slower than `.render()`.

[dynamic methods calls]: <https://doc.rust-lang.org/stable/std/keyword.dyn.html>
[`.render()`]: <https://docs.rs/rinja/latest/rinja/trait.Template.html#method.render>
[`.render_into()`]: <https://docs.rs/rinja/latest/rinja/trait.Template.html#tymethod.render_into>
[`.write_into()`]: <https://docs.rs/rinja/latest/rinja/trait.Template.html#method.write_into>
[`fmt::Write`]: <https://doc.rust-lang.org/stable/std/fmt/trait.Write.html>
[`String`]: <https://doc.rust-lang.org/stable/std/string/struct.String.html>
[`io::Write`]: <https://doc.rust-lang.org/stable/std/io/trait.Write.html>
[`Vec<u8>`]: <https://doc.rust-lang.org/stable/std/vec/struct.Vec.html>
[`.to_string()`]: <https://doc.rust-lang.org/stable/std/string/trait.ToString.html#tymethod.to_string>
[`format!()`]: <https://doc.rust-lang.org/stable/std/fmt/fn.format.html>

## Slow Debug Recompilations

If you experience slow compile times when iterating with lots of templates,
you can compile Rinja's derive macros with a higher optimization level.
This can speed up recompilation times dramatically.

Add the following to `Cargo.toml` or `.cargo/config.toml`:
```rust
[profile.dev.package.rinja_derive]
opt-level = 3
```

This may affect clean compile times in debug mode, but incremental compiles
will be faster.

## Profile-Guided Optimization (PGO)

To optimize askama's performance, you can compile your application with [Profile-Guided Optimization](https://doc.rust-lang.org/rustc/profile-guided-optimization.html). According to the [tests](https://github.com/mitsuhiko/minijinja/pull/588#issuecomment-2387957123), PGO can improve the library performance by 15%.
