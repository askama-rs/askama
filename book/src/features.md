# Opt-in features

Some features in askama are opt-in to reduce the amount of dependencies,
and to keep the compilation time low.

To opt-in to a feature, you can use `features = […]`.
E.g. if you want to use the filter [`|json`](filters.html#json),
you have to opt-in to the feature [`"serde_json"`](#serde_json):

```toml
[dependencies]
askama = { version = "0.14.0", features = ["serde_json"] }
```

Please read the [Cargo manual](https://doc.rust-lang.org/cargo/reference/features.html#dependency-features)
for more information.

## Default features

Any [semver-compatible](https://doc.rust-lang.org/cargo/reference/semver.html) upgrade
(e.g. `askama = "0.14.1"` to `askama = "0.14.2"`) will keep the same list of default features.
We will treat upgrades to a newer dependency version as a semver breaking change.

### `"default"`

You can opt-out of using the feature flags by using
`default-features = false`:

```toml
[dependencies]
askama = { version = "0.14.0", default-features = false }
```

Without `default-features = false`, i.e with default features enabled,
the following features are automatically selected for you:

```toml
default = ["config", "derive", "std", "urlencode"]
```

This should encompass most features an average user of askama might need.

*If you are writing a **library** that depends on askama,
and if you want it to be usable in by other users and in **other projects**,
then you should probably **opt-out of features you do not need**.*

### `"derive"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"default"</code>
</blockquote>

This feature enables `#[derive(Template)]`. Without it the trait `askama::Template` will still be
available, but if you want to derive a template, you have to manually depend on `askama_macros`.
`askama_macros` should be used with the same features as `askama`.

Not using this feature might be useful e.g. if you are writing a library with manual filters
for askama, without any templates. It might also very slightly speed-up the compilation,
because more dependencies can be compiled in parallel, because `askama` won't transitively depend
on e.g. `syn` or `proc-macro2`. On the author's PC the compilation of a trivial hello-world example
was about 0.2s faster without the feature when compiled in release mode.

*If you are writing a library that uses askama, consider **not using** this default-feature.*

### `"config"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"default"</code>
</blockquote>

Enables compile time [configurations](configuration.html).

### `"urlencode"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"default"</code>
</blockquote>

Enables the filters [`|urlencode` and `|urlencode_strict`](filters.html#urlencode).

## Addition features

<div class="warning">

Please note that we reserve the right to add more features to the current list,
**without** labeling it as a semver **breaking change**.
The newly added features might even depend on a newer rustc version than the previous list.

</div>

The most useful catch-all feature for a quick start might be `"full"`,
which enables all implemented features, i.e.:

```toml
full = ["default", "async", "code-in-doc", "serde_json"]
```

In production or once your project is “maturing” you might want to manually opt-in to any needed
features with a finer granularity instead of depending on `"full"`.

### `"serde_json"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"full"</code>
</blockquote>

<div class="warning">

This feature depends on the crate [`serde_json`](https://crates.io/crates/serde_json).
We won't treat upgrades to a newer `serde_json` version as a semver breaking change,
even if it raises the <abbr title="Minimum Supported Rust Version">MSRV</abbr>.

</div>

Enables the filter [`|json`](filters.html#json).

### `"code-in-doc"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"full"</code>
</blockquote>

<div class="warning">

This feature depends on the crate [`pulldown-cmark`](https://crates.io/crates/pulldown-cmark).
We won't treat upgrades to a newer `pulldown-cmark` version as a semver breaking change,
even if it raises the <abbr title="Minimum Supported Rust Version">MSRV</abbr>.

</div>

Enables using [documentations as template code](creating_templates.html#documentation-as-template-code).

### `"async"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"full"</code>
</blockquote>

<div class="warning">

This feature depends on the crate [`futures`](https://crates.io/crates/futures).
We won't treat upgrades to a newer `futures` version as a semver breaking change,
even if it raises the <abbr title="Minimum Supported Rust Version">MSRV</abbr>.

</div>

Enabling `"async"` enables `"std"`, too.

Adds the methods `async_render_into_with_values()` and `async_render_with_values()` to the
`Template` trait. `async_render_into_with_values()` takes the same arguments as
`render_into_with_values()`, except that the writer can be any
[`futures::io::AsyncWrite`](https://docs.rs/futures/0.3/futures/io/trait.AsyncWrite.html)
(which also needs to be `Unpin`), and that the values must be `Sync`
(like [`NO_VALUES`](https://docs.rs/askama/latest/askama/constant.NO_VALUES.html)):

```rust
use askama::{NO_VALUES, Template};

#[derive(Template)]
#[template(path = "hello.html")]
struct HelloTemplate<'a> {
    name: &'a str,
}

async fn send_hello(
    socket: &mut (impl futures::io::AsyncWrite + Unpin),
) -> askama::Result<()> {
    HelloTemplate { name: "world" }
        .async_render_into_with_values(socket, NO_VALUES)
        .await
}
```

Every write into the writer is `.await`ed, so a writer which is not ready (e.g. a socket with a
full send buffer) does not block the thread: the task is woken up once it can write again.
I/O errors of the writer are converted into `askama::Error` (usually `askama::Error::Custom`).
The writer is neither flushed nor closed, you need to do it yourself if needed.

`async_render_with_values()` is the asynchronous equivalent of `render_with_values()`: it renders
the template into a new `String`.

The returned futures are `Send` if the template is `Sync` and the writer is `Send`, so they can be
used with multi-threaded runtimes. To pass runtime values, use `Send + Sync` values:

```rust
use std::any::Any;

let values: (&str, &(dyn Any + Send + Sync)) = ("name", &"Ferris");
let rendered = HelloTemplate { name: "world" }
    .async_render_with_values(&values)
    .await?;
```

The compiler only knows that the future is `Send` if it knows the type of the template, i.e. not
in a generic function `fn f<T: Template>(t: &T)`, nor for the sub-templates returned by the
`as_<block>()` methods of [`blocks`](creating_templates.html#blocks), which return
`impl Template`.

If you are using [tokio](https://crates.io/crates/tokio), its writers implement tokio's own
`AsyncWrite` trait. You can use [`tokio-util`'s compatibility layer](https://docs.rs/tokio-util/latest/tokio_util/compat/index.html)
(`writer.compat_write()`) to turn them into a `futures::io::AsyncWrite`.

Please note that:

* Only the writes are asynchronous: consecutive text and `{{ expression }}`s are rendered into an
  internal buffer, which is then written into the writer at once (e.g. once per iteration of a
  `{% for %}` loop). The same is true for the content of `{% filter %}` blocks.
* If you implement `Template` manually, you also need to implement
  `async_render_into_with_values()` when this feature is enabled.

## “Anti-features” in a `#![no_std]` environment

Opting-out of the default features `"std"` and `"alloc"` is only interesting for the use
in a `#![no_std]` environment.
Please find more information in [The Embedded Rust Book](https://docs.rust-embedded.org/book/intro/no-std.html).

### `"alloc"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"default"</code>
</blockquote>

Without the default feature `"alloc"` askama can be used in a `#![no_std]` environment.
The method `Template::render()` will be absent, because askama won't have access to a default allocator.

Many filters need intermediate allocations, and won't be usable without this feature.

You can still render templates using e.g.
[`no_std_io2::io::Cursor`](https://docs.rs/no_std_io2/0.9.0/no_std_io2/io/struct.Cursor.html) or
[`embedded_io::Write`](https://docs.rs/embedded-io/0.6.1/embedded_io/trait.Write.html#method.write_fmt)

### `"std"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"default"</code>
</blockquote>

Without the feature `"std"` askama can be used in a `#![no_std]` environment.
The method `Template::write_into()` will be absent, because askama won't have access to standard IO operations.

Enabling `"std"` enables `"alloc"`, too.
