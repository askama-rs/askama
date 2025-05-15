# Opt-in features

Some features in askama are opt-in to reduce the amount of dependencies,
and to keep the compilation time low.

To opt-in to a feature, you can use `features = […]`.
E.g. if you want to use the filter [`|json`](filters.html#json--tojson),
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

Enables the filters [`|urlencode` and `|urlencode_strict`](filter.html#urlencode--urlencode_strict).

## Addition features

<div class="warning">

Please note that we reserve the right to add more features to the current list,
**without** labeling it as a semver **breaking change**.
The newly added features might even depend on a newer rustc version than the previous list.

</div>

The most useful catch-all feature for a quick start might be `"full"`,
which enables all implemented features, i.e.:

```toml
full = ["default", "blocks", "code-in-doc", "serde_json"]
```

In production or once your project is “maturing” you might want to manually opt-in to any needed
features with a finer granularity instead of depending on `"full"`.

### `"blocks"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"full"</code>
</blockquote>

Enables using [the template attribute `blocks`](creating_templates.html#the-template-attribute).

### `"serde_json"`

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"full"</code>
</blockquote>

<div class="warning">

This feature depends on the crate [`serde_json`](https://crates.io/crates/serde_json).
We won't treat upgrades to a newer `serde_json` version as a semver breaking change,
even if it raises the <abbr title="Minimum Supported Rust Version">MSRV</abbr>.

</div>

Enables the filter [`|json`](filters.html#json--tojson).

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
