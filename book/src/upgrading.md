# Upgrading to new versions

This file **only lists breaking changes** you need to be aware of when you upgrade to a new askama
version. Please see [our release notes](<https://github.com/askama-rs/askama/releases>) to get a
list of all changes and improvements that might be useful to you.

Also have a look at our blog posts that highlight some of the best features of our releases, and
give you more in-dept explanations:

* [docs.rs switching jinja template framework from tera to askama](
  <https://blog.guillaume-gomez.fr/articles/2024-07-31+docs.rs+switching+jinja+template+framework+from+tera+to+askama>)

## From askama v0.12 to askama v0.13

* The <abbr title="minimum supported rust version">MSRV</abbr> of this release is 1.81.

* The integration crates were removed.
  Instead of depending on e.g. `askama_axum` / `askama_axum`, please use `template.render()` to
  render to a `Result<String, askama::Error>`.

  Use e.g. `.map_err(|err| err.into_io_error())?` if your web-framework expects `std::io::Error`s,
  or `err.into_box()` if it expects `Box<dyn std::error::Error + Send + Sync>`.

  Please read the documentation of your web-framework how to turn a `String` into a web-response.

* The fields `Template::EXTENSION` and `Template::MIME_TYPE` were removed.

* You may not give variables a name starting with `__askama`,
  or the name of a [rust keyword](https://doc.rust-lang.org/reference/keywords.html).

* `#[derive(Template)]` cannot be used with `union`s.

* `|linebreaks`, `|linebreaksbr` and `|paragraphbreaks` escape their input automatically.

* `|json` does not prettify its output by default anymore. Use e.g. `|json(2)` for readable output.

* The binary operators `|`, `&` and `^` are now called `bitor`, `bitand` and `xor`, resp.

* The feature `"humansize"` was removed. The filter `|humansize` is always available.

* The feature `"serde-json"` is now called `"serde_json"`.

* The feature `"markdown"` was removed.
  Use [`comrak`](https://lib.rs/crates/comrak) directly.

* The feature `"serde-yaml"` was removed.
  Use e.g. [`yaml-rust2`](https://lib.rs/crates/yaml-rust2) directly.

## From rinja v0.3 to askama v0.13

* The <abbr title="minimum supported rust version">MSRV</abbr> of this release is 1.81.

* The projects rinja and askama were re-unified into one project.
  You need to replace instances of `rinja` with `askama`, e.g.

  ```diff
  -use rinja::Template;
  +use askama::Template;
  ```

  ```diff
   [dependencies]
  -rinja = "0.3.5"
  +askama = "0.13.0"
  ```

* The integration crates were removed.
  Instead of depending on e.g. `rinja_axum` / `askama_axum`, please use `template.render()` to
  render to a `Result<String, askama::Error>`.

  Use e.g. `.map_err(|err| err.into_io_error())?` if your web-framework expects `std::io::Error`s,
  or `err.into_box()` if it expects `Box<dyn std::error::Error + Send + Sync>`.

  Please read the documentation of your web-framework how to turn a `String` into a web-response.

* The fields `Template::EXTENSION` and `Template::MIME_TYPE` were removed.

* The feature `"humansize"` was removed. The filter `|humansize` is always available.

* You may not give variables a name starting with `__rinja`,
  or the name of a [rust keyword](https://doc.rust-lang.org/reference/keywords.html).

* `#[derive(Template)]` cannot be used with `union`s.

## From rinja v0.2 to rinja v0.3

* You should be able to upgrade to v0.3 without changes.

## From askama v0.12 to rinja v0.2

* The <abbr title="minimum supported rust version">MSRV</abbr> of this release is 1.71.

* You need to replace instances of `askama` with `rinja`, e.g.

  ```diff
  -use askama::Template;
  +use rinja::Template;
  ```

  ```diff
   [dependencies]
  -askama = "0.12.1"
  +rinja = "0.2.0"
  ```

* `|linebreaks`, `|linebreaksbr` and `|paragraphbreaks` escape their input automatically.

* `|json` does not prettify its output by default anymore. Use e.g. `|json(2)` for readable output.

* The binary operators `|`, `&` and `^` are now called `bitor`, `bitand` and `xor`, resp.

* The feature `"serde-json"` is now called `"serde_json"`.

* The feature `"markdown"` was removed.
  Use [`comrak`](https://lib.rs/crates/comrak) directly.

* The feature `"serde-yaml"` was removed.
  Use e.g. [`yaml-rust2`](https://lib.rs/crates/yaml-rust2) directly.

## From askama v0.11 to askama v0.12

* The magic `_parent` field to access `&**self` was removed.

* Integration implementations do not need an `ext` argument anymore.

* The `iron` integration was removed.
