# custom-escaper

This example demonstrates how to add a custom escaper and its associated extension.

First, create an `askama.toml` file containing:

```toml
[[escaper]]
path = "crate::Upper"
extensions = ["upper"]
```

`path` is where the type implementing the `askama::Escaper` trait is located (can be in
your crate or in a dependency, it's a `use` path).

`extensions` matches the template file extension or the `ext` field in the `template`
attribute.


Then in `src/main.rs`, you can see the implementation of the `askama::Escaper` trait on
the `Upper` type.
