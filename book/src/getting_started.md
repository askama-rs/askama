# Getting Started

First, add the following to your crate's `Cargo.toml`:

```toml
# in section [dependencies]
rinja = "0.3.5"
```

Now create a directory called `templates` in your crate root.
In it, create a file called `hello.html`, containing the following:

```jinja
Hello, {{ name }}!
```

In any Rust file inside your crate, add the following:

```rust
use rinja::Template; // bring trait in scope

#[derive(Template)] // this will generate the code...
#[template(path = "hello.html")] // using the template in this path, relative
                                 // to the `templates` dir in the crate root
struct HelloTemplate<'a> { // the name of the struct can be anything
    name: &'a str, // the field name should match the variable name
                   // in your template
}

fn main() {
    let hello = HelloTemplate { name: "world" }; // instantiate your struct
    println!("{}", hello.render().unwrap()); // then render it.
}
```

You should now be able to compile and run this code.

## Using integrations

To use one of the [integrations](./integrations.md), with axum as an example:

First, add this to your `Cargo.toml` instead:

```toml
# in section [dependencies]
rinja_axum = "0.3.5"
```

Then, import from rinja_axum instead of rinja:

```rust
use rinja_axum::Template;
```

This enables the implementation for axum's `IntoResponse` trait,
so an instance of the template can be returned as a response.

For other integrations, import and use their crate accordingly.
