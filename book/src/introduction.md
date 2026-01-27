# Askama

Askama implements a template rendering engine based on [Jinja](https://jinja.palletsprojects.com/).
It generates Rust code from your templates at compile time
based on a user-defined `struct` to hold the template's context.
See below for an example.

All feedback welcome! Feel free to file bugs, requests for documentation and
any other feedback to the [issue tracker][issues].

Have a look at our [*Askama Playground*](https://play.askama.rs/),
if you want to try out askama's code generation online.

## Feature highlights

* Construct templates using a familiar, easy-to-use syntax
* Benefit from the safety provided by Rust's type system
* Template code is compiled into your crate for optimal performance
* Debugging features to assist you in template development
* Templates must be valid UTF-8 and produce UTF-8 when rendered
* Works on stable Rust

## Supported in templates

* Template inheritance
* Loops, if/else statements and include support
* Macro support
* Variables (no mutability allowed)
* Many built-in filters, and the ability to use your own
* Whitespace suppressing with '-' markers
* Opt-out HTML escaping
* Syntax customization

[issues]: https://github.com/askama-rs/askama/issues

## Getting Started

First, add the following to your crate's `Cargo.toml`:

```toml
# in [dependencies] section
askama = "0.14.0"
```

Now create a directory called `templates` in your crate root.
In it, create a file called `hello.html`, containing the following:

```jinja
Hello, {{ name }}!
```

In any Rust file inside your crate, add the following:

```rust
use askama::Template; // bring trait in scope

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
