# Creating Templates

An Askama template is a `struct` definition which provides the template
context combined with a UTF-8 encoded text file (or inline source, see
below). Askama can be used to generate any kind of text-based format.
The template file's extension may be used to provide content type hints.

A template consists of **text contents**, which are passed through as-is,
**expressions**, which get replaced with content while being rendered, and
**tags**, which control the template's logic.
The [template syntax](template_syntax.md) is very similar to [Jinja](http://jinja.pocoo.org/),
as well as Jinja-derivatives like [Twig](https://twig.symfony.com/) or
[Tera](https://github.com/Keats/tera).

```rust
#[derive(Template)] // this will generate the code...
#[template(path = "hello.html")] // using the template in this path, relative
                                 // to the `templates` dir in the crate root
struct HelloTemplate<'a> { // the name of the struct can be anything
    name: &'a str, // the field name should match the variable name
                   // in your template
}
```

## The `template()` attribute

Askama works by generating one or more trait implementations for any
`struct` type decorated with the `#[derive(Template)]` attribute. The
code generation process takes some options that can be specified through
the `template()` attribute. The following sub-attributes are currently
recognized:

* `path` (e.g. `path = "foo.html"`): sets the path to the template file. The
  path is interpreted as relative to the configured template directories
  (by default, this is a `templates` directory next to your `Cargo.toml`).
  The file name extension is used to infer an escape mode (see below). In
  web framework integrations, the path's extension may also be used to
  infer the content type of the resulting response.
  Cannot be used together with `source`.
  ```rust
  #[derive(Template)]
  #[template(path = "hello.html")]
  struct HelloTemplate<'a> { ... }
  ```

* `source` (e.g. `source = "{{ foo }}"`): directly sets the template source.
  This can be useful for test cases or short templates. The generated path
  is undefined, which generally makes it impossible to refer to this
  template from other templates. If `source` is specified, `ext` must also
  be specified (see below). Cannot be used together with `path`.
  ```rust
  #[derive(Template)]
  #[template(source = "Hello {{ name }}")]
  struct HelloTemplate<'a> {
      name: &'a str,
  }
  ```

* `in_doc` (e.g. `in_doc = true`):
  please see the section ["documentation as template code"](#documentation-as-template-code).

* `ext` (e.g. `ext = "txt"`): lets you specify the content type as a file
  extension. This is used to infer an escape mode (see below), and some
  web framework integrations use it to determine the content type.
  Cannot be used together with `path`.
  ```rust
  #[derive(Template)]
  #[template(source = "Hello {{ name }}", ext = "txt")]
  struct HelloTemplate<'a> {
      name: &'a str,
  }
  ```

* `print` (e.g. `print = "code"`): enable debugging by printing nothing
  (`none`), the parsed syntax tree (`ast`), the generated code (`code`)
  or `all` for both. The requested data will be printed to stdout at
  compile time.
  ```rust
  #[derive(Template)]
  #[template(path = "hello.html", print = "all")]
  struct HelloTemplate<'a> { ... }
  ```

* `block` (e.g. `block = "block_name"`): renders the block by itself.
  Expressions outside of the block are not required by the struct, and
  inheritance is also supported. This can be useful when you need to
  decompose your template for partial rendering, without needing to
  extract the partial into a separate template or macro.
  ```rust
  #[derive(Template)]
  #[template(path = "hello.html", block = "hello")]
  struct HelloTemplate<'a> { ... }
  ```

* `blocks` (e.g. `blocks = ["title", "content"]`):
  automatically generates (a number of) sub-templates that act as if they had a
  `block = "..."` attribute. You can access the sub-templates with the method
  <code>my_template.as_<em>block_name</em>()</code>, where *`block_name`* is the
  name of the block:
  ```rust
  #[derive(Template)]
  #[template(
      ext = "txt",
      source = "
          {% block title %} ... {% endblock %}
          {% block content %} ... {% endblock %}
      ",
      blocks = ["title", "content"]
  )]
  struct News<'a> {
      title: &'a str,
      message: &'a str,
  }

  let news = News {
      title: "Announcing Rust 1.84.1",
      message: "The Rust team has published a new point release of Rust, 1.84.1.",
  };
  assert_eq!(
      news.as_title().render().unwrap(),
      "<h1>Announcing Rust 1.84.1</h1>"
  );
  ```

* `escape` (e.g. `escape = "none"`): override the template's extension used for
  the purpose of determining the escaper for this template. See the section
  on configuring custom escapers for more information.
  ```rust
  #[derive(Template)]
  #[template(path = "hello.html", escape = "none")]
  struct HelloTemplate<'a> { ... }
  ```

* `syntax` (e.g. `syntax = "foo"`): set the syntax name for a parser defined
  in the configuration file. The default syntax , "default", is the one
  provided by Askama.
  ```rust
  #[derive(Template)]
  #[template(path = "hello.html", syntax = "foo")]
  struct HelloTemplate<'a> { ... }
  ```

* `config` (e.g. `config = "config_file_path"`): set the path for the config file
  to be used. The path is interpreted as relative to your crate root.
  ```rust
  #[derive(Template)]
  #[template(path = "hello.html", config = "config.toml")]
  struct HelloTemplate<'a> { ... }
  ```

* `askama` (e.g. `askama = askama`):
  If you are using askama in a subproject, a library or a [macro][book-macro], it might be
  necessary to specify the [path][book-tree] where to find the module `askama`:

  [book-macro]: https://doc.rust-lang.org/book/ch19-06-macros.html
  [book-tree]: https://doc.rust-lang.org/book/ch07-03-paths-for-referring-to-an-item-in-the-module-tree.html

  ```rust
  #[doc(hidden)]
  use askama as __askama;

  #[macro_export]
  macro_rules! new_greeter {
      ($name:ident) => {
          #[derive(Debug, $crate::askama::Template)]
          #[template(
              ext = "txt",
              source = "Hello, world!",
              askama = $crate::__askama
          )]
          struct $name;
      }
  }

  new_greeter!(HelloWorld);
  assert_eq!(HelloWorld.to_string(), Ok("Hello, world."));
  ```
## Templating `enum`s

You can add derive `Template`s for `struct`s and `enum`s.
If you add `#[template()]` only to the item itself, both item kinds work exactly the same.
But with `enum`s you also have the option to add a specialized implementation to one, some,
or all variants:

```rust
#[derive(Debug, Template)]
#[template(path = "area.txt")]
enum Area {
    Square(f32),
    Rectangle { a: f32, b: f32 },
    Circle { radius: f32 },
}
```

```jinja
{%- match self -%}
    {%- when Self::Square(side) -%}
        {{side}}^2
    {%- when Self::Rectangle { a, b} -%}
        {{a}} * {{b}}
    {%- when Self::Circle { radius } -%}
        pi * {{radius}}^2
{%- endmatch -%}
```

will give you the same results as:

```rust
#[derive(Template, Debug)]
#[template(ext = "txt")]
enum AreaPerVariant {
    #[template(source = "{{self.0}}^2")]
    Square(f32),
    #[template(source = "{{a}} * {{b}}")]
    Rectangle { a: f32, b: f32 },
    #[template(source = "pi * {{radius}}^2")]
    Circle { radius: f32 },
}
```

As you can see with the `ext` attribute, `enum` variants inherit most settings of the `enum`:
`config`, `escape`, `ext`, `syntax`, and `whitespace`.
Not inherited are: `block`, and `print`.

If there is no `#[template]` annotation for an `enum` variant,
then the `enum` needs a default implementation, which will be used if `self` is this variant.
A good compromise between annotating only the template, or all its variants,
might be using the `block` argument on the members:

```rust
#[derive(Template, Debug)]
#[template(path = "area.txt")]
enum AreaWithBlocks {
    #[template(block = "square")]
    Square(f32),
    #[template(block = "rectangle")]
    Rectangle { a: f32, b: f32 },
    #[template(block = "circle")]
    Circle { radius: f32 },
}
```

```jinja
{%- block square -%}
    {{self.0}}^2
{%- endblock -%}

{%- block rectangle -%}
    {{a}} * {{b}}
{%- endblock -%}

{%- block circle -%}
    pi * {{radius}}^2
{%- endblock -%}
```

## Documentation as template code
[#documentation-as-template-code]: #documentation-as-template-code

As an alternative to supplying the code template code in an external file (e.g. `path` argument),
or as a string (e.g. `source` argument), you can also enable the `"code-in-doc"` feature.
With this feature, you can specify the template code directly in the documentation
of the template item.

Instead of `path = "…"` or `source = "…"`, specify `in_doc = true` in the `#[template]` attribute,
and in the item's documentation, add a code block with the `askama` attribute:

`````rust
/// Here you can put our usual comments.
///
/// ```askama
/// <div>{{ lines|linebreaksbr }}</div>
/// ```
///
/// Any usual docs, including tests can be put in here, too:
///
/// ```rust
/// assert_eq!(
///     Example { lines: "a\nb\nc" }.to_string(),
///     "<div>a<br/>b<br/>c</div>"
/// );
/// ```
///
/// All comments are still optional, though.
#[derive(Template)]
#[template(ext = "html", in_doc = true)]
struct Example<'a> {
    lines: &'a str,
}
`````

If you want to supply the template code in the comments,
then you have to specify the `ext` argument, too, e.g. `#[template(ext = "html")]`.

Instead of `askama`, you can also write `jinja` or `jinja2`,
e.g. to get it to work better in conjunction with syntax highlighters.
