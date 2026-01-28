# Template Syntax

## Syntax overview

| Syntax | Description |
| - | - |
| `{{ ... }}` | Expression to be evaluated, escaped and printed |
| `{{ ... \| ... }}` | [Expression with filter(s)](#filters) |
| `{% filter ... %} ... {% endfilter %}` | [Filter block](#filter-blocks) |
| `{# ... #}` | [Comment](#comments) |
| `{% let ... = ... %}` or `{% set ... = ... %}` | [Variable assignment](#assignments) |
| `{% decl ... %}` or `{% declare ... = ... %}` | [Set variable values later](#set-variable-values-later) |
| `{% if ... %} ... {% else if ... %} ... {% else %} ... {% endif %}` | [If-Else conditional block](#if) |
| `{% match ... %} {% when ... %} ... {% else %} ... {% endmatch %}` | [Match block](#match) |
| `{% for ... in ... %} ... {% else %} ... {% endfor %}` | [For loop block](#for) |
| `{% continue %}` | Continue to next iteration of loop |
| `{% break %}` | Break out of loop |
| `{% include "..." %}` | [Include another template](#include) |
| `{% extends "..." %}` | [Template inheritance](#template-inheritance) |
| `{% block ... %} ... {% endblock %}` | [Block definition for inheritance](#template-inheritance) |
| `{% macro ...(...) %} ... {% endmacro %}` | [Macro definition](#macros) |
| `{{ ...(...) }}` | [Macro invocation](#macros) |
| `{% call ...(...) %}{% endcall %}` | [Macro call block](#macro-call-blocks) |
| `{% import "..." as ... %}` | [Import macros from another template](#imports--scopes) |
| `{% raw %} ... {% endraw %}` | Raw block - prints contents as-is (without templating) |


## Variables

Top-level template variables are defined by the template's context type.
You can use a dot (`.`) to access variable's attributes or methods.
Reading from variables is subject to the usual borrowing policies.
For example, `{{ name }}` will get the ``name`` field from the template
context,
while `{{ user.name }}` will get the ``name`` field of the ``user``
field from the template context.

## Using constants in templates

You can use constants defined in your Rust code. For example if you
have:

```rust
pub const MAX_NB_USERS: usize = 2;
```

defined in your crate root, you can then use it in your templates by
using ``crate::MAX_NB_USERS``:

```jinja
<p>The user limit is {{ crate::MAX_NB_USERS }}.</p>
{% set value = 4 %}
{% if value > crate::MAX_NB_USERS %}
    <p>{{ value }} is bigger than MAX_NB_USERS.</p>
{% else %}
    <p>{{ value }} is less than MAX_NB_USERS.</p>
{% endif %}
```

## Assignments

Inside code blocks, you can also declare variables or assign values
to variables.
Assignments can't be imported by other templates.

Assignments use the `let` tag:

```jinja
{% let name = user.name %}
{% let len = name.len() %}
```

Like Rust, Askama also supports shadowing variables.

```jinja
{% let foo = "bar" %}
{{ foo }}

{% let foo = "baz" %}
{{ foo }}
```

You can declare variables as mutable with the `mut` keyword:

```jinja
{# In this example, `foo` is an iterator. If you want to be able to iterate it,
you need it to be mutable #}
{% let mut foo = [1, 2].iter() %}
{{ foo.next().unwrap() }}
```

For compatibility with Jinja, `set` can be used in place of `let`.

### Set variable values later

If you want to create a variable but set its value based on a condition, you can
declare it without a value by using the `decl` (or `declare`) keyword:

```jinja
{% decl val -%}
{% if len == 0 -%}
  {% let val = "foo" -%}
{% else -%}
  {% let val = name -%}
{% endif -%}
{{ val }}
```

### Borrow rules

In some cases, the value of a variable initialization will be put behind a reference
to prevent changing ownership. The rules are as follows:

 * If the value is an expression of more than one element (like `x + 2`), it WILL NOT BE put behind a reference.
 * If the value is a variable defined in the templates, it WILL NOT BE put behind a reference.
 * If the value has a filter applied to it (`x|capitalize`), it WILL NOT BE put behind a reference.
 * If the value is a field (`x.y`), it WILL BE put behind a reference.
 * If the expression ends with a question mark (like `x?`), it WILL NOT BE put behind a reference.

### Compound assignments

Using the keyword `mut`, [compound assignments][rust101-assignment-op] (also called
"augmented assignments"), such as `x += 1` to increment `x` by 1, are possible, too:

```jinja
{% let mut counter = 0 %}
{% for i in 1..=10 %}
    {% mut counter += 1 %}
    {{ counter }}
{% endfor %}
```

This example will output [`1 3 6 10 15`…][wikipedia-prefix-sum].

The target can be a variable or a more complex expression. The rules are the same as in rust,
e.g. the left-hand side of the expression, i.e. the assignment target, must be mutable.
All [compound assignment operators][reference-compound-assignment] that are valid in rust are
valid in askama, too.

[rust101-assignment-op]: <https://rustlabs.github.io/docs/rust101/assignment_compound_assignment_operators/#compound-assignment-operator> "Rust - Quick start: Assignment and Compound Assignment Operators"
[wikipedia-prefix-sum]: <https://en.wikipedia.org/wiki/Prefix_sum?curid=6109308> "Wikipedia: Prefix sum"
[reference-compound-assignment]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#compound-assignment-expressions> "The Rust Reference: Compound assignment expressions"

## Filters

Values such as those obtained from variables can be post-processed
using **filters**.
Filters are applied to values using the pipe symbol (`|`) and may
have optional extra arguments in parentheses.
Filters can be chained, in which case the output from one filter
is passed to the next.

For example, `{{ "{:?}"|format(name|escape) }}` will escape HTML
characters from the value obtained by accessing the `name` field,
and print the resulting string as a Rust literal.

The built-in filters are documented as part of the
[filters documentation](filters.md).

To define your own filters, simply have a module named `filters` in
scope of the context deriving a `Template` `impl`. Note that in case of
name collision, the built in filters take precedence.

## Filter blocks

You can apply a **filter** on a whole block at once using **filter
blocks**:

```jinja
{% filter lower %}
  {{ t }} / HELLO / {{ u }}
{% endfilter %}
```

The `lower` filter will be applied on the whole content.

Just like filters, you can combine them:

```jinja
{% filter lower|capitalize %}
  {{ t }} / HELLO / {{ u }}
{% endfilter %}
```

In this case, `lower` will be called and then `capitalize` will be
called on what `lower` returned.

## Whitespace control

Askama considers all tabs, spaces, newlines and carriage returns to be
whitespace. By default, it preserves all whitespace in template code,
except that a single trailing newline character is suppressed.
However, whitespace before and after expression and block delimiters
can be suppressed by writing a minus sign directly following a
start delimiter or leading into an end delimiter.

Here is an example:

```jinja
{% if foo %}
  {{- bar -}}
{% else if another -%}
  nothing
{%- endif %}
```

This discards all whitespace inside the if/else block. If a literal
(any part of the template not surrounded by `{% %}` or `{{ }}`)
includes only whitespace, whitespace suppression on either side will
completely suppress that literal content.

If the whitespace default control is set to "suppress" and you want
to preserve whitespace characters on one side of a block or of an
expression, you need to use `+`. Example:

```jinja
<a href="/" {#+ #}
   class="something">text</a>
```

In the above example, one whitespace character is kept
between the `href` and the `class` attributes.

There is a third possibility. In case you want to suppress all whitespace
characters except one (`"minimize"`), you can use `~`:

```jinja
{% if something ~%}
Hello
{%~ endif %}
```

To be noted, if one of the trimmed characters is a newline, then the only
character remaining will be a newline.

Whitespace controls can also be defined by a
[configuration file](configuration.md) or in the derive macro.
These definitions follow the global-to-local preference:
1. Inline (`-`, `+`, `~`)
2. Derive (`#[template(whitespace = "suppress")]`)
3. Configuration (in `askama.toml`, `whitespace = "preserve"`)

Two inline whitespace controls may point to the same whitespace span.
In this case, they are resolved by the following preference.
1. Suppress (`-`)
2. Minimize (`~`)
3. Preserve (`+`)

## Functions

There are several ways that functions can be called within templates,
depending on where the function definition resides. These are:

- Template `struct` fields
- Static functions
- Struct/Trait implementations

### Template struct field

When the function is a field of the template struct, we can simply call it
by invoking the name of the field, followed by parentheses containing any
required arguments. For example, we can invoke the function `foo` for the
following `MyTemplate` struct:

```rust
#[derive(Template)]
#[template(source = "{{ foo(123) }}", ext = "txt")]
struct MyTemplate {
  foo: fn(u32) -> String,
}
```

However, since we'll need to define this function every time we create an
instance of `MyTemplate`, it's probably not the most ideal way to associate
some behavior for our template.

### Static functions

When a function exists within the same Rust module as the template
definition, we can invoke it using the `self` path prefix, where `self`
represents the scope of the module in which the template struct resides.

For example, here we call the function `foo` by writing `self::foo(123)`
within the `MyTemplate` struct source:

```rust
fn foo(val: u32) -> String {
  format!("{}", val)
}

#[derive(Template)]
#[template(source = "{{ self::foo(123) }}", ext = "txt")]
struct MyTemplate;
```

This has the advantage of being able to share functionality across multiple
templates, without needing to expose the function publicly outside of its
module.

However, we are not limited to local functions defined within the same module.
We can call _any_ public function by specifying the full path to that function
within the template source. For example, given a utilities module such as:

```rust
// src/templates/utils/mod.rs

pub fn foo(val: u32) -> String {
  format!("{}", val)
}
```

Within our `MyTemplate` source, we can call the `foo` function by writing:

```rust
// src/templates/my_template.rs

#[derive(Template)]
#[template(source = "{{ crate::templates::utils::foo(123) }}", ext = "txt")]
struct MyTemplate;
```

### Struct / trait implementations

Finally, we can call methods of our template struct:

```rust
#[derive(Template)]
#[template(source = "{{ foo(123) }}", ext = "txt")]
struct MyTemplate {
  count: u32,
};

impl MyTemplate {
  fn foo(&self, val: u32) -> String {
    format!("{} is the count, {} is the value", self.count, val)
  }
}
```

You can also use `self.foo(123)`, or even `Self::foo(self, 123)`, as you see
fit.

Similarly, using the `Self` path, we can also call any method belonging
to a trait that has been implemented for our template struct:

```rust
trait Hello {
  fn greet(name: &str) -> String;
}

#[derive(Template)]
#[template(source = r#"{{ Self::greet("world") }}"#, ext = "txt")]
struct MyTemplate;

impl Hello for MyTemplate {
  fn greet(name: &str) -> String {
    format!("Hello {}", name)
  }
}
```

If you want to call a closure which is a field, you'll need to follow Rust's
syntax by surrounding the call with parens:

```rust
#[derive(Template)]
#[template(source = "{{ (closure)(12) }}", ext = "txt")]
struct MyTemplate {
    closure: fn(i32) -> i32,
}
```

## Calling functions

If you only provide a function name, askama will assume it's a method. If
you want to call a function, you will need to use a path instead:

```jinja
{# This is the equivalent of `self.method()`. #}
{{ method() }}
{# This is the equivalent of `self::function()`, which will call the
`function` function from the current module. #}
{{ self::function() }}
{# This is the equivalent of `super::b::f()`. #}
{{ super::b::f() }}
```

## Creating structs

Askama supports creating structs similarly as [in Rust](https://doc.rust-lang.org/reference/expressions/struct-expr.html):

```jinja
{{ MyStruct { field1: 1, field2: "foo" }.to_string() }}
```

Using base structs is supported too:

```jinja
{{ MyStruct { field1: 1, ..other_struct } }}
{{ MyStruct { field1: 1, ..Default::default() } }}
```

## Template inheritance

Template inheritance allows you to build a base template with common
elements that can be shared by all inheriting templates.
A base template defines **blocks** that child templates can override.

### Base template

```jinja
<!DOCTYPE html>
<html lang="en">
  <head>
    <title>{% block title %}{{ title }} - My Site{% endblock %}</title>
    {% block head %}{% endblock %}
  </head>
  <body>
    <div id="content">
      {% block content %}<p>Placeholder content</p>{% endblock %}
    </div>
  </body>
</html>
```

The `block` tags define three blocks that can be filled in by child
templates. The base template defines a default version of the block.
A base template must define one or more blocks in order to enable
inheritance. Blocks can only be specified at the top level of a template
or inside other blocks, not inside `if`/`else` branches or in `for`-loop
bodies.

It is also possible to use the name of the `block` in `endblock` (both in
declaration and use):

```jinja
{% block content %}<p>Placeholder content</p>{% endblock content %}
```

### Child template

Here's an example child template:

```jinja
{% extends "base.html" %}

{% block title %}Index{% endblock %}

{% block head %}
  <style>
  </style>
{% endblock %}

{% block content %}
  <h1>Index</h1>
  <p>Hello, world!</p>
  {{ super() }}
{% endblock %}
```

The `extends` tag tells the code generator that this template inherits
from another template. It will search for the base template relative to
itself before looking relative to the template base directory. It will
render the top-level content from the base template, and substitute
blocks from the base template with those from the child template. Inside
a block in a child template, the `super()` macro can be called to render
the parent block's contents.

Because top-level content from the child template is thus ignored, the `extends`
tag doesn't support whitespace control:

```jinja
{%- extends "base.html" +%}
```

The above code is rejected because we used `-` and `+`. For more information
about whitespace control, take a look [here](#whitespace-control).

### Block fragments

Additionally, a block can be rendered by itself. This can be useful when
you need to decompose your template for partial rendering, without
needing to extract the partial into a separate template or macro. This
can be done with the `block` parameter.

```rust
#[derive(Template)]
#[template(path = "...", block = "my_block")]
struct BlockFragment {
    name: String,
}
```

## HTML escaping

Askama by default escapes variables if it thinks it is rendering HTML
content. It infers the escaping context from the extension of template
filenames, escaping by default if the extension is one of `html`, `htm`,
or `xml`. When specifying a template as `source` in an attribute, the
`ext` attribute parameter must be used to specify a type. Additionally,
you can specify an escape mode explicitly for your template by setting
the `escape` attribute parameter value (to `none` or `html`).

Askama escapes `<`, `>`, `&`, `"`, and `'`, according to the
[OWASP escaping recommendations][owasp]. Use the `safe` filter to
prevent escaping for a single expression, or the `escape` (or `e`)
filter to escape a single expression in an unescaped context.

[owasp]: https://cheatsheetseries.owasp.org/cheatsheets/Cross_Site_Scripting_Prevention_Cheat_Sheet.html#output-encoding-for-html-contexts

```rust
#[derive(Template)]
#[template(source = "{{strvar}}")]
struct TestTemplate {
    strvar: String,
}

fn main() {
    let s = TestTemplate {
        strvar: "// my <html> is \"unsafe\" & should be 'escaped'".to_string(),
    };
    assert_eq!(
        s.render().unwrap(),
        "&#x2f;&#x2f; my &lt;html&gt; is &quot;unsafe&quot; &amp; \
         should be &#x27;escaped&#x27;"
    );
}
```

## Control structures

### For

Loop over each item in an iterator. For example:

```jinja
<h1>Users</h1>
<ul>
{% for user in users %}
  <li>{{ user.name }}</li>
{% endfor %}
</ul>
```

You can filter items by adding an `if` condition:

```jinja
<h1>Users</h1>
<ul>
{% for user in users if user.is_activated %}
  <li>{{ user.name }}</li>
{% endfor %}
</ul>
```

You can add an optional `{% else %}` block that is entered if the loop was never
entered, either because the iterator was empty, or the filter condition was never
match.

```jinja
<h1>Users</h1>
<ul>
{% for user in users %}
  <li>{{ user.name }}</li>
{% else %}
  <li>No users</li>
{% endfor %}
</ul>
```

Inside for-loop blocks, some useful variables are accessible:

* *loop.index*: current loop iteration (starting from 1)
* *loop.index0*: current loop iteration (starting from 0)
* *loop.first*: whether this is the first iteration of the loop
* *loop.last*: whether this is the last iteration of the loop

```jinja
<h1>Users</h1>
<ul>
{% for user in users %}
   {% if loop.first %}
   <li>First: {{user.name}}</li>
   {% else %}
   <li>User#{{loop.index}}: {{user.name}}</li>
   {% endif %}
{% endfor %}
</ul>
```

### If

The `if` statement essentially mirrors Rust's [`if` expression],
and is used as you might expect:

```jinja
{% if users.len() == 0 %}
  No users
{% else if users.len() == 1 %}
  1 user
{% elif users.len() == 2 %}
  2 users
{% else %}
  {{ users.len() }} users
{% endif %}
```

[`if` expression]: https://doc.rust-lang.org/reference/expressions/if-expr.html#if-expressions

#### If Let

Additionally, `if let` statements are also supported and similarly
mirror Rust's [`if let` expressions]:

```jinja
{% if let Some(user) = user %}
  {{ user.name }}
{% else %}
  No user
{% endif %}
```

[`if let` expressions]: https://doc.rust-lang.org/reference/expressions/if-expr.html#if-let-expressions

### `is (not) defined`

You can use `is (not) defined` to ensure a variable exists (or not):

```jinja
{% if x is defined %}
  x is defined!
{% endif %}
{% if y is not defined %}
  y is not defined
{% else %}
  y is defined
{% endif %}
```

You can combine conditions with this feature and even use it in expressions:

```jinja
{% if x is defined && x == "12" && y == Some(true) %}
...
{% endif %}

<script>
// It will generate `const x = true;` (or false is `x` is not defined).
const x = {{ x is defined }};
</script>
```

Due to proc-macro limitations, askama can only see the fields of your current type and the variables
declared in the templates. Because of this, you can not check if a field or a function is defined:

```jinja,error
{% if x.y is defined %}
  This code will not compile
{% endif %}
```

### Match

In order to deal with Rust `enum`s in a type-safe way, templates support
match blocks from version 0.6. Here is a simple example showing how to
expand an `Option`:

```jinja
{% match item %}
  {% when Some with ("foo") %}
    Found literal foo
  {% when Some with (val) %}
    Found {{ val }}
  {% when None %}
{% endmatch %}
```

That is, a `{% match %}` block may contain whitespaces (but no other literal content)
and comment blocks, followed by a number of `{% when %}` blocks
and an optional `{% else %}` block.

[Like in Rust](https://doc.rust-lang.org/book/ch18-00-patterns.html),
the matching is done against a pattern. Such a pattern may be a literal, e.g.

```jinja
{% match multiple_choice_answer %}
  {% when 3 %} Correct!
  {% else %} Sorry, the right answer is "3".
{% endmatch %}
```

Or some more complex type, such as a [`Result<T, E>`](https://doc.rust-lang.org/stable/std/result/enum.Result.html):

```jinja
{% match result %}
  {% when Ok(val) %} Good: {{ val }}.
  {% when Err(err) %} Bad: {{ err }}.
{% endmatch %}
```

Using the placeholder `_` to match against any value without capturing the datum, works too.
The wildcard operator `..` is used to match against an arbitrary amount of items,
and the same restrictions as in Rust, e.g. that it can be used only once in a slice or struct:

```jinja
{% match list_of_ints %}
  {% when [first, ..] %} The list starts with a {{ first }}
  {% when _ %} The list is empty.
{% endmatch %}
```

The `{% else %}` node is syntactical sugar for `{% when _ %}`.
If used, it must come last, after all other `{% when %}` blocks:

```jinja
{% match answer %}
  {% when Ok(42) %} The answer is "42".
  {% else %} No answer wrong answer?
{% endmatch %}
```

A `{% match %}` must be exhaustive, i.e. all possible inputs must have a case.
This is most easily done by providing an `{% else %}` case,
if not all possible values need an individual handling.

Because a `{% match %}` block could not generate valid code otherwise,
you have to provide at least one `{% when %}` case and/or an `{% else %}` case.

You can also match against multiple alternative patterns at once:

```jinja
{% match number %}
  {% when 1 | 4 | 86 %} Some numbers
  {% when n %} Number is {{ n }}
{% endmatch %}
```

For better interoperability with linters and auto-formatters like [djLint],
you can also use an optional `{% endwhen %}` node to close a `{% when %}` case:

```jinja
{% match number %}
  {% when 0 | 2 | 4 | 6 | 8 %}
    even
  {% endwhen %}
  {% when 1 | 3 | 5 | 7 | 9 %}
    odd
  {% endwhen %}
  {% else %}
    unknown
{% endmatch %}
```

[djLint]: <https://github.com/djlint/djlint>

### Referencing and dereferencing variables

If you need to put something behind a reference or to dereference it, you
can use `&` and `*` operators:

```jinja
{% let x = &"bla" %}
{% if *x == "bla" %}
Just talking
{% else if x == &"another" %}
Another?!
{% endif %}
```

They have the same effect as in Rust and you can put multiple of them:

```jinja
{% let x = &&"bla" %}
{% if *&**x == "bla" %}
You got it
{% endif %}
```

### Question mark operator

You can use the `?` operator similarly as [`?` operator in Rust] but only on `Result` types.

```jinja
{{ some_result? }}
{% let value = some_result? %}
```

When the operator unwraps erroneous value, the template rendering will fail with
[`askama::Error::Custom`](./doc/askama/enum.Error.html#variant.Custom) error that 
wraps the error.

Note that this operator currently only works with `Result` types - it doesn't support `Option` types.

[`?` operator in Rust]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator

### Include

The *include* statement lets you split large or repetitive blocks into
separate template files. Included templates get full access to the context
in which they're used, including local variables like those from loops:

```jinja
{% for i in iter %}
  {% include "item.html" %}
{% endfor %}
```

`item.html` file:

```jinja
* Item: {{ i }}
```

The path to include must be a string literal, so that it is known at
compile time. Askama will try to find the specified template relative
to the including template's path before falling back to the absolute
template path. Use `include` within the branches of an `if`/`else`
block to use includes more dynamically.

## Expressions

Askama supports string literals (`"foo"`) and integer literals (`1`).
It supports almost all binary operators that Rust supports,
including arithmetic, comparison and logic operators.
The parser applies the same [operator precedence] as the Rust compiler.
Expressions can be grouped using parentheses.

```jinja
{{ 3 * 4 / 2 }}
{{ 26 / 2 % 7 }}
{{ 3 % 2 * 6 }}
{{ 1 * 2 + 4 }}
{{ 11 - 15 / 3 }}
{{ (4 + 5) % 3 }}
```

The HTML special characters `&`, `<` and `>` will be replaced with their
character entities unless the `escape` mode is disabled for a template,
or the filter `| safe` is used.

Methods can be called on variables that are in scope, including `self`.

**Warning**: if the result of an expression (a `{{ }}` block) is
equivalent to `self`, this can result in a stack overflow from infinite
recursion. This is because the `Display` implementation for that expression
will in turn evaluate the expression and yield `self` again.

[operator precedence]: <https://doc.rust-lang.org/reference/expressions.html#expression-precedence>

### Expressions containing bit-operators

In Askama, the binary AND, OR, and XOR operators (called `&`, `|`, `^` in Rust, resp.),
are renamed to `bitand`, `bitor`, `xor` to avoid confusion with filter expressions.
They still have the same operator precedence as in Rust.
E.g. to test if the least significant bit is set in an integer field:

```jinja
{% if my_bitset bitand 1 != 0 %}
    It is set!
{% endif %}
```

### Type conversion

You can use the [`as`](https://doc.rust-lang.org/std/keyword.as.html) operator in `{{ … }}`
expressions, and `{% … %}` blocks. It works the same as in Rust, but with some deliberate
restrictions:

- You can only use [primitive types](https://doc.rust-lang.org/std/primitive/index.html)
  like `i32` or `f64` both as source variable type and as target type.
- If the source is a reference to a primitive type, e.g. `&&&bool`, then askama automatically
  dereferences the value until it gets the underlying `bool`.

### String concatenation

As a short-hand for `{{ a }}{{ b }}{{ c }}` you can use the concat operator `~`: `{{ a ~ b ~ c }}`.
The tilde `~` has to be surrounded by spaces to avoid confusion with the whitespace control operator.

## Templates in templates

Using expressions, it is possible to delegate rendering part of a template to another template.
This makes it possible to inject modular template sections into other templates and facilitates
testing and reuse.

```rust
use askama::Template;
#[derive(Template)]
#[template(source = "Section 1: {{ s1 }}", ext = "txt")]
struct RenderInPlace<'a> {
   s1: SectionOne<'a>
}

#[derive(Template)]
#[template(source = "A={{ a }}\nB={{ b }}", ext = "txt")]
struct SectionOne<'a> {
   a: &'a str,
   b: &'a str,
}

let t = RenderInPlace { s1: SectionOne { a: "a", b: "b" } };
assert_eq!(t.render().unwrap(), "Section 1: A=a\nB=b")
```

Note that if your inner template like `SectionOne` renders HTML content, then you may want to
disable escaping when injecting it into an outer template, e.g. `{{ s1 | safe }}`.
Otherwise it will render the HTML content literally, because
askama [escapes HTML variables](#html-escaping) by default.

Instead of disabling escaping for this template type at every single invocation within your template, you can alternatively mark the template itself as safe:

```rust
impl askama::filters::HtmlSafe for SectionOne<'_> {}
```

See the example
[render in place](https://github.com/askama-rs/askama/blob/master/testing/tests/render_in_place.rs), which demonstrates using a vector of templates in a for block.

## Comments

Askama supports block comments delimited by `{#` and `#}`.

```jinja
{# A Comment #}
```

Like Rust, Askama also supports nested block comments.

```jinja
{#
A Comment
{# A nested comment #}
#}
```

## Recursive Structures

Recursive implementations should preferably use a custom iterator and
use a plain loop. If that is not doable, call `.render()`
directly by using an expression as shown below.

```rust
use askama::Template;

#[derive(Template)]
#[template(source = r#"
{{ name }} {
{% for item in children %}
   {{ item.render()? }}
{% endfor %}
}
"#, ext = "html", escape = "none")]
struct Item<'a> {
    name: &'a str,
    children: &'a [Item<'a>],
}
```

## Macros

Macros are a jinja mechanism to declare reusable snippets. A macro can declare a set of required and optional arguments. Additionally, macros inherit the variable scope from their callsite. Defining and invoking a simple macro looks like this:

```jinja
{% macro heading(required_arg, optional_arg = "default subtitle") %}
    <h1>{{required_arg}}</h1>
    <h2>{{optional_arg}}</h2>
    {{ variable_in_scope }}
{% endmacro %}

{# Variable scope that will be passed into macro invocations #}
{% set variable_in_scope = 5 %}

{# Invoke the macro by supplying all arguments #}
{{ heading("test", "good subtitle") }}

{# Invoke the macro by leaving out the optional argument `optional_arg` #}
{# This will use the default value `default subtitle` #}
{{ heading("test") }}
```

Optionally, `{% endmacro %}` statements can also contain the macro's name, which would look something like this for the above example:

```jinja
{% macro heading(required_arg, optional_arg = "default subtitle") %}
    {# ... #}
{% endmacro heading %}
```

### Imports & Scopes

To have a small library of reusable snippets, it's best to declare the macros in some external file. This file can then be `import`ed with a named scope into your template. Moving the macro declaration above into the file `macro.html`, importing and then invoking it would look like this:

```jinja
{% import "macro.html" as scope %}

{{ scope::heading("test") }}
```

### Named Arguments

Additionally to specifying arguments positionally, you can also pass arguments by name. This allows passing the arguments in any order:

```jinja
{% macro heading(title, font_weight = "normal", font_size = 13) %}
    <h1 style="font-weight: {{ font_weight }}; font-size: {{ font_size }};">
        {{ title }}
    </h1>
{% endmacro %}

{# using positional arguments #}
{{ heading("Super Heading", "bold", 13) }}
{# using named arguments #}
{{ heading(title = "Super Heading", font_weight = "bold") }}
{{ heading(title = "Super Heading", font_weight = "bold", font_size = 23) }}
{{ heading(title = "Super Heading", font_size = 42, font_weight = "bold") }}
```

Both ways of invoking a macro can even be mixed, though optional arguments always have to come **last** (after all arguments specified positionally):

```jinja
{{ heading("Super Heading", font_weight = "bold", font_size = 26) }}
{{ heading("Super Heading", font_size = 26, font_weight = "bold") }}
{{ heading("Super Heading", "bold", font_size = 26) }}
```

Another thing to note, if a named argument is referring to an argument that would
be used for a non-named argument, it will error:

```jinja
{% macro heading(arg1, arg2, arg3, arg4) %}
{% endmacro %}

{{ heading("something", "b", arg4 = "ah", arg2 = "title") }}
```

In here it's invalid because `arg2` is the second argument and would be used by
`"b"`. So either you replace `"b"` with `arg3="b"` or you pass `"title"` before:

```jinja
{{ heading("something", arg3 = "b", arg4 = "ah", arg2 = "title") }}
{# Equivalent of: #}
{{ heading("something", "title", "b", arg4 = "ah") }}
```

### Macro Call Blocks

There is a second way to invoke macros, using the `call` block syntax. This syntax allows your invocation to have a "body". Within the macro, a special variable called `caller` will be defined, that behaves like a function and can insert the given body at any place:

```jinja
{% macro centered() %}
    <center>
        {# insert the invocation's body here: #}
        {{ caller() }}
    <center>
{% endmacro %}

{# This macro has to use the call block syntax, because it's expecting a body: #}
{% call centered() %}
    This text will be centered
{% endcall %}
```

Invoking this macro using the call expression syntax shown above (`{{ centered() }}`) will fail, because the macro is expecting the variable `caller()` to exist - but only `call`-block invocations define it.

However, you can declare macros in a way that allows invoking them with and without body:

```jinja
{% macro render_dialog(title, class="dialog") -%}
    <div class="{{ class }}">
        <h2>{{ title }}</h2>
        <div class="contents">
            {% if caller is defined %}
                {{ caller() }}
            {% else %}
                Empty dialog without content
            {% endif %}
        </div>
    </div>
{%- endmacro %}

{# invoking it without body: no `caller` will be defined #}
{{ render_dialog("Empty Dialog") }}

{# invoking it with body: #}
{% call render_dialog("Nice Dialog") %}
    This is a simple dialog rendered by using a macro and
    a call block.
{% endcall %}
```

### Macro Call Block Arguments

There is a reason why `caller` is a function instead of a variable.
It allows passing arguments, as well as calling it multiple times from the macro!
Here is an example macro that invokes the `caller()` method with the argument `user`.
To invoke this macro, your `call`-block has to declare arguments itself:

```jinja
{% macro dump_users(users) -%}
    <ul>
    {%- for user in users %}
        <li><p>{{ user.username }}</p>{{ caller(user) }}</li>
    {%- endfor %}
    </ul>
{%- endmacro %}

{# This callblock declares the argument `user` for `caller`: #}
{% call(user) dump_users(list_of_users) %}
    <dl>
        <dt>Realname</dt>
        <dd>{{ user.realname }}</dd>
        <dt>Description</dt>
        <dd>{{ user.description }}</dd>
    </dl>
{% endcall %}
```

### Nesting Macros With Content

At certain levels of abstraction, it might make sense to declare a macro that has a body - but will pass the body into another macro invocation.

Macro invocations instantly overwrite the `caller` variable with their own. To be able to access the outer `caller` variable, a small trick is required:

```jinja
{% macro container() %}
    <div class="container">
        {{ caller() }}
    </div>
{% endmacro %}

{% macro outer_container() %}
    {# Create an alias to our `caller`, so we can access it within container: #}
    {% set outer_caller = caller %}

    <div class="outer-container">
        {# nested macro invocation - will overwrite the `caller` variable: #}
        {% call container() %}
            {{ outer_caller() }}
        {% endcall %}
    </div>
{% endmacro %}
```


## Calling Rust macros

It is possible to call rust macros directly in your templates:

```jinja
{% let s = format!("{}", 12) %}
```

One important thing to note is that contrary to the rest of the expressions,
Askama cannot know if a token given to a macro is a variable or something
else, so it will always default to generate it "as is". So if you have:

```rust
macro_rules! test_macro{
    ($entity:expr) => {
        println!("{:?}", &$entity);
    }
}

#[derive(Template)]
#[template(source = "{{ test_macro!(entity) }}", ext = "txt")]
struct TestTemplate<'a> {
    entity: &'a str,
}
```

It will not compile, telling you it doesn't know `entity`. It didn't infer
that `entity` was a field of the current type unlike usual. You can go
around this limitation by binding your field's value into a variable:

```jinja
{% let entity = entity %}
{{ test_macro!(entity) }}
```
