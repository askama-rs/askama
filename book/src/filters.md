# Filters

Values such as those obtained from variables can be post-processed
using **filters**.
Filters are applied to values using the pipe symbol (`|`) and may
have optional extra arguments in parentheses.
Filters can be chained, in which case the output from one filter
is passed to the next.

```jinja
{{ "HELLO" | lower }}
```

Askama has a collection of built-in filters, documented below, but can also include custom filters.
Additionally, the `json` filter is included in the built-in filters, but is disabled by default.
Enable it with Cargo features (see below for more information).

## Built-In Filters
[#built-in-filters]: #built-in-filters

Built-in filters that take (optional) arguments can be called with named arguments, too.
The order of the named arguments does not matter, but named arguments must come after
positional (i.e. unnamed) arguments.

E.g. the filter `pluralize` takes two optional arguments: `singular` and `plural`
which are `singular = ""` and `plural = "s"` by default.
If you are fine with the default empty string for the singular, and you only want to set a
specific plural, then you can call the filter like `dog{{ count | pluralize(plural = "gies") }}`.

### assigned_or
[#assigned_or]: #assigned_or

```jinja
{{ variable_or_expression | assigned_or(fallback) }}
```

If the variable on the left-hand side is in its "default" state, e.g. an empty `""` string,
a `0` integer, a `None` optional, or an `Err(_)` result, then the `fallback` value is printed.
Otherwise the value.

```jinja
{% let greeting = Some("Hello") %}
{{ greeting.as_ref() | assigned_or("Hi", true) }}
```

```html
Hello
```

If the value is an identifier, then it is first tested of the variable name is defined.
See also [`|defined_or`][#defined_or].

### capitalize
[#capitalize]: #capitalize

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ text_to_capitalize | capitalize }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Capitalize a value. The first character will be uppercase, all others lowercase:

```jinja
{{ "hello" | capitalize }}
```

Output:

```text
Hello
```

### center
[#center]: #center

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ text_to_center | center(length) }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Centers the value in a field of a given width:

```jinja
-{{ "a" | center(5) }}-
```

Output:
```text
-  a  -
```

### default
[#default]: #default

```text
{{ variable_or_expression | default(default_value) }}
{{ variable_or_expression | default(default_value, [[boolean =] true]) }}
```

This filter works like the Jinja filter of the [same name](https://jinja.palletsprojects.com/en/stable/templates/#jinja-filters.default).
If the second argument is not a boolean `true`, then the filter behaves like [`|defined_or`][#defined_or].
If it is supplied and `true`, then the filter behaves like [`|assigned_or`][#assigned_or].

**This filter exists for compatibility with Jinja.**
Askama provides [`|defined_or`][#defined_or] and [`|assigned_or`][#assigned_or] which both
better express the intention and should generally be used instead of this filter.

### defined_or
[#defined_or]: #defined_or

```jinja
{{ variable | defined_or(fallback) }}
```

The left-hand side of the filter must be an identifier.
Return a `fallback` value if the identifier is undefined:

```jinja
{% let greeting = "Hello" %}
{{ greeting | default("Hi") }}
```

Since the variable `greeting` is defined, the output is its value: `Hello`.

If you remove the variable, then the output is the default value: `Hi`:

```jinja
{{ greeting | default("Hi") }}
```

See also [`|assigned_or`][#assigned_or].

### deref
[#deref]: #deref

```jinja
{{ expression | deref }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Dereferences the given argument.

```jinja
{% let s = String::from("a") | ref %}
{% if s | deref == String::from("b") %}
{% endif %}
```

will become:

```rust
let s = &String::from("a");
if *s == String::from("b") {}
```

### escape | e
[#escape]: #escape--e

```jinja
{{ text_to_escape | e }}
{{ text_to_escape | escape }}
{{ text_to_escape | escape(escaper) }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Escapes HTML characters in strings:

```jinja
{{ "Escape <>&" | e }}
```

Output:

```html
Escape &lt;&gt;&amp;
```

Optionally, it is possible to specify and override which escaper is used.
Consider a template where the escaper is configured as [`escape = "none"`].
However, somewhere escaping using the HTML escaper is desired.
Then it is possible to override and use the HTML escaper like this:

```jinja
{{ "Don't Escape <>&" | escape }}
{{ "Don't Escape <>&" | e }}

{{ "Escape <>&" | escape("html") }}
{{ "Escape <>&" | e("html") }}
```

Output:

```text
Don't Escape <>&
Don't Escape <>&

Escape &lt;&gt;&amp;
Escape &lt;&gt;&amp;
```

[`escape = "none"`]: creating_templates.html#the-template-attribute

### filesizeformat
[#filesizeformat]: #filesizeformat

```jinja
{{ number_of_bytes | filesizeformat }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Returns adequate string representation (in KB, ..) of number of bytes:

```jinja
{{ 1000 | filesizeformat }}
```

Output:
```text
1 KB
```

### fmt
[#fmt]: #fmt

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ expression | fmt("format_string") }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Formats arguments according to the specified format

The *second* argument to this filter must be a string literal (as in normal
Rust). The two arguments are passed through to [`format!()`] by
the Askama code generator, but the order is swapped to support filter
composition.

```jinja
{{ value | fmt("{:?}") }}
```

As an example, this allows filters to be composed like the following.
Which is not possible using the `format` filter.

```jinja
{{ value | capitalize | fmt("{:?}") }}
```

### format
[#format]: #format

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```text
{{ "format_string" | format([variables ...]) }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Formats arguments according to the specified format.

The first argument to this filter must be a string literal (as in normal Rust).

All arguments are passed through to [`format!()`] by the Askama code generator.

```jinja
{{ "{:?}" | format(var) }}
```

[`format!()`]: https://doc.rust-lang.org/stable/std/macro.format.html

### indent
[#indent]: #indent

```jinja
{{ text_to_indent | indent(width, [first], [blank]) }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Indent newlines with width spaces.

```jinja
{{ "hello\nfoo\nbar" | indent(4) }}
```

Output:

```text
hello
    foo
    bar
```

The first argument can also be a string that will be used to indent lines.

The first line and blank lines are not indented by default.
The filter has two optional [`bool`] arguments `first` and `blank`, that can be set to `true`
to indent the first and blank lines, resp.:

```jinja
{{ "hello\n\nbar" | indent("$ ", true, true) }}
```

Output:

```text
$ hello
$
$ bar
```

### join
[#join]: #join

```jinja
{{ iterable | join(separator) }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Joins iterable into a string separated by provided argument.

```rust
array = &["foo", "bar", "bazz"]
```

```jinja
{{ array | join(", ") }}
```

Output:

```text
foo, bar, bazz
```

### linebreaks
[#linebreaks]: #linebreaks

```jinja
{{ text_to_break | linebreaks }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Replaces line breaks in plain text with appropriate HTML.

A single newline becomes an HTML line break `<br>` and a new line followed by a blank line becomes a paragraph break `<p>`.

```jinja
{{ "hello\nworld\n\nfrom\naskama" | linebreaks }}
```

Output:

```html
<p>hello<br />world</p><p>from<br />askama</p>
```

### linebreaksbr
[#linebreaksbr]: #linebreaksbr

```jinja
{{ text_to_break | linebreaksbr }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Converts all newlines in a piece of plain text to HTML line breaks.

```jinja
{{ "hello\nworld\n\nfrom\naskama" | linebreaks }}
```

Output:

```html
hello<br />world<br /><br />from<br />askama
```

### paragraphbreaks
[#paragraphbreaks]: #paragraphbreaks

```jinja
{{ text_to_break | paragraphbreaks }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

A new line followed by a blank line becomes `<p>`, but, unlike `linebreaks`, single new lines are ignored and no `<br/>` tags are generated.

Consecutive double line breaks will be reduced down to a single paragraph break.

This is useful in contexts where changing single line breaks to line break tags would interfere with other HTML elements, such as lists and nested `<div>` tags.

```jinja
{{ "hello\nworld\n\nfrom\n\n\n\naskama" | paragraphbreaks }}
```

Output:

```html
<p>hello\nworld</p><p>from</p><p>askama</p>
```

### lower | lowercase
[#lower]: #lower--lowercase

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ text_to_convert | lower }}
{{ text_to_convert | lowercase }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Converts to lowercase.

```jinja
{{ "HELLO" | lower }}
```

Output:

```text
hello
```

### `pluralize`
[#pluralize]: #pluralize

```text
{{ integer | pluralize }}
{{ integer | pluralize([singular = ""], [plural = "s"]) }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Select a singular or plural version of a word, depending on the input value.

If the value of `self.count` is +1 or -1, then "cat" is returned, otherwise "cats":

```jinja
cat{{ count | pluralize }}
```

You can override the default empty singular suffix, e.g. to spell "doggo" for a single dog:

```jinja
dog{{ count | pluralize("go") }}
```

If the word cannot be declined by simply adding a suffix,
then you can also override singular and the plural, too:

```jinja
{{ count | pluralize("mouse", "mice") }}
```

More complex languages that know multiple plurals might be impossible to implement with this filter,
though.

### ref
[#ref]: #ref

```jinja
{{ expression | ref }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Creates a reference to the given argument.

```jinja
{{ "a" | ref }}
{{ self.x | ref }}
```

will become:

```rust
&"a"
&self.x
```

### reject
[#reject]: #reject

This filter filters out values matching the given value/filter.

With this data:

```rust
vec![1, 2, 3, 1]
```

And this template:

```jinja
{% for elem in data|reject(1) %}{{ elem }},{% endfor %}
```

Output will be:

```text
2,3,
```

For more control over the filtering, you can use a callback instead. Declare a function:

```jinja
fn is_odd(value: &&u32) -> bool {
    **value % 2 != 0
}
```

Then you can pass the path to the `is_odd` function:

```jinja
{% for elem in data|reject(crate::is_odd) %}{{ elem }},{% endfor %}
```

Output will be:

```text
2,
```

### safe
[#safe]: #safe

```jinja
{{ expression | safe }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Marks a string (or other Display type) as safe. By default all strings are escaped according to the format.

```jinja
{{ "<p>I'm Safe</p>" | safe }}
```

Output:

```html
<p>I'm Safe</p>
```

### title | titlecase
[#title]: #title--titlecase

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ text_to_convert | title }}
{{ text_to_convert | titlecase }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Return a title cased version of the value. Words will start with uppercase letters, all
remaining characters are lowercase.

```jinja
{{ "hello WORLD" | title }}
```

Output:

```text
Hello World
```

### trim
[#trim]: #trim

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ text_to_trim | trim }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Strip leading and trailing whitespace.

```jinja
{{ " hello " | trim }}
```

Output:

```text
hello
```

### truncate
[#truncate]: #truncate

```jinja
{{ text_to_truncate | truncate(length) }}
```

Limit string length, appends '...' if truncated.

```jinja
{{ "hello" | truncate(2) }}
```

Output:

```text
he...
```

### unique
[#unique]: #unique

Returns an iterator with all duplicates removed.

**This filter is only available with the `std` feature enabled.**

With this data:

```rust
vec!["a", "b", "a", "c"]
```

And this template:

```jinja
{% for elem in data|unique %}{{ elem }},{% endfor %}
```

Output will be:

```text
a,b,c,
```

### upper | uppercase
[#upper]: #upper--uppercase

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"alloc"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ text_to_convert | upper }}
{{ text_to_convert | uppercase }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Converts to uppercase.

```jinja
{{ "hello" | upper }}
```

Output:

```text
HELLO
```

### urlencode | urlencode_strict
[#urlencode]: #urlencode--urlencode_strict

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"urlencode"</code><br/>
enabled by <code>"default"</code>
</blockquote>

```jinja
{{ text_to_escape | urlencode }}
{{ text_to_escape | urlencode_strict }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Percent encodes the string. Replaces reserved characters with the % escape character followed by a byte value as two hexadecimal digits.

```jinja
{{ "hello?world" | urlencode }}
```

Output:

```text
hello%3Fworld
```

With `|urlencode` all characters except ASCII letters, digits, and `_.-~/` are escaped.
With `|urlencode_strict` a forward slash `/` is escaped, too.

### wordcount
[#wordcount]: #wordcount

```jinja
{{ text_with_words | wordcount }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Count the words in that string.

```jinja
{{ "askama is sort of cool" | wordcount }}
```

Output:

```text
5
```

## Optional / feature gated filters
[#optional-filters]: #optional--feature-gated-filters

The following filters can be enabled by requesting the respective feature in the Cargo.toml
[dependencies section](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html), e.g.

```toml
[dependencies]
askama = { version = "0.12", features = ["serde_json"] }
```

### `json` | `tojson`
[#json]: #json--tojson

<blockquote class="right" style="padding:0.5ex 1ex; margin:0 0 1ex 1ex; font-size:80%">
enabled by <code>"serde_json"</code>
</blockquote>

```jinja
{{ value_to_serialize | json }}
{{ value_to_serialize | json(indent) }}
```

<hr style="clear:both; border:0; border-bottom:1pt solid currentColor">

Enabling the `serde_json` feature will enable the use of the `json` filter.
This will output formatted JSON for any value that implements the required
[`Serialize`](https://docs.rs/serde/1.*/serde/trait.Serialize.html) trait.
The generated string does not contain ampersands `&`, chevrons `< >`, or apostrophes `'`.

To use it in a `<script>` you can combine it with the safe filter.
In HTML attributes, you can either use it in quotation marks `"{{data | json}}"` as is,
or in apostrophes with the (optional) safe filter `'{{data | json | safe}}'`.
In HTML texts the output of e.g. `<pre>{{data | json | safe}}</pre>` is safe, too.

```jinja
Good: <li data-extra="{{data | json}}">…</li>
Good: <li data-extra='{{data | json | safe}}'>…</li>
Good: <pre>{{data | json | safe}}</pre>
Good: <script>var data = {{data | json | safe}};</script>

Bad:  <li data-extra="{{data | json | safe}}">…</li>
Bad:  <script>var data = {{data | json}};</script>
Bad:  <script>var data = "{{data | json | safe}}";</script>

Ugly: <script>var data = "{{data | json}}";</script>
Ugly: <script>var data = '{{data | json | safe}}';</script>
```

By default, a compact representation of the data is generated, i.e. no whitespaces are generated
between individual values. To generate a readable representation, you can either pass an integer
how many spaces to use as indentation, or you can pass a string that gets used as prefix:

```jinja
Prefix with four spaces:
<textarea>{{data | tojson(4)}}</textarea>

Prefix with two &nbsp; characters:
<p>{{data | tojson("\u{a0}\u{a0}")}}</p>
```

## Custom Filters
[#custom-filters]: #custom-filters

To define your own filters, either have a module named `filters` in scope of the context of your
`#[derive(Template]) struct`, and define the filters as functions within this module;
or call the filter with a path, e.g. `{{ value | some_module::my_filter }}`.
The expressions `{{ value | my_filter }}` and `{{ value | filters::my_filter }}` behave identically,
unless "my_filter" happens to be a built-in filter.

The functions must have at least two arguments and the return type must be `askama::Result<T>`.
Although there are no restrictions on `T` for a single filter,
the final result of a chain of filters must implement `Display`.

The arguments to the filters are passed as follows:
* The first argument corresponds to the expression they are applied to.
* The second argument are the [runtime values](./runtime.html):
  [`values: &dyn askama::Values`](./doc/askama/trait.Values.html).
* Subsequent arguments, if any, must be given directly when calling the filter.
  The first argument may or may not be a reference, depending on the context in which the filter is called.

To abstract over ownership, consider defining your argument as a trait bound.
For example, the `trim` built-in filter accepts any value implementing `Display`.
Its signature is similar to `fn trim(s: impl std::fmt::Display, values: &dyn askama::Values) -> askama::Result<String>`.

Note that built-in filters have preference over custom filters, so, in case of name collision, the built-in filter is applied.
Custom filters cannot have named or optional arguments.

### Examples

Implementing a filter that replaces all instances of `"oo"` for `"aa"`.
```rust
use askama::Template;

#[derive(Template)]
#[template(source = "{{ s | myfilter }}", ext = "txt")]
struct MyFilterTemplate<'a> {
    s: &'a str,
}

// Any filter defined in the module `filters` is accessible in your template.
mod filters {
    // This filter does not have extra arguments
    pub fn myfilter<T: std::fmt::Display>(
        s: T,
        _: &dyn askama::Values,
    ) -> askama::Result<String> {
        let s = s.to_string();
        Ok(s.replace("oo", "aa"))
    }
}

fn main() {
    let t = MyFilterTemplate { s: "foo" };
    assert_eq!(t.render().unwrap(), "faa");
}
```

Implementing a filter that replaces all instances of `"oo"` for `n` times `"a"`.
```rust
use askama::Template;

#[derive(Template)]
#[template(source = "{{ s | myfilter(4) }}", ext = "txt")]
struct MyFilterTemplate<'a> {
    s: &'a str,
}

// Any filter defined in the module `filters` is accessible in your template.
mod filters {
    // This filter requires a `usize` input when called in templates
    pub fn myfilter<T: std::fmt::Display>(
        s: T,
        _: &dyn askama::Values,
        n: usize,
    ) -> askama::Result<String> {
        let s = s.to_string();
        let mut replace = String::with_capacity(n);
        replace.extend((0..n).map(|_| "a"));
        Ok(s.replace("oo", &replace))
    }
}

fn main() {
    let t = MyFilterTemplate { s: "foo" };
    assert_eq!(t.render().unwrap(), "faaaa");
}
```

### Runtime values
[#runtime-values]: #runtime-values

It is possible to access [runtime values](./runtime.html) in custom filters:

```rust
{{#include ../../testing/tests/book_example_runtime_values_in_custom_filters.rs}}
```

## HTML-safe types
[#html-safe-types]: #html-safe-types

Askama will try to avoid escaping types that generate string representations that do not contain
"HTML-unsafe characters".
HTML-safe characters are characters that can be used in any context in HTML texts and attributes.
The "unsafe" characters are: `<`, `>`, `&`, `"` and `'`.

In order to know which types do not need to be escaped, askama has the marker trait
`askama::filters::HtmlSafe`, and any type that implements that trait won't get automatically
escaped in a `{{expr}}` expression.
By default e.g. all primitive integer types are marked as HTML-safe.

You can also mark your custom type `MyStruct` as HTML-safe using:

```rust
impl askama::filters::HtmlSafe for MyStruct {}
```

This automatically marks references `&MyStruct` as HTML-safe, too.

### Safe output of custom filters
[#safe-output-of-custom-filters]: #safe-output-of-custom-filters

Say, you have a custom filter `| strip` that removes all HTML-unsafe characters:

```rust
fn strip(s: impl ToString) -> Result<String, askama::Error> {
    Ok(s.to_string()
        .chars()
        .filter(|c| !matches!(c, '<' | '>' | '&' | '"' | '\''))
        .collect()
    )
}
```

Then you can also mark the output as safe using `askama::filters::Safe`:

```rust
fn strip(s: impl ToString) -> Result<Safe<String>, askama::Error> {
    Ok(Safe(...))
}
```

There also is `askama::filters::MaybeSafe` that can be used to mark *some* output as safe,
if you know that *some* inputs for our filter will always result in a safe output:

```rust
fn as_sign(i: i32) -> Result<MaybeSafe<&'static str>, askama::Error> {
    match i.into() {
        i if i < 0 => Ok(MaybeSafe::NeedsEscaping("<0")),
        i if i > 0 => Ok(MaybeSafe::NeedsEscaping(">0")),
        _          => Ok(MaybeSafe::Safe("=0")),
    }
}
```
