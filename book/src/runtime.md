# Runtime values

It is possible to define variables at runtime and to use them in the templates using the `values`
filter or the `askama::get_value` function and to call the `_with_values` variants of the `render`
methods. It expects an extra argument implementing the `Values` trait. This trait is implemented on
a few types provided by the `std`, like `HashMap`:

```rust
use std::collections::HashMap;

let mut values: HashMap<&str, Box<dyn Any>> = HashMap::new();
// We add a new value named "name" with the value "Bibop".
values.insert("name", Box::new("Bibop"));
values.insert("age", Box::new(12u32));
```

The `Values` trait is expecting types storing data with the `Any` trait, allowing to store any type.

Then to render with these values:

```rust
template_struct.render_with_values(&values).unwrap();
```

There are two ways to get the values from the template, either by using the `value` filter
or by calling directly the `askama::get_value` function:

```jinja
{% if let Ok(name) = "name"|value::<&str> %}
  name is {{ name }}
{% endif %}
{% if let Ok(age) = askama::get_value::<u32>("age") %}
  age is {{ age }}
{% endif %}
```

If you try to retrieve a value with the wrong type or that you didn't set, you will get an
`Err(askama::Error::ValueType)` or a `Err(askama::Error::ValueMissing)`.

Another example with a key-value tuple:

```rust
let value = "value".to_string();
let tuple: (&str, &dyn Any) = ("a", &value);

template_struct.render_with_values(&tuple).unwrap();
```

With this setup, only the `"a"` key will return a value:

```jinja
{% if let Ok(name) = "a"|value::<String> %}
  a is {{ a }}
{% endif %}
```
