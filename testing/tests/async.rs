#![cfg(feature = "async")]

use std::any::Any;
use std::io;
use std::pin::Pin;
use std::task::{Context, Poll};

use askama::{NO_VALUES, Template};
use futures::executor::block_on;
use futures::io::AsyncWrite;

/// Writer which is pending once before each write completes, and records every write.
#[derive(Default)]
struct PendingWriter {
    chunks: Vec<String>,
    pending: bool,
}

impl PendingWriter {
    fn output(&self) -> String {
        self.chunks.concat()
    }
}

impl AsyncWrite for PendingWriter {
    fn poll_write(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        self.pending = !self.pending;
        if self.pending {
            cx.waker().wake_by_ref();
            return Poll::Pending;
        }
        self.chunks.push(String::from_utf8(buf.to_vec()).unwrap());
        Poll::Ready(Ok(buf.len()))
    }

    fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }

    fn poll_close(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }
}

#[track_caller]
fn check<T: Template>(tmpl: &T) -> Vec<String> {
    let mut writer = PendingWriter::default();
    block_on(tmpl.async_render_into_with_values(&mut writer, NO_VALUES)).unwrap();
    assert_eq!(writer.output(), tmpl.render().unwrap());
    writer.chunks
}

#[test]
fn test_async_simple() {
    #[derive(Template)]
    #[template(
        source = "Hello {{ name }}! {% for x in list %}[{{ x }}]{% endfor %}",
        ext = "html"
    )]
    struct Simple<'a> {
        name: &'a str,
        list: &'a [u32],
    }

    let chunks = check(&Simple {
        name: "<world>",
        list: &[1, 2],
    });
    // Consecutive literals and expressions are written at once.
    assert_eq!(chunks, ["Hello &#60;world&#62;! ", "[1]", "[2]"]);
}

#[test]
fn test_async_into_vec() {
    #[derive(Template)]
    #[template(source = "{{ a }} + {{ b }}", ext = "txt")]
    struct Add {
        a: u32,
        b: u32,
    }

    let mut v = Vec::new();
    block_on(Add { a: 1, b: 2 }.async_render_into_with_values(&mut v, NO_VALUES)).unwrap();
    assert_eq!(v, b"1 + 2");
}

#[test]
fn test_async_nested_blocks() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro m(x) -%}<{{ x }}>{{ caller(x) }}{%- endmacro -%}
{%- filter upper -%}a{{ s }}b{%- endfilter -%}
{%- let v -%}let{{ s }}{%- endlet -%}
[{{ v }}]
{%- call(x) m(1) -%}call{{ x }}{%- endcall -%}
{%- let c -%}{%- call(y) m(2) -%}in let {{ y }}{%- endcall -%}{%- endlet -%}
{{ c }}
"#,
        ext = "html"
    )]
    struct Nested<'a> {
        s: &'a str,
    }

    check(&Nested { s: "x" });
}

#[test]
fn test_async_inheritance_and_include() {
    #[derive(Template)]
    #[template(path = "child.html")]
    struct Child<'a> {
        title: &'a str,
    }

    #[derive(Template)]
    #[template(path = "include.html")]
    struct Include<'a> {
        strs: &'a [&'a str],
    }

    check(&Child { title: "t" });
    check(&Include { strs: &["a", "b"] });
}

#[test]
fn test_async_blocks() {
    #[derive(Template)]
    #[template(
        source = "{% block first %}1{{ a }}{% endblock %}|{% block second %}2{% endblock %}",
        ext = "txt",
        blocks = ["first"]
    )]
    struct Blocks {
        a: u32,
    }

    let tmpl = Blocks { a: 7 };
    check(&tmpl);
    assert_eq!(check(&tmpl.as_first()), ["17"]);
}

#[test]
fn test_async_enum() {
    #[derive(Template)]
    #[template(
        source = "{% match self %}{% when Self::C %}c{% else %}?{% endmatch %}",
        ext = "txt"
    )]
    enum E {
        #[template(source = "a={{ self.0 }}", ext = "txt")]
        A(u32),
        #[template(source = "b={{ x }}", ext = "txt")]
        B {
            x: u32,
        },
        C,
    }

    assert_eq!(check(&E::A(1)), ["a=1"]);
    assert_eq!(check(&E::B { x: 2 }), ["b=2"]);
    check(&E::C);
}

#[test]
fn test_async_error() {
    struct Failing;

    impl AsyncWrite for Failing {
        fn poll_write(
            self: Pin<&mut Self>,
            _: &mut Context<'_>,
            _: &[u8],
        ) -> Poll<io::Result<usize>> {
            Poll::Ready(Err(io::Error::other("nope")))
        }

        fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }

        fn poll_close(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }
    }

    #[derive(Template)]
    #[template(source = "a{{ b }}", ext = "txt")]
    struct T {
        b: u32,
    }

    let err = block_on(T { b: 1 }.async_render_into_with_values(&mut Failing, NO_VALUES));
    assert_eq!(err.unwrap_err().to_string(), "nope");
}

/// Fails to compile if `value` is not `Send`.
fn assert_send<T: Send>(value: T) -> T {
    value
}

#[test]
fn test_async_send() {
    #[derive(Template)]
    #[template(
        source = r#"
{%- macro m(x) -%}<{{ x }}>{{ caller(x) }}{%- endmacro -%}
{%- for (i, x) in list.iter().enumerate() -%}
    {%- if loop.first %}first {% endif -%}
    [{{ i }}: {{ x }}]
{%- endfor -%}
{%- filter upper -%}a{{ s }}b{%- endfilter -%}
{%- let v -%}let{{ s }}{%- endlet -%}
[{{ v }}]
{%- call(x) m(1) -%}call{{ x }}{%- endcall -%}
{%- if let Ok(name) = "name"|value::<&str> %} {{ name }}{% endif -%}
{%- block b %} block{% endblock -%}
{%- include "included.html" -%}
"#,
        ext = "html",
        blocks = ["b"]
    )]
    struct Everything<'a> {
        s: &'a str,
        list: Vec<u32>,
    }

    #[derive(Template)]
    #[template(ext = "txt")]
    enum E {
        #[template(source = "a={{ self.0 }}")]
        A(u32),
    }

    let tmpl = Everything {
        s: "x",
        list: vec![1, 2],
    };
    let name: &str = "Ferris";
    let values: (&str, &(dyn Any + Send + Sync)) = ("name", &name);

    let mut writer = PendingWriter::default();
    block_on(assert_send(
        tmpl.async_render_into_with_values(&mut writer, &values),
    ))
    .unwrap();
    assert_eq!(writer.output(), tmpl.render_with_values(&values).unwrap());
    assert!(writer.output().contains(" Ferris"));

    // the future can be moved to another thread
    let mut writer = PendingWriter::default();
    std::thread::scope(|scope| {
        scope
            .spawn(|| block_on(tmpl.async_render_into_with_values(&mut writer, NO_VALUES)))
            .join()
            .unwrap()
            .unwrap();
    });
    assert_eq!(writer.output(), tmpl.render().unwrap());

    // `as_b()` returns `impl Template`, so the compiler cannot know if its future is `Send`.
    let mut writer = Vec::new();
    block_on(
        tmpl.as_b()
            .async_render_into_with_values(&mut writer, NO_VALUES),
    )
    .unwrap();
    assert_eq!(writer, b" block");

    let mut writer = Vec::new();
    block_on(assert_send(
        E::A(1).async_render_into_with_values(&mut writer, NO_VALUES),
    ))
    .unwrap();
}

#[test]
fn test_async_not_sync_template() {
    // A template which is not `Sync` can still be rendered asynchronously, the future is just not
    // `Send`.
    #[derive(Template)]
    #[template(source = "{{ a.get() }}", ext = "txt")]
    struct NotSync {
        a: std::cell::Cell<u32>,
    }

    let tmpl = NotSync {
        a: std::cell::Cell::new(1),
    };
    assert_eq!(check(&tmpl), ["1"]);
}

#[test]
fn test_async_render_with_values() {
    #[derive(Template)]
    #[template(
        source = "Hello {{ name }}{% if let Ok(x) = \"x\"|value::<u32> %} {{ x }}{% endif %}",
        ext = "html"
    )]
    struct Hello<'a> {
        name: &'a str,
    }

    #[derive(Template)]
    #[template(ext = "txt")]
    enum E {
        #[template(source = "a={{ self.0 }}")]
        A(u32),
        #[template(source = "b")]
        B,
    }

    let values: (&str, &(dyn Any + Send + Sync)) = ("x", &7u32);
    let hello = Hello { name: "<you>" };
    assert_eq!(
        block_on(assert_send(hello.async_render_with_values(&values))).unwrap(),
        hello.render_with_values(&values).unwrap(),
    );
    assert_eq!(
        block_on(hello.async_render_with_values(NO_VALUES)).unwrap(),
        "Hello &#60;you&#62;",
    );
    assert_eq!(
        block_on(assert_send(E::A(1).async_render_with_values(NO_VALUES))).unwrap(),
        "a=1"
    );
    assert_eq!(
        block_on(E::B.async_render_with_values(NO_VALUES)).unwrap(),
        "b"
    );
}
