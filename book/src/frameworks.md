# Working with web-frameworks

Askama's [`Template::render()`] returns <code>Result&lt;String, [askama::Error]&gt;</code>.
To make this result work in your preferred web-framework, you'll need to handle both cases:
converting the `String` to a web-response with the correct `Content-Type`,
and the `Error` case to a proper error message.

While in many cases it will be enough to simply convert the `Error` to

* `Box<dyn std::error::Error + Send + Sync>` using `err.into_box()` or
* `std::io::Error` using `err.into_io_error()`

it is **recommended** to use a custom error type.
This way you can display the error message in your app's layout,
and you are better prepared for the likely case that your app grows in the future.
Maybe you'll need to access a database and handle errors?
Maybe you'll add multiple languages and you want to localize error messages?

The crates [`thiserror`] and [`displaydoc`] can be useful to implement this error type.

[`Template::render()`]: <https://docs.rs/askama/0.3.5/askama/trait.Template.html#method.render>
[askama::Error]: <https://docs.rs/askama/0.3.5/askama/enum.Error.html>
[`thiserror`]: <https://crates.io/crates/thiserror>
[`displaydoc`]: <https://crates.io/crates/displaydoc>

### Simplified alternative

Alternatively, you can use [`#[derive(askama_web::WebTemplate)]`](https://crates.io/crates/askama_web/)
to automatically implement e.g. actix-web's `Responder`, axum's `IntoResponse` or warp's `Reply`.
The library implements traits for all web-frameworks mentioned down below (and then some),
but it does not stylize error messages.

If you don't need custom / stylized error messages,
e.g. because you know that your templates won't have rendering errors, then using
[`askama_web`](https://crates.io/crates/askama_web/) might work for you, too.

## Actix-Web

[![our actix-web example web-app](
    https://img.shields.io/badge/actix--web-example-informational?style=flat-square&logo=git&logoColor=white&color=%23228b22
)](
    https://github.com/askama-rs/askama/tree/master/examples/actix-web-app "our actix-web example web-app"
)
[![crates.io: actix-web](
    https://img.shields.io/crates/v/actix-web?label=actix-web&style=flat-square&logo=rust&logoColor=white&color=informational
)](
    https://crates.io/crates/actix-web "crates.io: actix-web"
)

To convert the `String` to an HTML response, you can use
[`Html::new(_)`](https://docs.rs/actix-web/4.9.0/actix_web/web/struct.Html.html#method.new).

```rust
use actix_web::web::Html;
use actix_web::{Responder, handler};

#[handler]
fn handler() -> Result<impl Responder, AppError> {
    …
    Ok(Html::new(template.render()?))
}
```

To implement your own error type, you can use this boilerplate code:

```rust
use actix_web::{HttpResponse, Responder};
use actix_web::error::ResponseError;
use actix_web::http::StatusCode;
use actix_web::web::Html;
use askama::Template;

#[derive(Debug, displaydoc::Display, thiserror::Error)]
enum AppError {
    /// could not render template
    Render(#[from] askama::Error),
}

impl ResponseError for AppError {
    fn status_code(&self) -> StatusCode {
        match &self {
            AppError::Render(_) => StatusCode::INTERNAL_SERVER_ERROR,
        }
    }
}

impl Responder for AppError {
    type Body = String;

    fn respond_to(self, req: &HttpRequest) -> HttpResponse<Self::Body> {
        #[derive(Debug, Template)]
        #[template(path = "error.html")]
        struct Tmpl { … }

        let tmpl = Tmpl { … };
        if let Ok(body) = tmpl.render() {
            (Html::new(body), self.status_code()).respond_to(req)
        } else {
            (String::new(), self.status_code()).respond_to(req)
        }
    }
}
```

## Axum

[![our axum example web-app](
    https://img.shields.io/badge/axum-example-informational?style=flat-square&logo=git&logoColor=white&color=%23228b22
)](
    https://github.com/askama-rs/askama/tree/master/examples/axum-app "our axum example web-app"
)
[![crates.io: axum](
    https://img.shields.io/crates/v/axum?label=axum&style=flat-square&logo=rust&logoColor=white&color=informational
)](
    https://crates.io/crates/axum "crates.io: axum"
)

To convert the `String` to an HTML response, you can use
[`Html(_)`](https://docs.rs/axum/0.8.1/axum/response/struct.Html.html).

```rust
use axum::response::{Html, IntoResponse};

async fn handler() -> Result<impl IntoResponse, AppError> {
    …
    Ok(Html(template.render()?))
}
```

To implement your own error type, you can use this boilerplate code:

```rust
use axum::response::IntoResponse;
use askama::Template;

#[derive(Debug, displaydoc::Display, thiserror::Error)]
enum AppError {
    /// could not render template
    Render(#[from] askama::Error),
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        #[derive(Debug, Template)]
        #[template(path = "error.html")]
        struct Tmpl { … }

        let status = match &self {
            AppError::Render(_) => StatusCode::INTERNAL_SERVER_ERROR,
        };
        let tmpl = Tmpl { … };
        if let Ok(body) = tmpl.render() {
            (status, Html(body)).into_response()
        } else {
            (status, "Something went wrong").into_response()
        }
    }
}
```

## Poem

[![our poem example web-app](
    https://img.shields.io/badge/poem-example-informational?style=flat-square&logo=git&logoColor=white&color=%23228b22
)](
    https://github.com/askama-rs/askama/tree/master/examples/poem-app "our poem example web-app"
)
[![crates.io: poem](
    https://img.shields.io/crates/v/poem?label=poem&style=flat-square&logo=rust&logoColor=white&color=informational
)](
    https://crates.io/crates/poem "crates.io: poem"
)

To convert the `String` to an HTML response, you can use
[`Html(_)`](https://docs.rs/poem/3.1.6/poem/web/struct.Html.html).

```rust
use poem::web::Html;
use poem::{IntoResponse, handler};

#[handler]
async fn handler() -> Result<impl IntoResponse, AppError> {
    …
    Ok(Html(template.render()?))
}
```

To implement your own error type, you can use this boilerplate code:

```rust
use poem::error::ResponseError;
use poem::http::StatusCode;
use poem::web::Html;
use poem::{IntoResponse, Response};
use askama::Template;

#[derive(Debug, displaydoc::Display, thiserror::Error)]
enum AppError {
    /// could not render template
    Render(#[from] askama::Error),
}

impl ResponseError for AppError {
    fn status(&self) -> StatusCode {
        match &self {
            AppError::Render(_) => StatusCode::INTERNAL_SERVER_ERROR,
        }
    }
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        #[derive(Debug, Template)]
        #[template(path = "error.html")]
        struct Tmpl { … }

        let tmpl = Tmpl { … };
        if let Ok(body) = tmpl.render() {
            (self.status(), Html(body)).into_response()
        } else {
            (self.status(), "Something went wrong").into_response()
        }
    }
}
```

## Rocket

[![our rocket example web-app](
    https://img.shields.io/badge/rocket-example-informational?style=flat-square&logo=git&logoColor=white&color=%23228b22
)](
    https://github.com/askama-rs/askama/tree/master/examples/rocket-app "our rocket example web-app"
)
[![crates.io: rocket](
    https://img.shields.io/crates/v/rocket?label=rocket&style=flat-square&logo=rust&logoColor=white&color=informational
)](
    https://crates.io/crates/rocket "crates.io: rocket"
)

To convert the `String` to an HTML response, you can use
[`RawHtml(_)`](https://docs.rs/rocket/0.5.1/rocket/response/content/struct.RawHtml.html).

```rust
use rocket::get;
use rocket::response::content::RawHtml;
use rocket::response::Responder;

#[get(…)]
fn handler<'r>() -> Result<impl Responder<'r, 'static>, AppError> {
    …
    Ok(RawHtml(template.render()?))
}
```

To implement your own error type, you can use this boilerplate code:

```rust
use askama::Template;
use rocket::http::Status;
use rocket::response::content::RawHtml;
use rocket::response::Responder;
use rocket::{Request, Response};

#[derive(Debug, displaydoc::Display, thiserror::Error)]
enum AppError {
    /// could not render template
    Render(#[from] askama::Error),
}

impl<'r> Responder<'r, 'static> for AppError {
    fn respond_to(
        self,
        request: &'r Request<'_>,
    ) -> Result<Response<'static>, Status> {
        #[derive(Debug, Template)]
        #[template(path = "error.html")]
        struct Tmpl { … }

        let status = match &self {
            AppError::Render(_) => Status::InternalServerError,
        };
        let template = Tmpl { … };
        if let Ok(body) = template.render() {
            (status, RawHtml(body)).respond_to(request)
        } else {
            (status, "Something went wrong").respond_to(request)
        }
    }
}
```

## Warp

[![our warp example web-app](
    https://img.shields.io/badge/warp-example-informational?style=flat-square&logo=git&logoColor=white&color=%23228b22
)](
    https://github.com/askama-rs/askama/tree/master/examples/warp-app "our warp example web-app"
)
[![crates.io: warp](
    https://img.shields.io/crates/v/warp?label=warp&style=flat-square&logo=rust&logoColor=white&color=informational
)](
    https://crates.io/crates/warp "crates.io: warp"
)

To convert the `String` to an HTML response, you can use
[`html(_)`](https://docs.rs/warp/0.3.7/warp/reply/fn.html.html).

```rust
use warp::reply::{Reply, html};

fn handler() -> Result<impl Reply, AppError> {
    …
    Ok(html(template.render()?))
}
```

To implement your own error type, you can use this boilerplate code:

```rust
use http::StatusCode;
use warp::reply::{Reply, Response, html};

#[derive(Debug, displaydoc::Display, thiserror::Error)]
enum AppError {
    /// could not render template
    Render(#[from] askama::Error),
}

impl Reply for AppError {
    fn into_response(self) -> Response {
        #[derive(Debug, Template)]
        #[template(path = "error.html")]
        struct Tmpl { … }

        let status = match &self {
            AppError::Render(_) => StatusCode::INTERNAL_SERVER_ERROR,
        };
        let template = Tmpl { … };
        if let Ok(body) = template.render() {
            with_status(html(body), status).into_response()
        } else {
            status.into_response()
        }
    }
}
```
