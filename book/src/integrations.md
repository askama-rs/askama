# Integrations

## Rocket integration

In your template definitions, replace `rinja::Template` with
[`rinja_rocket::Template`][rinja_rocket].

Enabling the `with-rocket` feature appends an implementation of Rocket's
`Responder` trait for each template type. This makes it easy to trivially
return a value of that type in a Rocket handler. See
[the example](https://github.com/rinja-rs/rinja/blob/v0.3.5/rinja_rocket/tests/basic.rs)
from the Rinja test suite for more on how to integrate.

In case a run-time error occurs during templating, a `500 Internal Server
Error` `Status` value will be returned, so that this can be further
handled by your error catcher.

## Actix-web integration

In your template definitions, replace `rinja::Template` with
[`rinja_actix::Template`][rinja_actix].

Enabling the `with-actix-web` feature appends an implementation of Actix-web's
`Responder` trait for each template type. This makes it easy to trivially return
a value of that type in an Actix-web handler. See
[the example](https://github.com/rinja-rs/rinja/blob/v0.3.5/rinja_actix/tests/basic.rs)
from the Rinja test suite for more on how to integrate.

## Axum integration

In your template definitions, replace `rinja::Template` with
[`rinja_axum::Template`][rinja_axum].

Enabling the `with-axum` feature appends an implementation of Axum's
`IntoResponse` trait for each template type. This makes it easy to trivially
return a value of that type in a Axum handler. See
[the example](https://github.com/rinja-rs/rinja/blob/v0.3.5/rinja_axum/tests/basic.rs)
from the Rinja test suite for more on how to integrate.

In case of a run-time error occurring during templating, the response will be of the same
signature, with a status code of `500 Internal Server Error`, mime `*/*`, and an empty `Body`.
This preserves the response chain if any custom error handling needs to occur.

## Warp integration

In your template definitions, replace `rinja::Template` with
[`rinja_warp::Template`][rinja_warp].

Enabling the `with-warp` feature appends an implementation of Warp's `Reply`
trait for each template type. This makes it simple to return a template from
a Warp filter. See [the example](https://github.com/rinja-rs/rinja/blob/v0.3.5/rinja_warp/tests/warp.rs)
from the Rinja test suite for more on how to integrate.

[rinja_rocket]: https://docs.rs/rinja_rocket
[rinja_actix]: https://docs.rs/rinja_actix
[rinja_axum]: https://docs.rs/rinja_axum
[rinja_warp]: https://docs.rs/rinja_warp
