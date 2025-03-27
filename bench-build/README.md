Run the script `./run.sh` in this directory to compare the compile compile of `askama`

* uses feature `derive` vs
* it does not use that feature.

The output might look like:

```text
Benchmark 1: cargo run --features=derive
  Time (mean ± σ):      3.378 s ±  0.041 s    [User: 7.944 s, System: 1.018 s]
  Range (min … max):    3.345 s …  3.424 s    3 runs
 
Benchmark 2: cargo run
  Time (mean ± σ):      3.283 s ±  0.130 s    [User: 8.400 s, System: 1.091 s]
  Range (min … max):    3.141 s …  3.398 s    3 runs
 
Summary
  cargo run ran
    1.03 ± 0.04 times faster than cargo run --features=derive

----------

Benchmark 1: cargo run --release --features=derive
  Time (mean ± σ):      4.733 s ±  0.050 s    [User: 9.026 s, System: 0.749 s]
  Range (min … max):    4.689 s …  4.788 s    3 runs
 
Benchmark 2: cargo run --release
  Time (mean ± σ):      4.504 s ±  0.032 s    [User: 9.010 s, System: 0.733 s]
  Range (min … max):    4.481 s …  4.541 s    3 runs
 
Summary
  cargo run --release ran
    1.05 ± 0.01 times faster than cargo run --release --features=derive
```

This shows that – while it is less convenient – for small projects it might be better
to use the following setup.
This might be especially true if you are using `askama` in a library.
Without the feature, `cargo` will be able to compile more dependencies in parallel.

```toml
# Cargo.toml
[dependencies]
askama = { version = "0.13.0", default-features = false, features = ["std"] }
askama_derive = { version = "0.13.0", features = ["std"] }
```

```rust
// lib.rs
use askama::Template as _;
use askama_derive::Template;
```

The script uses [hyperfine](https://crates.io/crates/hyperfine).
Install it with `cargo install hyperfine`.
