// In Rust 1.19 and prior, `include!` in a doc test was relative to
// `Cargo.toml`, so we needed to include `src/example-helpers.rs`. On Rust
// 1.20, this was fixed to be relative to the file in question. In order to
// continue supporting older versions, we still include with the src/ prefix,
// and for 1.20+ have this redirect to the actual file.
include!("../example_helpers.rs");
