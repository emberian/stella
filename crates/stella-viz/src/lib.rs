//! stella-viz library crate.
//!
//! Exposes the `presets` and `stepper` modules for both the native TCP server
//! (via the `[[bin]]` target) and the WASM static-site build (via the `[lib]`
//! cdylib target, gated with `--features wasm`).

pub mod build;
pub mod exsem;
pub mod logic;
pub mod presets;
pub mod stepper;

// WASM bindings — compiled only when `--features wasm` is set.
#[cfg(feature = "wasm")]
pub mod wasm;
