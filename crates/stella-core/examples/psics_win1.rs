//! WIN-1 focused bench (docs/explore/perf-audit.md §3): the binarith
//! `add 999999 888888` large run — the corpus where the per-step
//! `psi_csyms(&psi)` O(|Ψ|) rebuild was the single largest measured phase
//! (psics = 0.3204 s = 81 % of `iex_fast` wall, 6594 steps). Runs ONLY the
//! Ψ-growing `iex_fast`/`iex_spec` tiers (skips the ~31 s reference `iex`
//! that `perf_audit` also benches) so the before/after KS-PROF comparison
//! is fast and reproducible:
//!
//!   STELLA_KS_PROF=1 cargo run -q --release --example psics_win1
//!
//! The `[KS-PROF] steps=… psics=…` line is the artifact: `steps` MUST be
//! identical before/after (same redex stream ⇒ faithful); `psics` MUST
//! collapse (incremental multiset vs. quadratic rebuild).

use std::time::Instant;
use stella_core::interactive::{iex_fast, iex_spec};

fn bench(tag: &str, f: impl Fn() -> stella_core::interactive::IExResult) {
    let t = Instant::now();
    let r = f();
    let dt = t.elapsed().as_secs_f64();
    eprintln!(
        ">>> {tag}: steps={} nf={} wall={dt:.4}s steps/s={:.0}",
        r.steps,
        r.is_normal_form,
        r.steps as f64 / dt.max(1e-9)
    );
}

fn main() {
    use stella_core::binarith::{binarith_module, nat};
    use stella_core::term::{mk_app_str as mk, mk_var};
    let phi = binarith_module();
    let qa = vec![
        mk("-add", vec![nat(999999), nat(888888), mk_var("R")]),
        mk_var("R"),
    ];
    eprintln!("--- binarith add 999999 888888 (iex_fast) ---");
    bench("binarith/add/iex_fast", || {
        iex_fast(&phi, vec![qa.clone()], 500_000)
    });
    eprintln!("--- binarith add 999999 888888 (iex_spec) ---");
    bench("binarith/add/iex_spec", || {
        iex_spec(&phi, vec![qa.clone()], 500_000)
    });
}
