//! Throwaway D-W3 attribution probe. perf-audit D-W3 measured a 73%
//! wall↔profiled-kernel GAP on galaxy [triple]; the *attribution* of
//! that gap to `term::get`/`is_ground`'s `TERM_STORE.read()` lock path
//! is [hypothesis]. This loops the [triple] force long enough for an
//! external sampling profiler (`sample <pid>`) to symbolicate where the
//! unattributed wall actually goes — confirm/refute before #3 commits
//! to a term.rs rewrite. No engine change; pure measurement.
//!   cargo run -q --release --example dw3_probe
use stella_core::galaxy::{self, eval_forced};
use stella_core::term::{self, TermId};
fn cst(n: &str) -> TermId { term::mk_app_str(n, vec![]) }
fn ap(f: TermId, x: TermId) -> TermId { term::mk_app_str("a", vec![f, x]) }
fn main() {
    let src = std::fs::read_to_string("/Users/ember/dev/embershot/src/galaxy.txt").unwrap();
    let g = galaxy::parse(&src).unwrap();
    let phi = galaxy::constellation(&g);
    let entry = galaxy::ref_atom(g.entry);
    let click = ap(ap(cst("cons"), stella_core::binarith::nat(0)), stella_core::binarith::nat(0));
    let prog = ap(ap(entry, cst("nil")), click);
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(60);
    let t0 = std::time::Instant::now();
    let mut steps = 0usize;
    for _ in 0..n {
        let f = eval_forced(&phi, prog, 2_000_000, 100_000);
        steps += f.steps;
    }
    eprintln!("dw3_probe: {n} [triple] forces, {steps} total steps, {:.2}s", t0.elapsed().as_secs_f64());
}
