//! READ-ONLY Σ(Φ) selection-residual KS-PROF harness.
//!
//!   STELLA_KS_PROF=1 cargo run -q --release --example spec_select_prof
//!
//! Runs ONLY the Σ(Φ) tier (`iex_spec`) on the two corpora the deepened
//! selection residual targets — combinator (Push/Splice) and galaxy Φ=405
//! (δ/Push/Splice) — and prints, per workload: steps + wall, plus the
//! per-phase breakdown (find/matchable) emitted on stderr by `ks_report`.
//! It does NOT run the slow reference `iex` (irrelevant to the find-phase
//! before/after delta and the reason `perf_audit` takes minutes). Pure
//! measurement; mutates no source.
//!
//! The faithfulness gate (`iex_spec_result_eq_iex`, decision-equivalence vs
//! reference `iex` + step-identity vs `iex_fast` + α-equivalence) is the
//! correctness oracle and lives in the test suite; this harness is solely
//! the KS-PROF lever measurement (steps printed here so the before/after
//! step-identity is visible alongside the find-phase shrink).

use std::time::Instant;
use stella_core::combinator::{a_, app_n, initial_process, machine_stars, Comb};
use stella_core::interactive::{iex_fast, iex_spec};

fn bench<F: Fn() -> stella_core::interactive::IExResult>(label: &str, f: F) {
    let t0 = Instant::now();
    let r = f();
    let dt = t0.elapsed().as_secs_f64();
    eprintln!(
        ">>> {label}: steps={} nf={} wall={:.4}s steps/s={:.0}",
        r.steps,
        r.is_normal_form,
        dt,
        r.steps as f64 / dt.max(1e-9)
    );
}

fn main() {
    // ── combinator: SKK x and a deep S/B/C nest (Push + Splice heavy) ────
    {
        let phi = machine_stars();
        let skk = app_n([a_("S"), a_("T"), a_("T"), a_("x")]);
        fn skk_app(arg: Comb) -> Comb {
            app_n([a_("S"), a_("T"), a_("T"), arg])
        }
        let mut big = a_("x");
        for _ in 0..8 {
            big = skk_app(big);
        }
        for (name, t) in [("SKKx", skk), ("SKK^8 x", big)] {
            let p = initial_process(&t);
            eprintln!("--- combinator {name} (iex_fast — selection oracle) ---");
            bench(&format!("comb/{name}/iex_fast"), || {
                iex_fast(&phi, vec![p.clone()], 2_000_000)
            });
            eprintln!("--- combinator {name} (iex_spec / Σ(Φ)) ---");
            bench(&format!("comb/{name}/iex_spec"), || {
                iex_spec(&phi, vec![p.clone()], 2_000_000)
            });
        }
    }

    // ── galaxy Φ=405 [triple] entry force — the δ/Push/Splice skeleton ──
    {
        use stella_core::galaxy;
        use stella_core::term::{self, TermId};
        fn cst(n: &str) -> TermId {
            term::mk_app_str(n, vec![])
        }
        fn ap(f: TermId, x: TermId) -> TermId {
            term::mk_app_str("a", vec![f, x])
        }
        let path = "/Users/ember/dev/embershot/src/galaxy.txt";
        match std::fs::read_to_string(path) {
            Err(e) => eprintln!("[skip galaxy] {path}: {e}"),
            Ok(src) => {
                let g = galaxy::parse(&src).expect("parse galaxy");
                let phi = galaxy::constellation(&g);
                let entry = galaxy::ref_atom(g.entry);
                let click = ap(
                    ap(cst("cons"), stella_core::binarith::nat(0)),
                    stella_core::binarith::nat(0),
                );
                let prog = ap(ap(entry, cst("nil")), click);
                let psi = galaxy::initial_psi(prog);
                eprintln!("--- galaxy [triple] entry (iex_fast — selection oracle) ---");
                bench("galaxy/triple/iex_fast", || {
                    iex_fast(&phi, psi.clone(), 2_000_000)
                });
                eprintln!("--- galaxy [triple] entry (iex_spec / Σ(Φ)) ---");
                bench("galaxy/triple/iex_spec", || {
                    iex_spec(&phi, psi.clone(), 2_000_000)
                });
            }
        }
    }
}
