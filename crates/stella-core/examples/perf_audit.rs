//! READ-ONLY perf audit harness (docs/explore/perf-audit.md).
//!
//!   STELLA_KS_PROF=1 cargo run -q --release --example perf_audit
//!
//! Pure measurement; mutates no source. Galaxy [triple] (Φ=405) FIRST —
//! the canonical benchmark. binarith uses small operands (binary mul is
//! O(bits²) stars — wide mul is a known docs/07 KS-gated cost, not the
//! per-step envelope we audit).

use std::time::Instant;
use stella_core::combinator::{a_, app_n, machine_stars, initial_process, Comb};
use stella_core::interactive::{iex, iex_fast, iex_spec, iex_tabled, build_accel};

fn bench<F: Fn() -> stella_core::interactive::IExResult>(label: &str, f: F) {
    let t0 = Instant::now();
    let r = f();
    let dt = t0.elapsed().as_secs_f64();
    eprintln!(
        ">>> {label}: steps={} nf={} wall={:.4}s steps/s={:.0}",
        r.steps, r.is_normal_form, dt, r.steps as f64 / dt.max(1e-9)
    );
}

fn main() {
    // ── galaxy [triple] SUB-force + Σ(Φ) — the Φ=405 canonical bench ────
    {
        use stella_core::galaxy;
        use stella_core::term::{self, TermId};
        fn cst(n: &str) -> TermId { term::mk_app_str(n, vec![]) }
        fn ap(f: TermId, x: TermId) -> TermId { term::mk_app_str("a", vec![f, x]) }
        let path = "/Users/ember/dev/embershot/src/galaxy.txt";
        match std::fs::read_to_string(path) {
            Err(e) => eprintln!("[skip galaxy] {path}: {e}"),
            Ok(src) => {
                let g = galaxy::parse(&src).expect("parse galaxy");
                let phi = galaxy::constellation(&g);
                eprintln!("[galaxy] Phi = {} stars", phi.len());
                let entry = galaxy::ref_atom(g.entry);
                let click = ap(
                    ap(cst("cons"), stella_core::binarith::nat(0)),
                    stella_core::binarith::nat(0),
                );
                let prog = ap(ap(entry, cst("nil")), click);
                let psi = galaxy::initial_psi(prog);
                // Cost of one IexAccel::build(Φ=405) in isolation (the
                // per-iex_fast-call overhead the eval_forced loop pays).
                let t0 = Instant::now();
                let n = 200;
                for _ in 0..n { std::hint::black_box(build_accel(&phi)); }
                eprintln!(
                    ">>> galaxy/build_accel: {:.6}s/build (Phi={} stars, n={})",
                    t0.elapsed().as_secs_f64() / n as f64, phi.len(), n
                );
                eprintln!("--- galaxy [triple] entry (iex_fast) ---");
                bench("galaxy/triple/iex_fast", || iex_fast(&phi, psi.clone(), 2_000_000));
                eprintln!("--- galaxy [triple] entry (iex_spec / Sigma-Phi) ---");
                bench("galaxy/triple/iex_spec", || iex_spec(&phi, psi.clone(), 2_000_000));
                eprintln!("--- galaxy [triple] entry (iex_tabled) ---");
                bench("galaxy/triple/iex_tabled", || iex_tabled(&phi, psi.clone(), 2_000_000));
            }
        }
    }

    // ── combinator ──────────────────────────────────────────────────────
    {
        let phi = machine_stars();
        let skk = app_n([a_("S"), a_("T"), a_("T"), a_("x")]);
        fn skk_app(arg: Comb) -> Comb { app_n([a_("S"), a_("T"), a_("T"), arg]) }
        let mut big = a_("x");
        for _ in 0..10 { big = skk_app(big); }
        eprintln!("--- combinator SKKx (reference iex) ---");
        bench("comb/SKKx/iex", || iex(&phi, vec![initial_process(&skk)], 200_000));
        eprintln!("--- combinator SKKx (iex_fast) ---");
        bench("comb/SKKx/iex_fast", || iex_fast(&phi, vec![initial_process(&skk)], 200_000));
        let p = initial_process(&big);
        eprintln!("--- combinator SKK^10 x (iex_fast) ---");
        bench("comb/SKK10/iex_fast", || iex_fast(&phi, vec![p.clone()], 2_000_000));
        eprintln!("--- combinator SKK^10 x (iex_spec) ---");
        bench("comb/SKK10/iex_spec", || iex_spec(&phi, vec![p.clone()], 2_000_000));
    }

    // ── binarith (small — proven-fast range) ────────────────────────────
    {
        use stella_core::binarith::{binarith_module, nat};
        use stella_core::term::{mk_app_str as mk, mk_var};
        let phi = binarith_module();
        let mkq = |op: &str, a: u128, b: u128| -> Vec<stella_core::term::TermId> {
            vec![mk(&format!("-{op}"), vec![nat(a), nat(b), mk_var("R")]), mk_var("R")]
        };
        let qa = mkq("add", 999999, 888888);
        eprintln!("--- binarith add 999999 888888 (reference iex) ---");
        bench("binarith/add/iex", || iex(&phi, vec![qa.clone()], 500_000));
        eprintln!("--- binarith add 999999 888888 (iex_fast) ---");
        bench("binarith/add/iex_fast", || iex_fast(&phi, vec![qa.clone()], 500_000));
        eprintln!("--- binarith add 999999 888888 (iex_spec) ---");
        bench("binarith/add/iex_spec", || iex_spec(&phi, vec![qa.clone()], 500_000));
        let qm = mkq("mul", 11, 13);
        eprintln!("--- binarith mul 11 13 (iex_fast) ---");
        bench("binarith/mul/iex_fast", || iex_fast(&phi, vec![qm.clone()], 500_000));
    }
}
