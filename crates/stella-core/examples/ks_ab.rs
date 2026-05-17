//! KS A/B harness — reference `iex` vs accelerated `iex_fast`, **release**.
//!
//!   cargo run -q --release --example ks_ab
//!
//! Prints wall-time, step count, and speedup factor across scaling workloads
//! so every KS change is *proven substantial*, not assumed. Step counts MUST
//! be identical (N-KS faithfulness); only wall-time may differ.

use std::time::Instant;
use stella_core::binarith::{binarith_module, nat as bnat};
use stella_core::combinator::{a_, app_n, initial_process, machine_stars, Comb};
use stella_core::interactive::{iex, iex_fast};
use stella_core::polarised::neg_ray;
use stella_core::term::mk_var;

fn timed(label: &str, run: impl Fn() -> (usize, bool)) -> (f64, usize) {
    let t0 = Instant::now();
    let (steps, _nf) = run();
    let dt = t0.elapsed().as_secs_f64();
    println!("    {label:<28} {dt:>9.4}s  steps={steps}");
    (dt, steps)
}

/// A combinator term that forces ~`n` reduction steps: nested `S T T`.
fn skk_chain(n: usize) -> Comb {
    // (S T T (S T T (... x ...)))  — each layer ↝ identity, deepens the spine.
    let mut t = a_("x");
    for _ in 0..n {
        t = app_n([a_("S"), a_("T"), a_("T"), t]);
    }
    t
}

fn main() {
    println!("== KS A/B: reference iex vs iex_fast (release) ==\n");

    println!("[combinator: nested S T T, depth d]");
    for d in [4usize, 8, 12, 16] {
        let prog = skk_chain(d);
        let phi = machine_stars();
        let psi = vec![initial_process(&prog)];
        println!("  d={d}");
        let (rt, rs) = timed("ref iex", || {
            let r = iex(&phi, psi.clone(), 200_000);
            (r.steps, r.is_normal_form)
        });
        let (ft, fs) = timed("fast iex_fast", || {
            let r = iex_fast(&phi, psi.clone(), 200_000);
            (r.steps, r.is_normal_form)
        });
        assert_eq!(rs, fs, "N-KS: step counts must match (d={d})");
        println!("    -> speedup x{:.2}\n", rt / ft.max(1e-9));
    }

    println!("[binarith: add(n,n) at increasing bit-width]");
    for bits in [4u32, 8, 12, 16] {
        let n = (1u128 << bits) - 1;
        let phi = binarith_module();
        let q = vec![vec![
            neg_ray("add", vec![bnat(n), bnat(n), mk_var("R")]),
            mk_var("R"),
        ]];
        println!("  {bits}-bit (n={n})");
        let (rt, rs) = timed("ref iex", || {
            let r = iex(&phi, q.clone(), 500_000);
            (r.steps, r.is_normal_form)
        });
        let (ft, fs) = timed("fast iex_fast", || {
            let r = iex_fast(&phi, q.clone(), 500_000);
            (r.steps, r.is_normal_form)
        });
        assert_eq!(rs, fs, "N-KS: step counts must match ({bits}-bit)");
        println!("    -> speedup x{:.2}\n", rt / ft.max(1e-9));
    }
}
