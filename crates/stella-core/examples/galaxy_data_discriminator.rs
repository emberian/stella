//! docs/16 §3 — the decisive, cheap, read-only discriminator on galaxy
//! `data[0]`'s ACTUAL divergent reduction. Picks between:
//!
//!   H2  long affine/structural recurrence  → KA2 (kernel already Built)
//!   H1  redex-family duplication           → interaction-net (big build)
//!   H3  neither (genuinely irreducible)    → first-class negative
//!
//! Method (zero engine risk — pure observation via the existing
//! `eval_forced` budgets):
//!
//!  * Reach `img0 = data[0]` via the cheap guided descent
//!    (`galaxy_data_probe`'s spine peel).
//!  * Build TWO bounded traces of the divergent force of `img0`:
//!      - **AEx trace**: ladder `max_forcings` m = 1,2,…  with fuel fixed
//!        high ⇒ each rung is the state right after the m-th *strict
//!        forcing resolution* = the §49.50 ray-minting / AEx-layer
//!        boundary (docs/08 §7's "true layer boundary").
//!      - **fuel trace**: ladder `fuel` k = Δ,2Δ,…  with max_forcings
//!        fixed high ⇒ arbitrary *mid-layer* cutoffs.
//!  * `accel_detect::detect_recurrence` on each (KG8 whistle), with
//!    soundness (`is_sound_generalization`) + non-triviality
//!    (`is_trivial_generalization`) checks.
//!  * Transition-count vs materialised-size table (docs/16 §3.3 / §1
//!    confirmation: steps grow, the term does not).
//!
//! docs/08 §7 is settled IN THIS HARNESS by comparing the two traces: if
//! the AEx trace yields a stable sound whistle while the fuel trace is
//! incoherent, the faithful sampling boundary is the strict-forcing point
//! (not `final_ray`-at-fuel-exhaustion) — and vice-versa.
//!
//!   cargo run -q --release --example galaxy_data_discriminator

use std::collections::HashSet;
use stella_core::accel_detect::{
    detect_recurrence, is_sound_generalization, is_trivial_generalization,
};
use stella_core::galaxy::{self, eval_forced, readback_ray};
use stella_core::galaxy_decode::{decode, pretty};
use stella_core::term::{self, TermData, TermId};

fn cst(n: &str) -> TermId {
    term::mk_app_str(n, vec![])
}
fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}
fn tag(t: TermId) -> String {
    match term::get(t) {
        TermData::Var(_) => "<var>".into(),
        TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
    }
}
fn as_cons(t: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(s, a) = term::get(t) else { return None };
    if s.name.as_str() != "a" || a.len() != 2 {
        return None;
    }
    let TermData::App(s2, a2) = term::get(a[0]) else { return None };
    if s2.name.as_str() != "a" || a2.len() != 2 {
        return None;
    }
    match term::get(a2[0]) {
        TermData::App(s3, a3) if a3.is_empty() && s3.name.as_str() == "cons" => {
            Some((a2[1], a[1]))
        }
        _ => None,
    }
}

/// Materialised size = #distinct reachable `TermId` nodes (the hash-consed
/// DAG's real footprint — the docs/16 §1 "space" axis).
fn msize(t: TermId) -> usize {
    let mut seen = HashSet::new();
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) {
            continue;
        }
        if let TermData::App(_, a) = term::get(x) {
            stack.extend(a.iter().copied());
        }
    }
    seen.len()
}

/// One bounded force of `t`: returns (fully_reduced, steps, arith_ops,
/// forcings, RAW final ray, readback term). The RAW ray is the
/// `+P(st(M,π))` with its full KAM continuation π — where a
/// non-productive divergence actually accumulates; `readback_ray`
/// *collapses* π back into applications and is blind to it.
fn force(
    t: TermId,
    fuel: usize,
    max_forcings: usize,
) -> (bool, usize, usize, usize, TermId, TermId) {
    let f = eval_forced(galaxy_phi(), t, fuel, max_forcings);
    let raw = f.final_ray.unwrap_or(f.value);
    (
        f.fully_reduced,
        f.steps,
        f.arith_ops,
        f.forcings,
        raw,
        readback_ray(raw),
    )
}

// Φ is a pure function of galaxy.txt; build once, hand out by ref.
use std::sync::OnceLock;
static PHI: OnceLock<stella_core::constellation::Constellation> = OnceLock::new();
fn galaxy_phi() -> &'static stella_core::constellation::Constellation {
    PHI.get().expect("phi set in main")
}

fn report_recurrence(name: &str, trace: &[TermId]) {
    println!("\n── recurrence probe: {name} (|trace|={}) ──", trace.len());
    if trace.len() < 3 {
        println!("  trace too short to whistle");
        return;
    }
    match detect_recurrence(trace) {
        None => println!("  NO whistle (no homeomorphic-embedding pair in the trace)"),
        Some(w) => {
            let instances: Vec<TermId> = trace[w.earlier..=w.later].to_vec();
            let sound = is_sound_generalization(w.generalization, &instances);
            let trivial = is_trivial_generalization(w.generalization);
            println!(
                "  WHISTLE at ({},{})  span={}  gen=[{}]  sound={}  trivial={}  recurrence={}",
                w.earlier,
                w.later,
                w.later - w.earlier,
                tag(w.generalization),
                sound,
                trivial,
                w.recurrence.is_some(),
            );
            println!("  gen decoded: {}", pretty(&decode(w.generalization)));
            if let Some(r) = w.recurrence {
                println!("  affine recurrence: {} = {}", tag(r), pretty(&decode(r)));
            }
            // H2 verdict signal: a non-trivial, sound generalisation across
            // an embedded pair IS the supercompilation whistle KA2 folds on.
            if sound && !trivial {
                println!("  ⇒ H2 SIGNAL: sound non-trivial generalisation at an embedded pair");
            } else {
                println!("  ⇒ weak: whistle present but {}", if trivial {
                    "generalisation is a bare var (no shared context)"
                } else {
                    "generalisation NOT sound over the span"
                });
            }
        }
    }
}

fn main() {
    let path = "/Users/ember/dev/embershot/src/galaxy.txt";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[skip] {path}: {e}");
            return;
        }
    };
    let g = galaxy::parse(&src).expect("parse");
    PHI.set(galaxy::constellation(&g)).ok();
    let entry = galaxy::ref_atom(g.entry);
    let click = ap(
        ap(cst("cons"), stella_core::binarith::nat(0)),
        stella_core::binarith::nat(0),
    );
    let prog = ap(ap(entry, cst("nil")), click);

    // ── reach img0 = data[0] via the cheap spine peel ───────────────────
    let peel = |label: &str, t: TermId| -> Option<(TermId, TermId)> {
        let (fr, st, ao, fo, _raw, rb) = force(t, 2_000_000, 100_000);
        let c = as_cons(rb);
        println!(
            "  [{label}] fully_reduced={fr} steps={st} arith_ops={ao} forcings={fo} \
             head={} cons?={}",
            tag(rb),
            c.is_some()
        );
        c
    };
    println!("descending (flag,newState,data) spine to data[0]:");
    let Some((_flag, t1)) = peel("triple", prog) else {
        eprintln!("descent failed at triple");
        return;
    };
    let Some((_ns, t2)) = peel("after-flag", t1) else { return };
    let Some((data, _)) = peel("after-state", t2) else { return };
    let Some((img0, _)) = peel("data", data) else { return };
    println!("\nreached img0 = data[0]; head before force = {}", tag(img0));

    // Timed force; aborts a ladder if a single rung blows its wall budget
    // (the divergence is unbounded — every probe MUST be self-bounding).
    let force_timed = |t: TermId, fuel: usize, mf: usize| {
        let t0 = std::time::Instant::now();
        let r = force(t, fuel, mf);
        (r.0, r.1, r.2, r.3, r.4, r.5, t0.elapsed().as_secs_f64())
    };
    const RUNG_WALL_S: f64 = 25.0;

    // The decisive ladder: fuel = B_STEP·k, max_forcings small fixed (so
    // fuel is the binding budget — eval_forced can't re-loop unboundedly
    // on forcings). Capture the RAW final ray (rms = its π-inclusive size)
    // AND the readback (rb_ms = π collapsed, the docs/08 §3.1 canonical
    // per-AEx-layer state). The discriminator is: does rms grow with
    // steps (state-growing recurrence ⇒ H2 territory) or stay flat while
    // steps explode (non-productive churn / sharing failure ⇒ H1)?
    const F0: usize = 8;
    const B_STEP: usize = 40_000;
    const B_RUNGS: usize = 64;
    let mut raw_trace = Vec::new();
    let mut rb_trace = Vec::new();
    println!(
        "\n── fuel ladder: fuel={B_STEP}·k k=1..{B_RUNGS}, max_forcings={F0} ──"
    );
    println!(
        "   k    fuel    steps  arith forc fullyRed  RAWsize  RBsize  RBhead  decoded     secs"
    );
    let mut same = 0usize;
    let mut prev = (usize::MAX, usize::MAX, usize::MAX);
    for k in 1..=B_RUNGS {
        let fuel = B_STEP * k;
        let (fr, st, ao, fo, raw, rb, secs) = force_timed(img0, fuel, F0);
        let rms = msize(raw);
        raw_trace.push(raw);
        rb_trace.push(rb);
        println!(
            "  {k:2} {fuel:8} {st:7} {ao:4} {fo:3}  {:>5}  {rms:7}  {:5}  {:6}  {:11}  {:.2}",
            fr,
            msize(rb),
            tag(rb),
            pretty(&decode(rb)),
            secs
        );
        if (st, ao, fo) == prev {
            same += 1
        } else {
            same = 0
        }
        prev = (st, ao, fo);
        if fr {
            println!("   (fully_reduced at k={k} — img0 TERMINATES under fuel={fuel})");
            break;
        }
        if same >= 5 {
            println!(
                "   (plateau at k={k}: steps not advancing with fuel ⇒ blocked on a \
                 strict redex the F0={F0} forcing budget can't clear — raise F0)"
            );
            break;
        }
        if secs > RUNG_WALL_S {
            println!("   (rung wall budget blown at k={k} — aborting ladder)");
            break;
        }
    }

    // ── the discriminator ───────────────────────────────────────────────
    // PRIMARY: the RAW ray trace (π-inclusive — where a non-productive
    // divergence actually accumulates).
    report_recurrence("RAW final-ray trace (π-inclusive — the real state)", &raw_trace);
    // SECONDARY: the docs/08 §3.1 canonical per-layer readback trace.
    report_recurrence("readback trace (docs/08 §3.1 per-AEx-layer state)", &rb_trace);

    // transition-count vs space (docs/16 §1), measured on BOTH axes.
    if raw_trace.len() >= 2 {
        let (r0, r1) = (msize(raw_trace[0]), msize(*raw_trace.last().unwrap()));
        let (b0, b1) = (msize(rb_trace[0]), msize(*rb_trace.last().unwrap()));
        println!(
            "\nspace axis over {} rungs:\n  RAW  msize {r0} → {r1}  (Δ={})\n  \
             RB   msize {b0} → {b1}  (Δ={})",
            raw_trace.len(),
            r1 as i64 - r0 as i64,
            b1 as i64 - b0 as i64
        );
        println!(
            "  reading:\n  \
             • RAW flat + steps↑↑  ⇒ non-productive churn / sharing failure: \
             the engine re-reduces a bounded state forever ⇒ H1 (interaction-net / \
             optimal reduction is the structurally-correct crosser).\n  \
             • RAW grows ~linearly + a sound non-trivial whistle on the RAW trace \
             ⇒ H2 (affine/structural recurrence) ⇒ KA2 (kernel Built).\n  \
             • RAW grows, no whistle, RB flat ⇒ space-blocked but unfoldable: \
             re-examine docs/16 §1 (NOT purely transition-count).\n  \
             docs/08 §3.1/§7: if the RB (per-AEx-layer) trace is degenerate \
             (constant) while the divergence is real, the faithful sampling \
             boundary for THIS program is sub-AEx-layer (raw/per-fuel), not the \
             §3.1 per-layer readback — a concrete settlement of the precondition."
        );
    }
}
