//! MEASURE (ii): the per-`force_value`-AEx-layer trace of `data[0]`'s
//! force (docs/08 §3.1 / Stage-1) — the trace the outer-`final_ray`
//! discriminator structurally cannot see. Installs the behaviour-
//! preserving `galaxy::layer_trace_begin` sink, forces `img0` under a
//! bounded budget, takes the canonicalised per-layer states, and runs
//! `accel_detect::detect_recurrence` on the REAL recursion trace.
//!
//! Reads: does the nested isnil/force_value recursion produce a Kruskal
//! embedding with a SOUND NON-TRIVIAL generalisation (⇒ H2: real affine/
//! structural recurrence ⇒ KA2 folds it) — or unboundedly-distinct
//! states with no recurrence (⇒ H1/H3) — or does it TERMINATE (trace
//! ends, img0 fully_reduced)?
//!
//!   cargo run -q --release --example galaxy_layer_trace

use std::collections::HashSet;
use stella_core::accel_detect::{
    detect_recurrence, is_sound_generalization, is_trivial_generalization,
};
use stella_core::galaxy::{self, eval_forced, layer_trace_begin, layer_trace_take, readback_ray};
use stella_core::galaxy_decode::{decode, pretty};
use stella_core::term::{self, TermData, TermId};

fn cst(n: &str) -> TermId {
    term::mk_app_str(n, vec![])
}
fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}
fn hd(t: TermId) -> String {
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
        TermData::App(s3, a3) if a3.is_empty() && s3.name.as_str() == "cons" => Some((a2[1], a[1])),
        _ => None,
    }
}
fn msize(t: TermId) -> usize {
    let mut seen = HashSet::new();
    let mut st = vec![t];
    while let Some(x) = st.pop() {
        if !seen.insert(x) {
            continue;
        }
        if let TermData::App(_, a) = term::get(x) {
            st.extend(a.iter().copied());
        }
    }
    seen.len()
}

fn main() {
    let src = std::fs::read_to_string("/Users/ember/dev/embershot/src/galaxy.txt").unwrap();
    let g = galaxy::parse(&src).unwrap();
    let phi = galaxy::constellation(&g);
    let entry = galaxy::ref_atom(g.entry);
    let click = ap(
        ap(cst("cons"), stella_core::binarith::nat(0)),
        stella_core::binarith::nat(0),
    );
    let mut t = ap(ap(entry, cst("nil")), click);
    for (_l, head) in [
        ("triple", false),
        ("after-flag", false),
        ("after-state", true),
        ("data", true),
    ] {
        let f = eval_forced(&phi, t, 2_000_000, 100_000);
        let rb = readback_ray(f.final_ray.unwrap_or(f.value));
        let (h, tl) = as_cons(rb).unwrap();
        t = if head { h } else { tl };
    }
    println!("img0 head={}", hd(t));

    // Ladder the forcing budget; at each, capture the FULL per-layer
    // recursion trace and analyse it.
    for &budget in &[8usize, 16, 24, 32, 48, 64, 96, 128] {
        layer_trace_begin();
        let t0 = std::time::Instant::now();
        let f = eval_forced(&phi, t, 4_000_000, budget);
        let secs = t0.elapsed().as_secs_f64();
        let trace = layer_trace_take();
        let distinct: HashSet<TermId> = trace.iter().copied().collect();
        println!(
            "\n══ budget={budget}  steps={} forc={} arith={} fullyRed={} secs={:.2}",
            f.steps, f.forcings, f.arith_ops, f.fully_reduced, secs
        );
        println!(
            "   layer-trace: len={} distinct={} (canonicalised force_value layers)",
            trace.len(),
            distinct.len()
        );
        if f.fully_reduced {
            println!(
                "   *** img0 TERMINATES at budget={budget}: {} ***",
                pretty(&decode(readback_ray(f.final_ray.unwrap_or(f.value))))
            );
        }
        if trace.len() >= 3 {
            // size envelope across layers
            let (mut mn, mut mx) = (usize::MAX, 0usize);
            for &s in &trace {
                let z = msize(s);
                mn = mn.min(z);
                mx = mx.max(z);
            }
            println!("   layer msize: min={mn} max={mx} (growing ⇒ structural recurrence candidate)");
            match detect_recurrence(&trace) {
                None => println!("   detect_recurrence: NO whistle"),
                Some(w) => {
                    let inst: Vec<TermId> = trace[w.earlier..=w.later].to_vec();
                    let sound = is_sound_generalization(w.generalization, &inst);
                    let trivial = is_trivial_generalization(w.generalization);
                    println!(
                        "   WHISTLE ({},{}) span={} gen={} sound={} trivial={} recurrence={}",
                        w.earlier,
                        w.later,
                        w.later - w.earlier,
                        hd(w.generalization),
                        sound,
                        trivial,
                        w.recurrence.is_some()
                    );
                    println!("   gen: {}", pretty(&decode(w.generalization)));
                    if sound && !trivial && w.later - w.earlier >= 2 {
                        println!(
                            "   ⇒ H2 CANDIDATE: sound non-trivial generalisation over a \
                             ≥2-span embedded pair in the REAL recursion trace"
                        );
                    } else {
                        println!(
                            "   ⇒ NOT H2: {}",
                            if trivial {
                                "trivial gen (constant/var — no folded structure)"
                            } else if !sound {
                                "unsound over the span"
                            } else {
                                "span<2 (degenerate)"
                            }
                        );
                    }
                }
            }
        } else {
            println!("   layer-trace too short to whistle (recursion shallow at this budget)");
        }
        if secs > 60.0 {
            println!("   (wall>60s — stop laddering)");
            break;
        }
    }
    println!(
        "\nINTERPRETATION:\n  \
         • trace TERMINATES (fullyRed) ⇒ data[0] is terminating-but-deep; \
         not a termination-crosser problem — a budget/perf one (Σ(Φ)+memo+depth).\n  \
         • len↑ with budget, distinct≪len, sound non-trivial whistle ⇒ H2 \
         (affine/structural recurrence) ⇒ KA2 (kernel Built) folds it.\n  \
         • len↑, distinct≈len, no whistle ⇒ H1/H3 (no foldable structure) ⇒ \
         interaction-net or first-class negative.\n  \
         docs/08 §3.1: this IS the faithful per-AEx-layer trace (force_value \
         recursion = the AEx^n nesting) — the discriminator's outer-ray trace \
         could not see it."
    );
}
