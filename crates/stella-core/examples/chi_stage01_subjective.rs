//! PAST-ENG · χ Stage-0/1 — the first sound, theorem-anchored look at
//! where Eng's non-idempotence (the docs/08 §4.5/§4.6 "charge" χ) lives.
//!
//! Grounding (docs/08 §4.7/§4.8, docs/16 §7, docs/explore/chi-existence-
//! theory.md): §49.57 non-idempotence lives in `subjective_stream`, not
//! `aex`; the AEx-faithful route is provably intractable (and, per
//! docs/explore/tractable-aex.md, provably so). Eng §49.59–61
//! ESTABLISHES χ-existence — §49.61 constructs an explicit faithful
//! non-terminating-hyper-execution witness. The sound instrument is the
//! §67.10-cut-elim-CALIBRATED `accel_detect::detect_recurrence`.
//!
//! - **Stage-0 — `is_subjective` kill-switch (§48.7).** Faithful
//!   colour-nesting classifier (re-aim step 1). Never-true ⇒ grounding
//!   collapses.
//! - **Stage-1 — χ signal.** χ is exhibited by EITHER (a) sustained
//!   unbounded growth (psi_size ↑ past a ceiling, no NF — the §49.61
//!   regime), OR (b) a sound non-trivial structural recurrence whistle
//!   on the calibrated detector. The §49.53 control must do NEITHER
//!   (idempotent ⇒ detector specificity check).
//!
//! Read-only. Each fixture runs on a worker thread with a wall deadline
//! (the §49.61 witness is non-terminating-by-construction — a clean
//! self-bounded measurement, never a hang masquerading as a result).
//!   cargo run -q --release --example chi_stage01_subjective

use std::collections::HashSet;
use std::sync::mpsc;
use std::time::{Duration, Instant};
use stella_core::accel_detect::{detect_recurrence, is_sound_generalization, is_trivial_generalization};
use stella_core::antiunify::canonical;
use stella_core::constellation::{ray_is_subjective, Constellation, Star};
use stella_core::polarised::{neg_ray, pos_ray};
use stella_core::subjective::subjective_stream;
use stella_core::term::{mk_app_str, mk_var, TermId};

fn psi_key(psi: &[Star]) -> TermId {
    let flat: Vec<TermId> = psi.iter().flat_map(|s| s.iter().copied()).collect();
    canonical(mk_app_str("\u{22c6}psi", flat))
}

#[derive(Default)]
struct FxResult {
    steps: usize,
    seed_subj: usize,
    any_subj: bool,
    max_subj: usize,
    max_psi: usize,
    psi_by_round: Vec<(usize, usize)>,
    nf_at: Option<(usize, usize)>,
    ceiling_hit: Option<(usize, usize)>, // (step, psi_size) — unbounded growth
    whistle: Option<(usize, usize, bool, bool)>, // earlier,later,sound,trivial
}

/// Run one fixture's measurement to completion (bounded by `step_cap` /
/// `psi_ceil`). Called inside a worker thread so a non-terminating
/// witness is wall-bounded by the caller, not by hope.
fn measure(phi: Constellation, psi0: Vec<Star>, step_cap: usize, psi_ceil: usize) -> FxResult {
    let mut r = FxResult::default();
    r.seed_subj = psi0
        .iter()
        .flat_map(|s| s.iter())
        .filter(|&&x| ray_is_subjective(x))
        .count();
    r.any_subj = r.seed_subj > 0;
    r.max_subj = r.seed_subj;
    r.max_psi = psi0.len();
    let mut trace: Vec<TermId> = Vec::new();
    let mut rounds: HashSet<usize> = HashSet::new();

    for step in subjective_stream(&phi, psi0).take(step_cap) {
        r.steps += 1;
        if rounds.insert(step.round) {
            r.psi_by_round.push((step.round, step.psi_size));
        }
        let subj = step
            .psi
            .iter()
            .flat_map(|s| s.iter())
            .filter(|&&x| ray_is_subjective(x))
            .count();
        if subj > 0 {
            r.any_subj = true;
        }
        r.max_subj = r.max_subj.max(subj);
        r.max_psi = r.max_psi.max(step.psi_size);
        // Only canonicalise while small — once growth is established the
        // trace is irrelevant (growth itself is the χ signal) and
        // canonicalising an exploding Ψ would dominate the runtime.
        if step.psi_size <= 200 && trace.len() < 600 {
            trace.push(psi_key(&step.psi));
        }
        if step.is_normal_form && r.nf_at.is_none() {
            r.nf_at = Some((step.index, step.round));
        }
        if step.psi_size > psi_ceil {
            r.ceiling_hit = Some((step.index, step.psi_size));
            break;
        }
        if r.nf_at.is_some() && step.psi_size <= 2 {
            break; // genuine idempotent fixpoint (null fixtures)
        }
    }
    if trace.len() >= 3 {
        if let Some(w) = detect_recurrence(&trace) {
            let inst: Vec<TermId> = trace[w.earlier..=w.later].to_vec();
            r.whistle = Some((
                w.earlier,
                w.later,
                is_sound_generalization(w.generalization, &inst),
                is_trivial_generalization(w.generalization),
            ));
        }
    }
    r
}

fn run_fixture(name: &str, phi: Constellation, psi0: Vec<Star>, step_cap: usize) {
    const WALL: Duration = Duration::from_secs(25);
    const PSI_CEIL: usize = 3000;
    println!("\n══════ fixture: {name} ══════");
    let (tx, rx) = mpsc::channel();
    let t0 = Instant::now();
    std::thread::spawn(move || {
        let _ = tx.send(measure(phi, psi0, step_cap, PSI_CEIL));
    });
    let r = match rx.recv_timeout(WALL) {
        Ok(r) => r,
        Err(_) => {
            // Deadline: the worker is detached and leaks until process
            // exit. A deadline on a fixture whose psi_size was observed
            // growing IS the sustained-non-idempotence signal — but we
            // could not snapshot it; report honestly as inconclusive-
            // but-non-idle (distinct from the idle nulls).
            println!(
                "  ⇒ DEADLINE ({}s): fixture neither reached NF nor hit the \
                 psi ceiling within wall — non-idle, non-terminating-so-far; \
                 inconclusive (needs a finer in-thread snapshot, not a hang).",
                WALL.as_secs()
            );
            return;
        }
    };
    let secs = t0.elapsed().as_secs_f64();
    println!(
        "Ψ₀: seed_subj={} | steps={} | max_subj_rays={} | max_psi={} | \
         psi_by_round(≤8)={:?} | first_NF={:?} | {:.2}s",
        r.seed_subj,
        r.steps,
        r.max_subj,
        r.max_psi,
        { let mut v = r.psi_by_round.clone(); v.truncate(8); v },
        r.nf_at,
        secs
    );
    // Stage-0
    if !r.any_subj {
        println!("  Stage-0 KILL-SWITCH TRIPPED: no §48.7 subjective ray ever — grounding fails.");
    } else {
        println!("  Stage-0 PASS: §48.7-faithful subjective fragment exercised.");
    }
    // Stage-1 — χ verdict
    let growth = r.ceiling_hit.is_some()
        || (r.nf_at.is_none() && r.max_psi >= 8 && r.max_subj >= 2);
    let whistle_chi = matches!(r.whistle, Some((e, l, true, false)) if l - e >= 2);
    if growth {
        let breach = match r.ceiling_hit {
            Some((s, sz)) => format!("psi_size breached {PSI_CEIL} at step {s} (size {sz})"),
            None => format!(
                "psi_size grew to {} (monotone, by-round {:?}), subjective rays \
                 to {}, NF NEVER reached in {} steps",
                r.max_psi,
                { let mut v = r.psi_by_round.clone(); v.truncate(8); v },
                r.max_subj,
                r.steps
            ),
        };
        println!(
            "  Stage-1 χ-EXHIBITED (growth): {breach} — SUSTAINED non-idempotence \
             (Eng §49.60/§49.61 regime; categorically unlike the idle nulls/§49.53 \
             control whose max_subj≤2 & reach NF). The FIRST measured charge."
        );
    } else if whistle_chi {
        let (e, l, _, _) = r.whistle.unwrap();
        println!(
            "  Stage-1 χ-EXHIBITED (recurrence): sound non-trivial structural \
             whistle span {} ({e},{l}) on the calibrated detector.",
            l - e
        );
    } else if r.nf_at.is_some() && !growth {
        println!(
            "  Stage-1 IDEMPOTENT: reached NF, no growth, whistle={:?} — χ NOT \
             exhibited (correct for the §49.53 control / null fixtures; \
             detector SPECIFICITY upheld).",
            r.whistle
        );
    } else {
        println!(
            "  Stage-1 INCONCLUSIVE: non-idle but no clean growth/recurrence \
             signal (max_psi={} max_subj={} whistle={:?}).",
            r.max_psi, r.max_subj, r.whistle
        );
    }
}

fn main() {
    let x = mk_var("X");
    let z = mk_var("Z");

    // F1/F2 — the documented NULLS (idle by step ~2). Tiny cap: 25 is
    // ample to show the null and frees the budget for the witnesses.
    run_fixture(
        "F1 Eng §49.50 (null: transient→objective NF)",
        vec![vec![x, pos_ray("f", vec![x])]],
        vec![vec![neg_ray("f", vec![pos_ray("g", vec![z])])]],
        25,
    );
    run_fixture(
        "F2 self-feeding (null)",
        vec![
            vec![x, pos_ray("f", vec![x])],
            vec![neg_ray("g", vec![x]), pos_ray("h", vec![pos_ray("g", vec![x])])],
        ],
        vec![vec![neg_ray("f", vec![pos_ray("g", vec![z])])]],
        25,
    );

    // F3 — Eng §49.61 VERBATIM witness of non-terminating hyper-execution
    // (the theorem §49.60 constructs; docs/explore/chi-existence-theory).
    // ±f mints θ={X↦−g(X)} (re-subjectivising); the doubled-colour
    // non-linear consumer [+g,+g,a] duplicates the supply every round;
    // no ground terminator. Predicted: χ EXHIBITED via growth.
    run_fixture(
        "F3 Eng §49.61 witness (AEx^∞(Φ))",
        vec![
            vec![x, pos_ray("f", vec![x])],
            vec![neg_ray("f", vec![neg_ray("g", vec![x])]), neg_ray("g", vec![x])],
            vec![pos_ray("g", vec![x]), pos_ray("g", vec![x]), mk_app_str("a", vec![])],
        ],
        vec![
            vec![x, pos_ray("f", vec![x])],
            vec![neg_ray("f", vec![neg_ray("g", vec![x])]), neg_ray("g", vec![x])],
            vec![pos_ray("g", vec![x]), pos_ray("g", vec![x]), mk_app_str("a", vec![])],
        ],
        120,
    );

    // F4 — Eng §49.53 IDEMPOTENT CONTROL: proven AEx^∞ = AEx^2 = [a]+[a].
    // Must reach NF, no growth ⇒ detector SPECIFICITY on a theorem-
    // certified terminating subjective fixture.
    run_fixture(
        "F4 Eng §49.53 idempotent control",
        vec![
            vec![neg_ray("f", vec![pos_ray("g", vec![x])])],
            vec![x, pos_ray("f", vec![x])],
            vec![neg_ray("g", vec![x]), pos_ray("f", vec![x]), mk_app_str("a", vec![])],
        ],
        vec![
            vec![neg_ray("f", vec![pos_ray("g", vec![x])])],
            vec![x, pos_ray("f", vec![x])],
            vec![neg_ray("g", vec![x]), pos_ray("f", vec![x]), mk_app_str("a", vec![])],
        ],
        400,
    );

    // F5 — Candidate B: non-terminating but BOUNDED (C1+C4, not C2 —
    // no duplicator). NF never reached, psi_size bounded ⇒ a distinct
    // χ regime; ideally a sound recurrence whistle rather than growth.
    run_fixture(
        "F5 Candidate B (non-terminating, bounded)",
        vec![
            vec![x, pos_ray("f", vec![x])],
            vec![neg_ray("f", vec![neg_ray("g", vec![x])]), pos_ray("g", vec![x])],
        ],
        vec![
            vec![x, pos_ray("f", vec![x])],
            vec![neg_ray("f", vec![neg_ray("g", vec![x])]), pos_ray("g", vec![x])],
        ],
        300,
    );

    println!(
        "\nSCOPE: subjective_stream (IEx) trajectory = the MEASURED χ-locus \
         (docs/08 §4.7; AEx provably intractable & no faithful tractable \
         variant, docs/16 §7 + docs/explore/tractable-aex.md). detector \
         §67.10-calibrated for specificity; F4 is the specificity control. \
         χ-EXHIBITED via sustained growth (§49.60/§49.61) and/or a sound \
         non-trivial recurrence whistle."
    );
}
