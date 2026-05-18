//! PAST-ENG · χ Stage-0/1 — the first sound, theorem-anchored look at
//! where Eng's non-idempotence (the docs/08 §4.5/§4.6 "charge" χ) lives.
//!
//! Grounding (docs/08 §4.7, docs/16 §7, thesis-audit 03): §49.57's
//! non-idempotence is MEASURED to live in `subjective::subjective_stream`,
//! NOT the prototype `aex` (which is idempotent even on Eng's §49.50
//! example); and the AEx-faithful route is provably intractable, so the
//! sound instrument is the §67.10-cut-elim-CALIBRATED
//! `accel_detect::detect_recurrence` (specificity established: zero
//! false-positive whistle on a theorem-certified strongly-normalising
//! trajectory) applied to the `subjective_stream` trajectory.
//!
//! - **Stage-0 — `is_subjective` kill-switch (§48.7).** Classify every
//!   ray of every Ψ_k with the FAITHFUL colour-nesting
//!   `constellation::ray_is_subjective` (re-aim step 1). If a subjective
//!   ray NEVER appears across the whole subjective trajectory, the
//!   forcing≡subjective-ray grounding collapses (the cheapest decisive
//!   kill, audit 03). Reported, not assumed.
//! - **Stage-1 — calibrated whistle on the χ-locus.** Canonicalise each
//!   Ψ_k, run the calibrated `detect_recurrence` on the per-step
//!   trajectory. A SOUND NON-TRIVIAL whistle = first theorem-anchored
//!   evidence of χ-relevant non-idempotence in the subjective dynamics;
//!   no/ trivial whistle = a sound "no recurrence on this trajectory"
//!   (specificity, not sensitivity — stated honestly).
//!
//! Read-only: reference engine untouched, instruments observe only.
//!   cargo run -q --release --example chi_stage01_subjective

use std::collections::HashSet;
use stella_core::accel_detect::{detect_recurrence, is_sound_generalization, is_trivial_generalization};
use stella_core::antiunify::canonical;
use stella_core::constellation::{ray_is_subjective, Constellation, Star};
use stella_core::polarised::{neg_ray, pos_ray};
use stella_core::subjective::subjective_stream;
use stella_core::term::{mk_app_str, mk_var, TermId};

/// One canonical key for a whole interaction space Ψ_k (α-normal — so a
/// genuine structural re-appearance is `TermId`-equal, the form
/// `detect_recurrence` consumes).
fn psi_key(psi: &[Star]) -> TermId {
    let flat: Vec<TermId> = psi.iter().flat_map(|s| s.iter().copied()).collect();
    canonical(mk_app_str("\u{22c6}psi", flat))
}

fn run_fixture(name: &str, phi: &Constellation, psi0: Vec<Star>, cap: usize) {
    println!("\n══════ fixture: {name} ══════");
    // Stage-0 seed check: the query itself.
    let seed_subj = psi0
        .iter()
        .flat_map(|s| s.iter())
        .filter(|&&r| ray_is_subjective(r))
        .count();
    println!("Ψ₀: {} stars, {seed_subj} subjective ray(s) at seed", psi0.len());

    let mut trace: Vec<TermId> = Vec::new();
    let mut steps = 0usize;
    let mut rounds_seen: HashSet<usize> = HashSet::new();
    let mut any_subjective = seed_subj > 0;
    let mut max_subj_in_a_step = seed_subj;
    let mut nf_at: Option<(usize, usize)> = None; // (index, round)

    for step in subjective_stream(phi, psi0).take(cap) {
        steps += 1;
        rounds_seen.insert(step.round);
        let subj = step
            .psi
            .iter()
            .flat_map(|s| s.iter())
            .filter(|&&r| ray_is_subjective(r))
            .count();
        if subj > 0 {
            any_subjective = true;
        }
        max_subj_in_a_step = max_subj_in_a_step.max(subj);
        trace.push(psi_key(&step.psi));
        if step.is_normal_form && nf_at.is_none() {
            nf_at = Some((step.index, step.round));
        }
    }

    // ── Stage-0 verdict ───────────────────────────────────────────────
    println!(
        "Stage-0: {steps} steps over rounds {:?}; max subjective rays in any Ψ_k = {max_subj_in_a_step}; first NF @ {:?}",
        {
            let mut r: Vec<_> = rounds_seen.iter().copied().collect();
            r.sort_unstable();
            r
        },
        nf_at
    );
    if !any_subjective {
        println!(
            "  ⇒ KILL-SWITCH TRIPPED: no Eng-subjective ray ever appears on this \
             trajectory — the forcing≡subjective-ray grounding does NOT hold here."
        );
    } else {
        println!(
            "  ⇒ Stage-0 PASS: the §48.7-faithful subjective fragment is \
             genuinely exercised (non-vacuous)."
        );
    }

    // ── Stage-1: calibrated recurrence on the χ-locus ─────────────────
    let distinct: HashSet<TermId> = trace.iter().copied().collect();
    println!(
        "Stage-1: trajectory len={} distinct={}",
        trace.len(),
        distinct.len()
    );
    if trace.len() < 3 {
        println!(
            "  trajectory too short for a recurrence verdict (fixture reaches NF \
             fast — a longer subjective fixture is the next infra, not a result)"
        );
        return;
    }
    match detect_recurrence(&trace) {
        None => println!(
            "  detect_recurrence: NO whistle ⇒ no structural re-appearance on \
             this subjective trajectory (SOUND per the §67.10 calibration: the \
             detector does not miss-by-false-negative on SN — here it simply \
             finds none; χ-non-idempotence not exhibited on this run)."
        ),
        Some(w) => {
            let inst: Vec<TermId> = trace[w.earlier..=w.later].to_vec();
            let sound = is_sound_generalization(w.generalization, &inst);
            let trivial = is_trivial_generalization(w.generalization);
            println!(
                "  WHISTLE ({},{}) span={} sound={sound} trivial={trivial} recurrence={}",
                w.earlier,
                w.later,
                w.later - w.earlier,
                w.recurrence.is_some()
            );
            if sound && !trivial && w.later - w.earlier >= 2 {
                println!(
                    "  ⇒ χ-SIGNAL: a sound non-trivial structural recurrence on the \
                     subjective_stream trajectory — the FIRST theorem-anchored \
                     (calibrated) evidence of §49.57 non-idempotence at the measured \
                     χ-locus. This is the object docs/08 §4.5/§4.6 χ integrates."
                );
            } else {
                println!(
                    "  ⇒ not a χ-signal: {}",
                    if trivial {
                        "trivial generalisation (no folded structure)"
                    } else if !sound {
                        "unsound over the span"
                    } else {
                        "span<2 (degenerate)"
                    }
                );
            }
        }
    }
}

fn main() {
    let x = mk_var("X");
    let z = mk_var("Z");

    // F1 — Eng's OWN §49.50 worked example (subjective.rs gate-a):
    //   Φ = { [X, +f(X)] }     (objective supply star)
    //   Ψ₀ = { [−f(+g(Z))] }   (the canonical SUBJECTIVE query: coloured
    //                            head f, colour g nested in its argument)
    // Reaches [+g(_)] — Eng's new-ray creation.
    let f1_phi: Constellation = vec![vec![x, pos_ray("f", vec![x])]];
    let f1_psi0: Vec<Star> = vec![vec![neg_ray("f", vec![pos_ray("g", vec![z])])]];
    run_fixture("Eng §49.50 new-ray example", &f1_phi, f1_psi0, 400);

    // F2 — a self-feeding subjective constellation: the supply re-creates
    // a subjective redex each §49.52 round (a longer trajectory, to give
    // the calibrated detector something to chew on). Φ pairs an objective
    // carrier with a subjective re-injector `+h(+g(X))`.
    let f2_phi: Constellation = vec![
        vec![x, pos_ray("f", vec![x])],
        vec![neg_ray("g", vec![x]), pos_ray("h", vec![pos_ray("g", vec![x])])],
    ];
    let f2_psi0: Vec<Star> = vec![vec![neg_ray("f", vec![pos_ray("g", vec![z])])]];
    run_fixture("self-feeding subjective (§49.52 rounds)", &f2_phi, f2_psi0, 400);

    println!(
        "\nSCOPE (honest): this is the subjective_stream (IEx) trajectory — the \
         MEASURED χ-locus (docs/08 §4.7), not the §49.52 AEx-layer (AEx provably \
         intractable, docs/16 §7). The detector is §67.10-calibrated for \
         SPECIFICITY (no false alarm on SN), not sensitivity. A sound whistle is \
         positive χ evidence; its absence is 'no recurrence on THIS trajectory', \
         not a termination proof."
    );
}
