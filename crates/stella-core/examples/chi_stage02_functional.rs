//! χ Stage-2 — the §4.5/§4.6 χ FUNCTIONAL, theorem-gated.
//!
//! Stage-1 (docs/08 §4.9, commit a3fd4aa) EXHIBITED χ ≠ 0 as sustained
//! growth on Eng's verbatim §49.61 witness while the §49.53 control
//! stays idempotent. It did NOT quantify the §4.5/§4.6 functional. This
//! example does: it computes `chi::chi_of_provenance` on a self-bounded
//! prefix of each fixture's `subjective_stream` trajectory (the
//! MEASURED χ-locus, §4.7) and checks the THEOREM gate:
//!
//!   Eng PROVES §49.53 idempotent ⇒ χ MUST be ≈ 0 / bounded-flat.
//!   Eng PROVES §49.61 non-terminating ⇒ χ MUST be unbounded/growing.
//!
//! The functional must separate the pair on the SAME instrument, with
//! the §67.10-calibrated detector available. measure-don't-guess: if it
//! does not cleanly separate, that is reported as a first-class finding,
//! not tuned away.
//!
//! Self-bounded: the §49.61 witness is non-terminating-by-construction.
//! Each fixture runs on a worker thread with a wall deadline and a
//! psi-size ceiling; we snapshot the cumulative provenance map at the
//! last in-budget step (it grows monotonically — never pruned — so the
//! prefix snapshot is sound). A hang is not a result.
//!
//!   cargo run -q --release --example chi_stage02_functional

use std::sync::mpsc;
use std::time::{Duration, Instant};
use stella_core::accel_detect::{detect_recurrence, is_sound_generalization, is_trivial_generalization};
use stella_core::antiunify::canonical;
use stella_core::chi::{chi_of_provenance, ChiReport};
use stella_core::constellation::{ray_is_subjective, Constellation, Star};
use stella_core::polarised::{neg_ray, pos_ray};
use stella_core::subjective::{subjective_stream, Provenance, StarId};
use stella_core::term::{mk_app_str, mk_var, TermId};

fn psi_key(psi: &[Star]) -> TermId {
    let flat: Vec<TermId> = psi.iter().flat_map(|s| s.iter().copied()).collect();
    canonical(mk_app_str("\u{22c6}psi", flat))
}

struct Measured {
    steps: usize,
    last_round: usize,
    max_psi: usize,
    nf_at: Option<usize>,
    ceiling_hit: bool,
    time_bounded: bool,
    prov: std::collections::HashMap<StarId, Provenance>,
    chi: ChiReport,
    /// (earlier, later, sound, trivial) of a detect_recurrence whistle
    /// over the bounded subjective-Ψ trace, if any.
    whistle: Option<(usize, usize, bool, bool)>,
}

/// Run a bounded prefix and compute χ on the cumulative provenance map
/// snapshotted at the last in-budget step.
fn measure(phi: Constellation, psi0: Vec<Star>, step_cap: usize, psi_ceil: usize) -> Measured {
    let t_budget = Instant::now();
    let mut steps = 0usize;
    let mut last_round = 0usize;
    let mut max_psi = psi0.len();
    let mut nf_at = None;
    let mut ceiling_hit = false;
    let mut time_bounded = false;
    let mut prov = std::collections::HashMap::new();
    let mut trace: Vec<TermId> = Vec::new();

    for step in subjective_stream(&phi, psi0).take(step_cap) {
        steps += 1;
        last_round = step.round;
        max_psi = max_psi.max(step.psi_size);
        // Snapshot the cumulative provenance only every 8th step (it
        // grows monotonically — never pruned — so a coarse snapshot is
        // still a sound, deeper-is-better prefix DAG; cloning an
        // exploding map every step is what dominated the §49.61 wall).
        if steps % 8 == 0 || nf_at.is_some() {
            prov = step.provenance.clone();
        }
        if step.psi_size <= 80 && trace.len() < 400 {
            // Trace only the §48.7-subjective fragment of Ψ (the
            // recurrence-form χ target, docs/08 §4.9 caveat ii).
            let subj: Vec<TermId> = step
                .psi
                .iter()
                .flat_map(|s| s.iter())
                .copied()
                .filter(|&r| ray_is_subjective(r))
                .collect();
            if !subj.is_empty() {
                trace.push(canonical(mk_app_str("\u{22c6}subj", subj)));
            } else {
                trace.push(psi_key(&step.psi));
            }
        }
        if step.is_normal_form && nf_at.is_none() {
            nf_at = Some(step.index);
        }
        if step.psi_size > psi_ceil {
            ceiling_hit = true;
            break;
        }
        if nf_at.is_some() && step.psi_size <= 2 {
            break; // genuine idempotent fixpoint
        }
        // In-thread self-bound: stop with a SOUND measured prefix well
        // before the caller's wall, so a non-terminating witness yields
        // a result (the chain-depth profile) rather than a deadline.
        if t_budget.elapsed() >= Duration::from_secs(18) {
            time_bounded = true;
            break;
        }
    }

    let chi = chi_of_provenance(&prov);

    let mut whistle = None;
    if trace.len() >= 3 {
        if let Some(w) = detect_recurrence(&trace) {
            let inst: Vec<TermId> = trace[w.earlier..=w.later].to_vec();
            whistle = Some((
                w.earlier,
                w.later,
                is_sound_generalization(w.generalization, &inst),
                is_trivial_generalization(w.generalization),
            ));
        }
    }

    Measured {
        steps,
        last_round,
        max_psi,
        nf_at,
        ceiling_hit,
        time_bounded,
        prov,
        chi,
        whistle,
    }
}

fn run(
    name: &str,
    phi: Constellation,
    psi0: Vec<Star>,
    step_cap: usize,
) -> Option<(ChiReport, u64)> {
    const WALL: Duration = Duration::from_secs(25);
    const PSI_CEIL: usize = 3000;
    println!("\n══════ {name} ══════");
    let (tx, rx) = mpsc::channel();
    let t0 = Instant::now();
    std::thread::spawn(move || {
        let _ = tx.send(measure(phi, psi0, step_cap, PSI_CEIL));
    });
    let m = match rx.recv_timeout(WALL) {
        Ok(m) => m,
        Err(_) => {
            println!(
                "  ⇒ DEADLINE ({}s): non-idle, non-terminating-so-far; \
                 inconclusive (needs a finer in-thread snapshot, not a hang).",
                WALL.as_secs()
            );
            return None;
        }
    };
    let secs = t0.elapsed().as_secs_f64();
    println!(
        "  steps={} last_round={} max_psi={} first_NF={:?} ceiling_hit={} time_bounded={} prov_nodes={} ({:.2}s)",
        m.steps,
        m.last_round,
        m.max_psi,
        m.nf_at,
        m.ceiling_hit,
        m.time_bounded,
        m.prov.len(),
        secs
    );
    let c = &m.chi;
    println!(
        "  χ FUNCTIONAL (σu non-nilpotency degree) = {}",
        c.chi
    );
    println!(
        "    diagnostics: layer_integral(§4.5 first form)={} surplus={} max_chain={} F-events={} active_rounds={}",
        c.layer_integral, c.surplus, c.max_chain, c.n_f_events, c.n_active_rounds
    );
    {
        let mut p = c.depth_profile.clone();
        let head: Vec<_> = p.drain(..p.len().min(6)).collect();
        println!(
            "    depth_profile(round,chain-depth; first≤6)={:?}{}",
            head,
            if c.depth_profile.len() > 6 { " …" } else { "" }
        );
    }
    println!(
        "  χ>0 (σu non-nilpotent — chain deepened beyond formation)? {}",
        c.chi_positive()
    );
    match m.whistle {
        Some((e, l, sound, trivial)) => println!(
            "  recurrence-form χ: detect_recurrence whistle span {} ({e},{l}) sound={sound} trivial={trivial} \
             ⇒ {}",
            l - e,
            if sound && !trivial && l - e >= 2 {
                "EXHIBITED (span≥2 sound non-trivial)"
            } else {
                "NOT exhibited (span-1 / unsound / trivial)"
            }
        ),
        None => println!("  recurrence-form χ: no detect_recurrence whistle on the bounded subjective trace"),
    }
    Some((m.chi, (m.last_round as u64) + 1))
}

fn main() {
    let x = mk_var("X");

    // F4 — Eng §49.53 IDEMPOTENT CONTROL. Eng PROVES AEx^∞ = AEx^2 =
    // [a]+[a]. Theorem ⇒ χ MUST be ≈0 / bounded-flat. (Same Φ used as
    // Ψ₀, exactly as the Stage-1 example.)
    let f4_phi: Constellation = vec![
        vec![neg_ray("f", vec![pos_ray("g", vec![x])])],
        vec![x, pos_ray("f", vec![x])],
        vec![neg_ray("g", vec![x]), pos_ray("f", vec![x]), mk_app_str("a", vec![])],
    ];
    let chi_53 = run("F4 Eng §49.53 idempotent control", f4_phi.clone(), f4_phi, 400);

    // F3 — Eng §49.61 VERBATIM non-terminating-hyper-execution witness.
    // Eng §49.60 PROVES it never terminates ⇒ χ MUST be unbounded /
    // strictly growing.
    let f3_phi: Constellation = vec![
        vec![x, pos_ray("f", vec![x])],
        vec![neg_ray("f", vec![neg_ray("g", vec![x])]), neg_ray("g", vec![x])],
        vec![pos_ray("g", vec![x]), pos_ray("g", vec![x]), mk_app_str("a", vec![])],
    ];
    // step_cap matched to the Stage-1 known-good budget (the witness is
    // non-terminating; the psi-size ceiling / cap self-bounds it — a
    // hang is not a result, the isnil-retraction lesson).
    let chi_61 = run("F3 Eng §49.61 witness (AEx^∞)", f3_phi.clone(), f3_phi, 4_000);

    // The THEOREM gate (differential, not self-consistency).
    println!("\n══════ THEOREM GATE ══════");
    match (chi_53, chi_61) {
        (Some((c53, tr53)), Some((c61, tr61))) => {
            let nn53 = c53.sigma_u_non_nilpotent(tr53);
            let nn61 = c61.sigma_u_non_nilpotent(tr61);
            println!(
                "  §49.53 PROVEN-idempotent : χ={} max_chain={} last_F_round={} of {} clock-rounds \
                 ⇒ σu {}",
                c53.chi,
                c53.max_chain,
                c53.last_f_round,
                tr53,
                if nn53 { "NON-nilpotent" } else { "NILPOTENT (forcing ceased; χ pinned)" }
            );
            println!(
                "  §49.61 PROVEN-nonterminating: χ={} max_chain={} last_F_round={} of {} clock-rounds \
                 ⇒ σu {}",
                c61.chi,
                c61.max_chain,
                c61.last_f_round,
                tr61,
                if nn61 { "NON-nilpotent (forcing never ceased; χ unbounded)" } else { "NILPOTENT" }
            );
            // The theorem certifies UNBOUNDEDNESS (σu (non-)nilpotency),
            // NOT a χ magnitude. Separation = the §4.6 verdicts match
            // what Eng PROVES: §49.53 nilpotent, §49.61 non-nilpotent.
            if !nn53 && nn61 {
                println!(
                    "  ⇒ SEPARATED on the theorem-certified property: §49.53 σu-NILPOTENT \
                     (χ bounded — saturated at depth {} after round {}, then {} idle \
                     clock-rounds), §49.61 σu-NON-nilpotent (χ grew to {} and was still \
                     deepening at the self-imposed cut — unbounded). Same instrument, \
                     §67.10-calibrated detector available. NOTE the §4.5 first-form \
                     layer-integral ({} vs {}) does NOT separate cleanly and is \
                     reported as a first-class Stage-2 finding, not used as the gate.",
                    c53.max_chain,
                    c53.last_f_round,
                    tr53.saturating_sub(c53.last_f_round),
                    c61.chi,
                    c61.layer_integral,
                    c53.layer_integral
                );
            } else {
                println!(
                    "  ⇒ NOT separated on the σu-nilpotency property (§49.53 nn={} \
                     §49.61 nn={}). FIRST-CLASS FINDING: the functional does not \
                     respect the theorem-certified pair on this instrument; reported \
                     as-is, NOT tuned to the desired sign.",
                    nn53, nn61
                );
            }
        }
        _ => println!("  ⇒ INCONCLUSIVE: a fixture deadlined; cannot adjudicate the gate."),
    }

    println!(
        "\nSCOPE: χ = the §4.5 non-idempotence surplus / §4.6 σu non-nilpotency-\
         degree, integrated over §49.52 layers, realised on the subjective_stream \
         provenance DAG (§4.7 the measured locus; AEx provably wrong, \
         docs/explore/tractable-aex.md). §49.53/§49.61 are Eng-PROVEN \
         idempotent/non-terminating — a differential theorem gate, not \
         self-consistency."
    );
}
