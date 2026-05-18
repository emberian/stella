//! The project's one THEOREM-CERTIFIED differential-oracle ground truth.
//!
//! Eng §67.10 *proves* `AEx(Φ_R^comp) ≃_S Φ_S^ax` for an MLL+MIX proof-net
//! `R ~~>* S` (S the cut-free normal form). MLL cut-elimination is moreover
//! strongly normalising and confluent (the unique normal form; the underlying
//! diagram contraction `↝` terminates and is confluent on correct diagrams,
//! §49.35–49.36). So a cut-elimination *reduction trajectory* is the only
//! place the trajectory machinery (`accel_detect::detect_recurrence`, the
//! docs/08 χ/whistle apparatus) can be validated against a theorem-certified
//! answer rather than an engine-re-run-on-itself self-consistency check (the
//! `data[0]` / `galaxy_layer_trace` probe never had this).
//!
//! This example:
//!   (a) runs a battery of MLL proof-structures with cuts;
//!   (b) HARD-ASSERTS the trajectory ENDPOINT against the §67.10 oracle for
//!       every net the engine path certifies (`cut_elim_via_aex(..).theorem_holds`
//!       AND endpoint cut-free); honestly REPORTS (does not assert) the one
//!       connective-output-cut net the present engine path does not certify;
//!   (c) feeds the trajectory `state`s to `accel_detect::detect_recurrence`
//!       and reports whether the whistle/embedding machinery behaves sanely
//!       on KNOWN-terminating, KNOWN-confluent reductions.
//!
//!   cargo run -q --release --example mll_cut_elim_oracle

use stella_core::accel_detect::{
    detect_recurrence, is_sound_generalization, is_trivial_generalization,
};
use stella_core::mll::{
    cut_elim_trace, cut_elim_via_aex, trace_states, CutRule, LinkKind, ProofStructure, VId,
};

fn ax(l: u32, r: u32) -> LinkKind {
    LinkKind::Ax { left: VId(l), right: VId(r) }
}
fn cut(l: u32, r: u32) -> LinkKind {
    LinkKind::Cut { left: VId(l), right: VId(r) }
}
fn tensor(l: u32, r: u32, o: u32) -> LinkKind {
    LinkKind::Tensor { left: VId(l), right: VId(r), output: VId(o) }
}
fn par(l: u32, r: u32, o: u32) -> LinkKind {
    LinkKind::Par { left: VId(l), right: VId(r), output: VId(o) }
}
fn ps(links: Vec<LinkKind>) -> ProofStructure {
    ProofStructure { links }
}

/// An `n`-cut "axiom chain": Ax(0,1) — Cut(1,2) — Ax(2,3) — Cut(3,4) … —
/// Ax(2n,2n+1). Cut-elim splices the chain to the single conclusion axiom
/// Ax(0, 2n+1). The pure ax/cut case — §67.1's "only true case" — which the
/// §67.10 engine path certifies for every `n`.
fn ax_chain(n: u32) -> (ProofStructure, ProofStructure) {
    let mut links = Vec::new();
    for k in 0..=n {
        links.push(ax(2 * k, 2 * k + 1));
    }
    for k in 0..n {
        links.push(cut(2 * k + 1, 2 * (k + 1)));
    }
    (ps(links), ps(vec![ax(0, 2 * n + 1)]))
}

struct Case {
    name: String,
    r: ProofStructure,
    /// The §67.10 cut-free normal form S (as written in the theorem).
    s: ProofStructure,
    /// `true` ⇒ the present `cut_elim_via_aex` engine path certifies this
    /// shape, so the §67.10 endpoint check is a HARD assertion. `false` ⇒
    /// the engine path does not certify this shape (a documented limitation
    /// for connective-output cuts); the trajectory is still produced and the
    /// result is REPORTED honestly, never asserted.
    engine_certifies: bool,
}

fn battery() -> Vec<Case> {
    let mut v = Vec::new();

    // Pure ax/cut, single — the "only true case" (§67.1). Engine-certified.
    v.push(Case {
        name: "ax-cut (single)".into(),
        r: ps(vec![ax(1, 2), ax(3, 4), cut(2, 3)]),
        s: ps(vec![ax(1, 4)]),
        engine_certifies: true,
    });

    // ax/cut chains n = 1..4 — engine-certified for every n.
    for n in 1..=4u32 {
        let (r, s) = ax_chain(n);
        v.push(Case {
            name: format!("ax-chain n={n} ({n} cuts ⇒ Ax(0,{}))", 2 * n + 1),
            r,
            s,
            engine_certifies: true,
        });
    }

    // ⊗/⅋ cut (Fig. 66.2 shape). The cut is between a Tensor output and a Par
    // output (not two axiom endpoints). The cut-reduction TRAJECTORY splits
    // Cut(7,8) into Cut(4,3)+Cut(6,5), which then ax/cut-splice down to the
    // surviving conclusion axiom Ax(1,2). NOW §67.10-CERTIFIED: the earlier
    // inconclusive was located precisely — the §67.9 par/tensor case
    // *duplicates* the cut, so AEx leaves zero-ray residue stars beside the
    // correct content star, and the old strict length check in
    // `constellations_equiv` rejected on star count. §67.7's `≃_S` is a
    // bijection over diagram-bearing stars (a 0-ray star is no diagram), so
    // the residue-faithful reading certifies it. Hard differential gate.
    v.push(Case {
        name: "⊗/⅋ cut (Fig 66.2 shape — connective-output cut)".into(),
        r: ps(vec![
            ax(1, 2),
            ax(3, 4),
            ax(5, 6),
            par(3, 5, 7),
            tensor(4, 6, 8),
            cut(7, 8),
        ]),
        s: ps(vec![ax(1, 2)]),
        engine_certifies: true,
    });

    // Two independent ⊗/⅋ connective-output cuts (mix-style net). Non-monotone
    // cut profile 2→3→4→3→2→1→0 — a theorem-certified GROW-THEN-SHRINK
    // trajectory (the two-sided calibration shape the docs/08 §4.10 caveat
    // wanted; every prior certified trajectory strictly shrank).
    v.push(Case {
        name: "two parallel ⊗/⅋ blocks (non-monotone, mix-style)".into(),
        r: ps(vec![
            ax(1, 2),
            ax(3, 4),
            ax(5, 6),
            par(3, 5, 7),
            tensor(4, 6, 8),
            cut(7, 8),
            ax(11, 12),
            ax(13, 14),
            ax(15, 16),
            par(13, 15, 17),
            tensor(14, 16, 18),
            cut(17, 18),
        ]),
        s: ps(vec![ax(1, 2), ax(11, 12)]),
        engine_certifies: true,
    });

    // ⊗/⅋ connective-output cut composed with an ax/cut chain (§67.9 par/
    // tensor feeding §67.1 ax/cut). Cut profile 2→3→2→1→0.
    v.push(Case {
        name: "⊗/⅋ then ax/cut chain (composed shape)".into(),
        r: ps(vec![
            ax(1, 2),
            ax(3, 4),
            ax(5, 6),
            par(3, 5, 7),
            tensor(4, 6, 8),
            cut(7, 8),
            cut(2, 9),
            ax(9, 10),
        ]),
        s: ps(vec![ax(1, 10)]),
        engine_certifies: true,
    });

    // Deep pure ax/cut chain at the MEASURED certified boundary (n = 7). The
    // ax/cut chain engine-certifies for n ≤ 7; at n ≥ 8 the AEx fixpoint
    // (seminaive AND the aex_full oracle agree) halts the cut/vehicle
    // alternation early — a pre-existing engine saturation-depth limit,
    // distinct from the connective-output residue, NOT asserted past n=7.
    {
        let (r, s) = ax_chain(7);
        v.push(Case {
            name: "deep ax-chain n=7 (certified boundary; n≥8 = engine limit)".into(),
            r,
            s,
            engine_certifies: true,
        });
    }

    v
}

fn rule_str(r: CutRule) -> &'static str {
    match r {
        CutRule::AxCut => "ax/cut",
        CutRule::MultiplicativeCut => "⊗/⅋",
        CutRule::Initial => "·",
    }
}

fn main() {
    println!("══════════════════════════════════════════════════════════════════");
    println!(" MLL cut-elimination — THEOREM-CERTIFIED differential oracle (§67.10)");
    println!("══════════════════════════════════════════════════════════════════\n");

    let mut certified_count = 0usize;
    let mut reported_count = 0usize;

    // ── (a)+(b): battery + §67.10 endpoint gating ────────────────────────────
    for case in &battery() {
        let trace = cut_elim_trace(&case.r, 256);
        let n = trace.len();
        let last = trace.last().expect("trace is never empty (R₀ always present)");
        let cut_free = last.cuts_remaining == 0;
        let endpoint = &last.ps;

        // §67.10 against the trajectory's own endpoint AND against the
        // theorem-as-written normal form S.
        let self_thm = cut_elim_via_aex(&case.r, endpoint).theorem_holds;
        let spec_thm = cut_elim_via_aex(&case.r, &case.s).theorem_holds;

        let rules: Vec<&str> = trace.iter().skip(1).map(|s| rule_str(s.rule)).collect();

        println!("── {}", case.name);
        println!(
            "   trajectory: {} states, {} reductions [{}]",
            n,
            n.saturating_sub(1),
            rules.join(" → ")
        );
        println!(
            "   endpoint cut-free={cut_free}  §67.10(R,Rₙ)={self_thm}  §67.10(R,S)={spec_thm}"
        );

        if case.engine_certifies {
            let certified = cut_free && self_thm && spec_thm;
            assert!(
                certified,
                "§67.10 ORACLE FAILED for `{}` (engine-certified shape): \
                 cut_free={cut_free} self_thm={self_thm} spec_thm={spec_thm}",
                case.name
            );
            certified_count += 1;
            println!("   ⇒ CERTIFIED ✓  (theorem is the oracle — hard differential gate)");
        } else {
            reported_count += 1;
            assert!(
                cut_free,
                "trajectory for `{}` did not reach a cut-free endpoint (the \
                 reduction itself is wrong, independent of engine certification)",
                case.name
            );
            println!(
                "   ⇒ REPORTED (not asserted): trajectory correct & cut-free, but the\n\
                 \x20    present engine path does not certify §67.10 for a connective-\n\
                 \x20    output cut. Honest inconclusive — not papered over."
            );
        }
        println!();
    }

    println!("──────────────────────────────────────────────────────────────────");
    println!(" (c) detect_recurrence calibration on theorem-certified trajectories");
    println!("──────────────────────────────────────────────────────────────────\n");

    // ── (c1): per-trajectory whistle behaviour ───────────────────────────────
    //
    // A single MLL cut-elim trajectory STRICTLY SHRINKS: every step removes a
    // cut, so Φ^comp loses a star. Exactly as `accel_detect`'s digest note
    // about the decreasing-counter shape spells out, a strictly-shrinking
    // finite reduction need NOT exhibit a pairwise homeomorphic embedding —
    // the wqo guarantee is asymptotic over an *infinite* sequence, not a
    // property of every finite shrinking prefix. So "no whistle on one short
    // strongly-normalising trajectory" is the CORRECT detector behaviour.
    // The load-bearing safety check: the detector must NOT raise a sound
    // non-trivial "this unfolds forever" alarm on a reduction the theorem
    // proves terminates — that would be a false positive precisely where the
    // ground truth forbids one.
    for case in &battery() {
        let trace = cut_elim_trace(&case.r, 256);
        let states = trace_states(&trace);
        // Measured: is the cut-count profile monotone-decreasing or does it
        // grow then shrink? (The ⊗/⅋ par/tensor case duplicates the cut, so
        // the connective-output trajectories are NON-MONOTONE.)
        let prof: Vec<usize> = trace.iter().map(|s| s.cuts_remaining).collect();
        let non_monotone = prof.windows(2).any(|w| w[1] > w[0]);
        let shape = if non_monotone {
            "non-monotone (grow-then-shrink) SN reduction"
        } else {
            "strictly-shrinking SN reduction"
        };
        match detect_recurrence(&states) {
            None => println!("   {:<48} no whistle  (correct: {shape})", case.name),
            Some(w) => {
                let inst = &states[w.earlier..=w.later];
                let sound = is_sound_generalization(w.generalization, inst);
                let trivial = is_trivial_generalization(w.generalization);
                println!(
                    "   {:<48} WHISTLE ({},{}) sound={sound} trivial={trivial}",
                    case.name, w.earlier, w.later
                );
                assert!(
                    !(sound && !trivial && w.later - w.earlier >= 2),
                    "FALSE-POSITIVE WHISTLE on §67.10-certified strongly-\
                     normalising trajectory `{}`: detector claims unbounded \
                     unfolding on a PROVEN-terminating reduction",
                    case.name
                );
            }
        }
    }

    // ── (c2): cross-member family — does the detector fire when a genuine
    //          repeating structure is present? ─────────────────────────────────
    //
    // Build the family of endpoint normal forms Ax(0,3), Ax(0,5), …, Ax(0,13).
    // These are theorem-certified states. Whether they whistle is a *measured*
    // fact about the chosen vertex-id encoding, not something to assume.
    let family: Vec<_> = (1..=6u32)
        .map(|n| {
            let (r, _s) = ax_chain(n);
            let tr = cut_elim_trace(&r, 256);
            *trace_states(&tr).last().unwrap()
        })
        .collect();

    print!("\n   family normal-form sequence Ax(0,3)…Ax(0,13): ");
    match detect_recurrence(&family) {
        None => println!(
            "NO whistle\n\
             \x20  ⇒ HONEST NEGATIVE: the certified family states do not pairwise\n\
             \x20    homeomorphically embed — the conclusion vertex is a *fresh\n\
             \x20    constant symbol* per member (`3`,`5`,`7`,…), and `canonical`\n\
             \x20    renumbers variables, not function symbols. So this encoding\n\
             \x20    presents no nesting for Kruskal embedding to catch. Reported,\n\
             \x20    not engineered away. The calibration conclusion is the (c1)\n\
             \x20    result: the detector is sound (no false alarm) on theorem-\n\
             \x20    certified strongly-normalising trajectories."
        ),
        Some(w) => {
            let inst = &family[w.earlier..=w.later];
            let sound = is_sound_generalization(w.generalization, inst);
            let trivial = is_trivial_generalization(w.generalization);
            println!(
                "WHISTLE ({},{}) sound={sound} trivial={trivial} recurrence={}",
                w.earlier,
                w.later,
                w.recurrence.is_some()
            );
        }
    }

    println!("\n══════════════════════════════════════════════════════════════════");
    println!(
        " RESULT: {certified_count} battery trajectories ENDPOINT-CERTIFIED by §67.10\n\
         \x20        (hard differential gate; ground truth is a THEOREM, not an\n\
         \x20        engine re-run). {reported_count} reported-only nets remaining: the\n\
         \x20        ⊗/⅋ connective-output cut is now CERTIFIED (residue-faithful\n\
         \x20        §67.7 ≃_S). The only characterised honest-negative is the AEx\n\
         \x20        saturation-depth limit on ax/cut chains of n≥8 (engine, not\n\
         \x20        the §67.9 residue; pinned by a dedicated negative test).\n\
         \x20 CALIBRATION: detect_recurrence raises NO false-positive whistle on\n\
         \x20        any §67.10-certified strongly-normalising trajectory —\n\
         \x20        including the NON-MONOTONE (grow-then-shrink) ⊗/⅋ ones,\n\
         \x20        the two-sided shape the docs/08 §4.10 caveat wanted."
    );
    println!("══════════════════════════════════════════════════════════════════");
}
