//! `evaluate()` + a live differential oracle for the stellar-resolution engine.
//!
//! # Why this module exists
//!
//! An evolutionary / valence search drives execution millions of times. It
//! reads a *substrate readout* (reached normal form? how many steps? how many
//! result stars?) and turns that into a fitness signal. The hot path therefore
//! runs an optimizing tier — [`iex_fast`] (byte-identical jet) or
//! [`iex_tabled`] (KA1 variant-deletion, result-equivalent). If an optimizing
//! tier ever returns a wrong-but-fast result, the search will *Goodhart* it:
//! amplify the wrong result into apparent viability and steer the whole
//! experiment off a phantom. The N-KS / KA1 *unit* gates check this once at
//! build time on three fixed corpora; they cannot witness the inputs the
//! search actually generates.
//!
//! So this module folds the reference oracle ([`iex`] — "the interpreter is
//! the spec") into the live path: when the oracle fires (per [`OracleMode`])
//! it re-runs reference `iex` on the *same* input and compares with the exact
//! differential-gate criterion the engine's own gates use
//! (`iex_eq_iex_fast` / `iex_tabled_result_eq_iex`). A divergence is reported
//! in-band so the search can discard the run instead of trusting it. Sampling
//! makes this affordable at search scale while still catching a fast-path
//! regression statistically. This is experiment-validity infrastructure, not
//! an optional check.
//!
//! # Boundary: substrate readout only, never fitness
//!
//! [`viability_readout`] exposes exactly the raw signals the valence side
//! consumes (`crate::valence::ViabilityScore` is computed from
//! `Step::is_normal_form` / `Step::psi_size` / step index; `crate::reafference`
//! reads `Step::is_normal_form`). This module deliberately exposes the same
//! shape — `{ reached_nf, steps, psi_stars }` — and **does not** combine them
//! into a score. Inventing a fitness metric here would split the definition of
//! viability across two modules; the valence loop owns that combining rule
//! (`valence::viability` / `viability_internal`). This module only guarantees
//! the readout it hands over is from a *faithful* execution.
//!
//! Depends only on the public APIs of `interactive` / `constellation` /
//! `execution`; does not modify the engine.

use crate::constellation::{Constellation, Star};
use crate::execution::stars_alpha_equiv;
use crate::interactive::{
    build_accel, iex, iex_fast_with_accel, iex_tabled_with_accel, IexAccel,
};

/// Which optimizing tier the hot path runs.
///
/// Both are gated against the reference [`iex`] by this module's live oracle.
/// `Fast` is the byte-identical jet (so the oracle may additionally assert
/// byte-identity); `Tabled` is result-equivalent only (drops α-variant stars,
/// so `psi` / `steps` legitimately differ — only the concealed answer set is
/// guaranteed equal).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tier {
    /// [`iex_fast`](crate::interactive::iex_fast) — byte-identical to `iex`.
    Fast,
    /// [`iex_tabled`](crate::interactive::iex_tabled) — result-equivalent.
    Tabled,
}

/// When to run the reference oracle alongside the fast tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleMode {
    /// Never cross-check. Cheapest; only safe once the gates are trusted and
    /// the input distribution is stable.
    Off,
    /// Cross-check 1-in-`N` calls (by a per-call counter, deterministic in
    /// [`evaluate_many`]). `Sample(0)` and `Sample(1)` both mean "always".
    Sample(u32),
    /// Cross-check every call. Use during search bring-up / fast-path changes.
    Always,
}

/// Outcome of the live differential check for one [`evaluate`] call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleStatus {
    /// The oracle fired and the fast tier matched reference `iex` under the
    /// tier's faithfulness criterion (answer-set α-equivalence; byte-identity
    /// for `Fast`).
    Faithful,
    /// The oracle did not fire (`Off`, or not the sampled call).
    Skipped,
    /// The oracle fired and the fast tier disagreed with reference `iex`.
    /// `detail` is a terse description of the disagreement. A search MUST
    /// treat this run's readout as untrustworthy.
    Divergent { detail: String },
}

/// Result of one [`evaluate`] call: the engine output plus the live-oracle
/// verdict on whether the tier that produced it was faithful.
#[derive(Debug, Clone)]
pub struct EvalReport {
    /// Final interaction space (from the chosen tier).
    pub psi: Vec<Star>,
    /// Whether the tier reached a true normal form.
    pub is_normal_form: bool,
    /// Steps taken by the tier (tier-relative; `Tabled` ≠ `iex` by design).
    pub steps: usize,
    /// `psi.len()` — number of stars in the result.
    pub psi_stars: usize,
    /// Live differential-oracle verdict for this call.
    pub oracle: OracleStatus,
}

/// The substrate signals the fitness side consumes — and nothing else.
///
/// Field names mirror what `crate::valence` / `crate::reafference` read off a
/// `crate::subjective::Step` (`is_normal_form`, `psi_size`, step index) so the
/// valence loop computes closure / viability from this without this module
/// inventing a metric. See the module-level boundary note.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ViabilityReadout {
    /// Did execution reach a true normal form (vs. fuel-out)?
    pub reached_nf: bool,
    /// Steps taken (substrate work proxy).
    pub steps: usize,
    /// Result-space star count (`Step::psi_size` analogue).
    pub psi_stars: usize,
}

/// Extract the substrate readout the valence loop needs.
///
/// Pure projection of [`EvalReport`]. Deliberately drops `oracle`: the caller
/// is responsible for checking `report.oracle` and discarding the run on
/// [`OracleStatus::Divergent`] *before* feeding this into a fitness function —
/// this module does not silently launder an unfaithful run into a readout.
pub fn viability_readout(report: &EvalReport) -> ViabilityReadout {
    ViabilityReadout {
        reached_nf: report.is_normal_form,
        steps: report.steps,
        psi_stars: report.psi.len(),
    }
}

/// The faithfulness criterion, applied exactly as the engine's own gates do.
///
/// * `Fast`: byte-identical to reference `iex` (`iex_eq_iex_fast`): same
///   `psi`, `is_normal_form`, `steps`. (Also implies answer-set equivalence.)
/// * `Tabled`: result-equivalence (`iex_tabled_result_eq_iex`): same
///   ɟ-concealed answer set up to α, and the tier reached a true normal form.
///   `psi` / `steps` differ by design, so they are NOT compared.
///
/// Returns `Ok(())` if faithful, `Err(detail)` with a terse divergence note.
fn differential_check(
    tier: Tier,
    fast_psi: &[Star],
    fast_nf: bool,
    fast_steps: usize,
    ref_psi: &[Star],
    ref_nf: bool,
    ref_steps: usize,
) -> Result<(), String> {
    match tier {
        Tier::Fast => {
            // Byte-identity, exactly as `iex_eq_iex_fast` asserts.
            if fast_psi != ref_psi {
                return Err(format!(
                    "Fast: psi differs (fast {} stars vs ref {} stars)",
                    fast_psi.len(),
                    ref_psi.len()
                ));
            }
            if fast_nf != ref_nf {
                return Err(format!(
                    "Fast: is_normal_form differs (fast {fast_nf} vs ref {ref_nf})"
                ));
            }
            if fast_steps != ref_steps {
                return Err(format!(
                    "Fast: step count differs (fast {fast_steps} vs ref {ref_steps})"
                ));
            }
            Ok(())
        }
        Tier::Tabled => {
            // Result-equivalence, exactly as `iex_tabled_result_eq_iex`:
            // ɟ-concealed answer sets equal up to α (mutual subset), and the
            // tabled tier must reach a true fixpoint.
            if !fast_nf {
                return Err("Tabled: did not reach a true normal form".to_string());
            }
            let av = crate::interactive::conceal_and_filter(&fast_psi.to_vec());
            let bv = crate::interactive::conceal_and_filter(&ref_psi.to_vec());
            let subset = |xs: &[Star], ys: &[Star]| {
                xs.iter()
                    .all(|x| ys.iter().any(|y| stars_alpha_equiv(x, y)))
            };
            if subset(&av, &bv) && subset(&bv, &av) {
                Ok(())
            } else {
                Err(format!(
                    "Tabled: concealed answer set differs (tier {} vs ref {} visible stars)",
                    av.len(),
                    bv.len()
                ))
            }
        }
    }
}

/// Should the oracle fire on call number `call_idx` (0-based) under `mode`?
fn oracle_fires(mode: OracleMode, call_idx: u64) -> bool {
    match mode {
        OracleMode::Off => false,
        OracleMode::Always => true,
        OracleMode::Sample(n) => {
            if n <= 1 {
                true
            } else {
                call_idx % (n as u64) == 0
            }
        }
    }
}

/// Run one execution on the chosen `tier`, with the live differential oracle
/// applied per `mode`. Builds the per-Φ accel internally; for many inputs use
/// [`evaluate_many`], which hoists it.
pub fn evaluate(
    phi: &Constellation,
    psi_init: Vec<Star>,
    fuel: usize,
    mode: OracleMode,
    tier: Tier,
) -> EvalReport {
    let accel = build_accel(phi);
    evaluate_with_accel(&accel, phi, psi_init, fuel, mode, tier, 0)
}

/// `evaluate` with a caller-supplied accel and explicit call index (so the
/// `Sample(N)` schedule is deterministic across a batch). `call_idx` only
/// drives the sampling decision.
fn evaluate_with_accel(
    accel: &IexAccel,
    phi: &Constellation,
    psi_init: Vec<Star>,
    fuel: usize,
    mode: OracleMode,
    tier: Tier,
    call_idx: u64,
) -> EvalReport {
    // Run the chosen optimizing tier on the (cloned) input. We clone because
    // the reference oracle needs the same input when it fires.
    let fast = match tier {
        Tier::Fast => iex_fast_with_accel(accel, phi, psi_init.clone(), fuel),
        Tier::Tabled => iex_tabled_with_accel(accel, phi, psi_init.clone(), fuel),
    };

    let oracle = if oracle_fires(mode, call_idx) {
        // "The interpreter is the spec" — reference iex on the SAME input.
        let reference = iex(phi, psi_init, fuel);
        match differential_check(
            tier,
            &fast.psi,
            fast.is_normal_form,
            fast.steps,
            &reference.psi,
            reference.is_normal_form,
            reference.steps,
        ) {
            Ok(()) => OracleStatus::Faithful,
            Err(detail) => OracleStatus::Divergent { detail },
        }
    } else {
        OracleStatus::Skipped
    };

    EvalReport {
        psi_stars: fast.psi.len(),
        psi: fast.psi,
        is_normal_form: fast.is_normal_form,
        steps: fast.steps,
        oracle,
    }
}

/// Evaluate many inputs against one fixed Φ — the shape the search calls.
///
/// Contract (see [`build_accel`]): `IexAccel` is a pure function of Φ with no
/// Ψ/run state, so building it once and reusing it across every input is
/// provably identical to rebuilding per call (the engine's
/// `iex_fast_with_accel_eq_iex_fast` gate). Hoisting it out of millions of
/// small executions is the entire point of this batch entry point. The
/// `Sample(N)` schedule is indexed by position in `inputs`, so it is
/// deterministic and stable across reruns.
pub fn evaluate_many(
    phi: &Constellation,
    inputs: Vec<Vec<Star>>,
    fuel: usize,
    mode: OracleMode,
    tier: Tier,
) -> Vec<EvalReport> {
    let accel = build_accel(phi);
    inputs
        .into_iter()
        .enumerate()
        .map(|(i, psi)| {
            evaluate_with_accel(&accel, phi, psi, fuel, mode, tier, i as u64)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::{mk_app_str, mk_var};

    fn var(x: &str) -> crate::term::Term {
        mk_var(x)
    }
    fn app(f: &str, a: Vec<crate::term::Term>) -> crate::term::Term {
        mk_app_str(f, a)
    }
    fn cst(n: &str) -> crate::term::Term {
        mk_app_str(n, vec![])
    }
    fn nat(n: usize) -> crate::term::Term {
        let mut t = cst("0");
        for _ in 0..n {
            t = app("s", vec![t]);
        }
        t
    }

    // ── Corpus (a): Horn `add` (the §55.6 corpus the interactive tests use) ──
    fn add_prog() -> Constellation {
        vec![
            vec![pos_ray("add", vec![cst("0"), var("Y"), var("Y")])],
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray(
                    "add",
                    vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])],
                ),
            ],
        ]
    }
    fn add_query(m: usize, n: usize) -> Star {
        vec![neg_ray("add", vec![nat(m), nat(n), var("R")]), var("R")]
    }

    // ── Corpus (b): combinator core, SKK (= I) — interactive `iex_eq_iex_fast` ──
    fn skk_phi_psi() -> (Constellation, Vec<Star>) {
        let prog = crate::combinator::app_n([
            crate::combinator::a_("S"),
            crate::combinator::a_("T"),
            crate::combinator::a_("T"),
            crate::combinator::a_("x"),
        ]);
        let phi = crate::combinator::machine_stars();
        let psi = vec![crate::combinator::initial_process(&prog)];
        (phi, psi)
    }

    // ── Corpus (c): binary arithmetic add(5,6) — interactive corpus ──
    fn binarith_phi_psi() -> (Constellation, Vec<Star>) {
        let phi = crate::binarith::binarith_module();
        let psi = vec![vec![
            neg_ray(
                "add",
                vec![crate::binarith::nat(5), crate::binarith::nat(6), var("R")],
            ),
            var("R"),
        ]];
        (phi, psi)
    }

    fn all_corpora() -> Vec<(&'static str, Constellation, Vec<Star>, usize)> {
        let (cphi, cpsi) = skk_phi_psi();
        let (bphi, bpsi) = binarith_phi_psi();
        vec![
            ("horn_add_3_2", add_prog(), vec![add_query(3, 2)], 5000),
            ("combinator_skk", cphi, cpsi, 3000),
            ("binarith_add_5_6", bphi, bpsi, 8000),
        ]
    }

    /// `evaluate` with `OracleMode::Always` reports `Faithful` on all three
    /// corpora, both tiers. (The live oracle agrees with reference `iex`.)
    #[test]
    fn evaluate_always_faithful_all_corpora_both_tiers() {
        for tier in [Tier::Fast, Tier::Tabled] {
            for (name, phi, psi, fuel) in all_corpora() {
                let r = evaluate(&phi, psi, fuel, OracleMode::Always, tier);
                assert_eq!(
                    r.oracle,
                    OracleStatus::Faithful,
                    "{name} / {tier:?}: live oracle should be Faithful, got {:?}",
                    r.oracle
                );
                // Sanity: these corpora all converge.
                assert!(
                    r.is_normal_form,
                    "{name} / {tier:?}: should reach normal form"
                );
                assert!(r.psi_stars >= 1, "{name} / {tier:?}: nonempty result");
            }
        }
    }

    /// THE GOODHART-GUARD TEST. Take a real, faithful `evaluate` result, then
    /// perturb its `psi` and feed *that* to the same differential criterion the
    /// live oracle uses. It MUST report `Divergent` — proving the oracle
    /// actually catches an unfaithful fast path rather than rubber-stamping it.
    /// This is the point of the module.
    #[test]
    fn goodhart_guard_oracle_catches_unfaithful_fast_path() {
        let phi = add_prog();
        let psi = vec![add_query(3, 2)];
        let fuel = 5000;

        // Ground truth via the reference oracle.
        let reference = iex(&phi, psi.clone(), fuel);
        assert!(reference.is_normal_form, "reference converges");

        // Forge a wrong-but-plausible "fast result": same shape, perturbed psi
        // with an extra all-neutral star (so it SURVIVES conceal+filter as a
        // spurious *visible answer* the real engine never produces). A
        // Goodharting search would happily consume this as viable.
        let mut forged_psi = reference.psi.clone();
        forged_psi.push(vec![app("BOGUS", vec![cst("0")])]);

        // Fast tier: byte-identity criterion must reject the perturbation.
        let verdict_fast = differential_check(
            Tier::Fast,
            &forged_psi,
            reference.is_normal_form,
            reference.steps,
            &reference.psi,
            reference.is_normal_form,
            reference.steps,
        );
        assert!(
            verdict_fast.is_err(),
            "Fast oracle must flag a perturbed psi as Divergent"
        );

        // Tabled tier: answer-set criterion must also reject it (the bogus
        // star survives conceal+filter as a spurious visible answer).
        let verdict_tabled = differential_check(
            Tier::Tabled,
            &forged_psi,
            true, // claim a fixpoint, as a deceptive fast path would
            reference.steps,
            &reference.psi,
            reference.is_normal_form,
            reference.steps,
        );
        assert!(
            verdict_tabled.is_err(),
            "Tabled oracle must flag a perturbed answer set as Divergent"
        );

        // And the same divergence surfaces through the public OracleStatus
        // shape (not just the internal helper): a tier that claims a fixpoint
        // it did not reach is caught.
        let status = match differential_check(
            Tier::Tabled,
            &forged_psi,
            false, // also fails the "must reach NF" leg
            reference.steps,
            &reference.psi,
            reference.is_normal_form,
            reference.steps,
        ) {
            Ok(()) => OracleStatus::Faithful,
            Err(detail) => OracleStatus::Divergent { detail },
        };
        match status {
            OracleStatus::Divergent { detail } => {
                assert!(!detail.is_empty(), "divergence carries a terse detail");
            }
            other => panic!("expected Divergent, got {other:?}"),
        }
    }

    /// `evaluate_many` builds the accel once and is result-identical to
    /// per-call `evaluate` (the build-once reuse contract). Checked across
    /// distinct inputs against one fixed Φ.
    #[test]
    fn evaluate_many_eq_per_call_build_once() {
        for tier in [Tier::Fast, Tier::Tabled] {
            let phi = add_prog();
            let inputs = vec![
                vec![add_query(1, 1)],
                vec![add_query(3, 2)],
                vec![add_query(2, 4)],
                vec![add_query(0, 5)],
            ];

            let batch = evaluate_many(&phi, inputs.clone(), 5000, OracleMode::Always, tier);

            for (i, inp) in inputs.into_iter().enumerate() {
                let single = evaluate(&phi, inp, 5000, OracleMode::Always, tier);
                assert_eq!(
                    batch[i].is_normal_form, single.is_normal_form,
                    "{tier:?} input {i}: nf differs batch vs per-call"
                );
                assert_eq!(
                    batch[i].psi_stars, single.psi_stars,
                    "{tier:?} input {i}: psi_stars differs batch vs per-call"
                );
                assert_eq!(
                    batch[i].steps, single.steps,
                    "{tier:?} input {i}: steps differ batch vs per-call"
                );
                assert_eq!(
                    batch[i].oracle, single.oracle,
                    "{tier:?} input {i}: oracle verdict differs batch vs per-call"
                );
                assert_eq!(
                    batch[i].oracle,
                    OracleStatus::Faithful,
                    "{tier:?} input {i}: should be Faithful"
                );
            }
        }
    }

    /// `viability_readout` is a faithful projection and `Off`/unsampled calls
    /// report `Skipped` (sampling schedule sanity).
    #[test]
    fn readout_projection_and_sampling() {
        let phi = add_prog();
        let r = evaluate(&phi, vec![add_query(2, 2)], 5000, OracleMode::Off, Tier::Fast);
        assert_eq!(r.oracle, OracleStatus::Skipped, "Off ⇒ Skipped");
        let vr = viability_readout(&r);
        assert_eq!(vr.reached_nf, r.is_normal_form);
        assert_eq!(vr.steps, r.steps);
        assert_eq!(vr.psi_stars, r.psi.len());

        // Sample(3): with evaluate_many's positional index, calls 0,3,6,… fire.
        let inputs: Vec<Vec<Star>> = (0..6).map(|_| vec![add_query(1, 1)]).collect();
        let batch = evaluate_many(&phi, inputs, 5000, OracleMode::Sample(3), Tier::Fast);
        let fired: Vec<bool> = batch
            .iter()
            .map(|r| r.oracle != OracleStatus::Skipped)
            .collect();
        assert_eq!(
            fired,
            vec![true, false, false, true, false, false],
            "Sample(3) fires on positional indices 0 and 3"
        );
    }
}
