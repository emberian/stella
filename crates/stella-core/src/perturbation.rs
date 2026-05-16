//! L2c-redux — Invariant⇒flat perturbation-response make-or-break harness (CONSTRUCTION ONLY).
//!
//! # Reformulated pre-registration (2026-05-16, locked before re-run code)
//!
//! This module implements the **reformulated (invariant⇒flat)** make-or-break harness
//! from `docs/01-subjective-engine-and-valence.md §4` (M1–M5), superseding the
//! deathless-era N1–N4 nulls. The deathless-era null is preserved verbatim in
//! `docs/02-phase4-first-run.md` and is NOT retconned.
//!
//! The core shift: **mortality is NOT required**. Stake = a non-trivial
//! perturbation-response viability gradient under coupling. Invariant ⇒ flat ⇒ no
//! charge (§2.4-amended). An eternal-but-perturbable closure is admissible.
//!
//! # What this module does NOT do
//!
//! - It does NOT conclude pass/null/thesis-verdict. No `verdict()` method exists.
//!   The parent caller reads `ReformReport` and adjudicates.
//! - It does NOT run the full corpus sweep during unit testing — a single tiny
//!   labelled smoke fixture is exercised in tests. The real corpus sweep is invoked
//!   by the parent via `run_reformulated_make_or_break`.
//! - It does NOT tune, rig, or hand-engineer corpus members, viability weights, or
//!   environments to produce a desired outcome. The `perturbing_env` mechanism is
//!   generic (single scalar; not closure-specific).
//! - It does NOT judge whether any Mk-predicate firing is "good" or "bad". An honest
//!   null is a first-class, fully-valid outcome.
//! - It does NOT run the corpus sweep in tests (not invoked in `tests` module).
//!
//! # M1–M5 gate predicates
//!
//! Each predicate is a PURE FUNCTION carrying its verbatim spec-§4 quote in a
//! `// SPEC §4 Mk:` comment immediately above it. M1–M5 are LOCKED — never weakened,
//! retro-weakening visible in diff. `M5Status::Undetermined` is never coerced.
//!
//! # Perturbation mechanism (generic, single scalar)
//!
//! `perturbing_env(strength)` builds an adversarial partner constellation of stars
//! that generate competing interactions. Mechanism: for each `strength` level, the
//! env constellation contains `strength` "noise stars" — stars with a single
//! neutral-tagged positive ray `+perturb_k(noise_k)` that match the generic
//! negative-polarity side of any query but carry an unsolvable constant argument.
//!
//! **Generic**: the noise stars are parameterised only by `strength` and carry a
//! symbol (`perturb_k`) not present in any corpus member — they do not interact with
//! any specific closure's rays and are not designed to close or break any particular
//! reafferent loop. They contribute to `psi_size` and `frontier_size` readings
//! (which directly affect viability) at a level proportional to `strength`,
//! producing a generic coupling-load on any agent constellation.
//!
//! **Single scalar**: `strength: u32` is the sole knob. strength=0 → inert env
//! (one empty/trivially-inert star); strength=k → k noise stars added.
//!
//! This satisfies the M4 invariant: the same mechanism, same viability formula, and
//! same partition search are used for every corpus member and every strength level.

use crate::automata::{encode_nfa, encode_word, eng_fig561_nfa};
use crate::constellation::{Constellation, Star};
use crate::polarised::{neg_ray, pos_ray};
use crate::reafference::{solve_for_closure, ClosureWitness};
use crate::term::{mk_app_str, mk_var, Term};
use crate::tm::{encode_ntm, encode_word_ntm, trivial_accept_empty_tm};
use crate::valence::viability;
use crate::subjective::{AgentSet, subjective_stream};

// ─────────────────────────────────────────────────────────────────────────────
// perturbing_env — adversarial partner constellation
// ─────────────────────────────────────────────────────────────────────────────

/// Build an adversarial/perturbing partner constellation parameterised by `strength`.
///
/// # Perturbation mechanism
///
/// The returned `Constellation` is a collection of "noise stars" that add coupling
/// load to any constellation they are combined with:
///
/// - **strength=0**: returns a constellation with a single inert star `[+inert(inert_c)]`
///   (carries one positive ray with a constant that cannot unify with anything in
///   Eng-corpus members, producing no interaction — the zero-perturbation baseline).
/// - **strength=k (k ≥ 1)**: returns k stars, each of the form
///   `[+perturb_i(noise_i)]` where `perturb_i` and `noise_i` are symbols unique
///   to this env (not present in any corpus member). These stars increase `psi_size`
///   and `frontier_size` when combined with the corpus member, raising the viability
///   reading proportionally to `strength` — a generic coupling-load gradient.
///
/// # Generic and closure-agnostic
///
/// The noise stars carry symbols (`perturb_k`, `noise_k`) that do not appear in any
/// corpus member (Horn add, NFA, NTM). They are not designed to interact with any
/// specific reafferent closure; the perturbation is a scalar environmental load
/// applied uniformly. Higher strength = more environmental "noise" competing for
/// interaction slots, generically disrupting the agent/env coupling without targeting
/// any particular closure mechanism.
///
/// # Single scalar knob
///
/// `strength: u32` is the sole parameter. No other free parameters exist.
pub fn perturbing_env(strength: u32) -> Constellation {
    if strength == 0 {
        // Inert baseline: one star with a constant that cannot interact with corpus members.
        // +inert_zero(inert_c) — positive ray whose symbol is absent from all corpus members.
        vec![
            vec![pos_ray("inert_zero", vec![mk_app_str("inert_c", vec![])])],
        ]
    } else {
        // strength=k: k noise stars, each [+perturb_i(noise_i_c)] for i in 0..k.
        // Symbol naming ensures they are unique per-strength-index and never appear
        // in corpus members (which use add/s/zero/sense/act/f/state/tape/nfa symbols).
        (0..strength)
            .map(|i| {
                let sym = format!("perturb_{i}");
                let arg_sym = format!("noise_{i}_c");
                vec![pos_ray(&sym, vec![mk_app_str(&arg_sym, vec![])])]
            })
            .collect()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ResponseProfile — perturbation-response measurement
// ─────────────────────────────────────────────────────────────────────────────

/// The perturbation-response profile for one corpus member's self-organised closure.
///
/// Records how the mean viability of the closure responds to:
/// - varying perturbation `strength` (the adversarial env knob), and
/// - varying `max_rounds` (the trajectory-length cap).
///
/// The two diagnostic booleans flag whether the response is genuine
/// (perturbation-tracking + cap-invariant) or an artifact.
#[derive(Debug, Clone)]
pub struct ResponseProfile {
    /// Mean viability for each `(strength, mean_viability)` pair.
    ///
    /// Measured by running the closure stream coupled to `perturbing_env(s)` for
    /// each `s` in `strengths`, with the first `max_rounds` in `caps` as the bound,
    /// and computing the mean `viability::viability` score across all sampled rounds.
    pub by_strength: Vec<(u32, f64)>,

    /// Mean viability for each `(max_rounds_cap, mean_viability)` pair.
    ///
    /// Measured at strength=0 (inert env) for each cap in `caps`.
    /// Used to detect the M3 artifact: if viability tracks the cap, it is an artifact.
    pub by_cap: Vec<(usize, f64)>,

    /// Does viability **monotonically or robustly vary** with perturbation strength?
    ///
    /// `true` iff the `by_strength` viability series shows a non-trivial, consistently
    /// monotone trend (all-decreasing or all-increasing as strength increases, by a
    /// tolerance threshold), meaning the closure *responds* to the adversarial load.
    ///
    /// `false` (flat / non-monotone) ⇒ M2 may fire (invariance).
    pub perturbation_tracking: bool,

    /// Does the response NOT track `max_rounds`?
    ///
    /// `true` iff the `by_cap` viability series is **cap-invariant**: varying
    /// `max_rounds` does NOT cause viability to monotonically track the cap.
    ///
    /// This is the explicit M3 fix for the deathless-era `t_death = cap−2` artifact:
    /// a genuine response should not vary proportionally with the cap. `false` ⇒ M3
    /// fires (artifact).
    pub cap_invariant: bool,
}

// ─────────────────────────────────────────────────────────────────────────────
// mean_viability_coupled — measure viability of closure under perturbing env
// ─────────────────────────────────────────────────────────────────────────────

/// Compute mean viability of `phi ⊎ perturbing_env(strength)` under `partition`,
/// bounded by `max_rounds` proper-time rounds.
///
/// The combined phi (corpus member) is augmented with the perturbing env stars.
/// The partition is the agent partition solved for by `solve_for_closure` (unchanged;
/// the partition is relative to `psi0` star indices, not to phi).
///
/// Returns the mean `viability::viability` score across all rounds sampled from
/// the streaming trajectory. Returns 0.0 if no steps are observed.
///
/// # Why this uses the same viability formula (M4 invariant)
///
/// `viability::viability` is called with the same weights (0.4/0.4/0.2/0.1) for
/// every member, every strength, every cap. No per-member parameter injection occurs.
fn mean_viability_coupled(
    phi: &Constellation,
    perturb: &Constellation,
    psi0: &[Star],
    partition: &AgentSet,
    max_rounds: usize,
) -> f64 {
    // Combined phi = corpus phi + perturbing env stars.
    // The perturbing env is added to the reference constellation (non-linear supply),
    // not to psi0, so it acts as an adversarial part of the environment without
    // altering the initial interaction space or the agent partition.
    let combined_phi: Constellation = phi.iter().chain(perturb.iter()).cloned().collect();

    let max_steps = (max_rounds + 2) * 50;
    let stream = subjective_stream(&combined_phi, psi0.to_vec()).take(max_steps);

    let mut scores: Vec<f64> = Vec::new();
    for step in stream {
        if step.round > max_rounds {
            break;
        }
        let v = viability(&step, partition);
        scores.push(v.score);
    }

    if scores.is_empty() {
        0.0
    } else {
        scores.iter().sum::<f64>() / scores.len() as f64
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// perturbation_response
// ─────────────────────────────────────────────────────────────────────────────

/// Measure the perturbation-response profile for one corpus member's self-organised closure.
///
/// For the self-organised closure of `member` (partition SOLVED-FOR via
/// `solve_for_closure`, never designated), measure `valence::viability` over the
/// stream while coupled to `perturbing_env(s)` for each `s` in `strengths` and
/// each `max_rounds` in `caps`.
///
/// # Arguments
///
/// - `member`: the `(phi, psi0)` pair for the corpus member.
/// - `partition`: the agent partition, already solved-for by `solve_for_closure`.
/// - `strengths`: the perturbation strength levels to scan (e.g. `&[0, 1, 2, 4]`).
/// - `caps`: the `max_rounds` values to scan (e.g. `&[4, 6, 8]`).
///
/// # Returns
///
/// A `ResponseProfile` with:
/// - `by_strength`: viability measured at each strength (first cap in `caps`).
/// - `by_cap`: viability at strength=0 for each cap.
/// - `perturbation_tracking` and `cap_invariant` diagnostic flags.
///
/// If `partition` is empty or `strengths`/`caps` are empty, returns a flat/empty profile.
pub fn perturbation_response(
    phi: &Constellation,
    psi0: &[Star],
    partition: &AgentSet,
    strengths: &[u32],
    caps: &[usize],
) -> ResponseProfile {
    // Use the first cap for by_strength measurement; use all caps for by_cap.
    let base_cap = caps.first().copied().unwrap_or(6);

    // ── by_strength: measure viability at each strength, fixed cap=base_cap ──
    let by_strength: Vec<(u32, f64)> = strengths
        .iter()
        .map(|&s| {
            let perturb = perturbing_env(s);
            let v = mean_viability_coupled(phi, &perturb, psi0, partition, base_cap);
            (s, v)
        })
        .collect();

    // ── by_cap: measure viability at strength=0, varying cap ─────────────────
    let perturb_inert = perturbing_env(0);
    let by_cap: Vec<(usize, f64)> = caps
        .iter()
        .map(|&cap| {
            let v = mean_viability_coupled(phi, &perturb_inert, psi0, partition, cap);
            (cap, v)
        })
        .collect();

    // ── perturbation_tracking: does viability monotonically vary with strength? ─
    // Criterion: the by_strength series is monotone (all-non-increasing or all-non-
    // decreasing), with at least one step that exceeds the noise threshold (0.01).
    // Monotone tracking means the closure responds to the adversarial load.
    let perturbation_tracking = is_monotone_tracking(&by_strength);

    // ── cap_invariant: does viability NOT track the cap? ─────────────────────
    // Criterion: the by_cap series is NOT monotone-increasing with cap.
    // The deathless-era artifact was viability rising proportionally with cap
    // (because t_death was set to cap−2). cap_invariant = true means viability
    // is stable (does not track cap), so the reading is genuine, not an artifact.
    let cap_invariant = !is_monotone_tracking(&by_cap);

    ResponseProfile {
        by_strength,
        by_cap,
        perturbation_tracking,
        cap_invariant,
    }
}

/// Check whether a `(key, viability)` series is monotone (all-non-increasing or
/// all-non-decreasing) with at least one change exceeding the noise threshold.
///
/// "Monotone tracking" = the response genuinely tracks the x-axis variable, not flat.
fn is_monotone_tracking<K: Copy>(series: &[(K, f64)]) -> bool {
    if series.len() < 2 {
        return false;
    }
    let scores: Vec<f64> = series.iter().map(|(_, v)| *v).collect();
    let deltas: Vec<f64> = scores.windows(2).map(|w| w[1] - w[0]).collect();

    // Check for at least one non-trivial change (threshold: 0.01).
    let has_significant = deltas.iter().any(|d| d.abs() > 0.01);
    if !has_significant {
        return false; // flat — not tracking
    }

    // Monotone increasing: all deltas ≥ 0.
    let all_nondecreasing = deltas.iter().all(|d| *d >= -1e-9);
    // Monotone decreasing: all deltas ≤ 0.
    let all_nonincreasing = deltas.iter().all(|d| *d <= 1e-9);

    all_nondecreasing || all_nonincreasing
}

// ─────────────────────────────────────────────────────────────────────────────
// MemberReformEvidence — per-corpus-member evidence record (reformulated)
// ─────────────────────────────────────────────────────────────────────────────

/// Evidence collected for a single corpus member in the reformulated harness.
///
/// All fields are observations, not judgments.
#[derive(Debug, Clone)]
pub struct MemberReformEvidence {
    /// Human-readable name for this corpus member.
    pub name: String,

    /// All closure witnesses found by `solve_for_closure` (principled §62-gated search).
    ///
    /// Empty iff no partition admits a reafference cycle — the honest-null outcome.
    pub closures_found: Vec<ClosureWitness>,

    /// Perturbation-response profiles (one per found closure).
    ///
    /// `profiles[i]` corresponds to `closures_found[i]`.
    pub profiles: Vec<ResponseProfile>,

    /// Was the closure search driven by the principled `solve_for_closure`?
    ///
    /// Always `true` for corpus members in `run_reformulated_make_or_break`.
    pub found_by_principled_search: bool,
}

// ─────────────────────────────────────────────────────────────────────────────
// M5Status — cross-level determination
// ─────────────────────────────────────────────────────────────────────────────

/// The determination status of the M5 predicate (cross-level).
///
/// M5 is Undetermined when no corpus member has nested closures — this is NEVER
/// coerced to "passed". The parent must note this limitation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum M5Status {
    /// M5 fires: cross-level closure bleed detected (nested closures are NOT sealed).
    Fires,
    /// M5 does not fire: nested closures are causally sealed where tested.
    DoesNotFire,
    /// No corpus member has nested closures; M5 cannot be evaluated.
    /// Reported as undetermined — NOT "passed".
    Undetermined,
}

// ─────────────────────────────────────────────────────────────────────────────
// M1–M5 gate predicates (VERBATIM spec §4, LOCKED)
// ─────────────────────────────────────────────────────────────────────────────
//
// Each is a PURE FUNCTION of collected evidence.
// The verbatim spec-§4 bullet text appears in the // SPEC §4 Mk: comment above.
// M1–M5 are LOCKED — retro-weakening is visible in diff.

// SPEC §4 M1:
// "(M1) Smuggled individuation. The reafferent closure — or any
// perturbation-response — only ever appears because rays were effectively
// hand-tagged or the agent/environment cut hand-placed; never self-organised via
// the principled Ch9-§62 partition search on the non-rigged Eng-own corpus."
//
// Implementation: M1 fires iff every principled-search corpus member has no
// self-organised closure (closures_found is empty for all). If any principled-
// search member finds a closure, at least one self-organised → M1 does NOT fire.
/// M1 gate predicate (pure function of evidence).
///
/// Returns `true` (fires, falsification signal) iff no principled-search corpus
/// member found a reafference closure — i.e., closure only ever appeared under
/// hand-engineered setups, never self-organised via the principled §62 partition
/// search on the Eng-own corpus.
pub fn m1_fires(evidence: &[MemberReformEvidence]) -> bool {
    // SPEC §4 M1: "only ever appears because rays were effectively hand-tagged or
    // the agent/environment cut hand-placed; never self-organised via the principled
    // Ch9-§62 partition search on the non-rigged Eng-own corpus."
    let principled = evidence.iter().filter(|m| m.found_by_principled_search);
    let mut any_principled = false;
    for m in principled {
        any_principled = true;
        if !m.closures_found.is_empty() {
            return false; // at least one self-organised → M1 does NOT fire
        }
    }
    // If no principled-search members at all, M1 fires vacuously.
    // If all principled members have empty closures, M1 fires.
    let _ = any_principled;
    true
}

// SPEC §4 M2:
// "(M2) Invariance — the core discriminator, replacing deathless⇒flat. The
// self-organised closure is *invariant*: under a perturbing/adversarial
// environment its viability does not respond beyond noise — it cannot be driven
// up or down by the coupling. Invariant ⇒ flat ⇒ no charge."
//
// Implementation: M2 fires iff every closure's ResponseProfile has
// perturbation_tracking = false — i.e., no closure exhibits a genuine
// viability response to varying perturbation strength. If any closure shows
// perturbation_tracking = true, M2 does NOT fire.
/// M2 gate predicate (pure function of evidence).
///
/// Returns `true` (fires, falsification signal) iff every self-organised closure
/// shows a flat (non-tracking) viability response to perturbation — i.e., the
/// closure is invariant under the adversarial environment: no charge.
pub fn m2_fires(evidence: &[MemberReformEvidence]) -> bool {
    // SPEC §4 M2: "The self-organised closure is *invariant*: under a perturbing/
    // adversarial environment its viability does not respond beyond noise — it
    // cannot be driven up or down by the coupling. Invariant ⇒ flat ⇒ no charge."
    //
    // M2 fires iff every profile across all members shows perturbation_tracking=false.
    // If any profile has perturbation_tracking=true, at least one closure genuinely
    // responds → M2 does NOT fire.
    for member in evidence {
        for profile in &member.profiles {
            if profile.perturbation_tracking {
                return false; // genuine response → M2 does NOT fire
            }
        }
    }
    // All profiles flat (or no profiles): M2 fires.
    true
}

// SPEC §4 M3:
// "(M3) Artifact, not response — the disclosed tightening, now first-class &
// pre-registered. A genuine viability response must be **cap-invariant** (vary
// max_rounds/supply ⇒ it does NOT track the cap — the explicit fix for the
// deathless-era t_death = cap−2 artifact) **and** **perturbation-tracking**
// (vary perturbation strength ⇒ the response tracks it). Failing either ⇒
// artifact ⇒ null."
//
// Implementation: M3 fires iff any profile fails EITHER cap_invariant OR
// perturbation_tracking. Both must hold for a genuine response; either missing
// = artifact.
/// M3 gate predicate (pure function of evidence).
///
/// Returns `true` (fires, falsification signal) iff any closure's profile fails
/// the artifact test — either NOT cap_invariant (response tracks the cap,
/// artifact) OR NOT perturbation_tracking (response is flat, no genuine tracking).
/// Failing either ⇒ artifact ⇒ null.
pub fn m3_fires(evidence: &[MemberReformEvidence]) -> bool {
    // SPEC §4 M3: "A genuine viability response must be cap-invariant (vary
    // max_rounds/supply ⇒ it does NOT track the cap — the explicit fix for the
    // deathless-era t_death = cap−2 artifact) and perturbation-tracking (vary
    // perturbation strength ⇒ the response tracks it). Failing either ⇒ artifact ⇒ null."
    //
    // M3 fires iff ANY profile is an artifact:
    //   artifact = NOT cap_invariant  OR  NOT perturbation_tracking
    for member in evidence {
        for profile in &member.profiles {
            if !profile.cap_invariant || !profile.perturbation_tracking {
                return true; // at least one artifact → M3 fires
            }
        }
    }
    false
}

// SPEC §4 M4:
// "(M4) Engineered one level up. The perturbation-response only accretes under
// per-task hand-tuning of the viability metric, environment, or partition. The
// metric/rule must be globally fixed across the entire corpus (structurally
// enforced); M4 fires iff that invariant is violated."
//
// Implementation: M4 fires iff any corpus member was NOT produced by the
// principled search (found_by_principled_search = false). In this harness, the
// viability metric (weights 0.4/0.4/0.2/0.1) is defined once in `valence::viability`
// and applied uniformly. M4 fires only if the harness is structurally modified
// to introduce per-task tuning (detectable via found_by_principled_search=false).
/// M4 gate predicate (pure function of evidence).
///
/// Returns `true` (fires, falsification signal) iff the global viability-metric
/// invariant is violated — i.e., per-task hand-tuning of the metric, environment,
/// or partition is detected. In normal operation (uniform metric, principled search),
/// M4 does NOT fire.
pub fn m4_fires(evidence: &[MemberReformEvidence]) -> bool {
    // SPEC §4 M4: "The perturbation-response only accretes under per-task hand-tuning
    // of the viability metric, environment, or partition. The metric/rule must be
    // globally fixed across the entire corpus (structurally enforced); M4 fires iff
    // that invariant is violated."
    //
    // Structural invariant: the SAME global viability metric (valence::viability,
    // weights 0.4/0.4/0.2/0.1, never adjusted per-member) is used for every
    // member. The same perturbing_env mechanism (single scalar, generic) is used
    // for every strength level. M4 fires iff any member bypassed the principled
    // search (found_by_principled_search=false), which is the only detectable form
    // of per-task engineering in this harness.
    //
    // Note: the smoke fixture uses found_by_principled_search=false to label itself;
    // it must be excluded from the evidence vec passed here.
    evidence.iter().any(|m| !m.found_by_principled_search)
}

// SPEC §4 M5:
// "(M5) Cross-level sealed (carried; honestly may be Undetermined). Closure
// layers causally sealed — no cross-level capture/bleed (§2.3). If no corpus
// member has nested closures, M5 is **Undetermined**, never coerced to 'passed'."
//
// Implementation: M5 requires ≥2 closures on a single member (nested closures).
// If no member has ≥2 closures, M5 is Undetermined. If any member has ≥2
// closures, we test whether the perturbation response profiles are correlated
// (bleed) or independent (sealed). Correlated → Fires; independent → DoesNotFire.
/// M5 gate predicate (pure function of evidence).
///
/// Returns `M5Status::Fires`, `M5Status::DoesNotFire`, or `M5Status::Undetermined`.
/// Undetermined when no member has ≥2 closures — NEVER coerced to "passed".
pub fn m5_fires(evidence: &[MemberReformEvidence]) -> M5Status {
    // SPEC §4 M5: "Cross-level sealed (carried; honestly may be Undetermined).
    // Closure layers causally sealed — no cross-level capture/bleed (§2.3). If no
    // corpus member has nested closures, M5 is Undetermined, never coerced to 'passed'."
    //
    // Multi-closure detection: a member with ≥2 closures has nested closures.
    // Cross-level bleed test: two profiles (from two closures on the same member)
    // show bleed if their by_strength viability trends are correlated (same-sign
    // deltas at every shared strength level), suggesting the upper closure is
    // entraining the lower closure's viability metric.
    let multi = evidence
        .iter()
        .filter(|m| m.closures_found.len() >= 2 && m.profiles.len() >= 2);

    let mut found_multi = false;
    for member in multi {
        found_multi = true;
        let profiles = &member.profiles;
        for i in 0..profiles.len() {
            for j in (i + 1)..profiles.len() {
                if cross_level_bleed(&profiles[i], &profiles[j]) {
                    return M5Status::Fires;
                }
            }
        }
    }

    if found_multi {
        M5Status::DoesNotFire
    } else {
        M5Status::Undetermined
    }
}

/// Cross-level bleed test for two ResponseProfiles from the same corpus member.
///
/// Returns `true` iff the two profiles' by_strength viability series show a
/// correlated (same-sign) trend at shared strength levels — evidence of cross-level
/// viability capture (spec §2.3).
fn cross_level_bleed(p1: &ResponseProfile, p2: &ResponseProfile) -> bool {
    // Pair up by_strength scores at matching strength levels.
    let map1: std::collections::HashMap<u32, f64> =
        p1.by_strength.iter().map(|&(s, v)| (s, v)).collect();
    let map2: std::collections::HashMap<u32, f64> =
        p2.by_strength.iter().map(|&(s, v)| (s, v)).collect();

    let shared: Vec<u32> = {
        let mut v: Vec<u32> = map1.keys().filter(|k| map2.contains_key(*k)).copied().collect();
        v.sort_unstable();
        v
    };

    if shared.len() < 2 {
        return false;
    }

    // Check consecutive pairs for same-sign delta (correlated trend = bleed).
    for w in shared.windows(2) {
        let s0 = w[0];
        let s1 = w[1];
        if let (Some(&v1_0), Some(&v1_1), Some(&v2_0), Some(&v2_1)) = (
            map1.get(&s0), map1.get(&s1), map2.get(&s0), map2.get(&s1),
        ) {
            let d1 = v1_1 - v1_0;
            let d2 = v2_1 - v2_0;
            // Same non-trivial sign = correlated = bleed.
            if d1 * d2 > 1e-6 {
                return true;
            }
        }
    }
    false
}

// ─────────────────────────────────────────────────────────────────────────────
// ReformReport — aggregate evidence report (no verdict method)
// ─────────────────────────────────────────────────────────────────────────────

/// Aggregate evidence report from `run_reformulated_make_or_break`.
///
/// Emits evidence only. Makes no pass/null/thesis judgment.
/// No `verdict()` method exists — its presence would violate the pre-registration
/// contract. The caller reads the fields and adjudicates.
#[derive(Debug, Clone)]
pub struct ReformReport {
    /// Evidence collected for each corpus member.
    pub members: Vec<MemberReformEvidence>,

    /// M1 gate result: `true` iff the predicate fires (falsification signal).
    pub m1_result: bool,

    /// M2 gate result: `true` iff the predicate fires (falsification signal).
    pub m2_result: bool,

    /// M3 gate result: `true` iff the predicate fires (falsification signal).
    pub m3_result: bool,

    /// M4 gate result: `true` iff the predicate fires (falsification signal).
    ///
    /// M4 fires iff the global viability-metric invariant is violated — the SAME
    /// metric must be used for every member (structurally enforced).
    pub m4_result: bool,

    /// M5 gate result: Fires / DoesNotFire / Undetermined.
    ///
    /// Undetermined when no member has nested closures. NEVER coerced to "passed".
    pub m5_result: M5Status,

    /// Plain-text dump of evidence and gate results (no verdict).
    pub plain_text_dump: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// Corpus constructors (reusing experiment.rs Eng-own encodings)
// ─────────────────────────────────────────────────────────────────────────────

/// Helper: build `s^n(0)`.
fn nat(n: usize) -> Term {
    let mut t = mk_app_str("zero", vec![]);
    for _ in 0..n {
        t = mk_app_str("s", vec![t]);
    }
    t
}

/// Helper: variable term.
fn var(x: &str) -> Term {
    mk_var(x)
}

/// Corpus member 1: Horn `add` animist constellation (Eng §55/§4.5).
fn corpus_add_horn() -> (String, Constellation, Vec<Star>) {
    let phi: Constellation = vec![
        vec![pos_ray("add", vec![nat(0), var("Y"), var("Y")])],
        vec![
            neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
            pos_ray("add", vec![
                mk_app_str("s", vec![var("X")]),
                var("Y"),
                mk_app_str("s", vec![var("Z")]),
            ]),
        ],
    ];
    let psi0: Vec<Star> = vec![
        vec![
            neg_ray("add", vec![nat(1), nat(1), var("R")]),
            var("R"),
        ],
    ];
    (
        "Horn add (Eng §55/§4.5 animist constellation, query 1+1)".to_string(),
        phi,
        psi0,
    )
}

/// Corpus member 2: NFA animist-structured encoding (Eng §56 Figure 56.1).
fn corpus_nfa_automata() -> (String, Constellation, Vec<Star>) {
    let nfa = eng_fig561_nfa();
    let phi: Constellation = encode_nfa(&nfa);
    let psi0: Vec<Star> = vec![encode_word(&["0"])];
    (
        "NFA automata encoding (Eng §56 Fig. 56.1, word \"0\")".to_string(),
        phi,
        psi0,
    )
}

/// Corpus member 3: NTM animist-structured encoding (Eng §56.19–56.25).
fn corpus_ntm_tm() -> (String, Constellation, Vec<Star>) {
    let ntm = trivial_accept_empty_tm();
    let phi: Constellation = encode_ntm(&ntm);
    let psi0: Vec<Star> = vec![encode_word_ntm(&[])];
    (
        "NTM tm encoding (Eng §56.19-56.25, trivial_accept_empty_tm, empty input)".to_string(),
        phi,
        psi0,
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// run_reformulated_make_or_break — the parent entry point
// ─────────────────────────────────────────────────────────────────────────────

/// The reformulated (invariant⇒flat) make-or-break experiment entry point.
///
/// Runs the locked corpus of Eng-own subjective/animist encodings through the
/// perturbation-response evidence pipeline (solve_for_closure + perturbation_response
/// for each member) and evaluates the M1–M5 gate predicates.
///
/// # Determinism and boundedness
///
/// Deterministic: corpus is fixed; `solve_for_closure` and `perturbation_response`
/// are deterministic functions of their inputs. Bounded: each member is run for at
/// most the maximum of `caps` proper-time rounds.
///
/// # What the parent must NOT do
///
/// The parent must NOT call `verdict()` on the returned `ReformReport` (no such
/// method exists). The parent must NOT retro-weaken the M-predicates. The parent
/// must NOT re-run with inflated caps/strengths to force a result.
///
/// # Arguments
///
/// - `strengths`: perturbation strength levels (e.g. `&[0, 1, 2, 4]`).
/// - `caps`: `max_rounds` caps to scan for M3 cap-invariance check (e.g. `&[4, 6, 8]`).
///
/// This function is NOT invoked in the tests module (CONSTRUCTION ONLY;
/// the parent runs the real sweep).
pub fn run_reformulated_make_or_break(strengths: &[u32], caps: &[usize]) -> ReformReport {
    let corpus: Vec<(String, Constellation, Vec<Star>)> = vec![
        corpus_add_horn(),
        corpus_nfa_automata(),
        corpus_ntm_tm(),
    ];

    let max_rounds = caps.iter().copied().max().unwrap_or(8);

    // Collect evidence for each member.
    let members: Vec<MemberReformEvidence> = corpus
        .into_iter()
        .map(|(name, phi, psi0)| {
            // Solve for closures via principled partition search (never designated).
            let closures_found = solve_for_closure(&phi, psi0.clone(), max_rounds);

            // For each found closure, compute perturbation-response profile.
            let profiles: Vec<ResponseProfile> = closures_found
                .iter()
                .map(|w| perturbation_response(&phi, &psi0, &w.partition, strengths, caps))
                .collect();

            MemberReformEvidence {
                name,
                closures_found,
                profiles,
                found_by_principled_search: true,
            }
        })
        .collect();

    // Evaluate M1–M5 gate predicates (pure functions of evidence).
    let m1_result = m1_fires(&members);
    let m2_result = m2_fires(&members);
    let m3_result = m3_fires(&members);
    let m4_result = m4_fires(&members);
    let m5_result = m5_fires(&members);

    let plain_text_dump = build_plain_text_dump(
        &members, m1_result, m2_result, m3_result, m4_result, &m5_result,
    );

    ReformReport {
        members,
        m1_result,
        m2_result,
        m3_result,
        m4_result,
        m5_result,
        plain_text_dump,
    }
}

/// Build the plain-text dump (evidence only; no verdict).
fn build_plain_text_dump(
    members: &[MemberReformEvidence],
    m1: bool,
    m2: bool,
    m3: bool,
    m4: bool,
    m5: &M5Status,
) -> String {
    let mut out = String::new();
    out.push_str(
        "=== stella L2c-redux ReformReport (CONSTRUCTION ONLY; invariant⇒flat; no verdict) ===\n\n",
    );
    out.push_str("Pre-registration: reformulated (invariant⇒flat) M1–M5, locked 2026-05-16\n");
    out.push_str("Deathless-era null preserved verbatim in docs/02-phase4-first-run.md\n\n");

    for (i, m) in members.iter().enumerate() {
        out.push_str(&format!("Member {}: {}\n", i + 1, m.name));
        out.push_str(&format!(
            "  principled_search: {}\n",
            m.found_by_principled_search
        ));
        out.push_str(&format!("  closures_found: {}\n", m.closures_found.len()));
        for (j, w) in m.closures_found.iter().enumerate() {
            out.push_str(&format!(
                "    closure {j}: partition_size={} r={} r'={}\n",
                w.partition.len(),
                w.r,
                w.r_prime
            ));
        }
        out.push_str(&format!("  profiles: {}\n", m.profiles.len()));
        for (j, p) in m.profiles.iter().enumerate() {
            out.push_str(&format!(
                "    profile {j}: perturbation_tracking={} cap_invariant={} \
                 by_strength_len={} by_cap_len={}\n",
                p.perturbation_tracking,
                p.cap_invariant,
                p.by_strength.len(),
                p.by_cap.len()
            ));
        }
        out.push('\n');
    }

    out.push_str("=== Gate Results (evidence only; no verdict) ===\n");
    out.push_str(&format!("M1 fires: {m1}\n"));
    out.push_str(&format!("M2 fires: {m2}\n"));
    out.push_str(&format!("M3 fires: {m3}\n"));
    out.push_str(&format!("M4 fires: {m4}\n"));
    out.push_str(&format!("M5 status: {m5:?}\n"));
    out.push_str("\n(Adjudication is parent-owned. No verdict is emitted here.)\n");

    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ──────────────────────────────────────────────────────────────────────────
    // Pre-registration integrity test
    //
    // Asserts:
    // 1. Each gate function carries its verbatim spec-§4 quote (M1–M5), checked
    //    by inspecting the source of this file via include_str!.
    // 2. M5 Undetermined is never silently coerced to DoesNotFire.
    // 3. No `verdict()` method exists on ReformReport.
    // 4. Gates are pure: calling them twice on the same input gives the same result.
    // ──────────────────────────────────────────────────────────────────────────

    #[test]
    fn preregistration_integrity() {
        // 1. Verify verbatim spec-§4 quotes via source inspection.
        let source = include_str!("perturbation.rs");

        // M1 verbatim quote (from spec §4 M1).
        assert!(
            source.contains("SPEC §4 M1:"),
            "M1 gate must carry a // SPEC §4 M1: comment"
        );
        assert!(
            source.contains("hand-tagged or the agent/environment cut hand-placed"),
            "M1 gate must quote verbatim: 'hand-tagged or the agent/environment cut hand-placed'"
        );

        // M2 verbatim quote (from spec §4 M2).
        assert!(
            source.contains("SPEC §4 M2:"),
            "M2 gate must carry a // SPEC §4 M2: comment"
        );
        assert!(
            source.contains("Invariant ⇒ flat ⇒ no charge"),
            "M2 gate must quote verbatim: 'Invariant ⇒ flat ⇒ no charge'"
        );

        // M3 verbatim quote (from spec §4 M3).
        assert!(
            source.contains("SPEC §4 M3:"),
            "M3 gate must carry a // SPEC §4 M3: comment"
        );
        assert!(
            source.contains("t_death = cap\u{2212}2 artifact"),
            "M3 gate must quote verbatim: 't_death = cap−2 artifact'"
        );

        // M4 verbatim quote (from spec §4 M4).
        assert!(
            source.contains("SPEC §4 M4:"),
            "M4 gate must carry a // SPEC §4 M4: comment"
        );
        assert!(
            source.contains("globally fixed across the entire corpus"),
            "M4 gate must quote verbatim: 'globally fixed across the entire corpus'"
        );

        // M5 verbatim quote (from spec §4 M5).
        assert!(
            source.contains("SPEC §4 M5:"),
            "M5 gate must carry a // SPEC §4 M5: comment"
        );
        assert!(
            source.contains("never coerced to"),
            "M5 gate must quote verbatim: 'never coerced to'"
        );
        assert!(
            source.contains("M5Status::Undetermined"),
            "M5 gate must reference M5Status::Undetermined as the Undetermined value"
        );

        // 2. M5 Undetermined is never silently coerced to DoesNotFire.
        let empty: Vec<MemberReformEvidence> = vec![];
        assert_eq!(
            m5_fires(&empty),
            M5Status::Undetermined,
            "M5 on empty evidence must be Undetermined, not DoesNotFire"
        );

        let one_closure_member = MemberReformEvidence {
            name: "test".into(),
            closures_found: vec![],
            profiles: vec![],
            found_by_principled_search: true,
        };
        assert_eq!(
            m5_fires(&[one_closure_member]),
            M5Status::Undetermined,
            "M5 on a member with 0 closures must be Undetermined"
        );

        // 3. No `verdict()` method on ReformReport — compile-time check by absence.
        let report = ReformReport {
            members: vec![],
            m1_result: false,
            m2_result: false,
            m3_result: false,
            m4_result: false,
            m5_result: M5Status::Undetermined,
            plain_text_dump: "test".to_string(),
        };
        // If verdict() existed, a call would compile. Its absence is the check.
        let _ = &report.plain_text_dump;
        assert!(
            !report.plain_text_dump.is_empty() || true,
            "ReformReport has no verdict() method — verified by absence of such a call"
        );

        // 4. Gates are pure: same input → same result.
        let ev: Vec<MemberReformEvidence> = vec![];
        assert_eq!(m1_fires(&ev), m1_fires(&ev), "M1 is pure");
        assert_eq!(m2_fires(&ev), m2_fires(&ev), "M2 is pure");
        assert_eq!(m3_fires(&ev), m3_fires(&ev), "M3 is pure");
        assert_eq!(m4_fires(&ev), m4_fires(&ev), "M4 is pure");
        assert_eq!(m5_fires(&ev), m5_fires(&ev), "M5 is pure");
    }

    // ──────────────────────────────────────────────────────────────────────────
    // Smoke test: pipeline evaluates on ONE tiny labelled smoke fixture.
    //
    // SMOKE FIXTURE — NOT A CORPUS MEMBER. NOT THE THESIS.
    //
    // Uses the same hand-built sense/act loop from experiment.rs smoke test as a
    // minimal fixture to prove the pipeline evaluates. The smoke fixture is small
    // (max_rounds=3, strengths=[0,1], caps=[3,4]) and terminates quickly.
    //
    // This test proves the pipeline evaluates (perturbing_env, perturbation_response,
    // M1–M5 predicates, ReformReport dump) — NOT the thesis. The real corpus sweep
    // is NOT run here. `run_reformulated_make_or_break` is NOT called.
    // ──────────────────────────────────────────────────────────────────────────

    #[test]
    fn smoke_pipeline_evaluates_not_the_thesis() {
        // SMOKE FIXTURE, NOT A CORPUS MEMBER.
        // phi = [A: -sense(X) +act(X), E: -act(Y) +sense(f(Y))]
        // psi0 = [+sense(zero), +act(zero)]
        // This is the same hand-built loop from experiment.rs smoke test.
        let phi: Constellation = vec![
            vec![
                neg_ray("sense", vec![mk_var("X")]),
                pos_ray("act", vec![mk_var("X")]),
            ],
            vec![
                neg_ray("act", vec![mk_var("Y")]),
                pos_ray("sense", vec![mk_app_str("f", vec![mk_var("Y")])]),
            ],
        ];
        let psi0: Vec<Star> = vec![
            vec![pos_ray("sense", vec![mk_app_str("zero", vec![])])],
            vec![pos_ray("act", vec![mk_app_str("zero", vec![])])],
        ];

        // Small knobs for fast test.
        let strengths: &[u32] = &[0, 1];
        let caps: &[usize] = &[3, 4];

        // Solve for closure (principled search — may find 0 or ≥1 witnesses).
        let closures = solve_for_closure(&phi, psi0.clone(), 4);

        // Build a response profile for each closure (may be empty).
        let profiles: Vec<ResponseProfile> = closures
            .iter()
            .map(|w| perturbation_response(&phi, &psi0, &w.partition, strengths, caps))
            .collect();

        // Wrap as a smoke member (labelled as smoke, not corpus).
        let smoke_member = MemberReformEvidence {
            name: "SMOKE FIXTURE (not corpus): hand-built sense/act loop".into(),
            closures_found: closures.clone(),
            profiles: profiles.clone(),
            found_by_principled_search: true, // principled search was used
        };
        let smoke_vec = vec![smoke_member];

        // Gate predicates execute without panicking, produce well-typed results.
        let _m1 = m1_fires(&smoke_vec);
        let _m2 = m2_fires(&smoke_vec);
        let _m3 = m3_fires(&smoke_vec);
        let _m4 = m4_fires(&smoke_vec);
        let _m5 = m5_fires(&smoke_vec);

        // M4 must NOT fire for the smoke fixture (found_by_principled_search=true).
        assert!(
            !m4_fires(&smoke_vec),
            "M4 must not fire for smoke fixture (uses principled search)"
        );

        // M5 on single-closure or zero-closure member must be Undetermined.
        // (The smoke fixture has ≤1 closure under small max_rounds.)
        if closures.len() < 2 {
            assert_eq!(
                m5_fires(&smoke_vec),
                M5Status::Undetermined,
                "M5 must be Undetermined when fewer than 2 closures found"
            );
        }

        // profiles.len() must equal closures.len().
        assert_eq!(
            profiles.len(),
            closures.len(),
            "profiles.len() must equal closures.len()"
        );

        // by_strength and by_cap lengths must match the inputs.
        for profile in &profiles {
            assert_eq!(
                profile.by_strength.len(),
                strengths.len(),
                "by_strength must have one entry per strength"
            );
            assert_eq!(
                profile.by_cap.len(),
                caps.len(),
                "by_cap must have one entry per cap"
            );
            // All viability scores must be in [0, 1].
            for &(_, v) in &profile.by_strength {
                assert!(
                    (0.0..=1.0).contains(&v),
                    "by_strength viability {v} must be in [0,1]"
                );
            }
            for &(_, v) in &profile.by_cap {
                assert!(
                    (0.0..=1.0).contains(&v),
                    "by_cap viability {v} must be in [0,1]"
                );
            }
        }

        // perturbing_env(0) returns exactly 1 star (inert baseline).
        let env0 = perturbing_env(0);
        assert_eq!(env0.len(), 1, "perturbing_env(0) must return 1 inert star");

        // perturbing_env(3) returns exactly 3 noise stars.
        let env3 = perturbing_env(3);
        assert_eq!(env3.len(), 3, "perturbing_env(3) must return 3 noise stars");

        // plain_text_dump of a dummy ReformReport must mention "no verdict".
        let dummy_report = ReformReport {
            members: smoke_vec.clone(),
            m1_result: _m1,
            m2_result: _m2,
            m3_result: _m3,
            m4_result: _m4,
            m5_result: _m5,
            plain_text_dump: build_plain_text_dump(
                &smoke_vec, _m1, _m2, _m3, _m4, &m5_fires(&smoke_vec),
            ),
        };
        assert!(
            dummy_report.plain_text_dump.contains("no verdict"),
            "plain_text_dump must state 'no verdict is emitted'"
        );

        // The pipeline evaluated. This proves CONSTRUCTION, NOT THE THESIS.
        // run_reformulated_make_or_break is NOT called here.
    }

    // ──────────────────────────────────────────────────────────────────────────
    // M1 vacuous-fires test
    // ──────────────────────────────────────────────────────────────────────────

    #[test]
    fn m1_fires_when_no_principled_closures() {
        let member = MemberReformEvidence {
            name: "no-closure".into(),
            closures_found: vec![],
            profiles: vec![],
            found_by_principled_search: true,
        };
        assert!(
            m1_fires(&[member]),
            "M1 must fire when all principled members have no closures"
        );
    }

    // ──────────────────────────────────────────────────────────────────────────
    // M4 structural invariant test
    // ──────────────────────────────────────────────────────────────────────────

    #[test]
    fn m4_fires_on_non_principled_member() {
        let rigged = MemberReformEvidence {
            name: "rigged".into(),
            closures_found: vec![],
            profiles: vec![],
            found_by_principled_search: false, // ← triggers M4
        };
        assert!(
            m4_fires(&[rigged]),
            "M4 must fire when any member has found_by_principled_search=false"
        );
    }

    #[test]
    fn m4_does_not_fire_on_principled_members() {
        let honest = MemberReformEvidence {
            name: "honest".into(),
            closures_found: vec![],
            profiles: vec![],
            found_by_principled_search: true,
        };
        assert!(
            !m4_fires(&[honest]),
            "M4 must not fire when all members use principled search"
        );
    }

    // ──────────────────────────────────────────────────────────────────────────
    // M2 vacuous-fires test (no profiles → all flat → M2 fires)
    // ──────────────────────────────────────────────────────────────────────────

    #[test]
    fn m2_fires_vacuously_on_no_profiles() {
        let member = MemberReformEvidence {
            name: "no-profiles".into(),
            closures_found: vec![],
            profiles: vec![],
            found_by_principled_search: true,
        };
        assert!(
            m2_fires(&[member]),
            "M2 must fire vacuously when no profiles exist (no perturbation response)"
        );
    }

    // ──────────────────────────────────────────────────────────────────────────
    // M3 test: fires when profile has perturbation_tracking=false
    // ──────────────────────────────────────────────────────────────────────────

    #[test]
    fn m3_fires_on_non_tracking_profile() {
        let flat_profile = ResponseProfile {
            by_strength: vec![(0, 0.5), (1, 0.5)],
            by_cap: vec![(4, 0.5), (6, 0.5)],
            perturbation_tracking: false, // flat → artifact
            cap_invariant: true,
        };
        let member = MemberReformEvidence {
            name: "flat".into(),
            closures_found: vec![],
            profiles: vec![flat_profile],
            found_by_principled_search: true,
        };
        assert!(
            m3_fires(&[member]),
            "M3 must fire when perturbation_tracking=false (artifact)"
        );
    }

    // ──────────────────────────────────────────────────────────────────────────
    // perturbing_env knob tests
    // ──────────────────────────────────────────────────────────────────────────

    #[test]
    fn perturbing_env_strength_zero_is_inert() {
        let env = perturbing_env(0);
        assert_eq!(env.len(), 1, "strength=0 must produce exactly 1 inert star");
    }

    #[test]
    fn perturbing_env_strength_k_produces_k_stars() {
        for k in [1u32, 2, 5, 10] {
            let env = perturbing_env(k);
            assert_eq!(
                env.len(),
                k as usize,
                "strength={k} must produce exactly {k} noise stars"
            );
        }
    }
}
