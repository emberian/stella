//! Online recurrence / loop detector over an execution trace.
//!
//! This sits directly on `crate::antiunify`'s homeomorphic-embedding
//! substrate. It does **not** accelerate or supercompile anything — it only
//! *detects* a recurrent unfolding and computes the generalization a later
//! speculative pass would consume.
//!
//! ## What "the whistle" is
//!
//! `antiunify::embeds(s, t)` is Kruskal homeomorphic embedding `s ⊴ t`. It is
//! a *well-quasi-order* on terms over a finite signature: in any infinite
//! sequence `t₀, t₁, …` there necessarily exist `i < j` with `tᵢ ⊴ tⱼ`. So if
//! we scan an execution trace and find an earlier state homeomorphically
//! embedded in a later one, that pair is a structural "this could unfold
//! forever" alarm — the supercompiler whistle. Detecting it (and producing a
//! generalization that covers both ends of the embedded pair) is the
//! foundation a recurrence-accelerating pass builds on; that pass is **not**
//! in this module.
//!
//! ## Generalization choice
//!
//! For a whistling pair `(earlier, later)` we report:
//! - `generalization`: the **rigid** (LCS) anti-unification skeleton
//!   `antiunify::rigid_generalize(earlier, later).skeleton`. Rigid AU is used
//!   rather than plain `lgg` because it is deterministic on head-matched
//!   arity-mismatched spines and degenerates to `lgg` on equal-arity
//!   structure, so it is never *less* general than `lgg` on the cases
//!   `lgg` handles. (`lgg` is still available and is what
//!   [`is_sound_generalization`]'s "lgg of two terms generalizes both" test
//!   exercises.)
//! - `recurrence`: `antiunify::affine_recurrence(earlier, later)` — `Some`
//!   only when that conservative embedding-gated + rigid filter additionally
//!   nominates the pair as an *accelerable affine step*. It is legitimately
//!   `None` for many real whistles (e.g. the trivial `f(a) ⊴ f(g(a))` shape
//!   whose rigid skeleton is a bare variable); a `None` recurrence does **not**
//!   weaken the whistle itself.
//!
//! ## One-unital NULLARY caution (carried over from `antiunify`)
//!
//! `antiunify`'s rigid generalizer documents a HARD CAUTION: anti-unification
//! *modulo unit* is finitary for one unital symbol but **NULLARY** for ≥2
//! (no minimal complete set of generalizers need exist). This module never
//! does AU-modulo-units; it only ever calls the syntactic/rigid `antiunify`
//! APIs. The practical hazard for a *detector* is reporting a degenerate
//! whole-term-variable "generalization" as if it abstracted a real common
//! context. [`is_sound_generalization`] is total and still *correct* on a
//! bare-variable `g` (a lone variable embeds nothing but itself, so
//! genuinely-distinct instances are rejected) — i.e. a bogus nullary
//! generalization is *detectable*, not silently accepted. A regression test
//! pins this on a ≥2-distinct-unit case.

use rustc_hash::FxHashMap;

use crate::antiunify;
use crate::term::{get, TermData, TermId, Var};

/// A blown whistle: an earlier trace state homeomorphically embedded in a
/// later one, plus the generalization that covers the embedded pair.
#[derive(Debug, Clone)]
pub struct Whistle {
    /// Trace index of the earlier (embedded) state.
    pub earlier: usize,
    /// Trace index of the later state it embeds into (`later > earlier`).
    pub later: usize,
    /// Rigid anti-unification skeleton of `trace[earlier]` and
    /// `trace[later]` (the candidate per-iteration context).
    pub generalization: TermId,
    /// `affine_recurrence(trace[earlier], trace[later])` — `Some` only when
    /// the conservative accelerable-affine-step filter also nominates the
    /// pair. `None` is common and does not weaken the whistle.
    pub recurrence: Option<TermId>,
}

/// Build the [`Whistle`] for an already-known embedding pair `i < j`.
fn whistle_for(trace: &[TermId], i: usize, j: usize) -> Whistle {
    let g = antiunify::rigid_generalize(trace[i], trace[j]);
    Whistle {
        earlier: i,
        later: j,
        generalization: g.skeleton,
        recurrence: antiunify::affine_recurrence(trace[i], trace[j]),
    }
}

/// Full-scan recurrence detection.
///
/// Returns the **first** pair `(i, j)` with `i < j` and
/// `antiunify::embeds(trace[i], trace[j])` — the earliest blown whistle.
/// "First" is lexicographic by `(j, i)`: we walk `j` forward and, for each
/// `j`, scan `i` from `0` upward, so the reported pair is the one a
/// left-to-right online scanner would hit first (smallest `j`, then smallest
/// `i`). Returns `None` if no state is embedded in any later state (no false
/// whistle) and for traces of length < 2 (nothing to compare).
pub fn detect_recurrence(trace: &[TermId]) -> Option<Whistle> {
    for j in 1..trace.len() {
        for i in 0..j {
            if antiunify::embeds(trace[i], trace[j]) {
                return Some(whistle_for(trace, i, j));
            }
        }
    }
    None
}

/// Windowed (online) recurrence detection.
///
/// Like [`detect_recurrence`] but, for each state `j`, only compares against
/// the at-most-`window` immediate predecessors `i ∈ [j-window, j)`. This is
/// the realistic streaming use: O(window) work per new state instead of
/// O(j). It can therefore **miss** an embedding whose two endpoints are more
/// than `window` apart that the full scan would find — a deliberate
/// online/precision tradeoff (a test pins exactly this gap). `window == 0`
/// disables detection (no predecessors are ever compared) and returns `None`.
pub fn detect_in_window(trace: &[TermId], window: usize) -> Option<Whistle> {
    for j in 1..trace.len() {
        let lo = j.saturating_sub(window);
        for i in lo..j {
            if antiunify::embeds(trace[i], trace[j]) {
                return Some(whistle_for(trace, i, j));
            }
        }
    }
    None
}

/// One-directional match (subsumption): is `inst` a *substitution instance*
/// of the pattern `pat`? Variables of `pat` are holes bound consistently
/// (each `pat` variable maps to exactly one `inst` subterm). `pat` `App`
/// nodes must match `inst` head & arity exactly (a variable in `pat` matches
/// any `inst` subterm; a variable in `inst` is just an ordinary nullary
/// position unless aligned with a `pat` variable). This is the precise
/// "`pat` is ≥-general than `inst`" relation (`∃θ. pat·θ ≡ inst`), which is
/// what a sound generalization must satisfy — strictly stronger than the
/// homeomorphic-embedding whistle.
fn matches(pat: TermId, inst: TermId, bind: &mut FxHashMap<Var, TermId>) -> bool {
    match get(pat) {
        TermData::Var(pv) => {
            if let Some(&bound) = bind.get(&pv) {
                bound == inst // consistent reuse (hash-cons identity)
            } else {
                bind.insert(pv, inst);
                true
            }
        }
        TermData::App(pf, pargs) => match get(inst) {
            TermData::App(inf, iargs) => {
                pf == inf
                    && pargs.len() == iargs.len()
                    && pargs
                        .iter()
                        .zip(iargs.iter())
                        .all(|(&p, &i)| matches(p, i, bind))
            }
            TermData::Var(_) => false, // structured pattern vs bare var ⇒ no
        },
    }
}

/// Soundness check for a candidate generalization `g` against the concrete
/// states `instances` it claims to abstract.
///
/// **Exact predicate implemented:** `g` is a sound generalization of
/// `instances` iff
///
/// 1. `instances` is non-empty, **and**
/// 2. for every `x ∈ instances`, `x` is a *substitution instance* of `g`
///    modulo α — formally `∃θ. canonical(g)·θ ≡ canonical(x)`, decided by the
///    one-directional [`matches`] above on the α-canonical forms.
///
/// This is the standard "`g` is more general than every state it abstracts"
/// soundness condition (`g`'s variables are holes filled per state). Modulo-α
/// (`canonical` on both sides) makes it stable under variable renaming, which
/// is the form the engine produces. It is strictly stronger than the
/// homeomorphic-embedding whistle (every match is an embedding; not
/// conversely), which is the right asymmetry for a *soundness* gate. Total:
/// well-defined for any `g` (variable or `App`) and any instance.
///
/// Consequences worth stating plainly:
/// - A **too-specific** candidate (a concrete state, or any `g` that does not
///   subsume some instance) is rejected.
/// - A **bare-variable** `g` matches *anything* (the lone hole binds the
///   whole instance), so it is trivially "sound" — which is *correct* set-
///   theoretically but useless as a detector signal. Distinguishing the
///   degenerate nullary case is the job of [`is_trivial_generalization`], not
///   of soundness; the module's one-unital test pins that the detector never
///   *reports* such a `g` for genuinely disjoint structural states (no
///   whistle fires there, so no bogus `g` is produced in the first place).
/// - The empty instance set is rejected (vacuous truth would let any `g`
///   pass, which is not a useful soundness statement for a detector).
pub fn is_sound_generalization(g: TermId, instances: &[TermId]) -> bool {
    if instances.is_empty() {
        return false;
    }
    let gc = antiunify::canonical(g);
    instances.iter().all(|&x| {
        let mut bind = FxHashMap::default();
        matches(gc, antiunify::canonical(x), &mut bind)
    })
}

/// `true` iff `t` is a single variable (used only by tests / callers that
/// want to flag a degenerate nullary generalization explicitly).
pub fn is_trivial_generalization(t: TermId) -> bool {
    matches!(get(t), TermData::Var(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{mk_app_str, mk_var};

    fn c(n: &str) -> TermId {
        mk_app_str(n, vec![])
    }
    fn app(h: &str, a: Vec<TermId>) -> TermId {
        mk_app_str(h, a)
    }
    fn v(n: &str) -> TermId {
        mk_var(n)
    }

    /// POSITIVE — a clearly recurrent trace `f(a)`, `f(g(a))`, `f(g(g(a)))`.
    /// `f(a) ⊴ f(g(a))` by DIVE, so the whistle blows on the very first pair
    /// `(0, 1)`. The rigid generalization is non-trivial (an `App`, not a
    /// lone var) and soundly generalizes the embedded slice.
    #[test]
    fn positive_recurrent_trace_fires_first_pair() {
        let t0 = app("f", vec![c("a")]);
        let t1 = app("f", vec![app("g", vec![c("a")])]);
        let t2 = app("f", vec![app("g", vec![app("g", vec![c("a")])])]);
        let trace = vec![t0, t1, t2];

        let w = detect_recurrence(&trace).expect("recurrent trace must whistle");
        assert_eq!((w.earlier, w.later), (0, 1), "first blown whistle is (0,1)");

        // Non-trivial generalization: rigid skeleton is an App (shared `f`),
        // not a bare variable.
        assert!(
            !is_trivial_generalization(w.generalization),
            "generalization of f(a)/f(g(a)) must keep the shared f context"
        );

        // Sound over the embedded slice trace[0..=1].
        assert!(
            is_sound_generalization(w.generalization, &trace[w.earlier..=w.later]),
            "rigid skeleton must generalize both endpoints of the embedded pair"
        );
        // And over the whole recurrent trace (every state embeds the f-context).
        assert!(is_sound_generalization(w.generalization, &trace));
    }

    /// POSITIVE — the embedding-shaped `add`-unfold (an *accumulating*
    /// argument that grows by a fixed `s` context each step). This is
    /// `affine_recurrence`'s textbook case, so `Whistle::recurrence` is
    /// additionally `Some`.
    ///
    /// (Note: the *decreasing-counter* shape `add(s(s z),y)`,
    /// `add(s z,s y)`, `add(z,s(s y))` does NOT homeomorphically embed
    /// pairwise — the first argument strictly shrinks, so no earlier state
    /// is embedded in a later one. The wqo guarantee is asymptotic over an
    /// *infinite* sequence, not a property of every finite shrinking prefix;
    /// a recurrence detector legitimately reports no whistle there. We
    /// therefore drive the accumulating shape, where the whistle genuinely
    /// blows.)
    #[test]
    fn positive_add_unfold_also_yields_recurrence() {
        // add(s X, Y, s Z)  →  add(s(s X), Y, s(s Z)) : args 1 & 3 grow by a
        // fixed `s` context (the accumulating-parameter recurrence).
        let prev = app("add", vec![app("s", vec![v("X")]), v("Y"), app("s", vec![v("Z")])]);
        let cur = app(
            "add",
            vec![
                app("s", vec![app("s", vec![v("X")])]),
                v("Y"),
                app("s", vec![app("s", vec![v("Z")])]),
            ],
        );
        let w = detect_recurrence(&[prev, cur]).expect("add-unfold must whistle");
        assert_eq!((w.earlier, w.later), (0, 1));
        assert!(
            w.recurrence.is_some(),
            "add-unfold is affine_recurrence's textbook case ⇒ recurrence Some"
        );
        assert!(
            is_sound_generalization(w.generalization, &[prev, cur]),
            "rigid skeleton must subsume both endpoints of the unfold"
        );

        // The decreasing-counter shape does NOT whistle on this finite prefix
        // (arg-1 shrinks ⇒ no pairwise homeomorphic embedding) — documented
        // above; assert the detector correctly stays silent.
        let d0 = app("add", vec![app("s", vec![app("s", vec![c("z")])]), v("y")]);
        let d1 = app("add", vec![app("s", vec![c("z")]), app("s", vec![v("y")])]);
        let d2 = app("add", vec![c("z"), app("s", vec![app("s", vec![v("y")])])]);
        assert!(
            detect_recurrence(&[d0, d1, d2]).is_none(),
            "strictly-shrinking counter ⇒ no pairwise embedding ⇒ no whistle"
        );
    }

    /// NEGATIVE — pairwise-unrelated terms: no earlier state is
    /// homeomorphically embedded in any later one ⇒ no false whistle.
    #[test]
    fn negative_unrelated_trace_no_whistle() {
        let trace = vec![
            c("alpha"),
            app("beta", vec![c("q")]),
            app("gamma", vec![c("r"), c("s")]),
            app("delta", vec![app("eps", vec![c("w")])]),
        ];
        assert!(
            detect_recurrence(&trace).is_none(),
            "unrelated terms must not produce a spurious whistle"
        );
        // Degenerate sizes are total and yield None.
        assert!(detect_recurrence(&[]).is_none());
        assert!(detect_recurrence(&[c("x")]).is_none());
    }

    /// `is_sound_generalization`: a too-specific candidate is rejected; the
    /// `lgg` of two terms is accepted as a sound generalization of both.
    #[test]
    fn soundness_rejects_too_specific_accepts_lgg() {
        let i0 = app("f", vec![c("a")]);
        let i1 = app("f", vec![c("b")]);

        // Too specific: `f(a)` is NOT >= general than `f(b)` (a ⋬ b), reject.
        assert!(
            !is_sound_generalization(i0, &[i0, i1]),
            "a concrete instance is not a sound generalization of a different one"
        );

        // lgg(f(a), f(b)) = f(Z); f(Z) ⊴ f(a) and f(Z) ⊴ f(b) modulo α.
        let lg = antiunify::lgg(i0, i1);
        assert!(
            is_sound_generalization(lg.skeleton, &[i0, i1]),
            "the lgg of two terms must be a sound generalization of both"
        );

        // Empty instance set ⇒ rejected (no vacuous pass).
        assert!(!is_sound_generalization(lg.skeleton, &[]));

        // Reflexive single instance: a term generalizes itself.
        assert!(is_sound_generalization(i0, &[i0]));
    }

    /// `detect_in_window` with a small window MISSES an out-of-window
    /// embedding that the full scan finds — the documented online/precision
    /// tradeoff. Trace: `f(a)` at index 0, then three unrelated fillers, then
    /// `f(g(a))` at index 4 which embeds index 0 (distance 4). A window of 2
    /// never compares index 4 against index 0.
    #[test]
    fn window_misses_far_embedding_that_full_scan_finds() {
        let t0 = app("f", vec![c("a")]);
        let trace = vec![
            t0,
            c("noise1"),
            c("noise2"),
            c("noise3"),
            app("f", vec![app("g", vec![c("a")])]),
        ];

        // Full scan finds the (0, 4) embedding.
        let full = detect_recurrence(&trace).expect("full scan finds far embedding");
        assert_eq!((full.earlier, full.later), (0, 4));

        // Window of 2 only ever compares (j-2 .. j); 4 vs 0 is never checked,
        // and the noise constants don't embed each other ⇒ None.
        assert!(
            detect_in_window(&trace, 2).is_none(),
            "small window must miss the distance-4 embedding (online tradeoff)"
        );

        // A window wide enough to span the gap recovers the full-scan result.
        let w4 = detect_in_window(&trace, 4).expect("window>=4 spans the gap");
        assert_eq!((w4.earlier, w4.later), (0, 4));

        // window == 0 never compares anything.
        assert!(detect_in_window(&trace, 0).is_none());
    }

    /// One-unital NULLARY caution (carried over from `antiunify`'s HARD
    /// CAUTION). AU *modulo unit* is finitary for one unital symbol but
    /// NULLARY for ≥2. We never do AU-modulo-units; the practical hazard for
    /// a *detector* is a degenerate **bare-variable** ("nullary") skeleton
    /// being reported as if it were a real shared context.
    ///
    /// Take two structurally-disjoint states whose only common anti-unifier
    /// is a single variable (the degenerate nullary skeleton). Pin three
    /// facts:
    ///
    /// 1. The lone-variable skeleton IS flagged by
    ///    [`is_trivial_generalization`] — it is *recognisable* as nullary,
    ///    not mistaken for a context. (A bare variable is, set-theoretically,
    ///    a perfectly *sound* generalizer of anything — `is_sound_*` will and
    ///    should accept it; soundness is the wrong tool to reject it, the
    ///    triviality flag is the right one.)
    /// 2. The detector does **not** whistle on the disjoint pair (neither
    ///    embeds the other), so no `Whistle` carrying this bogus skeleton is
    ///    produced in the first place — the silent-nullary path is closed at
    ///    the source.
    /// 3. When a whistle *does* legitimately fire, its `generalization` is a
    ///    real `App` context, never the nullary bare variable.
    #[test]
    fn two_unit_case_no_silent_nullary_generalization() {
        // Two distinct unital symbols / disjoint structures.
        let unit_a = app("ctxA", vec![c("u1")]);
        let unit_b = app("ctxB", vec![c("u2")]);

        // (1) lgg/rigid skeleton is a bare variable — recognisably nullary.
        let g = antiunify::lgg(unit_a, unit_b);
        assert!(
            is_trivial_generalization(g.skeleton),
            "disjoint heads ⇒ lgg skeleton is a lone variable (nullary shape)"
        );
        let rg = antiunify::rigid_generalize(unit_a, unit_b);
        assert!(
            is_trivial_generalization(rg.skeleton),
            "rigid skeleton of disjoint heads is also the nullary bare var"
        );

        // (2) The disjoint pair does not whistle in either order ⇒ no Whistle
        // carrying the bogus nullary skeleton is ever produced.
        assert!(detect_recurrence(&[unit_a, unit_b]).is_none());
        assert!(detect_recurrence(&[unit_b, unit_a]).is_none());

        // (3) A genuine whistle reports a real App context, not the nullary
        // bare var: f(a) ⊴ f(g(a)) ⇒ generalization is an `f(...)` App.
        let w = detect_recurrence(&[
            app("f", vec![c("a")]),
            app("f", vec![app("g", vec![c("a")])]),
        ])
        .expect("embedding pair must whistle");
        assert!(
            !is_trivial_generalization(w.generalization),
            "a real whistle's generalization is an App context, never nullary"
        );
    }
}
