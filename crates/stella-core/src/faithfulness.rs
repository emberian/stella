//! Stage 0 — the result-compatibility faithfulness validator (docs/09 §A).
//!
//! A **separate** result-compatibility validator: not part of the unifier and
//! not invoked by it. The unifier under test could be arbitrarily wrong; this
//! module's only job is to *catch* a wrong fast result against the reference
//! oracle by comparing the two final interaction spaces.
//!
//! What it computes (docs/09 §A.2):
//!
//! 1. `conceal_and_filter` each side — the ɟ-concealed *visible answer set*:
//!    drop every star with a coloured ray, then drop empty stars
//!    (`concrete::conceal_and_filter`, the same operator
//!    `iex_tabled_result_eq_iex` and `evaluate.rs` already use).
//! 2. α-canonicalize each surviving star: `antiunify::canonical` of the star
//!    reified as one term `canonical(mk_app_str("⋆star", rays))` — exactly the
//!    existing `star_key` shape. α-equivalent stars ⇒ identical hash-consed
//!    `TermId` ⇒ O(1) compare.
//! 3. Compare the two as **multisets** of canonical-star `TermId`s (sorted
//!    `Vec<TermId>` equality).
//!
//! `psi_compatible` returns yes/no only — no equivalence witness (no MGU, no
//! renaming map, no diff) is constructed or retained (docs/09 §A.1). A witness
//! would be expensive and a second thing to keep faithful; the point is a
//! cheap *decision*.
//!
//! Definition (docs/09 §A.3): `reference` and `fast` are **ψ-compatible** iff
//! their ɟ-concealed visible answer sets are equal as multisets of α-canonical
//! stars. Deliberately ignored, by construction:
//!
//! * **Variable names / identities** — `canonical` collapses all α-variants to
//!   one `TermId`; result-equivalence permits MGUs that differ only by
//!   renaming.
//! * **ɟ-concealed scaffolding** — `conceal` removes every star with a
//!   coloured ray; intermediate machine/colour stars never enter the compare,
//!   only logician-visible answers.
//! * **Star / answer order** — multiset compare; constellation order and
//!   cross-star order do not matter. (Ray order *inside* one star *is*
//!   significant: `⋆star` wraps the ray list, so the per-star key is
//!   ray-order-sensitive — docs/09 Risk G.3. Sound, not maximally permissive.)
//!
//! Soundness (docs/09 §A.4): `psi_compatible` has **no false "compatible"** —
//! if `reference` and `fast` denote different visible answer multisets it
//! returns `false`.
//!
//! * `conceal_and_filter` is a deterministic pure function applied identically
//!   to both sides; it cannot mask a divergence in the visible (uncoloured)
//!   fragment, and divergences in the concealed fragment are by definition not
//!   observable answers (§49.44).
//! * `canonical` is a complete *and* sound α-invariant:
//!   `canonical(s)==canonical(t)` **iff** `s,t` are α-equivalent (tested in
//!   `antiunify`, including the negative `f(X,Y) ≠ f(X,X)` sharing case). Two
//!   stars compare equal **iff** genuinely α-equal — no conflation of
//!   structurally different stars.
//! * Multiset equality catches *count* divergence (a missing OR a duplicated
//!   answer), strictly stronger than the `subset ∧ subset` set-only test in
//!   `iex_tabled_result_eq_iex` / `evaluate.rs`, which cannot see a duplicated
//!   answer. The B0b duplicated-answer test is what earns the multiset choice.
//!
//! The validator can still return `false` on a result that is "morally fine
//! but differently shaped" only if the shape difference survives
//! conceal+canonical — i.e. a genuine difference in the visible answer
//! multiset. That is exactly the contract: conservative toward *catching*,
//! never toward *passing*.
//!
//! Persistence note: [`ObsRecord`] / [`record`] / [`obs_record_to_string`] are
//! the observational-equivalence corpus substrate (docs/07 §G — data we
//! currently discard). They are OPT-IN and INERT: this module never writes a
//! file. It only makes the artifact *capturable* as a stable text line.

use crate::antiunify::canonical;
use crate::concrete::conceal_and_filter;
use crate::constellation::Star;
use crate::term::{mk_app_str, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// Per-star canonical key + multiset of keys
// ─────────────────────────────────────────────────────────────────────────────

/// α-canonical key of one star: `canonical` of its rays reified as a single
/// term `⋆star(r₀, r₁, …)`. Identical to the in-tree `star_key`
/// (`interactive.rs`): α-equivalent stars ⇒ identical hash-consed `TermId`.
/// Ray-order-sensitive within a star by construction (docs/09 Risk G.3) — the
/// engine never reorders rays, so keys match in practice and the validator
/// stays sound (it can only ever *over*-report a divergence, never miss one).
fn star_key(star: &Star) -> TermId {
    canonical(mk_app_str("\u{22c6}star", star.clone()))
}

/// Sorted multiset of per-star canonical keys for an already-concealed
/// constellation. Sorting an interned-`TermId` (`u32`) vector is the
/// `Counter<TermId>`-equality of docs/09 §A.2 done as `O(n log n)` sort then
/// `O(n)` slice compare.
fn key_multiset(concealed: &[Star]) -> Vec<TermId> {
    let mut keys: Vec<TermId> = concealed.iter().map(star_key).collect();
    keys.sort_unstable_by_key(|t| t.0);
    keys
}

// ─────────────────────────────────────────────────────────────────────────────
// The decision predicate
// ─────────────────────────────────────────────────────────────────────────────

/// `reference` and `fast` are ψ-compatible: equal ɟ-concealed visible answer
/// sets as **multisets** of α-canonical stars. Decision-only — no witness is
/// built or retained (docs/09 §A.1–§A.4).
///
/// Mechanism (docs/09 §A.2): `conceal_and_filter` each side → `canonical` each
/// surviving star (reified as `⋆star(rays)`) → compare the two sorted
/// `Vec<TermId>` key multisets for equality.
///
/// Sound: never returns `true` when the visible answer multisets genuinely
/// differ (a missing, extra, *duplicated*, or structurally-changed visible
/// answer is always caught). Ignores variable names, ɟ-concealed scaffolding,
/// and cross-star order by construction.
pub fn psi_compatible(reference: &[Star], fast: &[Star]) -> bool {
    let rv = conceal_and_filter(reference);
    let fv = conceal_and_filter(fast);
    key_multiset(&rv) == key_multiset(&fv)
}

/// Alias for [`psi_compatible`] — docs/09 §A.1 lists `star_set_compatible` as
/// the same predicate under its constellation-level name.
pub fn star_set_compatible(reference: &[Star], fast: &[Star]) -> bool {
    psi_compatible(reference, fast)
}

// ─────────────────────────────────────────────────────────────────────────────
// Observational-equivalence corpus record (docs/07 §G substrate)
// ─────────────────────────────────────────────────────────────────────────────

/// One captured observation: a Φ-tag plus the α-canonical inputs and the
/// α-canonical ɟ-concealed visible answer multiset of a run. This is the data
/// docs/07 §G wants and the engine currently discards. Pure value; producing
/// it changes no engine state and writes no file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObsRecord {
    /// Caller-supplied Φ/corpus tag (e.g. `"horn-add(3,2)"`).
    pub phi_tag: String,
    /// Sorted multiset of α-canonical keys of the *input* Ψ stars (concealed
    /// identically to the output so the record is symmetric and stable).
    pub psi_in_keys: Vec<TermId>,
    /// Sorted multiset of α-canonical keys of the ɟ-concealed visible answer
    /// stars of the result. This is the quantity [`psi_compatible`] compares.
    pub answer_keys: Vec<TermId>,
}

/// Build an [`ObsRecord`] from a tag, the input Ψ, and a run result. The two
/// key multisets are computed with the *same* conceal+canonical pipeline as
/// [`psi_compatible`], so two records are answer-equivalent iff their
/// `answer_keys` are equal.
pub fn record(phi_tag: &str, psi_in: &[Star], result: &[Star]) -> ObsRecord {
    ObsRecord {
        phi_tag: phi_tag.to_string(),
        psi_in_keys: key_multiset(&conceal_and_filter(psi_in)),
        answer_keys: key_multiset(&conceal_and_filter(result)),
    }
}

/// A stable, std-only, serde-free textual line for an [`ObsRecord`]. Format is
/// deterministic (sorted `TermId` lists) so two answer-equivalent records emit
/// identical `ans=[…]` segments. Capturable by a caller; this module never
/// writes it anywhere.
pub fn obs_record_to_string(rec: &ObsRecord) -> String {
    let ids = |v: &[TermId]| -> String {
        let mut s = String::with_capacity(v.len() * 4 + 2);
        s.push('[');
        for (i, t) in v.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            s.push_str(&t.0.to_string());
        }
        s.push(']');
        s
    };
    format!(
        "obs phi={} in={} ans={}",
        rec.phi_tag,
        ids(&rec.psi_in_keys),
        ids(&rec.answer_keys)
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — docs/09 §A.5 (corpus harness) + §A.6 (Stage-0 bootstrap)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constellation::Constellation;
    use crate::interactive::{iex, iex_fast};
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::{mk_app_str, mk_var, Term};

    const GALAXY_PATH: &str = "/Users/ember/dev/embershot/src/galaxy.txt";

    fn var(x: &str) -> Term {
        mk_var(x)
    }
    fn app(f: &str, a: Vec<Term>) -> Term {
        mk_app_str(f, a)
    }
    fn cst(n: &str) -> Term {
        mk_app_str(n, vec![])
    }
    fn nat(n: usize) -> Term {
        let mut t = cst("0");
        for _ in 0..n {
            t = app("s", vec![t]);
        }
        t
    }

    // ── Corpora (the exact ones already in tree, so the gate is a drop-in) ──

    fn horn() -> (Constellation, Vec<Star>, usize) {
        let phi = vec![
            vec![pos_ray("add", vec![cst("0"), var("Y"), var("Y")])],
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray(
                    "add",
                    vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])],
                ),
            ],
        ];
        let q = vec![vec![neg_ray("add", vec![nat(3), nat(2), var("R")]), var("R")]];
        (phi, q, 5000)
    }

    fn skk() -> (Constellation, Vec<Star>, usize) {
        let prog = crate::combinator::app_n([
            crate::combinator::a_("S"),
            crate::combinator::a_("T"),
            crate::combinator::a_("T"),
            crate::combinator::a_("x"),
        ]);
        let phi = crate::combinator::machine_stars();
        let psi = vec![crate::combinator::initial_process(&prog)];
        (phi, psi, 3000)
    }

    fn binarith() -> (Constellation, Vec<Star>, usize) {
        let phi = crate::binarith::binarith_module();
        let q = vec![vec![
            neg_ray(
                "add",
                vec![crate::binarith::nat(5), crate::binarith::nat(6), var("R")],
            ),
            var("R"),
        ]];
        (phi, q, 8000)
    }

    /// The galaxy entry interaction, if `galaxy.txt` is readable. Returns
    /// `None` (never panics) when the external file is absent — the corpus is
    /// then skipped with an eprintln, per docs/09 §A.5.
    fn galaxy() -> Option<(Constellation, Vec<Star>, usize)> {
        let src = match std::fs::read_to_string(GALAXY_PATH) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "SKIP galaxy corpus: galaxy.txt not readable at {GALAXY_PATH} \
                     ({e}) — skipped, not a failure."
                );
                return None;
            }
        };
        let g = match crate::galaxy::parse(&src) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("SKIP galaxy corpus: galaxy.txt parse error: {e}");
                return None;
            }
        };
        let phi = crate::galaxy::constellation(&g);
        use crate::galaxy::Ast;
        let zero = || Ast::Lit { neg: false, mag: 0 };
        let entry_ast = Ast::App(
            Box::new(Ast::App(
                Box::new(Ast::Ref(g.entry)),
                Box::new(Ast::Atom("nil".to_string())),
            )),
            Box::new(Ast::App(
                Box::new(Ast::App(
                    Box::new(Ast::Atom("cons".to_string())),
                    Box::new(zero()),
                )),
                Box::new(zero()),
            )),
        );
        let m = crate::galaxy::enc(&entry_ast);
        let eps = mk_app_str("eps", vec![]);
        let st = mk_app_str("st", vec![m, eps]);
        let ray = mk_app_str("+P", vec![st]);
        let psi_init: Vec<Star> = vec![vec![ray]];
        // Bounded fuel: B0a only needs iex and iex_fast to *agree* (they are
        // byte-identical today regardless of NF), not to reach a normal form.
        Some((phi, psi_init, 4000))
    }

    // ── B0a — bootstrap: validator accepts the known-equal pair ──────────────

    /// docs/09 §A.6 B0a: `iex` and `iex_fast` are byte-identical today, so
    /// conceal+canonical+multiset MUST return `true` on every corpus. A
    /// `false` here means the validator is over-strict and must be fixed
    /// before any unifier work proceeds.
    #[test]
    fn b0a_validator_accepts_byte_identical_iex_iex_fast() {
        for (name, (phi, psi, fuel)) in [
            ("horn", horn()),
            ("skk", skk()),
            ("binarith", binarith()),
        ] {
            let r = iex(&phi, psi.clone(), fuel);
            let f = iex_fast(&phi, psi, fuel);
            assert!(
                psi_compatible(&r.psi, &f.psi),
                "{name}: psi_compatible(iex, iex_fast) must be true (byte-identical)"
            );
            // Symmetry sanity (multiset equality is symmetric).
            assert!(psi_compatible(&f.psi, &r.psi), "{name}: not symmetric");
        }

        if let Some((phi, psi, fuel)) = galaxy() {
            let r = iex(&phi, psi.clone(), fuel);
            let f = iex_fast(&phi, psi, fuel);
            assert!(
                psi_compatible(&r.psi, &f.psi),
                "galaxy: psi_compatible(iex, iex_fast) must be true (byte-identical)"
            );
        }
    }

    // ── B0b — bootstrap: validator catches a perturbation (Goodhart guard) ───

    /// docs/09 §A.6 B0b, reusing the KG7 Goodhart forgery style
    /// (`evaluate.rs::goodhart_guard_oracle_catches_unfaithful_fast_path`):
    /// from a real faithful result, forge wrong-but-plausible variants and
    /// assert the validator's verdicts. The all-neutral spurious star is the
    /// right forgery vector — it survives conceal+filter as a visible answer
    /// the engine never produced (mirrors `evaluate.rs:422-423`).
    #[test]
    fn b0b_validator_catches_perturbations() {
        let (phi, psi, fuel) = horn();
        let real = iex(&phi, psi, fuel);
        assert!(real.is_normal_form, "reference Horn converges");
        // Self-compat: a result is always compatible with itself.
        assert!(psi_compatible(&real.psi, &real.psi));

        // Locate a visible (all-neutral, non-empty) answer star to perturb.
        let vis = conceal_and_filter(&real.psi);
        assert!(!vis.is_empty(), "Horn has at least one visible answer");

        // (1) extra spurious all-neutral star ⇒ NOT compatible.
        let mut extra = real.psi.clone();
        extra.push(vec![app("BOGUS", vec![cst("0")])]);
        assert!(
            !psi_compatible(&real.psi, &extra),
            "an extra spurious visible answer must be caught"
        );

        // (2) missing a visible answer ⇒ NOT compatible. Drop the first
        // surviving visible star from a full copy of the result.
        let mut missing = real.psi.clone();
        let drop_at = missing
            .iter()
            .position(|s| {
                use crate::polarised::{ray_polarity, Polarity};
                !s.is_empty() && s.iter().all(|&r| ray_polarity(r) == Polarity::Neutral)
            })
            .expect("a visible star exists in the raw psi");
        missing.remove(drop_at);
        assert!(
            !psi_compatible(&real.psi, &missing),
            "a missing visible answer must be caught"
        );

        // (3) DUPLICATED visible answer ⇒ NOT compatible. This is the
        // multiset-specific case the old subset∧subset set test would MISS;
        // it is what justifies the multiset strengthening (docs/09 §A.4/§D).
        let mut dup = real.psi.clone();
        dup.push(vis[0].clone());
        assert!(
            !psi_compatible(&real.psi, &dup),
            "a duplicated visible answer must be caught (multiset, not set)"
        );
        // Sanity that the set-only criterion would have *passed* this — i.e.
        // the strengthening is real, not vacuous.
        let setwise_would_pass = {
            let a = conceal_and_filter(&real.psi);
            let b = conceal_and_filter(&dup);
            let subset = |xs: &[Star], ys: &[Star]| {
                xs.iter().all(|x| {
                    ys.iter()
                        .any(|y| crate::execution::stars_alpha_equiv(x, y))
                })
            };
            subset(&a, &b) && subset(&b, &a)
        };
        assert!(
            setwise_would_pass,
            "the duplicated-answer forgery must be exactly the case set-compare \
             misses (else the multiset test proves nothing)"
        );

        // (4) pure α-rename of EVERY star ⇒ STILL compatible (validator
        // ignores variable names). Rename every Var consistently.
        let renamed: Vec<Star> = real
            .psi
            .iter()
            .map(|s| s.iter().map(|&r| alpha_bump(r)).collect())
            .collect();
        assert!(
            psi_compatible(&real.psi, &renamed),
            "a pure α-rename of every star must remain compatible"
        );

        // (5) structural perturbation of one visible answer (s(0) → s(s(0)))
        // ⇒ NOT compatible (a genuine answer-shape change survives canonical).
        let mut structural = real.psi.clone();
        let pidx = structural
            .iter()
            .position(|s| {
                use crate::polarised::{ray_polarity, Polarity};
                !s.is_empty() && s.iter().all(|&r| ray_polarity(r) == Polarity::Neutral)
            })
            .unwrap();
        structural[pidx] = structural[pidx]
            .iter()
            .map(|&r| app("s", vec![r]))
            .collect();
        assert!(
            !psi_compatible(&real.psi, &structural),
            "a structurally-perturbed visible answer must be caught"
        );
    }

    /// Consistently rename every variable in a term to a fresh name (a pure
    /// α-rename: `X` → `α§X`). Used by B0b case (4).
    fn alpha_bump(t: Term) -> Term {
        use crate::term::{get, TermData};
        match get(t) {
            TermData::Var(v) => {
                let name = format!("\u{3b1}\u{a7}{}", v.as_str());
                mk_var(&name)
            }
            TermData::App(sym, args) => {
                let new: Vec<Term> = args.iter().map(|&a| alpha_bump(a)).collect();
                crate::term::mk_app_interned(sym, new)
            }
        }
    }

    // ── docs/09 §G.5 — empirical: do genuine duplicate canonical stars occur? ─

    /// docs/09 §G.5 (the single most important Stage-0 empirical question):
    /// does `conceal_and_filter(iex(corpus).psi)` ever contain genuine
    /// duplicate α-canonical stars on ANY corpus? If never, multiset == set
    /// and the multiset strengthening is free for both the Fast and the
    /// Tabled (KA1 α-variant-dropping) tiers. If duplicates DO occur, the
    /// parent must keep the Tabled gate set-wise. This test only *reports*
    /// the fact (asserts nothing about it); it does not touch the tabled gate.
    #[test]
    fn g5_report_duplicate_canonical_stars_per_corpus() {
        fn dup_count(psi: &[Star]) -> (usize, usize) {
            let keys = key_multiset(&conceal_and_filter(psi));
            let total = keys.len();
            let mut dups = 0usize;
            let mut i = 0;
            while i < keys.len() {
                let mut j = i + 1;
                while j < keys.len() && keys[j] == keys[i] {
                    j += 1;
                }
                let run = j - i;
                if run > 1 {
                    dups += run - 1;
                }
                i = j;
            }
            (total, dups)
        }

        let mut any_dup = false;
        let mut lines: Vec<String> = Vec::new();
        for (name, (phi, psi, fuel)) in [
            ("horn", horn()),
            ("skk", skk()),
            ("binarith", binarith()),
        ] {
            let r = iex(&phi, psi, fuel);
            let (total, dups) = dup_count(&r.psi);
            any_dup |= dups > 0;
            lines.push(format!(
                "  {name:<9}: {total} visible star(s), {dups} duplicate(s)"
            ));
        }
        match galaxy() {
            Some((phi, psi, fuel)) => {
                let r = iex(&phi, psi, fuel);
                let (total, dups) = dup_count(&r.psi);
                any_dup |= dups > 0;
                lines.push(format!(
                    "  {:<9}: {total} visible star(s), {dups} duplicate(s)",
                    "galaxy"
                ));
            }
            None => lines.push("  galaxy   : SKIPPED (galaxy.txt unreadable)".to_string()),
        }

        eprintln!("─── docs/09 §G.5 empirical finding ─────────────────────────");
        for l in &lines {
            eprintln!("{l}");
        }
        eprintln!(
            "duplicates observed: {}",
            if any_dup { "YES" } else { "NO" }
        );
        eprintln!(
            "⇒ multiset gate is {} for the corpora measured",
            if any_dup {
                "STRICTER than set (Tabled tier needs a set-wise variant)"
            } else {
                "equal to set (multiset strengthening is FREE for both tiers)"
            }
        );
        eprintln!("────────────────────────────────────────────────────────────");
    }

    // ── ObsRecord substrate (docs/07 §G) — inert, capturable ─────────────────

    #[test]
    fn obs_record_is_stable_and_answer_keyed() {
        let (phi, psi, fuel) = horn();
        let r = iex(&phi, psi.clone(), fuel);
        let f = iex_fast(&phi, psi.clone(), fuel);

        let rec_ref = record("horn-add(3,2)", &psi, &r.psi);
        let rec_fast = record("horn-add(3,2)", &psi, &f.psi);

        // Answer keys are exactly what psi_compatible compares ⇒ equal here.
        assert_eq!(rec_ref.answer_keys, rec_fast.answer_keys);
        assert_eq!(
            obs_record_to_string(&rec_ref),
            obs_record_to_string(&rec_fast)
        );

        // The textual line is deterministic and self-describing; no file I/O
        // happens anywhere in this module (capture is the caller's choice).
        let line = obs_record_to_string(&rec_ref);
        assert!(line.starts_with("obs phi=horn-add(3,2) in=["));
        assert!(line.contains(" ans=["));

        // A divergent result yields a different line (the record is sound for
        // the same reason psi_compatible is).
        let mut forged = r.psi.clone();
        forged.push(vec![app("BOGUS", vec![cst("0")])]);
        let rec_forged = record("horn-add(3,2)", &psi, &forged);
        assert_ne!(rec_ref.answer_keys, rec_forged.answer_keys);
    }

    // ── unify-level property sanity (docs/09 §A.5, cheap tier) ───────────────

    /// Cheap below-iex sanity: if `unify` succeeds on a random small term
    /// pair, the two sides under the returned σ are α-equal (so `canonical` /
    /// `psi_compatible`'s α-invariant agrees with the unifier's own notion of
    /// equality). Deterministic LCG, no external deps — mirrors
    /// `polarised.rs`'s fuzz style. Small + fast.
    #[test]
    fn unify_success_implies_alpha_equal_sides() {
        use crate::antiunify::alpha_eq;
        use crate::unify::{unify, Equation};

        // Dependency-free LCG (Numerical Recipes constants).
        let mut seed: u64 = 0x5151_5151_2727_2727;
        let mut rng = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 33) as u32
        };

        // Build a random small term over a tiny signature with shared var
        // names possible across the two sides (stress α-disjointness).
        fn build(rng: &mut impl FnMut() -> u32, depth: u32) -> Term {
            if depth == 0 || rng() % 3 == 0 {
                match rng() % 4 {
                    0 => mk_var("X"),
                    1 => mk_var("Y"),
                    2 => mk_app_str("a", vec![]),
                    _ => mk_app_str("b", vec![]),
                }
            } else {
                let head = if rng() % 2 == 0 { "f" } else { "g" };
                let ar = 1 + (rng() % 2) as usize;
                let args = (0..ar).map(|_| build(rng, depth - 1)).collect();
                mk_app_str(head, args)
            }
        }

        for _ in 0..2000 {
            let lhs = build(&mut rng, 3);
            let rhs = build(&mut rng, 3);
            if let Some(sigma) = unify(vec![Equation::new(lhs, rhs)]) {
                let sl = sigma.apply(lhs);
                let sr = sigma.apply(rhs);
                assert!(
                    alpha_eq(sl, sr),
                    "unify σ must make the two sides α-equal"
                );
            }
        }
    }
}
