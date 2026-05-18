//! Stars and constellations (Eng §48.10, §48.14).

pub use crate::polarised::ray_polarity;
use crate::polarised::{Polarity, Ray};
use crate::term::{get, TermData, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// Star
// ─────────────────────────────────────────────────────────────────────────────

/// A star: a finite indexed family of rays (§48.10).
pub type Star = Vec<Ray>;

/// Star classification (§48.10).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StarKind {
    /// Objective.
    Objective,
    /// Subjective.
    Subjective,
    /// Animist: mixes objective and subjective rays.
    Animist,
}

/// **LEGACY — polarity census, NOT Eng's objective/subjective partition.**
///
/// This classifies by the *sign* of ray heads (all-pos⇒Objective,
/// all-neg⇒Subjective, sign-mixed⇒Animist). Eng §48.7/§48.10 defines the
/// partition by **colour nesting in arguments**, not head sign — see
/// [`star_kind_eng`]. The two disagree (e.g. `[+a(X), −a(Y)]` is Eng-
/// Objective but census-Animist; `+c(+d(X))` is Eng-Subjective but
/// census-Objective). 34 call sites across the subjective/valence/
/// reafference stack still consume this census; migrating each to the
/// faithful classifier is a deliberate per-site pass (a caller may want
/// the sign census for a different reason), NOT a blind sweep — so this
/// function's behaviour is intentionally left unchanged here. The
/// idempotence-metatheorem battery (Eng §49.55/§49.57) and any "objective
/// ⇒ dead/idempotent" reasoning MUST use [`star_kind_eng`].
pub fn star_kind(star: &Star) -> StarKind {
    let has_pos = star.iter().any(|&r| ray_polarity(r) == Polarity::Pos);
    let has_neg = star.iter().any(|&r| ray_polarity(r) == Polarity::Neg);
    match (has_pos, has_neg) {
        (false, false) => StarKind::Objective, // all neutral or empty
        (true, false) => StarKind::Objective,
        (false, true) => StarKind::Subjective,
        (true, true) => StarKind::Animist,
    }
}

/// Does `t` contain a **coloured** symbol anywhere (head or nested)?
///
/// Colour proxy: a symbol is *coloured* iff its polarity ≠ Neutral
/// (`F₊ ⊎ F₋`); *uncoloured* iff Neutral (`F₀`). This proxy collapses
/// Eng's two independent signature attributes (colour = predicate
/// identity that `⊂` ranges over; polarity = ±/none) — see
/// docs/thesis-audit/01 §2.1. It is exact for every encoding done so far
/// (colour and polarity coincide there) and is the audit-endorsed scoped
/// basis for the faithful *classifier*; lifting it to a genuinely
/// separate colour attribute in `Sym` is a recorded deeper item, not
/// this step. Iterative walk (galaxy spines overflow recursion).
pub fn term_contains_colour(t: TermId) -> bool {
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        match get(x) {
            TermData::Var(_) => {}
            TermData::App(sym, args) => {
                if sym.pol != Polarity::Neutral {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
        }
    }
    false
}

/// Eng §48.7 ray classification (faithful). Verbatim §48.7: a ray `r` is
/// **objective** iff it is *uncoloured*, **or** it is a coloured ray
/// `r = c(r₁,…,rₙ)` with `c` coloured and `r₁,…,rₙ` uncoloured ("uncoloured
/// terms prefixed by a colour"); **subjective** otherwise, i.e. a coloured
/// ray `r = f(r₁,…,rₙ)` with **at least one of `{r₁,…,rₙ}` coloured**. Note
/// "coloured" = *contains a colour anywhere* (§48.7: "A ray r is coloured if
/// it contains a colour"), NOT "coloured head". Hence the classification
/// reduces exactly to: **subjective iff ≥1 *direct argument* contains a
/// colour** — if some arg is coloured the ray is automatically a coloured
/// ray; if no arg is coloured the ray is objective regardless of the head
/// (either uncoloured, or the §48.7 "colour over uncoloured args" case). The
/// head's own colour/polarity is irrelevant. This is the verbatim §48.9
/// classification (`f(X,+h(Z))` is subjective even though its head `f` is
/// uncoloured). Returns `true` iff subjective.
///
/// HISTORY: a prior revision gated this on `sym.pol != Neutral` (coloured
/// *head*). That is the audit-01 §2.1-class divergence — Eng's split is on
/// "colours nested inside arguments, not the +/− sign of the head" (audit-01
/// §1.6, lines 66–70). The §48.9 verbatim example `f(X,+h(Z))` (uncoloured
/// head, coloured arg, declared *subjective* by Eng) is the counterexample;
/// the head-gate wrongly returned objective for it. Corrected here and
/// pinned by the §48.9 conformance battery below. Not on the iex/aex
/// reduction path (only `expand_constellation` consumes the *legacy*
/// `star_kind`), so the engine is byte-identical.
pub fn ray_is_subjective(r: Ray) -> bool {
    match get(r) {
        // A bare variable contains no colour ⇒ uncoloured ⇒ objective.
        TermData::Var(_) => false,
        // §48.7/§48.9: subjective iff ≥1 direct argument contains a colour.
        // (Head colour is irrelevant — see doc comment.) The empty-arg case
        // (constant, e.g. `+d`) has no coloured arg ⇒ objective: it is the
        // "colour over (zero) uncoloured args" objective form.
        TermData::App(_, args) => args.iter().any(|&a| term_contains_colour(a)),
    }
}

/// Eng §48.7/§48.10 star classification (faithful colour-nesting), the
/// partition Eng's idempotence metatheorem (§49.55 objective ⇒ idempotent;
/// §49.57 subjective ⇒ idempotence lost) is actually stated over. Distinct
/// from the legacy polarity-census [`star_kind`]. Empty / all-objective ⇒
/// Objective; all-subjective ⇒ Subjective; mixed ⇒ Animist.
pub fn star_kind_eng(star: &Star) -> StarKind {
    let has_subj = star.iter().any(|&r| ray_is_subjective(r));
    let has_obj = star.iter().any(|&r| !ray_is_subjective(r));
    match (has_obj, has_subj) {
        (_, false) => StarKind::Objective, // empty, or all objective
        (false, true) => StarKind::Subjective,
        (true, true) => StarKind::Animist,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Constellation
// ─────────────────────────────────────────────────────────────────────────────

/// A constellation: a finite indexed family of stars (§48.14).
pub type Constellation = Vec<Star>;

// ─────────────────────────────────────────────────────────────────────────────
// Multiset semantics (§48.10, §48.14) — additive, non-destructive
// ─────────────────────────────────────────────────────────────────────────────

/// Canonical **multiset key** of a star.
///
/// §48.10 verbatim: "a star ϕ … is a finite indexed family … of rays …
/// stars will be written as an **unordered sequence** `[r₁,…,rₙ]`". The
/// `Vec<Ray>` representation carries an incidental ray order (the index set
/// `Iϕ`); the *star itself* is the family up to that indexing — i.e. a
/// finite **multiset** of rays (a ray may legitimately occur with
/// multiplicity, so this is a multiset, not a set). The canonical key is the
/// sorted vector of interned ray ids: two stars have equal `star_multiset_key`
/// iff they are equal as multisets of rays *under term-interning identity*
/// (hash-consed structurally-identical rays share a `TermId`).
///
/// SCOPE (honest): this is multiset equality on **interned identity**, NOT
/// up to α-equivalence (§48.12/§48.13 quotient `≈α`). Eng considers stars up
/// to `≈α`; that is a strictly finer quotient and orthogonal to the index
/// order this key erases. Renaming-invariance is not claimed here and is a
/// separate (recorded) concern — this key only certifies that ray *index
/// order* is semantically inert, which is the §48.10 "unordered sequence"
/// claim.
pub fn star_multiset_key(star: &Star) -> Vec<u32> {
    let mut k: Vec<u32> = star.iter().map(|r| r.0).collect();
    k.sort_unstable();
    k
}

/// Canonical **multiset key** of a constellation.
///
/// §48.14 verbatim: "A constellation Φ is a countable indexed family of
/// stars … a finite constellation will be written as a **sum of stars**
/// `Φ = ϕ₁+…+ϕₙ`". A sum is commutative ⇒ the star order is inert and a
/// finite constellation is a **multiset of stars**. Key = sorted vector of
/// per-star multiset keys (so it is invariant under BOTH star permutation
/// AND, within each star, ray permutation). Same interning-identity scope
/// caveat as [`star_multiset_key`].
pub fn constellation_multiset_key(phi: &Constellation) -> Vec<Vec<u32>> {
    let mut k: Vec<Vec<u32>> = phi.iter().map(star_multiset_key).collect();
    k.sort_unstable();
    k
}

/// Multiset equality of two stars (§48.10): order-of-rays-insensitive,
/// multiplicity-sensitive.
pub fn stars_multiset_eq(a: &Star, b: &Star) -> bool {
    star_multiset_key(a) == star_multiset_key(b)
}

/// Multiset equality of two constellations (§48.14): order-of-stars and
/// order-of-rays insensitive, multiplicities preserved.
pub fn constellations_multiset_eq(a: &Constellation, b: &Constellation) -> bool {
    constellation_multiset_key(a) == constellation_multiset_key(b)
}

#[cfg(test)]
mod eng_classifier_tests {
    //! Conformance battery for the faithful Eng §48.7/§48.10 classifier
    //! (audit docs/thesis-audit/01 §3.3). Pins the colour-nesting
    //! definition AND the exact divergence from the legacy polarity
    //! census — the unit test whose absence let §2.1 stand.
    use super::*;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::{mk_app_str, mk_var};

    #[test]
    fn ray_objective_vs_subjective_eng() {
        let x = mk_var("X");
        // Bare var: uncoloured ⇒ objective.
        assert!(!ray_is_subjective(x));
        // §48.9 VERBATIM: `f(X,+h(Z))` is a **subjective** ray even though
        // its head `f` is uncoloured (it is a *coloured ray* — it contains
        // `+h` — with a coloured argument). This is the §2.1-class pin: the
        // earlier head-gate (`sym.pol != Neutral`) wrongly called this
        // objective. Eng's split is on colours nested in args, not head sign
        // (audit-01 §1.6 ll.66–70). Same shape as `f(+d(X))`.
        assert!(ray_is_subjective(mk_app_str(
            "f",
            vec![x, pos_ray("h", vec![mk_var("Z")])]
        )));
        assert!(ray_is_subjective(mk_app_str("f", vec![pos_ray("d", vec![x])])));
        // Colour over uncoloured arguments ⇒ objective (§48.7 "uncoloured
        // terms prefixed by a colour"; §48.9 objective examples `+c(X)`).
        assert!(!ray_is_subjective(pos_ray("c", vec![x])));
        assert!(!ray_is_subjective(pos_ray("c", vec![mk_app_str("f", vec![x])])));
        // §48.9 VERBATIM objective: `f(X,Y)` (uncoloured) and `−d(h(X))`
        // (colour over uncoloured arg).
        assert!(!ray_is_subjective(mk_app_str("f", vec![x, mk_var("Y")])));
        assert!(!ray_is_subjective(neg_ray("d", vec![mk_app_str("h", vec![x])])));
        // Coloured ray with a colour nested in an argument ⇒ subjective.
        assert!(ray_is_subjective(pos_ray("c", vec![pos_ray("d", vec![x])])));
        // Polarity of the nested colour is irrelevant — it is *coloured*.
        assert!(ray_is_subjective(pos_ray("c", vec![neg_ray("d", vec![x])])));
        // Deeper nesting under an uncoloured constructor still counts.
        assert!(ray_is_subjective(pos_ray(
            "c",
            vec![mk_app_str("g", vec![neg_ray("d", vec![x])])]
        )));
        // §48.9 VERBATIM subjective: `+c(+d,−c(Y))` — head coloured, args
        // contain a coloured *constant* `+d` and coloured `−c(Y)`. Exercises
        // the nullary-coloured-leaf path of `term_contains_colour`.
        assert!(ray_is_subjective(pos_ray(
            "c",
            vec![pos_ray("d", vec![]), neg_ray("c", vec![mk_var("Y")])]
        )));
        // §48.9 VERBATIM subjective: `+c(−d(+h(X,Y)))`.
        assert!(ray_is_subjective(pos_ray(
            "c",
            vec![neg_ray("d", vec![pos_ray("h", vec![x, mk_var("Y")])])]
        )));
        // §48.9 boundary: a coloured *constant* alone, `+d`, is objective
        // (coloured ray, but it has NO coloured argument — zero args).
        assert!(!ray_is_subjective(pos_ray("d", vec![])));
    }

    #[test]
    fn star_kind_eng_partition() {
        let x = mk_var("X");
        let y = mk_var("Y");
        // All objective ⇒ Objective.
        assert_eq!(
            star_kind_eng(&vec![pos_ray("c", vec![x]), neg_ray("a", vec![y])]),
            StarKind::Objective
        );
        // All subjective ⇒ Subjective.
        assert_eq!(
            star_kind_eng(&vec![pos_ray("c", vec![pos_ray("d", vec![x])])]),
            StarKind::Subjective
        );
        // Mixed ⇒ Animist.
        assert_eq!(
            star_kind_eng(&vec![
                pos_ray("c", vec![pos_ray("d", vec![x])]),
                pos_ray("e", vec![y])
            ]),
            StarKind::Animist
        );
        // Empty ⇒ Objective (vacuous).
        assert_eq!(star_kind_eng(&Vec::new()), StarKind::Objective);
    }

    /// The headline divergence the audit cited: `[+a(X), −a(Y)]` is
    /// Eng-**Objective** (both rays are colours over uncoloured args) but
    /// the legacy polarity census calls it **Animist** (sign-mixed). This
    /// test FAILS if anyone "fixes" them to agree the wrong way.
    #[test]
    fn eng_vs_legacy_census_divergence_is_pinned() {
        let s = vec![pos_ray("a", vec![mk_var("X")]), neg_ray("a", vec![mk_var("Y")])];
        assert_eq!(star_kind(&s), StarKind::Animist, "legacy = sign census");
        assert_eq!(star_kind_eng(&s), StarKind::Objective, "Eng = colour-nesting");
        // And the inverse: `+c(+d(X))` is census-Objective (all-pos) but
        // Eng-Subjective (nested colour).
        let t = vec![pos_ray("c", vec![pos_ray("d", vec![mk_var("X")])])];
        assert_eq!(star_kind(&t), StarKind::Objective, "legacy = all-pos");
        assert_eq!(star_kind_eng(&t), StarKind::Subjective, "Eng = nested colour");
    }
}

#[cfg(test)]
mod multiset_semantics_tests {
    //! Conformance for §48.10 (star = finite multiset of rays, written as an
    //! "unordered sequence") and §48.14 (finite constellation = "sum of
    //! stars" ϕ₁+…+ϕₙ ⇒ multiset of stars). Certifies which operations are
    //! multiset-invariant and records, as a first-class finding, the ones
    //! that are intentionally index-sensitive (§48.14 `IdRays` keeps the
    //! star instance). Additive: the `Vec<Ray>`/`Vec<Star>` types are
    //! untouched; this only adds a canonical key + the invariance proofs.
    use super::*;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::mk_var;

    #[test]
    fn star_key_invariant_under_ray_permutation() {
        let x = mk_var("X");
        let y = mk_var("Y");
        let r1 = pos_ray("a", vec![x]);
        let r2 = neg_ray("b", vec![y]);
        let r3 = pos_ray("c", vec![pos_ray("d", vec![x])]);
        let s_abc = vec![r1, r2, r3];
        let s_cba = vec![r3, r2, r1];
        let s_bac = vec![r2, r1, r3];
        // §48.10 "unordered sequence": every permutation has one key.
        assert_eq!(star_multiset_key(&s_abc), star_multiset_key(&s_cba));
        assert_eq!(star_multiset_key(&s_abc), star_multiset_key(&s_bac));
        assert!(stars_multiset_eq(&s_abc, &s_cba));
    }

    #[test]
    fn star_key_is_multiplicity_sensitive_not_a_set() {
        // §48.10: a *family*/multiset, not a set — a repeated ray counts
        // with multiplicity. `[r]` ≠ `[r, r]`.
        let r = pos_ray("a", vec![mk_var("X")]);
        let one = vec![r];
        let two = vec![r, r];
        assert_ne!(star_multiset_key(&one), star_multiset_key(&two));
        assert!(!stars_multiset_eq(&one, &two));
        // Permuting a star *with* a repeat is still invariant.
        let s = vec![r, neg_ray("b", vec![mk_var("Y")]), r];
        let sp = vec![r, r, neg_ray("b", vec![mk_var("Y")])];
        assert!(stars_multiset_eq(&s, &sp));
    }

    #[test]
    fn constellation_key_invariant_under_star_and_ray_permutation() {
        let x = mk_var("X");
        let s1 = vec![pos_ray("a", vec![x]), neg_ray("b", vec![x])];
        let s2 = vec![pos_ray("c", vec![pos_ray("d", vec![x])])];
        let s3 = vec![neg_ray("e", vec![x])];
        let phi = vec![s1.clone(), s2.clone(), s3.clone()];
        // §48.14 "sum of stars" is commutative ⇒ star order inert …
        let phi_star_perm = vec![s3.clone(), s1.clone(), s2.clone()];
        assert!(constellations_multiset_eq(&phi, &phi_star_perm));
        // … and §48.10 ray order inside each star is also inert.
        let s1_rev = vec![neg_ray("b", vec![x]), pos_ray("a", vec![x])];
        let phi_both_perm = vec![s2, s1_rev, s3];
        assert!(constellations_multiset_eq(&phi, &phi_both_perm));
        // Multiplicity of stars preserved: Φ ≠ Φ+ϕ₁.
        let mut phi_dup = phi.clone();
        phi_dup.push(s1);
        assert!(!constellations_multiset_eq(&phi, &phi_dup));
    }

    #[test]
    fn star_kind_eng_is_multiset_invariant() {
        // The faithful classifier is `any()`-quantified over rays ⇒ it is a
        // function of the ray *multiset*, not the index order. This is the
        // property a §48.10-respecting semantic operator MUST have. Verify
        // it directly on a mixed (animist) star under every permutation.
        let x = mk_var("X");
        let obj = pos_ray("e", vec![x]); // colour over uncoloured ⇒ objective
        let subj = pos_ray("c", vec![pos_ray("d", vec![x])]); // nested ⇒ subj
        let perms = [
            vec![obj, subj],
            vec![subj, obj],
            vec![obj, subj, obj],
            vec![subj, obj, obj],
        ];
        for p in &perms {
            assert_eq!(
                star_kind_eng(p),
                StarKind::Animist,
                "star_kind_eng must depend only on the ray multiset"
            );
        }
        // Legacy census is likewise `any()`-based ⇒ multiset-invariant
        // (pinned so a future refactor cannot make it order-sensitive).
        let a = pos_ray("a", vec![x]);
        let b = neg_ray("a", vec![mk_var("Y")]);
        assert_eq!(star_kind(&vec![a, b]), star_kind(&vec![b, a]));
    }

    /// HONEST-NEGATIVE (recorded, by design — not a defect): `IdRays` /
    /// `+IdRays` / `−IdRays` / `get_ray` are **index-sensitive** and
    /// therefore NOT multiset-invariant. §48.14 verbatim: `IdRays(Φ)` "keeps
    /// track of the instance of star from which rays come" — the identifier
    /// `(i,j)` IS the index, so permuting stars/rays deliberately changes
    /// these. They are *addressing* operations over the indexed family, not
    /// semantic operations over the multiset. This test pins that they are
    /// NOT invariant, so the distinction stays explicit and is never
    /// "papered" by a future invariance claim.
    #[test]
    fn id_rays_is_index_sensitive_by_design_not_multiset_invariant() {
        let x = mk_var("X");
        let s1 = vec![pos_ray("a", vec![x])];
        let s2 = vec![neg_ray("b", vec![x]), pos_ray("c", vec![x])];
        let phi = vec![s1.clone(), s2.clone()];
        let phi_perm = vec![s2.clone(), s1.clone()];
        // Same multiset of stars …
        assert!(constellations_multiset_eq(&phi, &phi_perm));
        // … but `get_ray` at the SAME identifier yields a DIFFERENT ray,
        // because (i,j) addresses the index, per §48.14. This inequality is
        // the design, not a bug.
        assert_ne!(get_ray(&phi, (0, 0)), get_ray(&phi_perm, (0, 0)));
        // And the per-polarity id-ray *sets* differ as index families even
        // though the underlying ray multiset is identical: +IdRays here is
        // {(0,0)} vs {(1,0)} after the star permutation.
        assert_ne!(pos_id_rays(&phi), pos_id_rays(&phi_perm));
        // (Sanity: the *rays pointed at* are the same multiset — invariance
        // lives at the key level, addressing does not.)
        let rays = |p: &Constellation| {
            let mut v: Vec<u32> =
                id_rays(p).into_iter().map(|id| get_ray(p, id).0).collect();
            v.sort_unstable();
            v
        };
        assert_eq!(rays(&phi), rays(&phi_perm));
    }
}

/// A ray identifier: `(star_index, ray_index)` (§48.10 notation `(i, j)`).
pub type RayId = (usize, usize);

/// `IdRays(Φ)` — the set of all ray identifiers (§48.10).
pub fn id_rays(phi: &Constellation) -> Vec<RayId> {
    phi.iter()
        .enumerate()
        .flat_map(|(i, star)| (0..star.len()).map(move |j| (i, j)))
        .collect()
}

/// `+IdRays(Φ)` — ray identifiers whose ray has positive polarity (§48.10).
pub fn pos_id_rays(phi: &Constellation) -> Vec<RayId> {
    id_rays(phi)
        .into_iter()
        .filter(|&(i, j)| ray_polarity(phi[i][j]) == Polarity::Pos)
        .collect()
}

/// `−IdRays(Φ)` — ray identifiers whose ray has negative polarity (§48.10).
pub fn neg_id_rays(phi: &Constellation) -> Vec<RayId> {
    id_rays(phi)
        .into_iter()
        .filter(|&(i, j)| ray_polarity(phi[i][j]) == Polarity::Neg)
        .collect()
}

/// Retrieve a ray from a constellation by its identifier.
pub fn get_ray(phi: &Constellation, (i, j): RayId) -> Ray {
    phi[i][j]
}
