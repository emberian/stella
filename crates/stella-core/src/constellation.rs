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

/// Eng §48.7 ray classification (faithful). A ray is **objective** if its
/// head is uncoloured, *or* it is a colour over colour-free arguments;
/// **subjective** if it is a coloured ray with ≥1 argument that contains a
/// colour (colour nested in an argument). Returns `true` iff subjective.
pub fn ray_is_subjective(r: Ray) -> bool {
    match get(r) {
        // Uncoloured (variable, or neutral-headed): objective by §48.7
        // ("objective if uncoloured"). Subjectivity is defined only for a
        // *coloured ray* (audit 01 §1.2, docs/00 §4.1 verbatim).
        TermData::Var(_) => false,
        TermData::App(sym, args) => {
            sym.pol != Polarity::Neutral
                && args.iter().any(|&a| term_contains_colour(a))
        }
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
        // Uncoloured (neutral) head, even over a coloured arg ⇒ objective
        // (§48.7: "objective if uncoloured"; subjectivity is defined only
        // for a *coloured* ray).
        assert!(!ray_is_subjective(mk_app_str("f", vec![pos_ray("d", vec![x])])));
        // Colour over uncoloured arguments ⇒ objective.
        assert!(!ray_is_subjective(pos_ray("c", vec![x])));
        assert!(!ray_is_subjective(pos_ray("c", vec![mk_app_str("f", vec![x])])));
        // Coloured ray with a colour nested in an argument ⇒ subjective.
        assert!(ray_is_subjective(pos_ray("c", vec![pos_ray("d", vec![x])])));
        // Polarity of the nested colour is irrelevant — it is *coloured*.
        assert!(ray_is_subjective(pos_ray("c", vec![neg_ray("d", vec![x])])));
        // Deeper nesting under an uncoloured constructor still counts.
        assert!(ray_is_subjective(pos_ray(
            "c",
            vec![mk_app_str("g", vec![neg_ray("d", vec![x])])]
        )));
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
