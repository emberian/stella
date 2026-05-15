//! Stars and constellations (Eng §48.10, §48.14).
//!
//! §48.7: A *ray* is a term in `Term(P)` over a polarised signature.
//! §48.10: A *star* `φ` is a finite indexed family of rays `[r₁, …, rₙ]`,
//!   taken up to α-equivalence (§48.12).  The empty star is `[]`.
//! §48.14: A *constellation* `Φ` is a finite indexed family of stars
//!   `φ₁ + … + φₙ`.
//!
//! ## Representation choices forced by Eng
//!
//! **Star indices** (§48.10, §49.10): Eng writes stars as indexed families.
//! We use `Vec<Ray>` (a star is a `Vec<Ray>`, its index type is `usize`).
//! A `Star` is therefore `Vec<Ray>`.
//!
//! **Constellation indices** `I_Φ` (§49.10): Eng quantifies over `I_Φ = {0,…,n-1}`
//! for a constellation with `n` stars; we use `usize`.
//!
//! **Polarity classification** of stars (§48.10, §48.7):
//! - A ray is *positive* / *negative* / *neutral* based on its head symbol
//!   prefix (`+`/`-`/none), as encoded by [`crate::polarised`].
//! - §48.10: A star is *objective* if all its rays are positive or neutral;
//!   *subjective* if all rays are negative or neutral; *animist* otherwise
//!   (mixed positive and negative).  (These terms are Eng's.)
//!
//! **`IdRays(Φ)`** (§48.10): the set of pairs `(i, j)` where `i` is a star
//! index and `j` is a ray index within that star.  `±IdRays` restricts to
//! rays whose head has the given polarity.

use crate::polarised::{parse_symbol, Polarity, Ray};

// ─────────────────────────────────────────────────────────────────────────────
// Star
// ─────────────────────────────────────────────────────────────────────────────

/// A star: a finite indexed family of rays (§48.10).
///
/// A star is a `Vec<Ray>`.  Ray index `j` is its position in the vec.
/// The empty star is the empty vec.  Stars are taken up to α-equivalence
/// (§48.12); we do NOT quotient them in memory — callers use
/// [`crate::alpha::alpha_unify`] when equivalence is needed.
pub type Star = Vec<Ray>;

/// The polarity classification of a star (§48.10).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StarKind {
    /// All rays are positive or neutral.
    Objective,
    /// All rays are negative or neutral.
    Subjective,
    /// Mixed: contains at least one positive and at least one negative ray.
    Animist,
}

/// Classify a star as objective, subjective, or animist (§48.10).
///
/// A star with no rays is vacuously objective *and* subjective.  We follow
/// §48.10 literally: a star is objective if it has no negative rays, and
/// subjective if it has no positive rays.  If it has both, it is animist.
///
/// Non-obvious choice: Eng does not specify the case of the empty star.
/// We return `Objective` for the empty star (vacuously: no negative rays).
pub fn star_kind(star: &Star) -> StarKind {
    let has_pos = star.iter().any(|r| ray_polarity(r) == Polarity::Pos);
    let has_neg = star.iter().any(|r| ray_polarity(r) == Polarity::Neg);
    match (has_pos, has_neg) {
        (false, false) => StarKind::Objective, // all neutral or empty
        (true, false) => StarKind::Objective,
        (false, true) => StarKind::Subjective,
        (true, true) => StarKind::Animist,
    }
}

/// Extract the polarity of a ray's head symbol.
///
/// A ray is a `Term`; its head is the outermost function symbol (a string).
/// Variables have no polarity; we treat them as neutral.
pub fn ray_polarity(r: &Ray) -> Polarity {
    match r {
        crate::term::Term::Var(_) => Polarity::Neutral,
        crate::term::Term::App(sym, _) => parse_symbol(sym).polarity,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Constellation
// ─────────────────────────────────────────────────────────────────────────────

/// A constellation: a finite indexed family of stars (§48.14).
///
/// `Constellation[i]` is star `i`; the index type is `usize`.
pub type Constellation = Vec<Star>;

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
        .filter(|&(i, j)| ray_polarity(&phi[i][j]) == Polarity::Pos)
        .collect()
}

/// `−IdRays(Φ)` — ray identifiers whose ray has negative polarity (§48.10).
pub fn neg_id_rays(phi: &Constellation) -> Vec<RayId> {
    id_rays(phi)
        .into_iter()
        .filter(|&(i, j)| ray_polarity(&phi[i][j]) == Polarity::Neg)
        .collect()
}

/// Retrieve a ray from a constellation by its identifier.
///
/// Panics if `(i, j)` is out of bounds.
pub fn get_ray(phi: &Constellation, (i, j): RayId) -> &Ray {
    &phi[i][j]
}
