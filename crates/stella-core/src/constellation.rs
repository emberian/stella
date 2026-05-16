//! Stars and constellations (Eng §48.10, §48.14).

pub use crate::polarised::ray_polarity;
use crate::polarised::{Polarity, Ray};
use crate::term::TermId;

// ─────────────────────────────────────────────────────────────────────────────
// Star
// ─────────────────────────────────────────────────────────────────────────────

/// A star: a finite indexed family of rays (§48.10).
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

// ─────────────────────────────────────────────────────────────────────────────
// Constellation
// ─────────────────────────────────────────────────────────────────────────────

/// A constellation: a finite indexed family of stars (§48.14).
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
