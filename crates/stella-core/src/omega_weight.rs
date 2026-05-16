//! Visibility and non-classical truth weight ω (Eng §79) and system-free
//! arithmetic [[p]] (Eng §80).
//!
//! # §79 — Visibility and Non-Classical Truth
//!
//! Girard's *visibility* (Gir20a, TS paper 4) is a non-classical truth notion
//! based on an Euler–Poincaré invariant called the **weight** ω.  Two conditions
//! for truth: (i) the special behaviour **0** is not true; (ii) truth is
//! preserved by cut-elimination.
//!
//! ## Weight of a star (§79.8)
//!
//! ```text
//! A star φ has objective rays o₁, …, oₙ and subjective rays s₁, …, sₘ.
//!
//! ω([o₁, …, oₙ])            := 2 − n    (fully objective: no subjective rays)
//! ω([o₁, …, oₙ, s₁, …, sₘ]) := −n      (mixed/subjective: at least one sⱼ)
//! ```
//!
//! Here *n* always counts the **objective** rays (positive or neutral head).
//! A fully subjective star (n = 0 objective rays) has weight 0 via the mixed
//! formula (−0 = 0).
//!
//! ## Weight of a constellation (§79.9)
//!
//! ```text
//! ω(φ₁ + … + φₙ) := Σᵢ ω(φᵢ)
//! ```
//!
//! ## Weight of a behaviour (§79.11)
//!
//! ```text
//! ω(A) := max { ω(Φ) | Φ ∈ A }
//! ```
//!
//! The type `&[Constellation]` represents the (finite, non-empty) family of
//! member constellations of A used for this maximum.
//!
//! ## Visibility (§79.15)
//!
//! A constellation Φ is *visible* (true) when ω(Φ) ≥ 0.
//!
//! ## Selected weight table (Figure 79.1, p. 367)
//!
//! ```text
//! ω(ℱ) = 1     ω(ꟓ) = 0
//! ω(A⊥)    = 2 − ω(A)
//! ω(A ⊗ B) = ω(A) + ω(B)
//! ω(A ⅋ B) = ω(A) + ω(B)     if both A, B contain ꟓ
//!           = ω(A) + ω(B) − 2  otherwise
//! ```
//!
//! # §80 — System-Free Arithmetic on Relative Numbers
//!
//! Relative integers (ℤ) are encoded as behaviours using only ℱ and ꟓ (§80.2):
//!
//! ```text
//! [[0]] := ꟓ
//! [[p]] := ℱₚ ⊗ ꟓ     (p > 0)
//! [[p]] := ℱₚ₊₂ ⅋ ꟓ  (p < 0)
//! ```
//!
//! where the Fu/Wo sequences (§79.23–24) are:
//!
//! ```text
//! ℱ₁ = ℱ;  ℱₙ = ℱ ⊗ ℱₙ₋₁ (n > 1);  ℱₙ = ℱ ⅋ ℱₙ₊₁ (n < 1)
//! ꟓ₀ = ꟓ;  ꟓₙ = ℱₙ ⊗ ꟓ   (n ≠ 0)
//! ```
//!
//! Key proposition (§80.5): ω([[p]]) = p — the weight of the encoding equals
//! the encoded integer.

use crate::constellation::{star_kind, Constellation, Star, StarKind};
use crate::polarised::Polarity;
use crate::term::{mk_app_str, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// § 79: Weight of a star
// ─────────────────────────────────────────────────────────────────────────────

/// Count the objective (positive or neutral head) rays in a star.
///
/// Per §79.8, positive rays carry the "objective" role in the weight formula.
/// Neutral (uncoloured) rays, as used in ℱ/ꟓ definitions (§77.13/77.16 "all rᵢ
/// are uncoloured"), are also counted as objective — they raise the 2−n
/// subtraction just as positive rays do.
fn count_objective_rays(star: &Star) -> i64 {
    star.iter()
        .filter(|&&r| {
            let pol = crate::polarised::ray_polarity(r);
            pol == Polarity::Pos || pol == Polarity::Neutral
        })
        .count() as i64
}

/// Compute the weight ω of a single star (§79.8).
///
/// ```text
/// ω([o₁, …, oₙ])             = 2 − n   (fully objective)
/// ω([o₁, …, oₙ, s₁, …, sₘ]) = −n       (mixed / contains a subjective ray)
/// ```
///
/// where `n` counts objective (positive + neutral) rays.
/// Fully subjective stars (n = 0) yield weight 0 by the mixed formula.
///
/// Uses [`star_kind`] from `constellation` to dispatch the two cases.
pub fn star_weight(star: &Star) -> i64 {
    let n = count_objective_rays(star);
    match star_kind(star) {
        StarKind::Objective => 2 - n,
        StarKind::Subjective | StarKind::Animist => -n,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// § 79: Weight of a constellation
// ─────────────────────────────────────────────────────────────────────────────

/// Compute the weight ω of a constellation Φ (§79.9).
///
/// ```text
/// ω(φ₁ + … + φₙ) = Σᵢ ω(φᵢ)
/// ```
pub fn constellation_weight(phi: &Constellation) -> i64 {
    phi.iter().map(star_weight).sum()
}

// ─────────────────────────────────────────────────────────────────────────────
// § 79: Weight of a behaviour
// ─────────────────────────────────────────────────────────────────────────────

/// Compute the weight ω of a behaviour A (§79.11).
///
/// ```text
/// ω(A) = max { ω(Φ) | Φ ∈ A }
/// ```
///
/// `members` is the slice of member constellations of A.
/// Panics if `members` is empty (a behaviour has at least one member).
pub fn behaviour_weight(members: &[Constellation]) -> i64 {
    assert!(!members.is_empty(), "behaviour must have at least one member constellation");
    members.iter().map(|phi| constellation_weight(phi)).max().unwrap()
}

// ─────────────────────────────────────────────────────────────────────────────
// § 79: Visibility
// ─────────────────────────────────────────────────────────────────────────────

/// Test whether a constellation Φ is *visible* (§79.15).
///
/// A constellation is visible (non-classically true) when ω(Φ) ≥ 0.
pub fn visible(phi: &Constellation) -> bool {
    constellation_weight(phi) >= 0
}

// ─────────────────────────────────────────────────────────────────────────────
// § 80: Canonical ray constructors for ℱ and ꟓ
// ─────────────────────────────────────────────────────────────────────────────

/// The canonical order-0 objective ray representing a member of ℱ (§77.13).
///
/// ℱ = { {[r, r₁, …, rₖ]} | ord(r) = 0, r polarised and **objective**, all rᵢ uncoloured }
///
/// We use the ground positive atom `+fu` (Fu = objective constant, §77).
/// The name "fu" is a mnemonic for the *Fu* constant ℱ.
///
/// **Faithfulness note**: The name of the concrete symbol is not specified by
/// Eng; §77.13 only requires ord(r) = 0 and r objective. We use `+fu` as an
/// unambiguous canonical choice. Any ground positive atom would be equivalent.
fn fu_ray() -> TermId {
    mk_app_str("+fu", vec![])
}

/// The canonical order-0 subjective ray representing a member of ꟓ (§77.16).
///
/// ꟓ = { {[r, r₁, …, rₖ]} | ord(r) = 0, r polarised and **subjective**, all rᵢ uncoloured }
///
/// We use the ground negative atom `-wo` (Wo = subjective constant, §77).
/// The name "wo" is a mnemonic for the *Wo* constant ꟓ.
///
/// **Faithfulness note**: Same as for `fu_ray` — symbol name is inferred.
fn wo_ray() -> TermId {
    mk_app_str("-wo", vec![])
}

// ─────────────────────────────────────────────────────────────────────────────
// § 80: [[p]] — the encoding of integer p as a behaviour
// ─────────────────────────────────────────────────────────────────────────────

/// Build a canonical representative constellation for the behaviour `[[p]]` (§80.2).
///
/// The encoding uses the Fu/Wo sequences (§79.23–24):
///
/// ```text
/// [[0]] := ꟓ
/// [[p]] := ℱₚ ⊗ ꟓ     (p > 0)
/// [[p]] := ℱₚ₊₂ ⅋ ꟓ  (p < 0)
/// ```
///
/// # Concrete encoding
///
/// **p ≥ 0** — tensor encoding:
///
/// ```text
/// [[0]] = ꟓ         ≅  one star with one subjective ray: { [-wo] }
/// [[1]] = ℱ ⊗ ꟓ    ≅  { [+fu], [-wo] }  (two disjoint stars)
/// [[2]] = ℱ₂ ⊗ ꟓ   ≅  { [+fu], [+fu], [-wo] }
/// [[p]]              ≅  p copies of { [+fu] } plus one { [-wo] }
/// ```
///
/// Each ℱ contributes an independent star `[+fu]` (weight 1); ꟓ contributes
/// one star `[-wo]` (weight 0). Total constellation weight = p · 1 + 0 = p.
///
/// **p < 0** — par encoding:
///
/// ```text
/// [[-1]] = ℱ₁ ⅋ ꟓ  ≅  one animist star { [+fu, -wo] }        (weight −1)
/// [[-2]] = ℱ₀ ⅋ ꟓ  ≅  one animist star { [+fu, +fu, -wo] }   (weight −2)
/// [[-n]] (n > 0)    ≅  one animist star with n copies of +fu and one -wo
/// ```
///
/// The ⅋ (par) of ℱ and ꟓ collapses into a single animist star because
/// par-combination in stellar resolution merges the participating rays into
/// one star (the axiom example [+1, +2] ∈ ℱ ⅋ ℱ at §77.25 confirms this).
/// An animist star with n objective + 1 subjective ray has weight −n,
/// satisfying ω([[p]]) = p for p < 0.
///
/// **Faithfulness notes**:
/// 1. The par-as-animist-star reading is inferred from §77.25 ("axiom [+1,+2]
///    ∈ ℱ ⅋ ℱ") and the weight identity requirement ω([[p]])=p. Eng does not
///    give an explicit stellar normal form for ℱₙ ⅋ ꟓ.
/// 2. For p = -1, ℱₚ₊₂ = ℱ₁ = ℱ, so [[−1]] = ℱ ⅋ ꟓ — confirmed by
///    §80.3 ("[[−1]] := ℱ ⅋ ꟓ").
/// 3. The specific symbol names (`+fu`, `-wo`) are inferred (see `fu_ray` /
///    `wo_ray` doc-comments).
pub fn nat_behaviour(p: i64) -> Constellation {
    if p >= 0 {
        // [[p]] = ℱₚ ⊗ ꟓ:
        //   p stars each { [+fu] }  (weight 2−1 = 1 per star)
        //   1 star        { [-wo] }  (weight −0  = 0 per star)
        // Σ = p
        let mut phi: Constellation = (0..p).map(|_| vec![fu_ray()]).collect();
        phi.push(vec![wo_ray()]);
        phi
    } else {
        // p < 0: [[p]] = ℱₚ₊₂ ⅋ ꟓ
        // For p = -n (n ≥ 1), we have p+2 = 2-n ≤ 1.
        // Expanding the ℱ sequence: ℱ_{2-n} = (n-1) par-levels of ℱ tensored
        // together then par'd with ꟓ → single animist star with (n) copies of
        // +fu and one -wo.  Weight = -n = p.
        let n = (-p) as usize; // number of objective rays in the animist star
        let mut animist_star: Star = (0..n).map(|_| fu_ray()).collect();
        animist_star.push(wo_ray());
        vec![animist_star] // single-star constellation
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── §80 axiom: ω([[p]]) = p ──────────────────────────────────────────────

    #[test]
    fn weight_nat_minus2() {
        let phi = nat_behaviour(-2);
        assert_eq!(behaviour_weight(&[phi]), -2,
            "ω([[−2]]) should be −2");
    }

    #[test]
    fn weight_nat_minus1() {
        let phi = nat_behaviour(-1);
        assert_eq!(behaviour_weight(&[phi]), -1,
            "ω([[−1]]) should be −1  (§80.3: [[−1]] = ℱ ⅋ ꟓ)");
    }

    #[test]
    fn weight_nat_zero() {
        let phi = nat_behaviour(0);
        assert_eq!(behaviour_weight(&[phi]), 0,
            "ω([[0]]) should be 0  (§80.2: [[0]] = ꟓ)");
    }

    #[test]
    fn weight_nat_one() {
        let phi = nat_behaviour(1);
        assert_eq!(behaviour_weight(&[phi]), 1,
            "ω([[1]]) should be 1");
    }

    #[test]
    fn weight_nat_two() {
        let phi = nat_behaviour(2);
        assert_eq!(behaviour_weight(&[phi]), 2,
            "ω([[2]]) should be 2");
    }

    #[test]
    fn weight_nat_three() {
        let phi = nat_behaviour(3);
        assert_eq!(behaviour_weight(&[phi]), 3,
            "ω([[3]]) should be 3");
    }

    // ── §79: weight of fully-objective vs mixed star ──────────────────────────

    /// A fully-objective star with n rays has weight 2 − n.
    #[test]
    fn weight_objective_star() {
        // Star with 1 objective ray: [+fu]  → ω = 2 − 1 = 1
        let s1: Star = vec![fu_ray()];
        assert_eq!(star_weight(&s1), 1,
            "one-objective-ray star: ω = 2 − 1 = 1");

        // Star with 2 objective rays: [+fu, +fu] → ω = 2 − 2 = 0
        let s2: Star = vec![fu_ray(), fu_ray()];
        assert_eq!(star_weight(&s2), 0,
            "two-objective-ray star: ω = 2 − 2 = 0");

        // Star with 3 objective rays: ω = 2 − 3 = −1
        let s3: Star = vec![fu_ray(), fu_ray(), fu_ray()];
        assert_eq!(star_weight(&s3), -1,
            "three-objective-ray star: ω = 2 − 3 = −1");
    }

    /// A fully-subjective star with m rays has weight 0 (n_obj = 0 → −n = 0).
    #[test]
    fn weight_subjective_star() {
        // Star with 1 subjective ray: [-wo] → ω = −0 = 0
        let s: Star = vec![wo_ray()];
        assert_eq!(star_weight(&s), 0,
            "one-subjective-ray star (ꟓ): ω = 0  (§79: ω(ꟓ) = 0)");
    }

    /// An animist (mixed) star [+fu, -wo] has ω = −1 (n_obj = 1).
    #[test]
    fn weight_animist_star() {
        // [+fu, -wo]: 1 objective + 1 subjective → ω = −1
        let s: Star = vec![fu_ray(), wo_ray()];
        assert_eq!(star_weight(&s), -1,
            "animist star [+fu, -wo]: ω = −1  (n_obj = 1, mixed)");
    }

    // ── §79 weight table spot-checks ─────────────────────────────────────────

    /// ω(ℱ) = 1 via the canonical ℱ representative constellation.
    #[test]
    fn weight_fu_behaviour() {
        // ℱ canonical member: { [+fu] }  (one star, one objective ray)
        let fu_member: Constellation = vec![vec![fu_ray()]];
        assert_eq!(behaviour_weight(&[fu_member]), 1,
            "ω(ℱ) = 1");
    }

    /// ω(ꟓ) = 0 via the canonical ꟓ representative constellation.
    #[test]
    fn weight_wo_behaviour() {
        // ꟓ canonical member: { [-wo] }  (one star, one subjective ray)
        let wo_member: Constellation = vec![vec![wo_ray()]];
        assert_eq!(behaviour_weight(&[wo_member]), 0,
            "ω(ꟓ) = 0");
    }

    // ── §79: visibility ──────────────────────────────────────────────────────

    /// **0** = (ℱ ⅋ ꟓ) ⊕ ꟓ has ω = −1 < 0, so it is invisible.
    ///
    /// **Faithfulness note**: We cannot directly construct the behaviour **0**
    /// without implementing ⊕ (additive disjunction) and ⅋ at the behaviour
    /// level.  We therefore test the simpler observable: the canonical [[−1]]
    /// constellation (= ℱ ⅋ ꟓ member, see §80.3) is invisible, confirming
    /// the mechanism behind **0**'s invisibility.
    #[test]
    fn zero_like_constellation_invisible() {
        // [[−1]] representative: animist star [+fu, -wo], weight −1
        let phi = nat_behaviour(-1);
        assert!(!visible(&phi),
            "[[−1]] constellation (ℱ ⅋ ꟓ member) is invisible: ω = −1 < 0");
    }

    /// ⊤ = **0**⊥ has ω = 1 > 0, so it is visible.
    ///
    /// **Faithfulness note**: ω(⊤) = 2 − ω(**0**) = 2 − (−1) = 1.  We use the
    /// canonical [[1]] constellation as a visible representative, which has the
    /// same weight.
    #[test]
    fn top_like_constellation_visible() {
        // [[1]] representative: { [+fu], [-wo] }, weight 1
        let phi = nat_behaviour(1);
        assert!(visible(&phi),
            "[[1]] constellation (⊤-weight representative) is visible: ω = 1 ≥ 0");
    }

    /// A constellation at exactly ω = 0 is visible (boundary case).
    #[test]
    fn zero_weight_constellation_visible() {
        // [[0]] representative: { [-wo] }, weight 0
        let phi = nat_behaviour(0);
        assert!(visible(&phi), "ω = 0 is visible (ω ≥ 0)");
    }

    // ── structural consistency ────────────────────────────────────────────────

    /// behaviour_weight is the max over members, not the sum.
    #[test]
    fn behaviour_weight_is_max() {
        let phi_neg: Constellation = nat_behaviour(-1); // weight −1
        let phi_pos: Constellation = nat_behaviour(2);  // weight 2
        assert_eq!(behaviour_weight(&[phi_neg, phi_pos]), 2,
            "behaviour_weight takes the maximum over member constellations");
    }

    /// constellation_weight is the sum of star weights.
    #[test]
    fn constellation_weight_is_sum() {
        // Two objective stars [+fu]: each weight 1; sum = 2
        let phi: Constellation = vec![vec![fu_ray()], vec![fu_ray()]];
        assert_eq!(constellation_weight(&phi), 2,
            "constellation_weight sums star weights");
    }
}
