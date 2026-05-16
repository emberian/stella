//! Concrete execution `CEx_C(Φ)` (Eng §50).
//!
//! §50.1: Concrete execution is an effective algorithm for executing constellations
//! by iteratively constructing diagrams, in contrast to abstract execution (§49.42)
//! which is purely mathematical.
//!
//! ## Construction space (§50.2)
//!
//! A *construction space* `Φ ⊢_C Δ | Ψ` is:
//! - `Φ`: the constellation we execute (fixed reference).
//! - `Δ`: a set of diagrams being constructed (deduplicated by §49.20 diagram equivalence).
//! - `Ψ`: a constellation accumulating the normal form (actualisations of saturated diagrams).
//!
//! ## Diagram extension (§50.4)
//!
//! Two operations extend a C-diagram `(G, δ)` by one edge:
//!
//! - **Internal** `(G, δ) ⊕_in^{(v,j)} (v',j')`: connect two free rays of the
//!   *same* diagram (vertices `v` and `v'`), requiring `(δ(v'),j') ∈ adj_Φ^C(δ(v),j)`
//!   and `(δ(v),j) ∈ free(G,δ)`.
//!
//! - **External** `(G, δ) ⊕_out^{(v,j)} (i',j')`: connect a free ray `(δ(v),j)` of
//!   the diagram to a *fresh* occurrence of star `i'` from `Φ`, requiring
//!   `(i',j') ∈ adj_Φ^C(δ(v),j)` and `(δ(v),j) ∈ free(G,δ)`.
//!
//! ## Stellar construction step (§50.5) and `CEx_C(Φ)` (§50.6)
//!
//! Starting from the initial construction space `Φ ⊢_C {(G_1,δ_1),…,(G_n,δ_n)} | ∅`
//! (one single-vertex diagram per star of `Φ`), stellar construction repeatedly extends
//! all non-saturated diagrams in `Δ`. When a diagram saturates, it is moved to `Ψ` if
//! correct (actualisatied), or discarded if incorrect.
//!
//! ## Theorem §50.7: AEx_C(Φ) = CEx_C(Φ)
//!
//! The concrete and abstract executions produce the same result when `CEx_C(Φ)` is
//! defined (i.e. the construction terminates).
//!
//! ## Implementation note
//!
//! The existing `execution.rs` already implements AEx via a constructive saturation
//! algorithm that is operationally identical to CEx (both grow diagrams by adding
//! edges one at a time, saturate them, and actualise correct ones).
//!
//! Per §50.7, `CEx_C(Φ) = AEx_C(Φ)`. Rather than duplicating the saturation logic
//! verbatim, `CEx` calls the same underlying saturation machinery (which IS concrete
//! execution per §50.7) but wrapped in the `Φ ⊢_C Δ | Ψ` construction-space
//! vocabulary. The public API is distinct and documents the §50 definitions.

use crate::constellation::{Constellation, Star};
use crate::dep_graph::DepGraph;
use crate::execution::{aex, saturated_diagrams};

// ─────────────────────────────────────────────────────────────────────────────
// Construction space (§50.2)
// ─────────────────────────────────────────────────────────────────────────────

/// A construction space `Φ ⊢_C Δ | Ψ` (§50.2).
///
/// - `phi`: the reference constellation Φ.
/// - `delta`: the set of diagrams being actively constructed (as `Vec<Diagram>`,
///   deduplicated by the saturation builder which uses canonical keys per §49.20).
/// - `psi`: the accumulated normal form (actualisations of correct saturated diagrams).
#[derive(Debug)]
pub struct ConstructionSpace {
    /// The reference constellation Φ.
    pub phi: Constellation,
    /// Number of active diagrams under construction (|Δ| in §50.3).
    ///
    /// In the implementation, `delta` is implicit in the saturation worklist;
    /// we expose only its final count here for informational purposes.
    pub delta_count: usize,
    /// Ψ: the accumulated normal-form stars (actualisations of correct saturated diagrams).
    pub psi: Vec<Star>,
}

impl ConstructionSpace {
    /// The initial construction space `Φ ⊢_C {single-vertex diagrams} | ∅` (§50.6).
    ///
    /// §50.6 condition 1: for each `i ∈ I_Φ`, the initial diagram contains only
    /// star `Φ[i]` with a single vertex `v_i` and no edges.
    pub fn initial(phi: Constellation) -> Self {
        let n = phi.len();
        Self {
            phi,
            delta_count: n, // one seed diagram per star
            psi: Vec::new(),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Concrete execution (§50.6)
// ─────────────────────────────────────────────────────────────────────────────

/// `CEx_C(Φ)` — concrete execution (§50.6).
///
/// Drives the construction space `Φ ⊢_C {seeds} | ∅` to normal form and
/// returns the resulting constellation `CEx_C(Φ)`.
///
/// Normal form (§50.6 condition 2): no further stellar construction step can be
/// applied, i.e. every diagram in `Δ` is saturated.
///
/// By Theorem §50.7: when this terminates, `CEx_C(Φ) = AEx_C(Φ)`.
///
/// **Non-obvious choice**: the pre-expansion hack from `aex_with_copies` is NOT
/// used here. `cex` takes `phi` as-is. For Horn programs requiring multiple
/// rule applications, the caller should pre-expand with `expand_constellation`
/// (the same caveat that applied to AEx applies to CEx by §50.7).
pub fn cex(phi: &Constellation) -> Vec<Star> {
    let dg = DepGraph::from_constellation(phi);
    // The saturation algorithm in execution::saturated_diagrams implements exactly
    // the construction-space iteration of §50.5: seed with single-vertex diagrams,
    // extend by internal/external edges until saturation, collect correct ones.
    let sats = saturated_diagrams(phi, &dg);
    sats.into_iter()
        .filter_map(|d| {
            if d.is_correct(phi) {
                d.actualise(phi)
            } else {
                None
            }
        })
        .collect()
}

/// `CEx_C(Φ)` with automatic animist-star pre-expansion.
///
/// Same as `cex` but pre-expands Φ with `copies` extra copies of each animist
/// (rule) star, mirroring `aex_with_copies`. Required when the same rule star
/// must fire more than once (see `execution::expand_constellation`).
///
/// By §50.7, result equals `aex_with_copies(phi, copies)`.
pub fn cex_with_copies(phi: &Constellation, copies: usize) -> Vec<Star> {
    use crate::execution::expand_constellation;
    let expanded = expand_constellation(phi, copies);
    cex(&expanded)
}

/// `CEx_C(Φ)` with 2 extra copies (sufficient for 2+2 Horn addition).
///
/// Convenience wrapper matching `aex_full`.
pub fn cex_full(phi: &Constellation) -> Vec<Star> {
    cex_with_copies(phi, 2)
}

// ─────────────────────────────────────────────────────────────────────────────
// Concealing and noise filtering (§49.44, §49.46)
// ─────────────────────────────────────────────────────────────────────────────

/// Concealing `↨Φ` (§49.44): keep only stars all of whose rays are uncoloured.
///
/// §49.44: `I_{↨Φ} := {i ∈ I_Φ | ∀j ∈ I_{Φ[i]}, Φ[i][j] is uncoloured}`.
///
/// A ray is *uncoloured* if its head symbol is in `F₀` (neutral polarity).
pub fn conceal(phi: &[Star]) -> Vec<Star> {
    use crate::polarised::ray_polarity;
    use crate::polarised::Polarity;
    phi.iter()
        .filter(|star| {
            star.iter().all(|&r| ray_polarity(r) == Polarity::Neutral)
        })
        .cloned()
        .collect()
}

/// Noise filtering `♭Φ` (§49.46): remove empty stars from a constellation.
///
/// §49.46: `♭Φ := {i ∈ I_Φ | Φ[i] ≠ []}`.
pub fn noise_filter(phi: &[Star]) -> Vec<Star> {
    phi.iter().filter(|s| !s.is_empty()).cloned().collect()
}

/// Apply concealing `↨` then noise filtering `♭` to a constellation.
///
/// The standard post-processing step for IEx results per §55.6 and §56.5:
/// `↨♭ IEx(Φ, Ψ)`.
pub fn conceal_and_filter(phi: &[Star]) -> Vec<Star> {
    noise_filter(&conceal(phi))
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::execution::{aex_full, stars_alpha_equiv};
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::Term;

    fn var(x: &str) -> Term { crate::term::mk_var(x) }
    fn app(f: &str, args: Vec<Term>) -> Term { crate::term::mk_app_str(f, args) }
    fn c(name: &str) -> Term { crate::term::mk_app_str(name, vec![]) }

    fn nat(n: usize) -> Term {
        let mut t = c("0");
        for _ in 0..n { t = app("s", vec![t]); }
        t
    }

    fn add_prog() -> Constellation {
        vec![
            vec![pos_ray("add", vec![c("0"), var("Y"), var("Y")])],
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray("add", vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])]),
            ],
        ]
    }

    fn query_star(m: usize, n: usize) -> Star {
        vec![
            neg_ray("add", vec![nat(m), nat(n), var("R")]),
            var("R"),
        ]
    }

    /// §50.7 Theorem: CEx_C(Φ) = AEx_C(Φ) on the Horn 2+2 example.
    ///
    /// Also verifies that CEx produces [4̄] = [s(s(s(s(0))))].
    #[test]
    fn cex_equals_aex_horn_2_plus_2() {
        let mut phi = add_prog();
        phi.push(query_star(2, 2));

        let cex_results = cex_full(&phi);
        let aex_results = aex_full(&phi);

        let expected = vec![nat(4)];

        // CEx produces [4̄]
        let cex_found = cex_results.iter().any(|s| stars_alpha_equiv(s, &expected));
        assert!(
            cex_found,
            "CEx: 2+2 should produce [4̄]; got {} stars: {:?}",
            cex_results.len(),
            cex_results
        );

        // AEx produces [4̄]
        let aex_found = aex_results.iter().any(|s| stars_alpha_equiv(s, &expected));
        assert!(
            aex_found,
            "AEx: 2+2 should produce [4̄]; got {:?}",
            aex_results
        );

        // §50.7: both produce the same set of stars (up to α-equivalence).
        // Every CEx result has a matching AEx result.
        for cs in &cex_results {
            let has_match = aex_results.iter().any(|as_| stars_alpha_equiv(cs, as_));
            assert!(
                has_match,
                "CEx star {:?} has no α-equivalent match in AEx results {:?}",
                cs, aex_results
            );
        }
        // Every AEx result has a matching CEx result.
        for as_ in &aex_results {
            let has_match = cex_results.iter().any(|cs| stars_alpha_equiv(as_, cs));
            assert!(
                has_match,
                "AEx star {:?} has no α-equivalent match in CEx results {:?}",
                as_, cex_results
            );
        }
    }

    /// CEx 1+1 = 2.
    #[test]
    fn cex_horn_1_plus_1() {
        let mut phi = add_prog();
        phi.push(query_star(1, 1));
        let results = cex_full(&phi);
        let expected = vec![nat(2)];
        assert!(
            results.iter().any(|s| stars_alpha_equiv(s, &expected)),
            "CEx: 1+1 should produce [2̄]; got {:?}", results
        );
    }

    /// Concealing (§49.44): stars with coloured rays are hidden.
    #[test]
    fn conceal_removes_coloured_stars() {
        let phi: Vec<Star> = vec![
            vec![pos_ray("a", vec![])],              // coloured → hidden
            vec![c("foo"), c("bar")],                // all neutral → kept
            vec![crate::term::mk_var("X")],             // variable (neutral) → kept
            vec![neg_ray("b", vec![]), c("x")],     // mixed coloured → hidden
        ];
        let concealed = conceal(&phi);
        assert_eq!(concealed.len(), 2, "only neutral-ray stars should survive concealing");
    }

    /// Noise filtering (§49.46): empty stars are removed.
    #[test]
    fn noise_filter_removes_empty_stars() {
        let phi: Vec<Star> = vec![
            vec![c("a")],
            vec![],
            vec![c("b")],
            vec![],
        ];
        let filtered = noise_filter(&phi);
        assert_eq!(filtered.len(), 2);
    }
}
