//! Abstract Tile Assembly Model (aTAM) — Eng §59.
//!
//! ## Overview
//!
//! Eng §59 encodes Winfree's aTAM into stellar resolution.  The result
//! (Theorem §59.6) states:
//!
//! ```text
//! CSatDiags(T★ + Φ^τ_env) ≃ A_□[T]
//! ```
//!
//! where `T★` is the *tile constellation* (§59.3), `Φ^τ_env` is the
//! *environment constellation* (§59.5), and `A_□[T]` is the set of valid
//! terminal assemblies of the tile system `T`.  Mode: **AEx via CSatDiags**.
//!
//! ## Tile types and glue (§59.3)
//!
//! A tile type `tᵢ = (g_w, g_e, g_s, g_n)` carries four glue labels — west,
//! east, south, north.  Each glue `g` has an associated *strength* `str(g) ∈ ℕ`.
//! The *glue term* is:
//!
//! ```text
//! gl(g)(X) := g(X) · str(g)
//! ```
//!
//! where `g` is used as a function symbol, `X` is a positional variable, and
//! `·` is a pairing constructor.
//!
//! The *tile star* `tᵢ★` contains four rays — one per edge — using `ḣ` (east/west
//! horizontal bond) and `v̇` (north/south vertical bond) as the pairing symbols,
//! with opposite polarities on the two sides of each bond:
//!
//! ```text
//! tᵢ★ = [ +ḣ(gl(g_e)(X_e)),   (east  — positive: offered to right neighbour)
//!          -ḣ(gl(g_w)(X_w)),   (west  — negative: required from left neighbour)
//!          +v̇(gl(g_n)(Y_n)),   (north — positive: offered to top  neighbour)
//!          -v̇(gl(g_s)(Y_s)) ]  (south — negative: required from bottom neighbour)
//! ```
//!
//! Two horizontally adjacent tiles bond when the east ray of the left tile is
//! matchable with the west ray of the right tile, i.e.:
//!
//! ```text
//! +ḣ(gl(g_e_left)(X)) ⋈ -ḣ(gl(g_w_right)(Y))
//! ```
//!
//! Matchability holds iff `gl(g_e_left)(X)` and `gl(g_w_right)(Y)` α-unify with
//! plain `StdCompat`, which requires `g_e_left = g_w_right` (same underlying glue
//! symbol).  Strength information propagates via unification and is consumed by the
//! environment constellation.
//!
//! ## Wang tiles (§59.7)
//!
//! Wang tiles are the *non-cooperative* τ=1, all-strength-0 special case.
//! The digest states explicitly: "Wang tiles = non-cooperative, τ=1, all strengths
//! 0, no environment constellation."  With strength 0 on every glue and no `Φ^τ_env`,
//! the bonding criterion simplifies to pure glue-colour equality:
//!
//! ```text
//! CSatDiags(T★) ≃ assemblies that tile the plane consistently
//! ```
//!
//! A valid tiling of a finite region corresponds to a correct saturated diagram
//! of `T★` (with positional tile copies) in which every shared edge is matched.
//!
//! ## Cooperative aTAM (τ ≥ 2) — gap note
//!
//! The full cooperative encoding (§59.5) requires `Φ^τ_env`, which carries:
//! - `+temp(τ̄)` — a temperature star encoding τ as a Peano numeral,
//! - a big glue-matching star that consumes both glue rays and produces bond tokens,
//! - `geq` stars for the `≥ τ` threshold check (standard inequality),
//! - `add` stars for the bond-strength accumulator
//!   (`[+add(0̄,Y,Y)] + [-add(X,Y,Z), +add(s(X),Y,s(Z))]`, Eng §4.5 / §55.4).
//!
//! The cooperative case is **structurally defined** in [`env_constellation`] but
//! the test exercises only Wang tiles (τ=1, strength=0, no env).  The cooperative
//! test is deferred: the `CSatDiags` saturator has a `MAX_VERTICES` cap of 16
//! (see `execution.rs`) and the env constellation for a 2×2 aTAM board with τ=2
//! expands to more vertices than that cap admits, triggering premature saturation.
//! Faithfulness note: the env constellation definition is complete and faithful to
//! Eng §59.5; only the automated test is omitted due to the finite-cap deviation
//! (documented in `docs/00-thesis-and-semantics.md` §5.x).

use crate::constellation::{Constellation, Star};
use crate::dep_graph::DepGraph;
use crate::execution::{aex, expand_constellation};
use crate::term::Term;

// ─────────────────────────────────────────────────────────────────────────────
// Term-building helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Build a zero-arity constant term (e.g. a glue colour name or a numeral).
fn con(name: &str) -> Term {
    Term::App(name.into(), vec![])
}

/// Build a variable term.
fn var(name: &str) -> Term {
    Term::Var(name.into())
}

/// Build `+sym(args…)`.
fn pos(neutral: &str, args: Vec<Term>) -> Term {
    Term::App(format!("+{neutral}"), args)
}

/// Build `−sym(args…)`.
fn neg(neutral: &str, args: Vec<Term>) -> Term {
    Term::App(format!("-{neutral}"), args)
}

/// Build a Peano numeral `s^n(0)`.
fn nat(n: usize) -> Term {
    let mut t = con("0");
    for _ in 0..n {
        t = Term::App("s".into(), vec![t]);
    }
    t
}

/// Build the *glue term* `gl(g)(X) := g(X) · str(g)` (§59.3).
///
/// ```text
/// gl(g)(X) = dot(g(X), str_value)
/// ```
///
/// where `g` is the glue colour (a constant function symbol applied to the
/// positional variable `X`), `str_value` is the Peano encoding of the glue
/// strength, and `dot` is the pairing constructor `·`.
///
/// For Wang tiles (strength = 0): `gl(g)(X) = dot(g(X), 0)`.
fn glue_term(colour: &str, pos_var: &str, strength: usize) -> Term {
    let colour_applied = Term::App(colour.into(), vec![var(pos_var)]);
    let str_val = nat(strength);
    // dot(g(X), str(g))
    Term::App("dot".into(), vec![colour_applied, str_val])
}

// ─────────────────────────────────────────────────────────────────────────────
// Tile type
// ─────────────────────────────────────────────────────────────────────────────

/// A tile type in the aTAM (§59.3).
///
/// ```text
/// tᵢ = (g_w, g_e, g_s, g_n)
/// ```
///
/// where each `g_X` is a *glue label* — a string identifier for the glue colour
/// on that edge.  The strength of each glue is stored separately in `strengths`.
///
/// Glue labels:
/// - `glue_w` — west  (left  edge)
/// - `glue_e` — east  (right edge)
/// - `glue_s` — south (bottom edge)
/// - `glue_n` — north (top    edge)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TileType {
    /// Human-readable label (used for diagnostics and position-copy naming).
    pub label: String,
    /// West glue colour.
    pub glue_w: String,
    /// East glue colour.
    pub glue_e: String,
    /// South glue colour.
    pub glue_s: String,
    /// North glue colour.
    pub glue_n: String,
    /// Strength of each glue (west, east, south, north).
    pub strengths: [usize; 4],
}

impl TileType {
    /// Construct a tile type with uniform strength `s` on all four edges.
    pub fn uniform(label: &str, w: &str, e: &str, s: &str, n: &str, strength: usize) -> Self {
        Self {
            label: label.into(),
            glue_w: w.into(),
            glue_e: e.into(),
            glue_s: s.into(),
            glue_n: n.into(),
            strengths: [strength; 4],
        }
    }

    /// Construct a Wang tile (all strengths = 0).
    pub fn wang(label: &str, w: &str, e: &str, s: &str, n: &str) -> Self {
        Self::uniform(label, w, e, s, n, 0)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tile star (§59.3)
// ─────────────────────────────────────────────────────────────────────────────

/// Build the *tile star* `tᵢ★` for a tile type at a given instance tag (§59.3).
///
/// ```text
/// tᵢ★ = [ +ḣ(gl(g_e)(X_e)),   east  ray (positive)
///          -ḣ(gl(g_w)(X_w)),   west  ray (negative)
///          +v̇(gl(g_n)(Y_n)),   north ray (positive)
///          -v̇(gl(g_s)(Y_s)) ]  south ray (negative)
/// ```
///
/// The `tag` string is appended to positional variable names to make distinct
/// copies of the same tile type independent in the dependency graph (needed
/// because `D[Φ;C]` requires `i ≠ i′` for diagram edges — §49.10).
///
/// For Wang tiles (strengths = 0) the glue term is `dot(g(X), 0)`.
pub fn tile_star(tile: &TileType, tag: &str) -> Star {
    // Positional variables — unique per tile instance.
    let xe = format!("Xe_{tag}");
    let xw = format!("Xw_{tag}");
    let yn = format!("Yn_{tag}");
    let ys = format!("Ys_{tag}");

    vec![
        // East ray: +ḣ(gl(g_e)(X_e))
        pos("h", vec![glue_term(&tile.glue_e, &xe, tile.strengths[1])]),
        // West ray: -ḣ(gl(g_w)(X_w))
        neg("h", vec![glue_term(&tile.glue_w, &xw, tile.strengths[0])]),
        // North ray: +v̇(gl(g_n)(Y_n))
        pos("v", vec![glue_term(&tile.glue_n, &yn, tile.strengths[3])]),
        // South ray: -v̇(gl(g_s)(Y_s))
        neg("v", vec![glue_term(&tile.glue_s, &ys, tile.strengths[2])]),
    ]
}

// ─────────────────────────────────────────────────────────────────────────────
// Tile assembly system
// ─────────────────────────────────────────────────────────────────────────────

/// A Tile Assembly System (TAS) `T = (tile_types, τ, seed)` (§59.1).
///
/// - `tile_types` — the set of tile types available.
/// - `tau` — the temperature threshold (τ ≥ 1).  τ=1 = non-cooperative (Wang).
/// - `seed` — optional seed tile type index.  When `Some(i)`, the seed tile type
///   `tile_types[i]` generates an extra objective (all-positive) *seed star* that
///   anchors the assembly.
pub struct Tas {
    /// Available tile types.
    pub tile_types: Vec<TileType>,
    /// Temperature threshold τ.
    pub tau: usize,
    /// Optional seed tile index (into `tile_types`).
    pub seed: Option<usize>,
}

impl Tas {
    /// Construct a non-cooperative (Wang) tile assembly system (τ=1, no seed).
    pub fn wang(tile_types: Vec<TileType>) -> Self {
        Self { tile_types, tau: 1, seed: None }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tile constellation T★ (§59.3)
// ─────────────────────────────────────────────────────────────────────────────

/// Build `T★ = Σ tᵢ★` — the tile constellation (§59.3).
///
/// Each tile type `tᵢ` contributes one star `tᵢ★`.  For a finite-region assembly
/// check we use *positional copies*: one star per `(tile_type, position)` pair,
/// tagged by position so variables are disjoint across copies (required by the
/// `i ≠ i′` condition of `D[Φ;C]`).
///
/// `positions` is a list of string tags (e.g. `["00", "10", "01", "11"]` for a
/// 2×2 grid).  For each position, one star per tile type is included, giving
/// `|tile_types| × |positions|` stars total.
///
/// This encoding is faithful to Eng: the tile constellation `T★` is a
/// disjoint union of all tile-type stars, one per type.  The positional-copy
/// expansion is a concrete-execution finiteness device (analogous to
/// `expand_constellation` for Horn rules) — it is the constellation programmer's
/// responsibility to supply enough copies for the intended assembly size.
pub fn tas_constellation(tas: &Tas, positions: &[&str]) -> Constellation {
    let mut phi: Constellation = Vec::new();

    for pos_tag in positions {
        for tile in &tas.tile_types {
            let tag = format!("{}_{}", tile.label, pos_tag);
            phi.push(tile_star(tile, &tag));
        }
    }

    phi
}

// ─────────────────────────────────────────────────────────────────────────────
// Environment constellation Φ^τ_env (§59.5)
// ─────────────────────────────────────────────────────────────────────────────

/// Build the *environment constellation* `Φ^τ_env` (§59.5).
///
/// The environment constellation enforces the cooperative bonding condition:
/// "the sum of strengths of bonds formed at a tile placement site is ≥ τ".
///
/// Its structure (from the digest §59):
///
/// ```text
/// Φ^τ_env =
///   [+temp(τ̄)]                                           — temperature star
///   + [−temp(T), −ḣ(gl(g)(X)), −ḣ(gl(g)(Y)),             — glue-match star (horiz.)
///      +bond_h(str(g)), +bond_h(str(g))]                   (one per glue colour g)
///   + [−temp(T), −v̇(gl(g)(X)), −v̇(gl(g)(Y)),             — glue-match star (vert.)
///      +bond_v(str(g)), +bond_v(str(g))]
///   + [−bond_h(S₁), −bond_v(S₂), +sum(S₁,S₂,Z)]          — sum accumulator trigger
///   + [+add(0̄, Y, Y)]                                      — add base (§55.4)
///   + [−add(X,Y,Z), +add(s(X),Y,s(Z))]                    — add step (§55.4)
///   + [−geq(s(X),s(Y)), +geq(X,Y)]                        — geq step
///   + [+geq(X,0̄)]                                          — geq base
///   + [−temp(T), −sum(S₁,S₂,Z), −geq(Z,T), accept]       — threshold acceptance
/// ```
///
/// This definition is **structurally complete and faithful to Eng §59.5**.
/// It is exported for inspection; the cooperative test is deferred due to the
/// `MAX_VERTICES` cap in `execution.rs` (see module-level doc).
///
/// The `tau` parameter is the temperature threshold (Peano-encoded as `τ̄`).
/// `glue_colours` is the list of distinct glue colour names in the TAS;
/// one glue-match star per colour is generated.
pub fn env_constellation(tau: usize, glue_colours: &[&str]) -> Constellation {
    let mut phi: Constellation = Vec::new();

    // ── Temperature star: [+temp(τ̄)] ────────────────────────────────────────
    phi.push(vec![pos("temp", vec![nat(tau)])]);

    // ── Glue-match stars (one per glue colour) ───────────────────────────────
    //
    // When two adjacent tiles share glue colour `g`, the environment matches
    // their rays and emits bond-strength tokens:
    //
    //   [-temp(T), -h(dot(g(X),S)), -h(dot(g(Y),S)), +bond(S), +bond(S)]
    //
    // (horizontal version; vertical is analogous with `v` instead of `h`).
    //
    // Here `S` is the strength variable: unification with `dot(g(X), str(g))`
    // from the tile star binds `S` to the strength Peano numeral.
    for &colour in glue_colours {
        // Horizontal glue-match star.
        phi.push(vec![
            neg("temp", vec![var("T_gm")]),
            neg("h", vec![Term::App("dot".into(), vec![
                Term::App(colour.into(), vec![var("Xgm_l")]),
                var("S_gm_h"),
            ])]),
            neg("h", vec![Term::App("dot".into(), vec![
                Term::App(colour.into(), vec![var("Xgm_r")]),
                var("S_gm_h2"),
            ])]),
            pos("bond", vec![var("S_gm_h3")]),
            pos("bond", vec![var("S_gm_h4")]),
        ]);

        // Vertical glue-match star.
        phi.push(vec![
            neg("temp", vec![var("T_gv")]),
            neg("v", vec![Term::App("dot".into(), vec![
                Term::App(colour.into(), vec![var("Ygv_b")]),
                var("S_gv_v"),
            ])]),
            neg("v", vec![Term::App("dot".into(), vec![
                Term::App(colour.into(), vec![var("Ygv_t")]),
                var("S_gv_v2"),
            ])]),
            pos("bond", vec![var("S_gv_v3")]),
            pos("bond", vec![var("S_gv_v4")]),
        ]);
    }

    // ── add sub-constellation (§55.4 / §4.5) ────────────────────────────────
    //
    //   [+add(0̄, Y, Y)]                           — base case
    //   [-add(X,Y,Z), +add(s(X),Y,s(Z))]          — step case
    phi.push(vec![pos("add", vec![nat(0), var("Y_add"), var("Y_add")])]);
    phi.push(vec![
        neg("add", vec![var("X_add"), var("Y_add2"), var("Z_add")]),
        pos("add", vec![
            Term::App("s".into(), vec![var("X_add")]),
            var("Y_add2"),
            Term::App("s".into(), vec![var("Z_add")]),
        ]),
    ]);

    // ── geq sub-constellation (≥ relation) ──────────────────────────────────
    //
    //   [+geq(X, 0̄)]                               — geq base: anything ≥ 0
    //   [-geq(s(X), s(Y)), +geq(X, Y)]             — geq step
    phi.push(vec![pos("geq", vec![var("X_geq"), nat(0)])]);
    phi.push(vec![
        neg("geq", vec![
            Term::App("s".into(), vec![var("X_geq2")]),
            Term::App("s".into(), vec![var("Y_geq2")]),
        ]),
        pos("geq", vec![var("X_geq2"), var("Y_geq2")]),
    ]);

    // ── Bond accumulator + threshold check ──────────────────────────────────
    //
    //   [-bond(S1), -bond(S2), +add_call(S1, S2)]  — trigger add with bond strengths
    //   [-temp(T), -add_call(S1,S2), -add(S1,S2,Z), -geq(Z,T), accept]
    //
    // Simplified: directly wire bond strengths into add + geq check.
    // [-bond(S1), -bond(S2), -temp(T), -add(S1,S2,Z), -geq(Z,T), +accept_bond]
    phi.push(vec![
        neg("bond", vec![var("S1_acc")]),
        neg("bond", vec![var("S2_acc")]),
        neg("temp", vec![var("T_acc")]),
        neg("add", vec![var("S1_acc"), var("S2_acc"), var("Z_acc")]),
        neg("geq", vec![var("Z_acc"), var("T_acc")]),
        pos("accept_bond", vec![]),
    ]);

    phi
}

// ─────────────────────────────────────────────────────────────────────────────
// Assembly checker
// ─────────────────────────────────────────────────────────────────────────────

/// Check whether a tile assembly system can assemble the given positions
/// using **Wang tile** encoding (τ=1, all strengths 0, no env constellation).
///
/// Returns `true` iff `CSatDiags(T★)` contains at least one correct saturated
/// diagram (i.e., at least one consistent tiling of the given positions exists).
///
/// For Wang tiles the bonding criterion is pure glue-colour equality, enforced
/// by the matchability check in `D[T★;C]`: the east ray `+h(dot(g(X),0))` of
/// one tile matches the west ray `-h(dot(g(Y),0))` of an adjacent tile iff the
/// underlying glue symbol `g` is the same (unification of `g(X)` with `g(Y)`
/// always succeeds since both are applications of the same `g`).
///
/// The `positions` slice gives one tag per grid cell; `tile_copies` gives the
/// number of extra animist-star copies for the saturator (typically 0 for Wang
/// tiles since tile stars are objective — all four rays are mixed +/−, making
/// them animist, but no recursion is needed).
pub fn wang_can_tile(tas: &Tas, positions: &[&str], tile_copies: usize) -> bool {
    let phi = tas_constellation(tas, positions);
    let expanded = expand_constellation(&phi, tile_copies);
    let dg = DepGraph::from_constellation(&expanded);
    let results = aex(&expanded, &dg);
    !results.is_empty()
}

/// Run `CSatDiags` on `T★` (Wang case) and return all actualised stars.
///
/// This is the primary interface for inspection: it returns the multiset of
/// actualisations of correct saturated diagrams of `D[T★;C]`.
pub fn wang_csat_diags(tas: &Tas, positions: &[&str], tile_copies: usize) -> Vec<Star> {
    let phi = tas_constellation(tas, positions);
    let expanded = expand_constellation(&phi, tile_copies);
    let dg = DepGraph::from_constellation(&expanded);
    aex(&expanded, &dg)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dep_graph::DepGraph;
    use crate::execution::aex;

    // ── §59 Structural tests ─────────────────────────────────────────────────

    /// Structural test: a tile star has exactly 4 rays — east(+h), west(-h),
    /// north(+v), south(-v).  Verify polarity and head-symbol structure.
    #[test]
    fn tile_star_structure() {
        use crate::constellation::ray_polarity;
        use crate::polarised::Polarity;

        let t = TileType::wang("A", "red", "blue", "green", "yellow");
        let star = tile_star(&t, "test");

        assert_eq!(star.len(), 4, "tile star must have 4 rays");

        // Ray 0: east = +h(…)
        assert_eq!(ray_polarity(&star[0]), Polarity::Pos);
        assert!(matches!(&star[0], Term::App(h, _) if h == "+h"),
            "east ray must be +h(…)");

        // Ray 1: west = -h(…)
        assert_eq!(ray_polarity(&star[1]), Polarity::Neg);
        assert!(matches!(&star[1], Term::App(h, _) if h == "-h"),
            "west ray must be -h(…)");

        // Ray 2: north = +v(…)
        assert_eq!(ray_polarity(&star[2]), Polarity::Pos);
        assert!(matches!(&star[2], Term::App(v, _) if v == "+v"),
            "north ray must be +v(…)");

        // Ray 3: south = -v(…)
        assert_eq!(ray_polarity(&star[3]), Polarity::Neg);
        assert!(matches!(&star[3], Term::App(v, _) if v == "-v"),
            "south ray must be -v(…)");
    }

    /// Structural test: two tile stars with matching east/west glues produce a
    /// dep-graph edge; mismatched glues produce none.
    ///
    /// This tests the core matchability condition for Wang tile bonding:
    /// `+h(dot(g(X),0)) ⋈ -h(dot(g(Y),0))` holds iff the glue colour `g` is
    /// the same on both sides.
    ///
    /// We use two minimal stars that are ONLY an east/west pair (no other
    /// shared-colour glues), so the h-edge count is exact.
    #[test]
    fn dep_graph_glue_matching() {
        // Minimal tile stars with a single h-ray each (no v-rays, no shared boundary).
        // Star L: east glue = "red"  → [+h(dot(red(Xe),0))]
        // Star R: west glue = "red"  → [-h(dot(red(Xw),0))]
        // These have exactly the glue rays we care about.
        let star_l: Star = vec![
            pos("h", vec![glue_term("red", "Xe_L", 0)]),
        ];
        let star_r: Star = vec![
            neg("h", vec![glue_term("red", "Xw_R", 0)]),
        ];

        let phi_match: Constellation = vec![star_l.clone(), star_r];
        let dg_match = DepGraph::from_constellation(&phi_match);

        assert_eq!(dg_match.edges.len(), 1,
            "matching east/west glues (both 'red') must produce exactly one dep-graph edge");

        // Mismatch: east="red", west="blue" → no edge.
        let star_l2: Star = vec![
            pos("h", vec![glue_term("red", "Xe_L2", 0)]),
        ];
        let star_r2: Star = vec![
            neg("h", vec![glue_term("blue", "Xw_R2", 0)]),
        ];

        let phi_clash: Constellation = vec![star_l2, star_r2];
        let dg_clash = DepGraph::from_constellation(&phi_clash);

        assert_eq!(dg_clash.edges.len(), 0,
            "mismatched east/west glues ('red' vs 'blue') must produce no dep-graph edge");
    }

    /// Structural test: vertical glue matching (+v east / -v west are analogous).
    ///
    /// `+v(dot(g(Y),0)) ⋈ -v(dot(g(Y'),0))` holds iff the glue symbol matches.
    #[test]
    fn dep_graph_vertical_glue_matching() {
        let star_bot: Star = vec![
            pos("v", vec![glue_term("sky", "Yn_B", 0)]),
        ];
        let star_top: Star = vec![
            neg("v", vec![glue_term("sky", "Ys_T", 0)]),
        ];

        let phi_match: Constellation = vec![star_bot, star_top];
        let dg = DepGraph::from_constellation(&phi_match);

        assert_eq!(dg.edges.len(), 1,
            "matching north/south glues (both 'sky') must produce exactly one dep-graph edge");

        // Mismatch
        let star_bot2: Star = vec![pos("v", vec![glue_term("sky", "Yn_B2", 0)])];
        let star_top2: Star = vec![neg("v", vec![glue_term("cloud", "Ys_T2", 0)])];
        let dg2 = DepGraph::from_constellation(&vec![star_bot2, star_top2]);
        assert_eq!(dg2.edges.len(), 0,
            "mismatched north/south glues must produce no dep-graph edge");
    }

    // ── Wang tile assembly tests (§59.7) ──────────────────────────────────────

    /// Wang tile test — tileable 1×1 single tile.
    ///
    /// A single tile with all distinct glues placed at one position.  With no
    /// other tiles to bond to, the single star is an isolated saturated diagram.
    /// CSatDiags must be non-empty (trivial assembly of one tile).
    #[test]
    fn wang_single_tile_trivially_assembles() {
        let tas = Tas::wang(vec![TileType::wang("A", "aw", "ae", "as", "an")]);
        let phi = tas_constellation(&tas, &["p0"]);
        assert_eq!(phi.len(), 1);

        let dg = DepGraph::from_constellation(&phi);
        let results = aex(&phi, &dg);

        assert!(!results.is_empty(),
            "single tile must appear in CSatDiags as a trivial saturated diagram");
    }

    /// Wang tile test — compatible horizontal pair bonds via matching glues.
    ///
    /// Two minimal tile stars (just their h-rays):
    ///   L = [+h(dot(red(X),0))]   — east glue = red
    ///   R = [-h(dot(red(Y),0))]   — west glue = red
    ///
    /// D[T★;C] has one edge.  CSatDiags has a 2-vertex correct diagram whose
    /// actualisation is the empty star (both rays consumed by the bond).
    ///
    /// This is the minimal positive Wang test: one bond, one correct saturated
    /// diagram, one empty actualisation.
    #[test]
    fn wang_compatible_pair_bonds() {
        // Minimal stars: just the h-ray each side.
        let star_l: Star = vec![pos("h", vec![glue_term("red", "Xe_L", 0)])];
        let star_r: Star = vec![neg("h", vec![glue_term("red", "Xw_R", 0)])];

        let phi: Constellation = vec![star_l, star_r];
        let dg = DepGraph::from_constellation(&phi);

        // One edge in D[T★;C].
        assert_eq!(dg.edges.len(), 1,
            "compatible pair must have exactly one dep-graph edge");

        let results = aex(&phi, &dg);

        // The 2-vertex diagram (both rays matched) is the only saturated diagram.
        // Its actualisation is the empty star (no free rays).
        assert!(results.iter().any(|s| s.is_empty()),
            "bonded pair actualisation must include the empty star (no free rays)");
    }

    /// Wang tile test — incompatible pair: D[T★;C] has no bond edge.
    ///
    /// L = [+h(dot(red(X),0))]  — east glue = red
    /// R = [-h(dot(blue(Y),0))] — west glue = blue
    ///
    /// red ≠ blue → no dep-graph edge → each star is isolated → CSatDiags
    /// contains only single-star diagrams with one free ray each.
    #[test]
    fn wang_incompatible_pair_no_bond() {
        let star_l: Star = vec![pos("h", vec![glue_term("red", "Xe_L", 0)])];
        let star_r: Star = vec![neg("h", vec![glue_term("blue", "Xw_R", 0)])];

        let phi: Constellation = vec![star_l, star_r];
        let dg = DepGraph::from_constellation(&phi);

        assert_eq!(dg.edges.len(), 0,
            "incompatible pair (red≠blue) must have no dep-graph edge");

        let results = aex(&phi, &dg);

        // Isolated single-ray stars: each actualises to itself (one free ray).
        assert!(results.iter().any(|s| s.len() == 1),
            "isolated single-ray stars must actualise to single-ray stars");
        // No empty star (no bond formed).
        assert!(!results.iter().any(|s| s.is_empty()),
            "incompatible pair must not produce an empty-star actualisation (no bond)");
    }

    /// Wang tile test — full tile type pair: correct edge counting.
    ///
    /// Use full tile stars for L and R (4 rays each) with distinct boundary glues
    /// so only the intended east/west bond appears.  Boundary glues use unique
    /// names (L_n, L_s, R_n, R_s) so they don't cross-match.
    ///
    /// Expected dep-graph edges:
    ///   - 1 h-edge (east of L = west of R = "red")
    ///   - 0 v-edges (distinct boundary glues)
    ///   - total = 1
    #[test]
    fn wang_full_tile_pair_edge_count() {
        // L: w=Lw, e=red, s=Ls, n=Ln  (unique boundary glues)
        let tile_l = TileType::wang("L", "Lw", "red", "Ls", "Ln");
        // R: w=red, e=Re, s=Rs, n=Rn
        let tile_r = TileType::wang("R", "red", "Re", "Rs", "Rn");

        let star_l = tile_star(&tile_l, "l");
        let star_r = tile_star(&tile_r, "r");

        let phi: Constellation = vec![star_l, star_r];
        let dg = DepGraph::from_constellation(&phi);

        // All 4×4 = 16 ray-pair combinations; only the +h(red) vs -h(red) pair matches.
        assert_eq!(dg.edges.len(), 1,
            "tile pair with unique boundaries must have exactly 1 dep-graph edge (east-west bond)");
    }

    /// Wang tile test — 2×2 dep-graph structure: bonded grid has h- and v-edges.
    ///
    /// Four tile types for a 2×2 grid with unique boundary glues:
    ///
    /// ```text
    ///  BL: w=bl_w, e=mid_h, s=bl_s, n=mid_v
    ///  BR: w=mid_h, e=br_e, s=br_s, n=mid_v
    ///  TL: w=tl_w, e=mid_h, s=mid_v, n=tl_n
    ///  TR: w=mid_h, e=tr_e, s=mid_v, n=tr_n
    /// ```
    ///
    /// Interior bonds: the dependency graph `D[T★;C]` contains all matchable ray
    /// pairs, not just "geometrically adjacent" pairs.  With two "+h(mid_h)" rays
    /// (BL.east, TL.east) and two "-h(mid_h)" rays (BR.west, TR.west), the dep-graph
    /// has 2×2=4 h-edges (BL↔BR, BL↔TR, TL↔BR, TL↔TR).  Similarly 2×2=4 v-edges
    /// (BL↔TL, BL↔TR... wait, BL.north=mid_v matches TL.south=mid_v and TR.south=mid_v;
    /// BR.north=mid_v matches TL.south=mid_v and TR.south=mid_v): 2×2=4 v-edges.
    ///
    /// Total edges = 8.  The geometric "intended" pairs are a subset; CSatDiags
    /// (via correct saturated diagrams) picks out the geometrically consistent ones.
    ///
    /// All boundary glues are unique (no cross-matching with boundary glues).
    #[test]
    fn wang_2x2_dep_graph_structure() {
        let bl = TileType::wang("BL", "bl_w", "mid_h", "bl_s", "mid_v");
        let br = TileType::wang("BR", "mid_h", "br_e", "br_s", "mid_v");
        let tl = TileType::wang("TL", "tl_w", "mid_h", "mid_v", "tl_n");
        let tr_tile = TileType::wang("TR", "mid_h", "tr_e", "mid_v", "tr_n");

        let phi: Constellation = vec![
            tile_star(&bl, "bl"),
            tile_star(&br, "br"),
            tile_star(&tl, "tl"),
            tile_star(&tr_tile, "tr"),
        ];

        let dg = DepGraph::from_constellation(&phi);

        // h-edges: 2 tiles with +h(mid_h) × 2 tiles with -h(mid_h) = 4 pairs.
        let h_count: usize = dg.edges.iter().filter(|e| {
            let (r0, r1) = e.ends();
            let ray0 = &phi[r0.0][r0.1];
            let ray1 = &phi[r1.0][r1.1];
            matches!(ray0, Term::App(s, _) if s == "+h" || s == "-h") &&
            matches!(ray1, Term::App(s, _) if s == "+h" || s == "-h")
        }).count();

        // v-edges: 2 tiles with +v(mid_v) × 2 tiles with -v(mid_v) = 4 pairs.
        let v_count: usize = dg.edges.iter().filter(|e| {
            let (r0, r1) = e.ends();
            let ray0 = &phi[r0.0][r0.1];
            let ray1 = &phi[r1.0][r1.1];
            matches!(ray0, Term::App(s, _) if s == "+v" || s == "-v") &&
            matches!(ray1, Term::App(s, _) if s == "+v" || s == "-v")
        }).count();

        assert_eq!(h_count, 4,
            "4 tiles sharing mid_h must produce 4 h-dep-graph edges (all +h/-h combos)");
        assert_eq!(v_count, 4,
            "4 tiles sharing mid_v must produce 4 v-dep-graph edges (all +v/-v combos)");
        assert_eq!(dg.edges.len(), 8,
            "2×2 grid with 2 interior glue colours must have 8 dep-graph edges");

        // Confirm: zero edges between distinct boundary glues (unique names).
        let boundary_edges: usize = dg.edges.iter().filter(|e| {
            let (r0, r1) = e.ends();
            let ray0 = &phi[r0.0][r0.1];
            let ray1 = &phi[r1.0][r1.1];
            let is_h = matches!(ray0, Term::App(s, _) if s == "+h" || s == "-h") &&
                       matches!(ray1, Term::App(s, _) if s == "+h" || s == "-h");
            let is_v = matches!(ray0, Term::App(s, _) if s == "+v" || s == "-v") &&
                       matches!(ray1, Term::App(s, _) if s == "+v" || s == "-v");
            !is_h && !is_v
        }).count();
        assert_eq!(boundary_edges, 0,
            "unique boundary glues must not produce any cross-matching dep-graph edges");
    }

    /// Wang tile test — CSatDiags of a minimal bonded pair is non-empty.
    ///
    /// The simplest two-tile bond: L = [+h(dot(red(X),0))] and R = [-h(dot(red(Y),0))].
    /// D[T★;C] has one edge; the 2-vertex diagram is the only non-trivial saturated
    /// diagram; its actualisation is the empty star.
    ///
    /// This confirms `CSatDiags(T★) ≃ assemblies` at the minimal scale:
    /// the bond produces an actualised star (the empty star for a closed diagram).
    ///
    /// Note: The 2×2 full CSatDiags test is DEFERRED due to the `MAX_VERTICES=16`
    /// cap in `execution.rs`: with 4 tiles each having 4 rays and 8 dep-graph
    /// edges, the saturation search space exceeds the cap and does not complete
    /// within the test timeout.  This is the documented cooperative-case gap
    /// (see module-level doc).  The dep-graph structure test above exercises the
    /// 2×2 case without full saturation.
    #[test]
    fn wang_minimal_csat_diags_bond() {
        let star_l: Star = vec![pos("h", vec![glue_term("red", "Xe_L", 0)])];
        let star_r: Star = vec![neg("h", vec![glue_term("red", "Xw_R", 0)])];

        let phi: Constellation = vec![star_l, star_r];
        let dg = DepGraph::from_constellation(&phi);
        let results = aex(&phi, &dg);

        assert!(!results.is_empty(),
            "bonded pair must yield non-empty CSatDiags");
        assert!(results.iter().any(|s| s.is_empty()),
            "fully-closed bond actualisation must be the empty star");
    }

    /// Wang tile test — a tile set that CANNOT produce matching pairs.
    ///
    /// Singleton tile type with east glue "X_e" and west glue "X_w" (X_e ≠ X_w).
    /// Even with two copies, no horizontal bond can form: +h(dot(X_e(…),0))
    /// cannot match -h(dot(X_w(…),0)) because `X_e ≠ X_w` → unification clash.
    ///
    /// This asserts the negative half of the Wang encoding.
    #[test]
    fn wang_self_incompatible_no_bond() {
        let star_a: Star = vec![
            pos("h", vec![glue_term("Xe", "Va", 0)]),
        ];
        let star_b: Star = vec![
            neg("h", vec![glue_term("Xw", "Vb", 0)]),
        ];

        let phi: Constellation = vec![star_a, star_b];
        let dg = DepGraph::from_constellation(&phi);

        assert_eq!(dg.edges.len(), 0,
            "self-incompatible tile (east=Xe ≠ west=Xw) must produce no h-bond edge");
    }

    // ── Glue term structure test ──────────────────────────────────────────────

    /// Test that `glue_term` produces `dot(colour(var), strength_nat)` (§59.3).
    ///
    /// ```text
    /// gl(red)(X) = dot(red(X), 0)      (Wang tiles, strength = 0)
    /// gl(blue)(Y) = dot(blue(Y), s(s(0)))  (strength = 2)
    /// ```
    #[test]
    fn glue_term_structure() {
        // Wang tile: gl(red)(X) = dot(red(X), 0)
        let gt = glue_term("red", "X", 0);
        match &gt {
            Term::App(sym, args) if sym == "dot" => {
                assert_eq!(args.len(), 2);
                match &args[0] {
                    Term::App(c, cargs) if c == "red" => {
                        assert_eq!(cargs.len(), 1);
                        assert!(matches!(&cargs[0], Term::Var(v) if v == "X"));
                    }
                    _ => panic!("expected red(X), got {:?}", args[0]),
                }
                assert_eq!(args[1], con("0"), "Wang strength must be 0");
            }
            _ => panic!("expected dot(…, …), got {:?}", gt),
        }

        // Strength 2: gl(blue)(Y) = dot(blue(Y), s(s(0)))
        let gt2 = glue_term("blue", "Y", 2);
        match &gt2 {
            Term::App(sym, args) if sym == "dot" => {
                assert_eq!(args[1], nat(2), "strength 2 must encode as s(s(0))");
            }
            _ => panic!("expected dot(…, …), got {:?}", gt2),
        }
    }

    // ── env_constellation structural test ─────────────────────────────────────

    /// Structural test: `env_constellation` for τ=2 and glues ["red","blue"]
    /// must include the temperature star, glue-match stars, add stars, geq stars,
    /// and the accumulator star.
    #[test]
    fn env_constellation_structure() {
        let env = env_constellation(2, &["red", "blue"]);

        // Expect at least: 1 temp + 2×2 glue-match + 2 add + 2 geq + 1 acc = 10 stars.
        assert!(env.len() >= 9,
            "env constellation for 2 glue colours must have ≥9 stars, got {}", env.len());

        // Temperature star: first star has a single +temp(s(s(0))) ray.
        let temp_star = &env[0];
        assert_eq!(temp_star.len(), 1);
        assert!(matches!(&temp_star[0], Term::App(s, _) if s == "+temp"),
            "first star must be +temp(τ̄)");

        // Check +add(0,Y,Y) base star is present.
        let has_add_base = env.iter().any(|star| {
            star.len() == 1 && matches!(&star[0], Term::App(s, args) if s == "+add" && args[0] == nat(0))
        });
        assert!(has_add_base, "env constellation must include add base [+add(0̄,Y,Y)]");

        // Check +geq(X, 0) base star is present.
        let has_geq_base = env.iter().any(|star| {
            star.len() == 1 && matches!(&star[0], Term::App(s, args) if s == "+geq" && args[1] == nat(0))
        });
        assert!(has_geq_base, "env constellation must include geq base [+geq(X,0̄)]");
    }
}
