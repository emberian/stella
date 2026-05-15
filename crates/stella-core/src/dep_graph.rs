//! Dependency graph `D[Φ; C]` (Eng §49.10–§49.14).
//!
//! §49.10: Let `Φ` be a constellation and `C ⊆ F₊ ∪ F₋` a set of *coloured*
//! symbols.  The **dependency graph** `D[Φ; C]` is the multigraph:
//!
//! - **Vertices** = `I_Φ` (star indices).
//! - **Edges** = `{ {(i,j),(i′,j′)} | r = Φ[i][j], r′ = Φ[i′][j′],
//!                                      r ⋈ r′, i ≠ i′,
//!                                      colours(r) ∪ colours(r′) ⊆ C }`.
//!
//! where:
//! - `r ⋈ r′` is matchability ([`crate::polarised::matchable`]).
//! - `colours(r)` for a ray `r = f(…)` is `{f}` if `f` is coloured (positive
//!   or negative), else `∅` (§48.4; Eng uses colours to restrict which symbols
//!   participate).
//!
//! ## Non-obvious choices
//!
//! **Colour set `C`**: Eng specifies `C ⊆ F₊ ∪ F₋`.  In practice we represent
//! `C` as a `HashSet<String>` of symbol names (e.g. `"+add"`, `"-add"`).  A
//! ray whose head is *not* in `C` still participates: Eng's condition is
//! `colours(r) ∪ colours(r′) ⊆ C`, and `colours(r) = ∅` when `r` is neutral,
//! so neutral rays are always compatible with any `C`.  However, for Horn
//! encoding (§55) every relevant ray is coloured; using `C = all_coloured`
//! (the set of all coloured symbols appearing in Φ) is the standard choice,
//! which we expose as `DepGraph::from_constellation`.
//!
//! **Self-edges**: §49.10 requires `i ≠ i′` (rays from *different* stars).
//! We enforce this.
//!
//! **Multigraph**: Eng says "multigraph" because two different pairs of rays
//! can give rise to "the same" vertex pair.  We store edges as a `Vec` of
//! unordered pairs of `RayId`.

use std::collections::{HashMap, HashSet};

use crate::constellation::{get_ray, id_rays, Constellation, RayId};
use crate::polarised::{matchable, parse_symbol, Polarity};

// ─────────────────────────────────────────────────────────────────────────────
// Colour set helpers
// ─────────────────────────────────────────────────────────────────────────────

/// `colours(r)` for a ray (§48.4): the set of coloured (non-neutral) symbols
/// in `r`'s head.  Returns the head symbol name if it is coloured, else `∅`.
///
/// Non-obvious choice: Eng defines `colours(r)` as the coloured symbols in the
/// *entire* term, but for the edge condition of `D[Φ;C]` only the *head* symbol
/// matters (the edge condition is about which symbol of the polarised signature
/// is being "matched").  We follow the head-only interpretation consistent with
/// §49.10's statement: an edge exists when the colours of `r` and `r′` are
/// subsets of `C`.  Because `matchable` already checks the head, and because
/// in practice Eng's examples only have one coloured symbol per ray (the head),
/// we use the head.
pub fn ray_colours(r: &crate::polarised::Ray) -> HashSet<String> {
    match r {
        crate::term::Term::Var(_) => HashSet::new(),
        crate::term::Term::App(sym, _) => {
            let ps = parse_symbol(sym);
            if ps.polarity != Polarity::Neutral {
                let mut s = HashSet::new();
                s.insert(sym.clone());
                s
            } else {
                HashSet::new()
            }
        }
    }
}

/// Collect all coloured (non-neutral) head symbols from a constellation.
pub fn all_colours(phi: &Constellation) -> HashSet<String> {
    id_rays(phi)
        .into_iter()
        .flat_map(|id| ray_colours(get_ray(phi, id)))
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// Dependency graph
// ─────────────────────────────────────────────────────────────────────────────

/// An edge in the dependency graph `D[Φ; C]`.
///
/// An edge is an unordered pair of ray identifiers `{(i,j), (i′,j′)}` (§49.10).
/// We store them as a sorted pair `(lo, hi)` so that equality and hashing are
/// well-defined.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DepEdge {
    /// The two ray identifiers, in a canonical (sorted) order.
    pub endpoints: [RayId; 2],
}

impl DepEdge {
    /// Construct a `DepEdge`, normalising to sorted order.
    pub fn new(a: RayId, b: RayId) -> Self {
        if a <= b {
            Self { endpoints: [a, b] }
        } else {
            Self { endpoints: [b, a] }
        }
    }

    /// The two endpoint ray identifiers.
    pub fn ends(&self) -> (RayId, RayId) {
        (self.endpoints[0], self.endpoints[1])
    }

    /// The two star indices connected by this edge.
    pub fn star_indices(&self) -> (usize, usize) {
        (self.endpoints[0].0, self.endpoints[1].0)
    }

    /// Does this edge have the given ray id as an endpoint?
    pub fn contains_ray(&self, rid: RayId) -> bool {
        self.endpoints[0] == rid || self.endpoints[1] == rid
    }
}

/// The dependency graph `D[Φ; C]` (§49.10).
///
/// Stores the edges as a vector (multigraph: duplicates allowed if two
/// ray-pairs yield the same star pair, which cannot happen for simple rays
/// but the API is general).
#[derive(Debug, Clone)]
pub struct DepGraph {
    /// Number of stars (= number of vertices).
    pub n_stars: usize,
    /// The multiset of edges in `D[Φ; C]`.
    pub edges: Vec<DepEdge>,
}

impl DepGraph {
    /// Build `D[Φ; C]` for a given colour set `C` (§49.10).
    ///
    /// `C` is a set of coloured symbol names (e.g. `{"+add", "-add"}`).
    /// Pass `all_colours(phi)` for the "use all" case.
    pub fn build(phi: &Constellation, c: &HashSet<String>) -> Self {
        let ids: Vec<RayId> = id_rays(phi);
        let mut edges = Vec::new();

        for (a, &rid_a) in ids.iter().enumerate() {
            for &rid_b in &ids[a + 1..] {
                // §49.10: i ≠ i′ (different stars)
                if rid_a.0 == rid_b.0 {
                    continue;
                }
                let r = get_ray(phi, rid_a);
                let rp = get_ray(phi, rid_b);

                // colour condition: colours(r) ∪ colours(r′) ⊆ C
                let cr = ray_colours(r);
                let crp = ray_colours(rp);
                if !cr.is_subset(c) || !crp.is_subset(c) {
                    continue;
                }

                // matchability: r ⋈ r′
                if matchable(r, rp) {
                    edges.push(DepEdge::new(rid_a, rid_b));
                }
            }
        }

        Self { n_stars: phi.len(), edges }
    }

    /// Build `D[Φ; all_colours(Φ)]` — the standard choice for Horn execution.
    pub fn from_constellation(phi: &Constellation) -> Self {
        let c = all_colours(phi);
        Self::build(phi, &c)
    }

    /// `adj^C_Φ(i, j)` — the multiset of ray ids adjacent to `(i, j)` (§49.12).
    ///
    /// A ray `(i′, j′)` is adjacent to `(i, j)` if there is an edge
    /// `{(i,j), (i′,j′)}` in `D[Φ;C]`.
    pub fn adj(&self, rid: RayId) -> Vec<RayId> {
        let mut result = Vec::new();
        for e in &self.edges {
            if e.endpoints[0] == rid {
                result.push(e.endpoints[1]);
            } else if e.endpoints[1] == rid {
                result.push(e.endpoints[0]);
            }
        }
        result
    }

    /// `deg^C_Φ(i, j)` — the degree of ray `(i, j)` in `D[Φ;C]` (§49.12).
    pub fn deg(&self, rid: RayId) -> usize {
        self.adj(rid).len()
    }

    /// Ray degree classification (§49.12–14):
    /// - deg = 0: **free**
    /// - deg = 1: **deterministic**
    /// - deg > 1: **branching**
    pub fn ray_class(&self, rid: RayId) -> RayClass {
        match self.deg(rid) {
            0 => RayClass::Free,
            1 => RayClass::Deterministic,
            _ => RayClass::Branching,
        }
    }

    /// Edges incident to a given *star* index (both endpoints of an edge
    /// involving star `i`).
    pub fn star_edges(&self, star_idx: usize) -> Vec<&DepEdge> {
        self.edges
            .iter()
            .filter(|e| e.endpoints[0].0 == star_idx || e.endpoints[1].0 == star_idx)
            .collect()
    }
}

/// Classification of a ray's degree in `D[Φ;C]` (§49.12–14).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RayClass {
    /// Degree 0: not connected to any other ray.
    Free,
    /// Degree 1: connected to exactly one other ray.
    Deterministic,
    /// Degree > 1: connected to more than one other ray.
    Branching,
}

// ─────────────────────────────────────────────────────────────────────────────
// Adjacency index for efficient lookup
// ─────────────────────────────────────────────────────────────────────────────

/// An edge-lookup index for `D[Φ;C]`: maps each `RayId` to the list of
/// `(edge_index, other_ray_id)` pairs.
#[derive(Debug, Clone)]
pub struct AdjIndex {
    /// Map from `RayId` to list of `(edge_index, adjacent_ray_id)`.
    pub map: HashMap<RayId, Vec<(usize, RayId)>>,
}

impl AdjIndex {
    /// Build from a `DepGraph`.
    pub fn build(dg: &DepGraph) -> Self {
        let mut map: HashMap<RayId, Vec<(usize, RayId)>> = HashMap::new();
        for (idx, e) in dg.edges.iter().enumerate() {
            let (a, b) = e.ends();
            map.entry(a).or_default().push((idx, b));
            map.entry(b).or_default().push((idx, a));
        }
        Self { map }
    }

    /// Get the neighbours of `rid`: list of `(edge_index, other_ray_id)`.
    pub fn neighbours(&self, rid: RayId) -> &[(usize, RayId)] {
        self.map.get(&rid).map(|v| v.as_slice()).unwrap_or(&[])
    }
}
