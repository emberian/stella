//! Dependency graph `D[Φ; C]` (Eng §49.10–§49.14).

use rustc_hash::FxHashMap;
use std::collections::HashSet;

use crate::constellation::{get_ray, id_rays, Constellation, RayId};
use crate::polarised::{matchable, Polarity, Ray};
use crate::term::{get, TermData};

// ─────────────────────────────────────────────────────────────────────────────
// Colour set helpers
// ─────────────────────────────────────────────────────────────────────────────

/// `colours(r)` for a ray (§48.4): the set of coloured (non-neutral) head symbols.
///
/// Returns a singleton `HashSet<String>` for the head name if coloured, else empty.
/// (The public API uses `HashSet<String>` for compatibility with dep_graph colour sets.)
pub fn ray_colours(r: Ray) -> HashSet<String> {
    match get(r) {
        TermData::Var(_) => HashSet::new(),
        TermData::App(sym, _) => {
            if sym.pol != Polarity::Neutral {
                let mut s = HashSet::new();
                s.insert(sym.display_name());
                s
            } else {
                HashSet::new()
            }
        }
    }
}

/// Collect all coloured (non-neutral) head symbol display-names from a constellation.
pub fn all_colours(phi: &Constellation) -> HashSet<String> {
    id_rays(phi)
        .into_iter()
        .flat_map(|id| ray_colours(get_ray(phi, id)))
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// Colour-set parameter for `Ex_C` (Eng §51.6, §69.4)
// ─────────────────────────────────────────────────────────────────────────────

/// The colour set `C ⊆ F₊ ⊎ F₋` an interactive execution runs *under*
/// (Eng §51.6: `mat_Φ^C(r) := {(i,j) | r ⋈ Φ[i][j],
/// colours(r)∪colours(Φ[i][j]) ⊆ C}`).
///
/// Until now `C` was *derived* — every code path forced
/// `C = colours(Φ) ∪ colours(Ψ)`, which makes `colours(r)∪colours(Φ[i][j]) ⊆ C`
/// trivially true (every ray that appears is in the union by construction), so
/// the §51.6 colour gate, the §69.4 colour-restricted orthogonalities, and the
/// GoI computational/logical separation could never be exercised (thesis-audit
/// 01 §2.1/§3.2: `Ex_C` for a proper subset was structurally dead).
///
/// This type makes `C` a *first-class caller parameter*:
///  - [`ColourSet::All`] — `C = colours(Φ) ∪ colours(Ψ)`: the exact derived
///    behaviour, **byte-identical** to the pre-existing engine (the gate
///    `cr ⊆ C` is the same always-true predicate it always was).
///  - [`ColourSet::Only`] — `C` is the explicit, caller-chosen set. A ray whose
///    colour ∉ `C` is *invisible* to matching, so a **proper subset** `C ⊊
///    colours(Φ)∪colours(Ψ)` genuinely restricts the reachable redexes. This is
///    the new, previously-unreachable `Ex_C` surface.
#[derive(Debug, Clone)]
#[derive(Default)]
pub enum ColourSet {
    /// `C := colours(Φ) ∪ colours(Ψ)` (the historical, always-true gate).
    #[default]
    All,
    /// `C` is exactly this caller-chosen set of coloured head display-names
    /// (e.g. `{"+t","-t"}` for the typing colour, `{"+c","-c"}` for the
    /// computation colour — the GoI logical/computational split).
    Only(HashSet<String>),
}

impl ColourSet {
    /// Does the §51.6 gate `colours(r) ⊆ C` admit a ray whose colour set is
    /// `rc` (a `ray_colours` result: `∅` for Var/Neutral, else a singleton)?
    ///
    /// For [`ColourSet::All`] always `true` (the historical always-true
    /// behaviour: the caller's full union contains every ray that occurs).
    /// For [`ColourSet::Only`] the subset membership genuinely restricts.
    #[inline]
    pub fn admits(&self, rc: &HashSet<String>) -> bool {
        match self {
            ColourSet::All => true,
            ColourSet::Only(c) => rc.is_subset(c),
        }
    }

    /// `true` iff this is the historical derived (`All`) mode.
    #[inline]
    pub fn is_all(&self) -> bool {
        matches!(self, ColourSet::All)
    }
}


// ─────────────────────────────────────────────────────────────────────────────
// Dependency graph
// ─────────────────────────────────────────────────────────────────────────────

/// An edge in the dependency graph `D[Φ; C]` (§49.10).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DepEdge {
    /// The two ray identifiers, in canonical (sorted) order.
    pub endpoints: [RayId; 2],
}

impl DepEdge {
    pub fn new(a: RayId, b: RayId) -> Self {
        if a <= b { Self { endpoints: [a, b] } } else { Self { endpoints: [b, a] } }
    }

    pub fn ends(&self) -> (RayId, RayId) {
        (self.endpoints[0], self.endpoints[1])
    }

    pub fn star_indices(&self) -> (usize, usize) {
        (self.endpoints[0].0, self.endpoints[1].0)
    }

    pub fn contains_ray(&self, rid: RayId) -> bool {
        self.endpoints[0] == rid || self.endpoints[1] == rid
    }
}

/// The dependency graph `D[Φ; C]` (§49.10).
#[derive(Debug, Clone)]
pub struct DepGraph {
    pub n_stars: usize,
    pub edges: Vec<DepEdge>,
}

impl DepGraph {
    /// Build `D[Φ; C]` for a given colour set `C` (§49.10).
    ///
    /// This is the O(n²) pairwise scan — kept as the oracle for testing.
    /// Production callers should prefer `build_indexed` / `from_constellation`.
    pub fn build(phi: &Constellation, c: &HashSet<String>) -> Self {
        Self::build_scan(phi, c)
    }

    /// O(n²) pairwise scan oracle for `D[Φ; C]` (§49.10).
    ///
    /// Examines every cross-star ray pair and emits an edge when `matchable`
    /// returns true and both rays' colour sets are subsets of `c`.
    /// This is the reference implementation used to validate `build_indexed`.
    pub fn build_scan(phi: &Constellation, c: &HashSet<String>) -> Self {
        let ids: Vec<RayId> = id_rays(phi);
        let mut edges = Vec::new();

        for (a, &rid_a) in ids.iter().enumerate() {
            for &rid_b in &ids[a + 1..] {
                if rid_a.0 == rid_b.0 {
                    continue;
                }
                let r = get_ray(phi, rid_a);
                let rp = get_ray(phi, rid_b);

                let cr = ray_colours(r);
                let crp = ray_colours(rp);
                if !cr.is_subset(c) || !crp.is_subset(c) {
                    continue;
                }

                if matchable(r, rp) {
                    edges.push(DepEdge::new(rid_a, rid_b));
                }
            }
        }

        Self { n_stars: phi.len(), edges }
    }

    /// Build `D[Φ; all_colours(Φ)]` using the first-symbol index (default).
    ///
    /// Delegates to `from_constellation_indexed` (defined in `index.rs`), which
    /// produces the same edge set as the O(n²) scan but runs faster on large
    /// constellations.  The scan oracle is preserved as `build_scan` /
    /// `from_constellation_scan`.
    pub fn from_constellation(phi: &Constellation) -> Self {
        Self::from_constellation_indexed(phi)
    }

    /// O(n²) scan version of `from_constellation` — the oracle.
    ///
    /// Use this in tests that need the reference (scan) build path explicitly.
    pub fn from_constellation_scan(phi: &Constellation) -> Self {
        let c = all_colours(phi);
        Self::build_scan(phi, &c)
    }

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

    pub fn deg(&self, rid: RayId) -> usize {
        self.adj(rid).len()
    }

    pub fn ray_class(&self, rid: RayId) -> RayClass {
        match self.deg(rid) {
            0 => RayClass::Free,
            1 => RayClass::Deterministic,
            _ => RayClass::Branching,
        }
    }

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
    Free,
    Deterministic,
    Branching,
}

// ─────────────────────────────────────────────────────────────────────────────
// Adjacency index
// ─────────────────────────────────────────────────────────────────────────────

/// An edge-lookup index for `D[Φ;C]`.
#[derive(Debug, Clone)]
pub struct AdjIndex {
    pub map: FxHashMap<RayId, Vec<(usize, RayId)>>,
}

impl AdjIndex {
    pub fn build(dg: &DepGraph) -> Self {
        let mut map: FxHashMap<RayId, Vec<(usize, RayId)>> = FxHashMap::default();
        for (idx, e) in dg.edges.iter().enumerate() {
            let (a, b) = e.ends();
            map.entry(a).or_default().push((idx, b));
            map.entry(b).or_default().push((idx, a));
        }
        Self { map }
    }

    pub fn neighbours(&self, rid: RayId) -> &[(usize, RayId)] {
        self.map.get(&rid).map(|v| v.as_slice()).unwrap_or(&[])
    }
}
