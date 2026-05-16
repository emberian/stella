//! Dependency graph `D[Φ; C]` (Eng §49.10–§49.14).

use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::HashSet;

use crate::constellation::{get_ray, id_rays, Constellation, RayId};
use crate::polarised::{matchable, ray_polarity, Polarity, Ray};
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
    pub fn build(phi: &Constellation, c: &HashSet<String>) -> Self {
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

    /// Build `D[Φ; all_colours(Φ)]` — the standard choice for Horn execution.
    pub fn from_constellation(phi: &Constellation) -> Self {
        let c = all_colours(phi);
        Self::build(phi, &c)
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
