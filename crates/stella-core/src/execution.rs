//! Abstract execution `AEx_C(Φ)` (Eng §49.42) and the equivalent concrete
//! execution via saturated diagram construction.
//!
//! §49.42: `AEx_C(Φ) := ↓CSatDiags_C(Φ)` — the multiset of actualisations of
//! the **correct saturated** diagrams of `D[Φ;C]`.
//!
//! §49.23 / §49.24: A diagram is **saturated** if it is ⊑-maximal: no proper
//! extension exists within `D[Φ;C]`.
//!
//! ## Strategy: constructive saturation
//!
//! We implement saturation constructively (equivalent to §50 concrete execution):
//!
//! 1. **Seed**: for each star index `i`, create the single-vertex diagram
//!    `δ = (i, ∅)`.
//! 2. **Extend**: for each diagram vertex `v` and each unused ray `j` at `v`,
//!    for each edge `{(i,j),(i′,j′)}` in `D[Φ;C]` with `i = vertex_star[v]`,
//!    try adding a new vertex `v′` mapped to star `i′` and a new edge connecting
//!    `v` (via ray `j`) to `v′` (via ray `j′`).  Also try connecting to an
//!    *existing* vertex `v′` already in the diagram if it is mapped to star `i′`
//!    and ray `j′` is unused at `v′`.
//! 3. **Saturate**: repeat until no more edges can be added.
//! 4. **Correct**: keep only diagrams where `Prob(δ)` is unifiable.
//! 5. **Actualise**: for each correct saturated diagram, compute `↓δ`.
//!
//! **Caveat**: The full saturation space is exponential.  For Horn queries the
//! dependency graph is acyclic and the saturation terminates quickly.  We cap
//! diagram size at `MAX_VERTICES` to avoid runaway computation on cyclic
//! constellations; this is faithful to Eng's finite-diagram requirement.
//!
//! ## Non-obvious choice: diagram identity
//!
//! Two diagrams with the same structure but different vertex labellings are
//! distinct during construction but yield the same actualisation.  We
//! deduplicate actualisations at the end by comparing the resulting stars
//! (α-equivalence would be ideal; we use syntactic equality after applying ψ).

use std::collections::{HashMap, HashSet};

use crate::constellation::{Constellation, RayId, Star};
use crate::dep_graph::{AdjIndex, DepEdge, DepGraph};
use crate::diagram::{Diagram, DiagramEdge};

/// Maximum number of diagram vertices before we stop extending.
///
/// Non-obvious choice: Eng's definition requires finite diagrams, but does not
/// bound their size.  For Horn execution the sizes are bounded by the number
/// of rule applications.  We set a generous cap to handle the 2+2 addition
/// test (which requires ≈5 rule steps) while preventing pathological blowup.
const MAX_VERTICES: usize = 16;

// ─────────────────────────────────────────────────────────────────────────────
// Diagram builder state
// ─────────────────────────────────────────────────────────────────────────────

/// Internal mutable state for building a diagram by extension.
#[derive(Debug, Clone)]
struct DiagBuilder {
    /// `vertex_star[v]` = star index.
    vertex_star: Vec<usize>,
    /// Edges added so far.
    edges: Vec<DiagramEdge>,
    /// `vertex_edge_ray[v][e]` = ray index at v for edge e.
    vertex_edge_ray: Vec<HashMap<usize, usize>>,
    /// `vertex_used_rays[v]` = set of ray indices already committed at v.
    vertex_used_rays: Vec<HashSet<usize>>,
}

impl DiagBuilder {
    fn new_single(star_idx: usize) -> Self {
        Self {
            vertex_star: vec![star_idx],
            edges: vec![],
            vertex_edge_ray: vec![HashMap::new()],
            vertex_used_rays: vec![HashSet::new()],
        }
    }

    /// Compute a canonical key for this diagram state, used for deduplication.
    ///
    /// **Content-based canonicalization**: We represent each vertex by its
    /// star CONTENT (sorted ray index = `j`) rather than its star INDEX.  This
    /// means two diagrams that use different copies of the same star (e.g., step1
    /// vs step2, which have identical rays) get the SAME canonical key and are
    /// deduplicated.  This is correct because two such diagrams yield identical
    /// actualisations (up to α-renaming of variables).
    ///
    /// The key is: sorted list of edges, each encoded as
    /// `(ray_content_u, ju, ray_content_v, jv)` in normalized order.
    fn canonical_key(&self, phi: &Constellation) -> String {
        // Encode each vertex as (star_content_key, used_rays_mask).
        // Star content key = sorted display of rays.
        let vert_key = |v: usize| -> String {
            let si = self.vertex_star[v];
            let star = &phi[si];
            let mut rays: Vec<String> = star.iter().map(|r| format!("{r:?}")).collect();
            rays.sort();
            let used: Vec<usize> = {
                let mut u: Vec<usize> = self.vertex_used_rays[v].iter().copied().collect();
                u.sort();
                u
            };
            format!("{rays:?}{used:?}")
        };

        // Represent each edge as sorted pair of (vert_key_u + ju, vert_key_v + jv).
        let mut edge_keys: Vec<String> = self
            .edges
            .iter()
            .enumerate()
            .map(|(e_idx, e)| {
                let (u, v) = e.vertices;
                let ku = vert_key(u);
                let kv = vert_key(v);
                let ju = self.vertex_edge_ray[u][&e_idx];
                let jv = self.vertex_edge_ray[v][&e_idx];
                let a = format!("{ku}@{ju}");
                let b = format!("{kv}@{jv}");
                if a <= b { format!("[{a}|{b}]") } else { format!("[{b}|{a}]") }
            })
            .collect();
        edge_keys.sort();

        // Include isolated vertices.
        let has_edge: HashSet<usize> = self.edges.iter().flat_map(|e| [e.vertices.0, e.vertices.1]).collect();
        let mut isolated: Vec<String> = (0..self.n_vertices())
            .filter(|v| !has_edge.contains(v))
            .map(vert_key)
            .collect();
        isolated.sort();

        format!("I{isolated:?}E{edge_keys:?}")
    }

    fn n_vertices(&self) -> usize {
        self.vertex_star.len()
    }

    fn add_vertex(&mut self, star_idx: usize) -> usize {
        let v = self.vertex_star.len();
        self.vertex_star.push(star_idx);
        self.vertex_edge_ray.push(HashMap::new());
        self.vertex_used_rays.push(HashSet::new());
        v
    }

    /// Add an edge between vertex `u` (using ray `ju`) and vertex `v` (using ray `jv`).
    /// Returns the new edge index, or `None` if a ray is already used.
    fn add_edge(
        &mut self,
        u: usize,
        ju: usize,
        v: usize,
        jv: usize,
        dep_edge: DepEdge,
    ) -> Option<usize> {
        // Check ray availability.
        if self.vertex_used_rays[u].contains(&ju) || self.vertex_used_rays[v].contains(&jv) {
            return None;
        }
        let e_idx = self.edges.len();
        self.edges.push(DiagramEdge { vertices: (u, v), dep_edge });
        self.vertex_edge_ray[u].insert(e_idx, ju);
        self.vertex_edge_ray[v].insert(e_idx, jv);
        self.vertex_used_rays[u].insert(ju);
        self.vertex_used_rays[v].insert(jv);
        Some(e_idx)
    }

    fn to_diagram(&self) -> Diagram {
        Diagram {
            vertex_star: self.vertex_star.clone(),
            edges: self.edges.clone(),
            vertex_edge_ray: self.vertex_edge_ray.clone(),
        }
    }

    /// Check connectivity.
    fn is_connected(&self) -> bool {
        let n = self.n_vertices();
        if n <= 1 {
            return true;
        }
        let mut adj: Vec<Vec<usize>> = vec![vec![]; n];
        for e in &self.edges {
            adj[e.vertices.0].push(e.vertices.1);
            adj[e.vertices.1].push(e.vertices.0);
        }
        let mut visited = vec![false; n];
        let mut stack = vec![0usize];
        visited[0] = true;
        while let Some(v) = stack.pop() {
            for &u in &adj[v] {
                if !visited[u] {
                    visited[u] = true;
                    stack.push(u);
                }
            }
        }
        visited.iter().all(|&b| b)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Saturation
// ─────────────────────────────────────────────────────────────────────────────

/// Generate all saturated diagrams of `D[Φ;C]` constructively.
///
/// We use a worklist/DFS stack: start from single-vertex diagrams, then extend
/// by adding any matchable edge that does not conflict with an already-used ray.
/// A diagram is saturated when it cannot be further extended within `D[Φ;C]`.
///
/// **Deduplication**: We track canonical keys of visited states to avoid
/// exploring isomorphic diagrams reachable via different construction orders.
///
/// Returns all distinct saturated diagrams.
pub fn saturated_diagrams(phi: &Constellation, dg: &DepGraph) -> Vec<Diagram> {
    let adj_idx = AdjIndex::build(dg);

    let mut saturated: Vec<Diagram> = Vec::new();
    let mut saturated_keys: HashSet<String> = HashSet::new();
    // visited tracks states we've already pushed to the stack to avoid re-pushing.
    let mut visited: HashSet<String> = HashSet::new();

    // Iterative DFS using an explicit stack.
    let mut stack: Vec<DiagBuilder> = Vec::new();
    for seed in (0..phi.len()).map(DiagBuilder::new_single) {
        let key = seed.canonical_key(phi);
        if visited.insert(key) {
            stack.push(seed);
        }
    }

    while let Some(b) = stack.pop() {
        // Find all candidate one-step extensions.
        let mut any_extension_exists = false;
        let mut new_extensions: Vec<DiagBuilder> = Vec::new();

        for v in 0..b.n_vertices() {
            let si = b.vertex_star[v];
            let n_rays = phi[si].len();
            for j in 0..n_rays {
                if b.vertex_used_rays[v].contains(&j) {
                    continue;
                }
                let rid: RayId = (si, j);
                for &(e_didx, rid_other) in adj_idx.neighbours(rid) {
                    let (si2, j2) = rid_other;
                    let dep_edge = dg.edges[e_didx].clone();

                    // Option A: connect to an EXISTING vertex mapped to si2 or an
                    // existing vertex with the same star CONTENT as si2.
                    for v2 in 0..b.n_vertices() {
                        if v2 == v {
                            continue;
                        }
                        if b.vertex_star[v2] != si2 {
                            continue;
                        }
                        if b.vertex_used_rays[v2].contains(&j2) {
                            continue;
                        }
                        any_extension_exists = true;
                        let mut b2 = b.clone();
                        if b2.add_edge(v, j, v2, j2, dep_edge.clone()).is_some() {
                            let key = b2.canonical_key(phi);
                            if visited.insert(key) {
                                new_extensions.push(b2);
                            }
                        }
                    }

                    // Option B: add a NEW vertex mapped to si2.
                    if b.n_vertices() < MAX_VERTICES {
                        any_extension_exists = true;
                        let mut b2 = b.clone();
                        let v2 = b2.add_vertex(si2);
                        if b2.add_edge(v, j, v2, j2, dep_edge.clone()).is_some() {
                            let key = b2.canonical_key(phi);
                            if visited.insert(key) {
                                new_extensions.push(b2);
                            }
                        }
                    }
                }
            }
        }

        if !any_extension_exists {
            // No extension possible AT ALL: this diagram is truly saturated.
            if b.is_connected() {
                let sat_key = b.canonical_key(phi);
                if saturated_keys.insert(sat_key) {
                    saturated.push(b.to_diagram());
                }
            }
        } else {
            // Extensions exist; push the new (unvisited) ones for further exploration.
            stack.extend(new_extensions);
        }
    }

    saturated
}

// ─────────────────────────────────────────────────────────────────────────────
// Abstract Execution
// ─────────────────────────────────────────────────────────────────────────────

/// `AEx_C(Φ)` — abstract execution (§49.42).
///
/// Returns the multiset (as a `Vec`) of actualisations of correct saturated
/// diagrams of `D[Φ;C]`.
pub fn aex(phi: &Constellation, dg: &DepGraph) -> Vec<Star> {
    let sats = saturated_diagrams(phi, dg);
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

/// Expand a constellation by adding `copies` extra copies of **animist** stars.
///
/// **Design choice forced by Eng §50**: The dependency graph `D[Φ;C]` requires
/// `i ≠ i'` for edges, meaning two diagram vertices cannot connect if they map
/// to the same star index.  For Horn programs that need to apply the same rule
/// `k` times, the constellation must contain `k+1` distinct copies of the rule
/// star.
///
/// Eng's §50 concrete execution uses "construction sequences" that are multisets
/// of stars.  We make this explicit by pre-expanding Φ: only **animist** stars
/// (stars with both positive and negative rays — i.e., inference rules) need
/// replication; objective (base cases) and subjective (queries) stars do not.
///
/// The `copies` parameter = number of EXTRA copies added per animist star.
/// For `add(n, m, ?)`, `copies` must be ≥ max(n, m).
pub fn expand_constellation(phi: &Constellation, copies: usize) -> Constellation {
    use crate::constellation::StarKind;
    use crate::constellation::star_kind;
    let mut expanded = phi.clone();
    for _ in 0..copies {
        for star in phi.iter() {
            if star_kind(star) == StarKind::Animist {
                expanded.push(star.clone());
            }
        }
    }
    expanded
}

/// `AEx_C(Φ)` using the full colour set of `Φ`, with automatic star replication.
///
/// Runs saturation on `Φ` expanded with `copies` extra copies of each animist
/// (rule) star.  For the Horn addition tests, `copies = 2` suffices for 2+2.
pub fn aex_with_copies(phi: &Constellation, copies: usize) -> Vec<Star> {
    let expanded = expand_constellation(phi, copies);
    let dg = DepGraph::from_constellation(&expanded);
    aex(&expanded, &dg)
}

/// `AEx_C(Φ)` using the full colour set of `Φ`.
///
/// Uses `copies = 2` extra copies of each animist (rule) star to handle
/// Horn programs with up to 2 recursive steps.
pub fn aex_full(phi: &Constellation) -> Vec<Star> {
    aex_with_copies(phi, 2)
}

// ─────────────────────────────────────────────────────────────────────────────
// Alpha-equivalence check for stars (for test assertions)
// ─────────────────────────────────────────────────────────────────────────────

/// Check whether two stars are α-equivalent (§48.12).
///
/// Two stars are α-equivalent if there is a bijection between their rays such
/// that each pair of corresponding rays is α-unifiable (i.e., unifiable after
/// renaming variables apart).
///
/// Non-obvious choice: §48.12 says stars are taken "up to α-equivalence", which
/// in the first-order setting means there exists a renaming α such that applying
/// α to one star produces the other.  Because our stars may be one-element, we
/// implement pairwise α-equivalence: for single-ray stars, check that the two
/// rays are α-equivalent.  For multi-ray stars we check a bijection with
/// α-unification for each matched pair.
pub fn stars_alpha_equiv(s1: &Star, s2: &Star) -> bool {
    if s1.len() != s2.len() {
        return false;
    }
    // For small stars: check that there is a permutation of s2 such that each
    // paired ray is α-unifiable.
    // For length 1:
    if s1.len() == 1 {
        return crate::alpha::alpha_unify(&s1[0], &s2[0]).is_some();
    }
    // For length 0:
    if s1.is_empty() {
        return true;
    }
    // General: try all permutations (only small stars expected in tests).
    let n = s1.len();
    let mut indices: Vec<usize> = (0..n).collect();
    // Heap's permutation algorithm.
    fn permutations(arr: &mut Vec<usize>, k: usize, result: &mut Vec<Vec<usize>>) {
        if k == 1 {
            result.push(arr.clone());
            return;
        }
        for i in 0..k {
            permutations(arr, k - 1, result);
            if k % 2 == 0 {
                arr.swap(i, k - 1);
            } else {
                arr.swap(0, k - 1);
            }
        }
    }
    let mut perms = Vec::new();
    permutations(&mut indices, n, &mut perms);

    for perm in perms {
        let all_match = s1
            .iter()
            .zip(perm.iter().map(|&p| &s2[p]))
            .all(|(r1, r2)| crate::alpha::alpha_unify(r1, r2).is_some());
        if all_match {
            return true;
        }
    }
    false
}
