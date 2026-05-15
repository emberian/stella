//! Diagrams, correctness, and actualisation (Eng §49.16–§49.34).
//!
//! §49.16: A **diagram** is a pair `(G_δ, δ)` where:
//! - `G_δ` is a finite connected multigraph (vertices = `V_δ`, edges = `E_δ`).
//! - `δ` is a *homomorphism* from `G_δ` into `D[Φ;C]`:
//!   - `δ_V : V_δ → I_Φ` maps each diagram vertex to a star index.
//!   - `δ_E : E_δ → edges(D[Φ;C])` maps each diagram edge to a dependency edge.
//!   - For each diagram vertex `v`, the map `j ↦ ray-index-of-δ_E(e)` over
//!     incident edges `e` at `v` must be injective (distinct rays per edge).
//!
//! §49.21: `free(δ)` = ray identifiers of `(δ_V(v), j)` for which no incident
//! diagram edge uses ray index `j` at `v`.  δ is *closed* if `free(δ) = ∅`.
//!
//! §49.27: The **underlying equation** of a diagram edge `e` with `δ_E(e) =
//! {(i,j),(i′,j′)}`, using per-vertex fresh renamings α_v and α_{v′}:
//!
//! ```text
//! α_v(Φ[i][j]) =? α_{v′}(Φ[i′][j′])
//! ```
//!
//! The **underlying problem** `Prob(δ)` is the set of all such equations.
//!
//! §49.34: A diagram is **correct** if `Prob(δ)` has a unifier.
//!
//! §49.34: The **actualisation** `↓δ` of a correct diagram is the star with
//! index set `free(δ)` where `(↓δ)[(i,j)] = (ψ ∘ θ)(Φ[i][j])`, with `ψ` the
//! mgu of `Prob(δ)` and `θ` the per-vertex renaming.
//!
//! ## Representation choices
//!
//! **Diagram vertices and edges**: We use integer indices (`usize`).  A diagram
//! vertex `v` maps to a star index via `vertex_star: Vec<usize>`.  A diagram
//! edge `e` maps to a `DepEdge` via `edge_dep: Vec<DepEdge>`.  Each edge also
//! records which of its two endpoints corresponds to which diagram vertex.
//!
//! **Per-vertex ray assignment** (injection condition of §49.16): For each
//! diagram vertex `v`, we maintain a map from diagram-edge index to the ray
//! index *at that vertex*.  This is `vertex_edge_ray: Vec<HashMap<usize,
//! usize>>` — for vertex `v`, `vertex_edge_ray[v][e]` is the ray index `j` at
//! `v` for edge `e`.
//!
//! **Per-vertex renamings** (§49.27): Each diagram vertex `v` receives a fresh
//! renaming `θ_v` that renames all variables of star `Φ[δ_V(v)]` to fresh
//! names.  We use the `freshen` function from `subst`.

use std::collections::{HashMap, HashSet};

use crate::constellation::{Constellation, Star};
use crate::dep_graph::DepEdge;
use crate::polarised::underlying_term;
use crate::subst::Substitution;
use crate::term::Term;
use crate::unify::{unify, Equation};

// ─────────────────────────────────────────────────────────────────────────────
// Diagram
// ─────────────────────────────────────────────────────────────────────────────

/// A diagram `(G_δ, δ)` as described in §49.16.
///
/// The multigraph `G_δ` is represented implicitly:
/// - `vertex_star[v]` = star index `δ_V(v)`.
/// - `edges[e]` = `DiagramEdge`, which stores the dep-graph edge and the two
///   diagram vertex indices it connects.
///
/// The per-vertex injection from incident edges to ray indices of the mapped
/// star is stored in `vertex_edge_ray[v][e]` = ray index `j` at vertex `v` for
/// edge `e` (§49.16 coherence condition).
#[derive(Debug, Clone)]
pub struct Diagram {
    /// `vertex_star[v]` = star index in the constellation that vertex `v` maps to.
    pub vertex_star: Vec<usize>,
    /// The edges of the diagram multigraph.
    pub edges: Vec<DiagramEdge>,
    /// `vertex_edge_ray[v]` maps diagram edge index `e` (incident to `v`)
    /// to the ray index `j` at `v`.
    pub vertex_edge_ray: Vec<HashMap<usize, usize>>,
}

/// An edge in the diagram multigraph `G_δ`, together with its image in `D[Φ;C]`.
#[derive(Debug, Clone)]
pub struct DiagramEdge {
    /// The two diagram vertex indices `(u, v)` this edge connects.
    pub vertices: (usize, usize),
    /// The dependency-graph edge `δ_E(e)`.
    pub dep_edge: DepEdge,
}

impl Diagram {
    /// Create a trivial diagram with a single vertex mapped to star `star_idx`,
    /// and no edges.
    pub fn single(star_idx: usize, _n_rays: usize) -> Self {
        // A single vertex with no incident edges.
        let vertex_edge_ray = vec![HashMap::new()];
        Self {
            vertex_star: vec![star_idx],
            edges: vec![],
            vertex_edge_ray,
        }
    }

    /// Number of diagram vertices.
    pub fn n_vertices(&self) -> usize {
        self.vertex_star.len()
    }

    /// Number of diagram edges.
    pub fn n_edges(&self) -> usize {
        self.edges.len()
    }

    /// The star index mapped to by diagram vertex `v`.
    pub fn star_of(&self, v: usize) -> usize {
        self.vertex_star[v]
    }

    /// Check connectivity of the diagram graph (required by §49.16).
    pub fn is_connected(&self) -> bool {
        let n = self.n_vertices();
        if n == 0 {
            return true;
        }
        // BFS/DFS.
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

    /// `free(δ)` — ray identifiers `(i, j)` not used by any edge (§49.21).
    ///
    /// For each diagram vertex `v` with star index `i = vertex_star[v]`,
    /// the used ray indices are `vertex_edge_ray[v].values()`.  Any ray index
    /// `j` of star `i` that is not used is free.
    ///
    /// Note: The same star index can appear multiple times (multiple vertices
    /// mapped to the same star); each vertex contributes independently.  The
    /// free rays are keyed by `(vertex_index, ray_index)` so that distinct
    /// copies of a star have independent free rays.
    pub fn free_rays(&self, phi: &Constellation) -> Vec<(usize, usize)> {
        // Returns (vertex_idx, ray_idx_within_star) pairs that are free.
        let mut free = Vec::new();
        for (v, &si) in self.vertex_star.iter().enumerate() {
            let used: HashSet<usize> = self.vertex_edge_ray[v].values().copied().collect();
            let n_rays = phi[si].len();
            for j in 0..n_rays {
                if !used.contains(&j) {
                    free.push((v, j));
                }
            }
        }
        free
    }

    /// `free(δ)` expressed as `RayId`s (star_index, ray_index).
    ///
    /// Non-obvious choice: §49.21 defines free rays as those with degree 0 in
    /// the diagram.  We express this as `(star_index, ray_index)` pairs derived
    /// from `(vertex, ray_j)` pairs.  When multiple vertices map to the same
    /// star, a ray `j` of that star is free for each vertex that does not use it.
    /// We return one entry per `(vertex, j)`.  For actualisation we apply the
    /// per-vertex substitution, so the (vertex, j) key is sufficient.
    pub fn free_ray_ids(&self, phi: &Constellation) -> Vec<(usize, usize)> {
        self.free_rays(phi)
    }

    /// Is this diagram closed? (`free(δ) = ∅`, §49.21.)
    pub fn is_closed(&self, phi: &Constellation) -> bool {
        self.free_ray_ids(phi).is_empty()
    }

    /// Build per-vertex renamings: rename ALL variables in the
    /// star at vertex `v` with a single consistent renaming.
    pub fn build_vertex_renamings(&self, phi: &Constellation) -> Vec<(Vec<Term>, Substitution)> {
        let mut counter = 0u32;
        self.vertex_star
            .iter()
            .enumerate()
            .map(|(v, &si)| {
                let star = &phi[si];
                // Collect all variables in the star.
                let all_vars: Vec<String> = star
                    .iter()
                    .flat_map(|r| r.vars())
                    .collect::<HashSet<_>>()
                    .into_iter()
                    .collect();
                // Create fresh names for all vars.
                let mut map = HashMap::new();
                for var in &all_vars {
                    let fresh = format!("v{v}_{}{}", var, counter);
                    counter += 1;
                    map.insert(var.clone(), Term::Var(fresh));
                }
                let subst = Substitution::from_pairs(map);
                let renamed: Vec<Term> = star.iter().map(|r| subst.apply(r)).collect();
                (renamed, subst)
            })
            .collect()
    }

    /// `Prob(δ)` — the underlying unification problem (§49.27).
    ///
    /// Each edge equation is:
    ///
    /// ```text
    /// α_v(|Φ[i][j]|)  =?  α_{v′}(|Φ[i′][j′]|)
    /// ```
    ///
    /// where `|·|` is the underlying-term operator (§48.7) that strips colour
    /// from every node, and `α_v`, `α_{v′}` are the per-vertex variable
    /// renamings.  The equations are over **colour-stripped underlying terms**
    /// and must be solved with **plain unification** (`StdCompat`).
    ///
    /// NOTE: edge *existence* in `D[Φ;C]` is determined by §49.7 matchability
    /// (α-unifiability under `PolarisedCompat ⊂`), which is a SEPARATE test
    /// from §49.27's equation system.  Do not collapse these two uses of
    /// unification.
    ///
    /// Returns the list of equations and the per-vertex `(renamed_star, θ_v)`.
    /// The renamed_star still holds the full (polarised) renamed rays so that
    /// actualisation (§49.34) can apply ψ to the original rays — only the
    /// equation/solve step strips colour.
    pub fn underlying_problem(
        &self,
        phi: &Constellation,
    ) -> (Vec<Equation>, Vec<(Vec<Term>, Substitution)>) {
        let renamings = self.build_vertex_renamings(phi);
        let mut eqs = Vec::new();

        for (e_idx, edge) in self.edges.iter().enumerate() {
            let (u, v) = edge.vertices;
            // Ray index at u and v for this edge.
            let ju = self.vertex_edge_ray[u][&e_idx];
            let jv = self.vertex_edge_ray[v][&e_idx];

            // §49.27: equations are over the underlying (colour-stripped) terms.
            // α_v has already been applied (the renamed star holds renamed rays);
            // we then strip colour with |·| before forming the equation.
            let ray_u = underlying_term(&renamings[u].0[ju]);
            let ray_v = underlying_term(&renamings[v].0[jv]);

            eqs.push(Equation::new(ray_u, ray_v));
        }

        (eqs, renamings)
    }

    /// Check correctness: `Prob(δ)` has a unifier (§49.34).
    ///
    /// The equations in `Prob(δ)` are over underlying (colour-stripped) terms
    /// (§49.27), so we solve with **plain unification** (`StdCompat`).
    ///
    /// NOTE: edge existence is governed by §49.7 matchability (PolarisedCompat);
    /// that is a separate concern from this correctness check.
    pub fn is_correct(&self, phi: &Constellation) -> bool {
        let (eqs, _) = self.underlying_problem(phi);
        unify(eqs).is_some()
    }

    /// Compute the actualisation `↓δ` (§49.34) for a correct diagram.
    ///
    /// Returns `None` if the diagram is incorrect.
    ///
    /// The actualisation is the star `[(ψ ∘ θ_v)(Φ[i][j]) | (v, j) ∈ free(δ)]`
    /// where `ψ` is the mgu of `Prob(δ)` (over underlying terms, §49.27) and
    /// `θ_v` is the per-vertex renaming.
    ///
    /// §49.34: ψ is applied to the **original polarised** renamed rays
    /// (the renamed star), not to the colour-stripped versions.  Only the
    /// equation-formation and solve use underlying terms.
    pub fn actualise(&self, phi: &Constellation) -> Option<Star> {
        let (eqs, renamings) = self.underlying_problem(phi);
        // §49.27/§49.34: solve the underlying problem with plain unification.
        let psi = unify(eqs)?;

        let free = self.free_ray_ids(phi);
        let result: Star = free
            .into_iter()
            .map(|(v, j)| {
                // θ_v has already been applied (renamed star at v holds renamed polarised rays).
                // Apply ψ (derived from underlying equations) to the original polarised renamed ray.
                let renamed_ray = &renamings[v].0[j];
                psi.apply(renamed_ray)
            })
            .collect();

        Some(result)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Diagram ordering ⊑ (§49.23)
// ─────────────────────────────────────────────────────────────────────────────

/// `δ ⊑ δ′` — diagram embedding (§49.23).
///
/// δ embeds in δ′ if there are injections `V_δ → V_{δ′}` and `E_δ → E_{δ′}`
/// that preserve the homomorphism structure.
///
/// For the saturation algorithm we use a simpler structural check: δ is a
/// sub-diagram of δ′ if the edge set of δ (as dep-edges plus vertex-star
/// assignments) is a subset of those in δ′ under some vertex injection.
/// Full implementation for the general case uses the sub-isomorphism approach.
///
/// Non-obvious choice: Eng gives ⊑ to define saturated diagrams as ⊑-maximal.
/// For our constructive saturation (we grow diagrams until no edge can be added)
/// we do not need to evaluate ⊑ directly.  We expose this as a stub that
/// reports `true` when δ has at most as many edges as δ′ (a necessary condition
/// for embedding).  The saturation constructor below uses maximality directly.
pub fn diagram_embeds(_delta: &Diagram, _delta_prime: &Diagram) -> bool {
    // Stub: used only conceptually; saturation uses the growth algorithm below.
    _delta.n_edges() <= _delta_prime.n_edges()
}
