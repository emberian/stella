//! Diagrams, correctness, and actualisation (Eng §49.16–§49.34).

use rustc_hash::{FxHashMap, FxHashSet};

use crate::constellation::{Constellation, Star};
use crate::dep_graph::DepEdge;
use crate::polarised::underlying_term;
use crate::subst::{freshen, Substitution};
use crate::term::{get, mk_var_interned, TermData, TermId, Var};
use crate::unify::{unify, Equation};

// ─────────────────────────────────────────────────────────────────────────────
// Diagram
// ─────────────────────────────────────────────────────────────────────────────

/// A diagram `(G_δ, δ)` as described in §49.16.
#[derive(Debug, Clone)]
pub struct Diagram {
    pub vertex_star: Vec<usize>,
    pub edges: Vec<DiagramEdge>,
    pub vertex_edge_ray: Vec<FxHashMap<usize, usize>>,
}

/// An edge in the diagram multigraph.
#[derive(Debug, Clone)]
pub struct DiagramEdge {
    pub vertices: (usize, usize),
    pub dep_edge: DepEdge,
}

impl Diagram {
    pub fn single(star_idx: usize, _n_rays: usize) -> Self {
        Self {
            vertex_star: vec![star_idx],
            edges: vec![],
            vertex_edge_ray: vec![FxHashMap::default()],
        }
    }

    pub fn n_vertices(&self) -> usize {
        self.vertex_star.len()
    }

    pub fn n_edges(&self) -> usize {
        self.edges.len()
    }

    pub fn star_of(&self, v: usize) -> usize {
        self.vertex_star[v]
    }

    pub fn is_connected(&self) -> bool {
        let n = self.n_vertices();
        if n == 0 { return true; }
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
                if !visited[u] { visited[u] = true; stack.push(u); }
            }
        }
        visited.iter().all(|&b| b)
    }

    /// `free(δ)` — ray identifiers `(vertex, ray_j)` not used by any edge (§49.21).
    pub fn free_rays(&self, phi: &Constellation) -> Vec<(usize, usize)> {
        let mut free = Vec::new();
        for (v, &si) in self.vertex_star.iter().enumerate() {
            let used: FxHashSet<usize> = self.vertex_edge_ray[v].values().copied().collect();
            for j in 0..phi[si].len() {
                if !used.contains(&j) {
                    free.push((v, j));
                }
            }
        }
        free
    }

    pub fn free_ray_ids(&self, phi: &Constellation) -> Vec<(usize, usize)> {
        self.free_rays(phi)
    }

    pub fn is_closed(&self, phi: &Constellation) -> bool {
        self.free_ray_ids(phi).is_empty()
    }

    /// Build per-vertex renamings: rename ALL variables in the star at vertex `v`
    /// with fresh names (counter-based, no String allocation in the logic).
    pub fn build_vertex_renamings(&self, phi: &Constellation) -> Vec<(Vec<TermId>, Substitution)> {
        let mut counter = 0u32;
        self.vertex_star
            .iter()
            .enumerate()
            .map(|(v, &si)| {
                let star = &phi[si];
                // Collect all variables in the star.
                let all_vars: Vec<Var> = star
                    .iter()
                    .flat_map(|&r| r.vars())
                    .collect::<FxHashSet<_>>()
                    .into_iter()
                    .collect();
                // Create fresh TermId mappings.
                let pairs: Vec<(Var, TermId)> = all_vars
                    .into_iter()
                    .map(|var| {
                        // Create a fresh var: prefix v<vertex>_ + var name + counter
                        let fresh_name = format!("v{}_{}{}", v, var.as_str(), counter);
                        counter += 1;
                        let fresh_var = Var::intern(&fresh_name);
                        (var, mk_var_interned(fresh_var))
                    })
                    .collect();
                let subst = Substitution::from_var_pairs(pairs);
                let renamed: Vec<TermId> = star.iter().map(|&r| subst.apply(r)).collect();
                (renamed, subst)
            })
            .collect()
    }

    /// `Prob(δ)` — the underlying unification problem (§49.27).
    pub fn underlying_problem(
        &self,
        phi: &Constellation,
    ) -> (Vec<Equation>, Vec<(Vec<TermId>, Substitution)>) {
        let renamings = self.build_vertex_renamings(phi);
        let mut eqs = Vec::new();

        for (e_idx, edge) in self.edges.iter().enumerate() {
            let (u, v) = edge.vertices;
            let ju = self.vertex_edge_ray[u][&e_idx];
            let jv = self.vertex_edge_ray[v][&e_idx];

            let ray_u = underlying_term(renamings[u].0[ju]);
            let ray_v = underlying_term(renamings[v].0[jv]);

            eqs.push(Equation::new(ray_u, ray_v));
        }

        (eqs, renamings)
    }

    /// Check correctness: `Prob(δ)` has a unifier (§49.34).
    pub fn is_correct(&self, phi: &Constellation) -> bool {
        let (eqs, _) = self.underlying_problem(phi);
        unify(eqs).is_some()
    }

    /// Compute the actualisation `↓δ` (§49.34) for a correct diagram.
    pub fn actualise(&self, phi: &Constellation) -> Option<Star> {
        let (eqs, renamings) = self.underlying_problem(phi);
        let psi = unify(eqs)?;

        let free = self.free_ray_ids(phi);
        let result: Star = free
            .into_iter()
            .map(|(v, j)| psi.apply(renamings[v].0[j]))
            .collect();

        Some(result)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Diagram ordering (stub)
// ─────────────────────────────────────────────────────────────────────────────

pub fn diagram_embeds(_delta: &Diagram, _delta_prime: &Diagram) -> bool {
    _delta.n_edges() <= _delta_prime.n_edges()
}
