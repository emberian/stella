//! Abstract execution `AEx_C(Φ)` (Eng §49.42) and saturation.

use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::HashSet;

use crate::constellation::{Constellation, RayId, Star};
use crate::dep_graph::{AdjIndex, DepEdge, DepGraph};
use crate::diagram::{Diagram, DiagramEdge};

const MAX_VERTICES: usize = 16;

// ─────────────────────────────────────────────────────────────────────────────
// Diagram builder state
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
struct DiagBuilder {
    vertex_star: Vec<usize>,
    edges: Vec<DiagramEdge>,
    vertex_edge_ray: Vec<FxHashMap<usize, usize>>,
    vertex_used_rays: Vec<FxHashSet<usize>>,
}

impl DiagBuilder {
    fn new_single(star_idx: usize) -> Self {
        Self {
            vertex_star: vec![star_idx],
            edges: vec![],
            vertex_edge_ray: vec![FxHashMap::default()],
            vertex_used_rays: vec![FxHashSet::default()],
        }
    }

    fn canonical_key(&self, phi: &Constellation) -> String {
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

        let has_edge: FxHashSet<usize> = self.edges.iter()
            .flat_map(|e| [e.vertices.0, e.vertices.1])
            .collect();
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
        self.vertex_edge_ray.push(FxHashMap::default());
        self.vertex_used_rays.push(FxHashSet::default());
        v
    }

    fn add_edge(
        &mut self,
        u: usize,
        ju: usize,
        v: usize,
        jv: usize,
        dep_edge: DepEdge,
    ) -> Option<usize> {
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

    fn is_connected(&self) -> bool {
        let n = self.n_vertices();
        if n <= 1 { return true; }
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
}

// ─────────────────────────────────────────────────────────────────────────────
// Saturation
// ─────────────────────────────────────────────────────────────────────────────

pub fn saturated_diagrams(phi: &Constellation, dg: &DepGraph) -> Vec<Diagram> {
    let adj_idx = AdjIndex::build(dg);

    let mut saturated: Vec<Diagram> = Vec::new();
    let mut saturated_keys: HashSet<String> = HashSet::new();
    let mut visited: HashSet<String> = HashSet::new();

    let mut stack: Vec<DiagBuilder> = Vec::new();
    for seed in (0..phi.len()).map(DiagBuilder::new_single) {
        let key = seed.canonical_key(phi);
        if visited.insert(key) {
            stack.push(seed);
        }
    }

    while let Some(b) = stack.pop() {
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

                    for v2 in 0..b.n_vertices() {
                        if v2 == v { continue; }
                        if b.vertex_star[v2] != si2 { continue; }
                        if b.vertex_used_rays[v2].contains(&j2) { continue; }
                        any_extension_exists = true;
                        let mut b2 = b.clone();
                        if b2.add_edge(v, j, v2, j2, dep_edge.clone()).is_some() {
                            let key = b2.canonical_key(phi);
                            if visited.insert(key) {
                                new_extensions.push(b2);
                            }
                        }
                    }

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
            if b.is_connected() {
                let sat_key = b.canonical_key(phi);
                if saturated_keys.insert(sat_key) {
                    saturated.push(b.to_diagram());
                }
            }
        } else {
            stack.extend(new_extensions);
        }
    }

    saturated
}

// ─────────────────────────────────────────────────────────────────────────────
// Abstract Execution
// ─────────────────────────────────────────────────────────────────────────────

pub fn aex(phi: &Constellation, dg: &DepGraph) -> Vec<Star> {
    let sats = saturated_diagrams(phi, dg);
    sats.into_iter()
        .filter_map(|d| {
            if d.is_correct(phi) { d.actualise(phi) } else { None }
        })
        .collect()
}

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

pub fn aex_with_copies(phi: &Constellation, copies: usize) -> Vec<Star> {
    let expanded = expand_constellation(phi, copies);
    let dg = DepGraph::from_constellation(&expanded);
    aex(&expanded, &dg)
}

pub fn aex_full(phi: &Constellation) -> Vec<Star> {
    aex_with_copies(phi, 2)
}

// ─────────────────────────────────────────────────────────────────────────────
// Alpha-equivalence check for stars
// ─────────────────────────────────────────────────────────────────────────────

pub fn stars_alpha_equiv(s1: &Star, s2: &Star) -> bool {
    if s1.len() != s2.len() { return false; }
    if s1.len() == 1 {
        return crate::alpha::alpha_unify(s1[0], s2[0]).is_some();
    }
    if s1.is_empty() { return true; }

    let n = s1.len();
    let mut indices: Vec<usize> = (0..n).collect();
    fn permutations(arr: &mut Vec<usize>, k: usize, result: &mut Vec<Vec<usize>>) {
        if k == 1 { result.push(arr.clone()); return; }
        for i in 0..k {
            permutations(arr, k - 1, result);
            if k % 2 == 0 { arr.swap(i, k - 1); } else { arr.swap(0, k - 1); }
        }
    }
    let mut perms = Vec::new();
    permutations(&mut indices, n, &mut perms);

    for perm in perms {
        let all_match = s1
            .iter()
            .zip(perm.iter().map(|&p| &s2[p]))
            .all(|(&r1, &r2)| crate::alpha::alpha_unify(r1, r2).is_some());
        if all_match { return true; }
    }
    false
}
