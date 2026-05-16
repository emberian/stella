//! Pluggable selection strategies for abstract execution (Eng §60.8).
//!
//! ## Design space
//!
//! ```text
//! The stellar-resolution engine (AEx, §49.42) enumerates saturated diagrams by
//! extending partial diagrams one edge at a time.  At each step there may be many
//! *matchable* extensions: a new edge to an existing vertex, or a new edge to a
//! freshly-introduced vertex.  The order in which these extensions are explored
//! affects:
//!
//!   1. COMPLETENESS — blind (BFS/DFS) saturation is always complete under the
//!      MAX_VERTICES bound.  Smarter orderings that prune cannot guarantee this
//!      without additional checks; the strategies here preserve completeness by
//!      *ordering* rather than *pruning*.
//!
//!   2. PERFORMANCE — extensions that close the diagram fastest are explored
//!      first, leading to earlier saturation signals and fewer wasted branches.
//!
//!   3. FAIRNESS — in the presence of many animist copies, round-robin over stars
//!      avoids starvation and finds shorter derivations quickly.
//!
//! The abstraction below mirrors SLD resolution's *selection rule* (§60.8): it
//! selects from the frontier of possible next extensions.  Every strategy produces
//! an ordering of the same candidate set; none drop candidates.  The oracle
//! (`Blind`) processes candidates in the order they were generated — exactly the
//! behaviour of the original saturation loop — ensuring backward compatibility.
//!
//! ## Strategies implemented
//!
//!   * `Blind`         — original LIFO (DFS) order; the reference oracle.
//!   * `SmallestFirst` — prefer extensions that keep total vertex count small;
//!                       ties broken by fewer free rays (most-constrained).
//!   * `RoundRobin`    — cycle uniformly over source vertices so every star gets
//!                       a chance to extend before any star extends twice.
//! ```

use crate::constellation::Constellation;
use crate::dep_graph::DepGraph;

// ─────────────────────────────────────────────────────────────────────────────
// Candidate extension
// ─────────────────────────────────────────────────────────────────────────────

/// A single candidate extension of a partial diagram.
///
/// Produced by the engine and passed to [`SelectionStrategy::order`] so the
/// strategy can reorder them before they are pushed onto the worklist.
#[derive(Debug, Clone)]
pub struct Candidate {
    /// The vertex (in the current diagram) that is being extended from.
    pub src_vertex: usize,
    /// The ray index at `src_vertex` that initiates the new edge.
    pub src_ray: usize,
    /// The vertex the edge connects to (existing vertex or `n_vertices` = new).
    pub dst_vertex: usize,
    /// The ray index at `dst_vertex`.
    pub dst_ray: usize,
    /// `true` when `dst_vertex` is a freshly-added vertex (not yet in the diagram).
    pub is_new_vertex: bool,
    /// Number of vertices the resulting diagram would have.
    pub result_n_vertices: usize,
    /// Number of free (unused) rays the resulting diagram would have.
    /// A rough estimate: current free rays - 2 (the two rays being consumed).
    pub result_free_rays: usize,
}

// ─────────────────────────────────────────────────────────────────────────────
// SelectionStrategy trait
// ─────────────────────────────────────────────────────────────────────────────

/// A pluggable selection strategy (§60.8 "STRATEGY" component).
///
/// The engine calls [`SelectionStrategy::order`] with the list of candidate
/// extensions generated at each step.  The strategy returns an ordering of
/// those candidates; all candidates are retained (no pruning), so completeness
/// is never broken.
pub trait SelectionStrategy: Send + Sync + 'static {
    /// Sort / reorder `candidates` in-place.
    ///
    /// The engine pushes them onto the worklist **in the returned order**, so
    /// the *last* element is processed *first* (LIFO stack semantics).
    /// A strategy that wants to prioritise small diagrams should put the
    /// small-diagram candidate *last* so it is popped first.
    fn order(&self, candidates: &mut Vec<Candidate>, _phi: &Constellation, _dg: &DepGraph);
}

// ─────────────────────────────────────────────────────────────────────────────
// Blind — reference oracle strategy
// ─────────────────────────────────────────────────────────────────────────────

/// The original saturation order: no reordering of candidates.
///
/// `Blind` is a no-op strategy — it leaves candidates in the order that the
/// engine generated them, which matches exactly the order used by the original
/// `saturated_diagrams` loop (inner-loop order over vertices × rays × adjacency
/// × existing/new-vertex).  This guarantees that `aex_stratified(phi, Blind)`
/// produces bit-for-bit identical output to `aex_full`.
///
/// Use `Blind` as the oracle for faithfulness tests.
#[derive(Debug, Clone, Default)]
pub struct Blind;

impl SelectionStrategy for Blind {
    #[inline]
    fn order(&self, _candidates: &mut Vec<Candidate>, _phi: &Constellation, _dg: &DepGraph) {
        // nothing — preserve generation order
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SmallestFirst — most-constrained heuristic
// ─────────────────────────────────────────────────────────────────────────────

/// Prefer extensions that keep the diagram small and maximally constrained.
///
/// Scoring (lower score = processed first = placed at the end of the vec,
/// because the engine pops from the end — LIFO):
///   primary key:   `result_n_vertices`  (smaller = better, avoid vertex explosion)
///   secondary key: `result_free_rays`   (fewer free = more constrained = better)
///   tertiary key:  `!is_new_vertex`     (prefer existing-vertex edges first)
///
/// This corresponds roughly to the "smallest-clause" heuristic in SLD and
/// "most-constrained-first" in CSP solvers.  It finds short derivations
/// quickly and reduces the saturation frontier on dense dependency graphs.
#[derive(Debug, Clone, Default)]
pub struct SmallestFirst;

impl SelectionStrategy for SmallestFirst {
    fn order(&self, candidates: &mut Vec<Candidate>, _phi: &Constellation, _dg: &DepGraph) {
        // Sort DESCENDING by (n_vertices, free_rays, is_new_vertex).
        // The engine uses a LIFO stack: `stack.extend(ordered_builders)` then
        // `stack.pop()`.  The last element extended is popped first.
        // We want the *best* (smallest n_vertices) candidate to be popped first,
        // so it must be placed *last* in the vec.  Sort descending → smallest last.
        candidates.sort_by(|a, b| {
            let ka = (a.result_n_vertices, a.result_free_rays, a.is_new_vertex as usize);
            let kb = (b.result_n_vertices, b.result_free_rays, b.is_new_vertex as usize);
            kb.cmp(&ka) // descending
        });
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// RoundRobin — fair interleaving across source vertices
// ─────────────────────────────────────────────────────────────────────────────

/// A fair round-robin strategy: interleave extensions across source vertices.
///
/// At each selection step, candidates originating from `src_vertex = 0` are
/// interleaved with those from `src_vertex = 1`, etc.  Within each group,
/// existing-vertex edges are preferred over new-vertex edges (same as
/// `SmallestFirst`'s tertiary key).
///
/// This prevents any single vertex from monopolising the search and is
/// particularly useful when many animist copies exist and the dependency graph
/// is dense.  It is equivalent to a fair BFS-like interleaving rather than the
/// DFS of `Blind`.
///
/// Note: `RoundRobin` carries no mutable state — the "round" is computed from
/// the candidates' `src_vertex` distribution at each call, so it is stateless
/// and can be shared across threads.
#[derive(Debug, Clone, Default)]
pub struct RoundRobin;

impl SelectionStrategy for RoundRobin {
    fn order(&self, candidates: &mut Vec<Candidate>, _phi: &Constellation, _dg: &DepGraph) {
        if candidates.is_empty() {
            return;
        }

        // Group by src_vertex, then interleave groups round-robin.
        // We produce a new ordering: candidates sorted by
        //   (round_index within group, src_vertex, is_new_vertex)
        // so they are pushed in ascending order (best = last = popped first).

        // Determine max src_vertex.
        let max_v = candidates.iter().map(|c| c.src_vertex).max().unwrap_or(0);

        // Build a per-vertex bucket (index in the original vec).
        let mut buckets: Vec<Vec<usize>> = vec![vec![]; max_v + 1];
        for (i, c) in candidates.iter().enumerate() {
            buckets[c.src_vertex].push(i);
        }

        // Sort within each bucket: existing-vertex first (placed last in LIFO
        // means popped first, i.e. we want existing-vertex last in the sub-vec).
        // But we're about to interleave, so let's just sort each bucket by
        // is_new_vertex ascending so existing-vertex slots come first in the bucket,
        // and will be placed later in the final vec (= popped first).
        for bucket in &mut buckets {
            bucket.sort_by_key(|&i| candidates[i].is_new_vertex as usize);
        }

        // Interleave: take one from each non-empty bucket per round.
        let mut result: Vec<usize> = Vec::with_capacity(candidates.len());
        loop {
            let mut any = false;
            for bucket in &mut buckets {
                if !bucket.is_empty() {
                    result.push(bucket.remove(0));
                    any = true;
                }
            }
            if !any {
                break;
            }
        }

        // `result` is now the desired pop order (first element = first to pop).
        // Since we push in order and pop from the back, we need to reverse so
        // the first-to-pop is at the end.
        result.reverse();

        // Rebuild candidates in the new order.
        let old = candidates.clone();
        for (i, &idx) in result.iter().enumerate() {
            candidates[i] = old[idx].clone();
        }
    }
}

#[cfg(test)]
mod strategy_tests {
    use super::*;
    use crate::constellation::Constellation;
    use crate::dep_graph::DepGraph;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::Term;

    fn var(x: &str) -> Term { crate::term::mk_var(x) }

    fn tiny_phi() -> Constellation {
        vec![
            vec![pos_ray("a", vec![var("X")])],
            vec![neg_ray("a", vec![var("Y")])],
        ]
    }

    fn make_cand(src: usize, dst: usize, is_new: bool, n_v: usize, free: usize) -> Candidate {
        Candidate {
            src_vertex: src,
            src_ray: 0,
            dst_vertex: dst,
            dst_ray: 0,
            is_new_vertex: is_new,
            result_n_vertices: n_v,
            result_free_rays: free,
        }
    }

    #[test]
    fn blind_preserves_order() {
        let phi = tiny_phi();
        let dg = DepGraph::from_constellation(&phi);
        let mut cands = vec![
            make_cand(0, 1, false, 2, 0),
            make_cand(1, 0, true,  3, 2),
            make_cand(0, 2, true,  4, 4),
        ];
        let src_before: Vec<usize> = cands.iter().map(|c| c.src_vertex).collect();
        Blind.order(&mut cands, &phi, &dg);
        let src_after: Vec<usize> = cands.iter().map(|c| c.src_vertex).collect();
        assert_eq!(src_before, src_after, "Blind must not reorder candidates");
    }

    #[test]
    fn smallest_first_orders_by_size() {
        let phi = tiny_phi();
        let dg = DepGraph::from_constellation(&phi);
        let mut cands = vec![
            make_cand(0, 2, true,  4, 4),  // worst
            make_cand(0, 1, false, 2, 0),  // best (smallest, most constrained)
            make_cand(1, 0, true,  3, 2),  // middle
        ];
        SmallestFirst.order(&mut cands, &phi, &dg);
        // Sorted DESCENDING: worst (n_v=4) first, best (n_v=2) last.
        // LIFO pops from the end → best is popped first.
        assert_eq!(cands.last().unwrap().result_n_vertices, 2,
            "SmallestFirst: best candidate (n_v=2) must be last (popped first by LIFO)");
        assert_eq!(cands.first().unwrap().result_n_vertices, 4,
            "SmallestFirst: worst candidate (n_v=4) must be first");
    }

    #[test]
    fn round_robin_interleaves_vertices() {
        let phi = tiny_phi();
        let dg = DepGraph::from_constellation(&phi);
        let mut cands = vec![
            make_cand(0, 1, false, 2, 0),
            make_cand(0, 2, true,  3, 2),
            make_cand(1, 0, false, 2, 0),
            make_cand(1, 2, true,  3, 2),
        ];
        RoundRobin.order(&mut cands, &phi, &dg);
        // After round-robin, src_vertices should alternate 0,1,0,1 (or similar
        // interleaved pattern), not all-0 then all-1.
        let src_order: Vec<usize> = cands.iter().map(|c| c.src_vertex).collect();
        // Check that both 0 and 1 appear in the first half.
        let first_half: std::collections::HashSet<usize> = src_order[..2].iter().copied().collect();
        assert!(first_half.contains(&0) && first_half.contains(&1),
            "RoundRobin: first two elements must come from different vertices, got {:?}", src_order);
    }
}
