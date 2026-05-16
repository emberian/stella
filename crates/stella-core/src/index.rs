//! First-symbol term index for sublinear matchable-ray lookup (§49.7).
//!
//! ## Design
//!
//! `matchable(r, r′)` requires (§49.7, §48.2):
//!   1. Both `r` and `r′` are `App` nodes (variables cannot be matchable heads).
//!   2. Their head symbols have the *same* underlying `SymName` and *opposite*
//!      (or both-neutral) polarities.
//!   3. They are α-unifiable under `PolarisedCompat`.
//!
//! The index exploits condition (2): it maps `(SymName, Polarity)` → `Vec<RayId>`.
//! To find all rays that *could* match a query ray with head `(name, pol)`,
//! we look up the single bucket for `(name, opposite(pol))`.  For neutral
//! symbols both polarities coincide, so `Neutral ↦ Neutral`.
//!
//! This gives **O(bucket_size)** candidate retrieval instead of **O(n)** full scan,
//! where `bucket_size ≪ n` in practice (rays with the same underlying symbol and
//! opposite polarity are typically a small fraction of all rays).
//!
//! The index is a *pure speed optimisation*: it yields exactly the same set of
//! matchable pairs as the naïve O(n²) scan (oracle-equivalence tests in this module
//! verify this).

use std::collections::HashSet;

use rustc_hash::FxHashMap;

use crate::constellation::{get_ray, id_rays, Constellation, RayId};
use crate::dep_graph::{ray_colours, DepEdge, DepGraph};
use crate::polarised::{matchable, Polarity};
use crate::term::{get, SymName, TermData};

// ─────────────────────────────────────────────────────────────────────────────
// Index key helpers
// ─────────────────────────────────────────────────────────────────────────────

/// The key used for the first-symbol index.
///
/// Rays with head `(name, pol)` are stored under this key.
/// To find matchable partners for such a ray, look up `matchable_key(name, pol)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct IndexKey(SymName, Polarity);

/// Given the head `(name, pol)` of a ray, return the bucket key whose rays
/// satisfy the polarity pre-condition for `matchable`.
///
/// - Pos  → partners are Neg (same name)
/// - Neg  → partners are Pos (same name)
/// - Neutral → partners are Neutral (same name)
fn partner_key(name: SymName, pol: Polarity) -> IndexKey {
    let partner_pol = match pol {
        Polarity::Pos => Polarity::Neg,
        Polarity::Neg => Polarity::Pos,
        Polarity::Neutral => Polarity::Neutral,
    };
    IndexKey(name, partner_pol)
}

// ─────────────────────────────────────────────────────────────────────────────
// RayIndex
// ─────────────────────────────────────────────────────────────────────────────

/// First-symbol index over a constellation's rays.
///
/// Maps `(SymName, Polarity)` → `Vec<RayId>`.  Only `App`-headed rays (the
/// matchable ones) are stored; `Var` rays are skipped.
#[derive(Debug, Clone)]
pub struct RayIndex {
    map: FxHashMap<IndexKey, Vec<RayId>>,
}

impl RayIndex {
    /// Build a `RayIndex` from a constellation, restricting to rays whose
    /// colours are a subset of `c` (mirroring the colour-set filter in
    /// `DepGraph::build`).
    pub fn build(phi: &Constellation, c: &HashSet<String>) -> Self {
        let mut map: FxHashMap<IndexKey, Vec<RayId>> = FxHashMap::default();

        for rid in id_rays(phi) {
            let ray = get_ray(phi, rid);
            // Only App-headed rays can be matchable.
            if let TermData::App(sym, _) = get(ray) {
                // Apply the same colour-subset filter as DepGraph::build.
                let colours = ray_colours(ray);
                if colours.is_subset(c) {
                    let key = IndexKey(sym.name, sym.pol);
                    map.entry(key).or_default().push(rid);
                }
            }
        }

        Self { map }
    }

    /// Return all rays that satisfy the polarity pre-condition for
    /// `matchable` with a ray whose head is `(name, pol)`.
    ///
    /// Note: this is a *necessary* condition only — callers must still
    /// call `matchable(r, candidate)` to confirm α-unifiability.
    pub fn candidates(&self, name: SymName, pol: Polarity) -> &[RayId] {
        let key = partner_key(name, pol);
        self.map.get(&key).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Index-based DepGraph construction
// ─────────────────────────────────────────────────────────────────────────────

impl DepGraph {
    /// Build `D[Φ; C]` using the first-symbol index for sublinear candidate
    /// retrieval, instead of the naïve O(n²) pairwise scan.
    ///
    /// Produces *exactly* the same edge set as `DepGraph::build` (oracle
    /// equivalence is verified in the tests below).
    pub fn build_indexed(phi: &Constellation, c: &HashSet<String>) -> Self {
        let idx = RayIndex::build(phi, c);
        let ids: Vec<RayId> = id_rays(phi);
        let mut edges: Vec<DepEdge> = Vec::new();
        // Use an FxHashSet to deduplicate — we might encounter (a,b) from both
        // the a-bucket and the b-bucket when neutral rays query themselves.
        let mut seen: rustc_hash::FxHashSet<(RayId, RayId)> = rustc_hash::FxHashSet::default();

        for &rid_a in &ids {
            let ray_a = get_ray(phi, rid_a);
            let sym_a = match get(ray_a) {
                TermData::App(sym, _) => sym,
                TermData::Var(_) => continue,
            };
            // Colour filter (same as DepGraph::build).
            if !ray_colours(ray_a).is_subset(c) {
                continue;
            }

            for &rid_b in idx.candidates(sym_a.name, sym_a.pol) {
                // No self-edges within the same star.
                if rid_a.0 == rid_b.0 {
                    continue;
                }
                // Skip pairs already processed in the opposite direction.
                let canonical = if rid_a <= rid_b { (rid_a, rid_b) } else { (rid_b, rid_a) };
                if !seen.insert(canonical) {
                    continue;
                }

                let ray_b = get_ray(phi, rid_b);
                if matchable(ray_a, ray_b) {
                    edges.push(DepEdge::new(rid_a, rid_b));
                }
            }
        }

        Self { n_stars: phi.len(), edges }
    }

    /// Index-based version of `from_constellation` (uses `all_colours`).
    pub fn from_constellation_indexed(phi: &Constellation) -> Self {
        let c = crate::dep_graph::all_colours(phi);
        Self::build_indexed(phi, &c)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::time::Instant;

    use crate::circuits::{bool_module, circuit_constellation, excluded_middle_circuit_input1};
    use crate::automata::{eng_fig561_nfa, nfa_constellation};
    use crate::constellation::{Constellation, RayId};
    use crate::dep_graph::{all_colours, DepGraph};
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::{mk_app_str, mk_var, Term};

    // ── helpers ──────────────────────────────────────────────────────────────

    fn var(x: &str) -> Term { mk_var(x) }
    fn c(name: &str) -> Term { mk_app_str(name, vec![]) }
    fn app(f: &str, args: Vec<Term>) -> Term { mk_app_str(f, args) }
    fn nat(n: usize) -> Term {
        let mut t = c("0");
        for _ in 0..n { t = app("s", vec![t]); }
        t
    }

    /// Canonical edge-set: sorted Vec of sorted endpoint pairs.
    fn edge_set(dg: &DepGraph) -> Vec<[RayId; 2]> {
        let mut v: Vec<[RayId; 2]> = dg.edges.iter().map(|e| e.endpoints).collect();
        v.sort();
        v
    }

    /// Assert that `build_indexed` produces the same edges as `build` on a
    /// constellation.
    fn assert_oracle_equiv(phi: &Constellation) {
        let c = all_colours(phi);
        let scan = DepGraph::build(phi, &c);
        let indexed = DepGraph::build_indexed(phi, &c);
        assert_eq!(
            edge_set(&scan),
            edge_set(&indexed),
            "index-built dep-graph differs from scan-built dep-graph"
        );
    }

    // ── Oracle-equivalence: Horn addition ────────────────────────────────────

    fn add_prog() -> Constellation {
        vec![
            vec![pos_ray("add", vec![c("0"), var("Y"), var("Y")])],
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray("add", vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])]),
            ],
        ]
    }

    #[test]
    fn oracle_equiv_horn_add_1_plus_1() {
        let mut phi = add_prog();
        phi.push(vec![
            neg_ray("add", vec![nat(1), nat(1), var("R")]),
            var("R"),
        ]);
        assert_oracle_equiv(&phi);
    }

    #[test]
    fn oracle_equiv_horn_add_2_plus_2() {
        let mut phi = add_prog();
        phi.push(vec![
            neg_ray("add", vec![nat(2), nat(2), var("R")]),
            var("R"),
        ]);
        assert_oracle_equiv(&phi);
    }

    // ── Oracle-equivalence: NFA (fig 56.1) ───────────────────────────────────

    #[test]
    fn oracle_equiv_nfa() {
        let nfa = eng_fig561_nfa();
        let phi = nfa_constellation(&nfa, &["0", "0"], 1);
        assert_oracle_equiv(&phi);
    }

    // ── Oracle-equivalence: circuits (excluded-middle) ────────────────────────

    #[test]
    fn oracle_equiv_circuits() {
        let c_star = circuit_constellation(&excluded_middle_circuit_input1());
        let m_star = bool_module().module_constellation();
        let mut phi: Constellation = c_star;
        phi.extend(m_star);
        assert_oracle_equiv(&phi);
    }

    // ── Oracle-equivalence: tiny constellations ───────────────────────────────

    #[test]
    fn oracle_equiv_tiny_one_edge() {
        let phi = vec![
            vec![pos_ray("a", vec![])],
            vec![neg_ray("a", vec![])],
        ];
        assert_oracle_equiv(&phi);
    }

    #[test]
    fn oracle_equiv_tiny_no_edge() {
        let phi = vec![
            vec![pos_ray("a", vec![])],
            vec![pos_ray("a", vec![])],
        ];
        assert_oracle_equiv(&phi);
    }

    #[test]
    fn oracle_equiv_two_edges() {
        let phi = vec![
            vec![pos_ray("a", vec![]), pos_ray("b", vec![])],
            vec![neg_ray("a", vec![]), neg_ray("b", vec![])],
        ];
        assert_oracle_equiv(&phi);
    }

    #[test]
    fn oracle_equiv_with_variables() {
        let phi = vec![
            vec![pos_ray("f", vec![var("X")])],
            vec![neg_ray("f", vec![c("0")])],
            vec![neg_ray("f", vec![var("Y")]), var("Y")],
        ];
        assert_oracle_equiv(&phi);
    }

    // ── Timing micro-comparison ───────────────────────────────────────────────
    //
    // Synthetic constellation: n stars each with one positive ray and one
    // negative ray over the same symbol.  The scan has O(n²) pairs;
    // the index converges on the same set in O(n·bucket_size).

    fn synthetic_constellation(n: usize) -> Constellation {
        // n/2 stars with +sym(i), n/2 stars with -sym(i) for varying i.
        // Make n/4 symbols so each bucket has ~2 rays.
        let symbols = n / 4 + 1;
        (0..n)
            .map(|i| {
                let sym = format!("s{}", i % symbols);
                if i % 2 == 0 {
                    vec![pos_ray(&sym, vec![c(&format!("c{i}"))])]
                } else {
                    vec![neg_ray(&sym, vec![var(&format!("X{i}"))])]
                }
            })
            .collect()
    }

    #[test]
    fn timing_scan_vs_indexed() {
        let n = 200; // enough to show a ratio; still very fast
        let phi = synthetic_constellation(n);
        let c_set = all_colours(&phi);

        let t0 = Instant::now();
        for _ in 0..10 {
            let _ = DepGraph::build(&phi, &c_set);
        }
        let scan_us = t0.elapsed().as_micros() / 10;

        let t1 = Instant::now();
        for _ in 0..10 {
            let _ = DepGraph::build_indexed(&phi, &c_set);
        }
        let indexed_us = t1.elapsed().as_micros() / 10;

        // Also verify oracle equivalence on the synthetic constellation.
        assert_oracle_equiv(&phi);

        let ratio = scan_us as f64 / indexed_us.max(1) as f64;
        println!(
            "dep-graph build n={n}: scan={scan_us}µs  indexed={indexed_us}µs  ratio={ratio:.2}x"
        );
        // We don't assert a ratio — it varies by machine — but we do print it.
    }
}
