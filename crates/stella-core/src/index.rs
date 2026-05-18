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
use crate::term::{get, SymName, Term, TermData};

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
// DiscIndex — discrimination (substitution) tree over Φ's pattern rays
// (perf #4 / strategic-map C-#1)
//
// The head/colour `RayIndex` above narrows candidates to a single
// `(SymName, Polarity)` bucket. For galaxy Φ=405 a head bucket still holds
// many δ-rays, so `mat_phi_c_accel`/`any_match_accel` run
// `fp_unifiable`+`matchable_fast` over the whole bucket (~98 % of `find`).
//
// `DiscIndex` refines *within each head bucket* by each ray's **depth-1
// argument signature**: for `±h(a₁,…,a_k)` the discriminant is the
// per-position top-functor vector `[sig(a₁),…,sig(a_k)]`, where
// `sig(App(g,_)) = Some(g.name)` and `sig(Var) = None` (a wildcard slot).
// This is the proven-sound `fp_unifiable` discriminator, *lifted into the
// index* (built once per Φ) instead of run per-candidate.  The structure
// is a fixed-depth trie: level `i` branches on argument `i`'s `sig`, so
// the recursion depth is the head **arity** (≤ a handful), never the term
// size — no deep recursion, no stack growth with galaxy δ-body depth.
//
// ── FAITHFULNESS (the non-negotiable gate) ───────────────────────────────
// The retrieved set is a **superset** of the true `matchable` set — it
// never drops a real match.  Proof:
//
//   Let `q = ±h(q₁,…,q_k)`, `s = ∓h(s₁,…,s_m)` be App rays in the same
//   `partner_key` head bucket.  `matchable(q,s)` ⇒ `q`,`s` are
//   α-unifiable under `PolarisedCompat` ⇒ (i) `k = m` (equal arity — the
//   `App` rule of unification requires it) and (ii) for every position
//   `i`, `qᵢ` and `sᵢ` are unifiable.  If both `qᵢ` and `sᵢ` are `App`,
//   unifiability forces their top functors to be `PolarisedCompat`-
//   compatible; for non-head (inner) functors `PolarisedCompat` is exactly
//   `SymName` equality, so `sig(qᵢ) = sig(sᵢ)`.  If either is a `Var`
//   then the corresponding `sig` is `None` — a wildcard that the query
//   walk treats as "matches every stored alternative", imposing no
//   constraint.  Hence:
//
//       matchable(q,s)  ⇒  same arity ∧ ∀i. sig(qᵢ)=None ∨ sig(sᵢ)=None
//                          ∨ sig(qᵢ)=sig(sᵢ)
//                       ⇒  `s` is visited by `for_each_candidate(q)`.
//
//   The converse does NOT hold (occurs-check, variable *linking*, and
//   sub-argument structure below depth 1 are ignored) — so the result is
//   a strict *superset*, exactly the sound over-approximation required.
//   The per-candidate `matchable_fast` stays in the consumer and remains
//   the sole decider; the index only shrinks *how many* candidates reach
//   it.  Dropped-match impossibility is fuzz-proven against the reference
//   `matchable` (`disc_superset_of_matchable_fuzz`, this module) and by
//   the N-KS byte-identity gate (`iex_fast_*_eq_iex`).
// ─────────────────────────────────────────────────────────────────────────────

/// Depth-1 signature of one argument position.
///
/// `Sig(name)` for an `App` (top functor — sub-structure ignored, so a
/// variable *anywhere below* never over-constrains); `Wild` for a `Var`
/// (a hole that unifies with anything in that slot).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ArgSig {
    Sig(SymName),
    Wild,
}

#[inline]
fn arg_sig(t: Term) -> ArgSig {
    match get(t) {
        TermData::App(sym, _) => ArgSig::Sig(sym.name),
        TermData::Var(_) => ArgSig::Wild,
    }
}

/// Push the depth-1 argument-signature vector of a ray onto `out`.
/// `App(_, args)` ⇒ one `ArgSig` per argument (NOT recursive — depth-1
/// only, so the structure depth is bounded by head arity).  A `Var` ray
/// cannot reach here (only `App` rays are indexed).
fn ray_sig(ray: Term, out: &mut Vec<ArgSig>) {
    if let TermData::App(_, args) = get(ray) {
        for &a in args.iter() {
            out.push(arg_sig(a));
        }
    }
}

/// A fixed-depth signature trie node.  Depth = head arity; level `i`'s
/// edges are argument `i`'s `ArgSig`.  `rays` holds the rays whose full
/// signature vector ends exactly at this node, in `id_rays` (build) order
/// (so a path's `(i,j)` come out ascending).
#[derive(Debug, Clone, Default)]
struct SigNode {
    kids: FxHashMap<ArgSig, SigNode>,
    rays: Vec<RayId>,
}

impl SigNode {
    fn insert(&mut self, sig: &[ArgSig], rid: RayId) {
        match sig.split_first() {
            None => self.rays.push(rid),
            Some((s, rest)) => self.kids.entry(*s).or_default().insert(rest, rid),
        }
    }

    /// Visit a **superset** of the rays whose stored signature is
    /// position-wise compatible with the query signature `q[qi..]`.
    ///
    /// At level `i` (argument `i`):
    ///   * stored edge `Wild` ⇒ a stored variable: matches *any* query
    ///     arg — always followed.
    ///   * query `q[qi] == Wild` ⇒ a query variable: matches *any* stored
    ///     arg — follow **every** edge.
    ///   * else (both concrete) ⇒ follow only the exact `Sig(name)` edge.
    ///
    /// Recursion depth = signature length = head arity (bounded; no stack
    /// growth with term depth).
    fn query(&self, q: &[ArgSig], qi: usize, cb: &mut impl FnMut(RayId)) {
        if qi == q.len() {
            for &r in &self.rays {
                cb(r);
            }
            return;
        }
        // A stored `Wild` edge unifies with whatever the query has here.
        if let Some(kid) = self.kids.get(&ArgSig::Wild) {
            kid.query(q, qi + 1, cb);
        }
        match q[qi] {
            ArgSig::Wild => {
                // Query variable: every stored alternative is compatible.
                for (s, kid) in self.kids.iter() {
                    if *s != ArgSig::Wild {
                        kid.query(q, qi + 1, cb);
                    }
                }
            }
            qs @ ArgSig::Sig(_) => {
                // Concrete query functor: only the identical stored
                // functor can unify (Wild already handled above).
                if let Some(kid) = self.kids.get(&qs) {
                    kid.query(q, qi + 1, cb);
                }
            }
        }
    }
}

/// Per-head depth-1-signature discrimination index: `partner_key` bucket
/// → fixed-depth signature trie.
///
/// Built once per fixed Φ alongside (and consistent with) [`RayIndex`].
/// The bucket key is identical to `RayIndex`'s (`partner_key`), so the
/// polarity/colour gate is byte-identical; the trie only sub-divides the
/// already-correct head bucket by argument signature.
#[derive(Debug, Clone)]
pub struct DiscIndex {
    /// Bucket key → root signature node.  Empty bucket ⇒ absent.
    buckets: FxHashMap<IndexKey, SigNode>,
}

impl DiscIndex {
    /// Build the discrimination index from Φ, restricting to rays whose
    /// colours ⊆ `c` — the **same** ray set, same key, same `id_rays`
    /// order as [`RayIndex::build`] (so it is a pure refinement of it).
    pub fn build(phi: &Constellation, c: &HashSet<String>) -> Self {
        let mut buckets: FxHashMap<IndexKey, SigNode> = FxHashMap::default();
        let mut sig: Vec<ArgSig> = Vec::new();
        for rid in id_rays(phi) {
            let ray = get_ray(phi, rid);
            if let TermData::App(sym, _) = get(ray) {
                if ray_colours(ray).is_subset(c) {
                    let key = IndexKey(sym.name, sym.pol);
                    sig.clear();
                    ray_sig(ray, &mut sig);
                    buckets.entry(key).or_default().insert(&sig, rid);
                }
            }
        }
        Self { buckets }
    }

    /// Visit a **superset** of the rays matchable with a query ray whose
    /// head is `(name, pol)` and whose term is `q_ray`.
    ///
    /// Faithful: the visited set ⊇ `{ rid | matchable(q_ray, ray[rid]) }`
    /// (module gate).  Callers still confirm with `matchable`/`matchable_fast`.
    /// Allocation: one small `Vec<ArgSig>` of length = head arity (a
    /// handful) — orders of magnitude below the bucket scan it replaces.
    pub fn for_each_candidate(
        &self,
        name: SymName,
        pol: Polarity,
        q_ray: Term,
        mut cb: impl FnMut(RayId),
    ) {
        let key = partner_key(name, pol);
        let Some(root) = self.buckets.get(&key) else {
            return;
        };
        let mut sig: Vec<ArgSig> = Vec::new();
        ray_sig(q_ray, &mut sig);
        root.query(&sig, 0, &mut cb);
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

    // ─────────────────────────────────────────────────────────────────────
    // DiscIndex faithfulness harness (perf #4 — non-negotiable gate).
    //
    // The disc-tree candidate set must be a **superset** of the reference
    // matchable set: for the head/colour bucket of every query ray `q`, the
    // tree must visit *every* ray `s` with `matchable(q, s)` (it may visit
    // more — that is the sound over-approximation; it must never visit
    // fewer — that would silently drop a redex).  Proven by oracle:
    // disc-tree visited set ⊇ { s | RayIndex.candidates ∧ matchable(q,s) }.
    // We anchor on `RayIndex` (already oracle-proven == naïve O(n²) scan)
    // as the reference candidate domain, so this transitively proves
    // disc ⊇ true-matchable.
    // ─────────────────────────────────────────────────────────────────────
    use super::{DiscIndex, RayIndex};
    use crate::constellation::get_ray;
    use crate::polarised::matchable;
    use crate::term::{get, TermData};

    /// For every App ray `q` in Φ: assert
    ///   { s ∈ RayIndex.candidates(q) : matchable(q,s) }
    ///       ⊆  DiscIndex.for_each_candidate(q)
    /// and additionally that DiscIndex ⊆ RayIndex.candidates (same bucket
    /// domain — a refinement, never a widening of the colour/polarity gate).
    fn assert_disc_superset(phi: &Constellation) {
        let cset = all_colours(phi);
        let ri = RayIndex::build(phi, &cset);
        let di = DiscIndex::build(phi, &cset);

        for (si, star) in phi.iter().enumerate() {
            for (ji, &q) in star.iter().enumerate() {
                let (name, pol) = match get(q) {
                    TermData::App(sym, _) => (sym.name, sym.pol),
                    TermData::Var(_) => continue,
                };
                // Reference candidate domain (oracle-proven == naïve scan).
                let ref_bucket: std::collections::HashSet<RayId> =
                    ri.candidates(name, pol).iter().copied().collect();
                // True matchable subset of that domain.
                let mut must_have: std::collections::HashSet<RayId> =
                    std::collections::HashSet::new();
                for &rid in &ref_bucket {
                    if matchable(q, get_ray(phi, rid)) {
                        must_have.insert(rid);
                    }
                }
                // Disc-tree visited set for this query.
                let mut got: std::collections::HashSet<RayId> =
                    std::collections::HashSet::new();
                di.for_each_candidate(name, pol, q, |rid| {
                    got.insert(rid);
                });

                // (1) SUPERSET of the true matchable set — the gate.
                for rid in &must_have {
                    assert!(
                        got.contains(rid),
                        "DROPPED MATCH: query ray ({si},{ji})={q:?} \
                         matchable with {rid:?} but disc-tree did not visit it"
                    );
                }
                // (2) Refinement of (not wider than) the head bucket — the
                // disc-tree must never invent a candidate outside the
                // already-correct (polarity/colour-gated) RayIndex bucket.
                for rid in &got {
                    assert!(
                        ref_bucket.contains(rid),
                        "WIDENED: disc-tree visited {rid:?} outside the \
                         RayIndex bucket for query ({si},{ji})={q:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn disc_superset_horn_add() {
        let mut phi = add_prog();
        phi.push(vec![neg_ray("add", vec![nat(3), nat(2), var("R")]), var("R")]);
        assert_disc_superset(&phi);
    }

    #[test]
    fn disc_superset_nfa() {
        let nfa = eng_fig561_nfa();
        let phi = nfa_constellation(&nfa, &["0", "0"], 1);
        assert_disc_superset(&phi);
    }

    #[test]
    fn disc_superset_circuits() {
        let c_star = circuit_constellation(&excluded_middle_circuit_input1());
        let m_star = bool_module().module_constellation();
        let mut phi: Constellation = c_star;
        phi.extend(m_star);
        assert_disc_superset(&phi);
    }

    #[test]
    fn disc_superset_with_variables() {
        let phi = vec![
            vec![pos_ray("f", vec![var("X")])],
            vec![neg_ray("f", vec![c("0")])],
            vec![neg_ray("f", vec![var("Y")]), var("Y")],
            vec![pos_ray("f", vec![app("s", vec![var("Z")])])],
            vec![neg_ray("f", vec![app("s", vec![app("s", vec![c("0")])])])],
        ];
        assert_disc_superset(&phi);
    }

    #[test]
    fn disc_superset_nested_mixed() {
        // Deep, var-rich, multi-arity rays in one head bucket — the case
        // the trie's `Star`/skip-subterm logic must get exactly right.
        let phi = vec![
            vec![pos_ray("p", vec![app("g", vec![var("X"), c("a")]), var("Y")])],
            vec![neg_ray("p", vec![app("g", vec![c("b"), var("W")]), app("h", vec![c("c")])])],
            vec![neg_ray("p", vec![var("Q"), var("R")])],
            vec![neg_ray("p", vec![app("g", vec![var("X"), var("X")]), c("z")])],
            vec![neg_ray("p", vec![app("k", vec![c("a")]), c("d")])],
            vec![pos_ray("p", vec![var("M"), app("g", vec![c("a"), c("b")])])],
        ];
        assert_disc_superset(&phi);
    }

    /// Deterministic LCG fuzz: random multi-symbol, var-sharing, nested
    /// constellations.  The disc-tree visited set MUST be a superset of the
    /// reference `matchable` set on EVERY query ray of EVERY generated Φ.
    /// A single dropped match here ⇒ the index is unfaithful and must NOT
    /// ship (it would silently change redex selection — docs/07).
    #[test]
    fn disc_superset_of_matchable_fuzz() {
        struct Lcg(u64);
        impl Lcg {
            fn next(&mut self) -> u64 {
                self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
                self.0 >> 17
            }
            fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
                &xs[(self.next() as usize) % xs.len()]
            }
        }
        fn gen(rng: &mut Lcg, depth: u32) -> Term {
            if depth == 0 || rng.next() % 3 == 0 {
                return *rng.pick(&[var("X"), var("Y"), var("Z")]);
            }
            let head = *rng.pick(&["f", "g", "h", "k"]);
            let ar = (rng.next() % 3) as usize;
            app(head, (0..ar).map(|_| gen(rng, depth - 1)).collect())
        }
        fn gen_ray(rng: &mut Lcg) -> Term {
            let pos = rng.next() % 2 == 0;
            let nm = *rng.pick(&["p", "q", "r"]);
            let ar = 1 + (rng.next() % 3) as usize;
            let args: Vec<Term> = (0..ar).map(|_| gen(rng, 3)).collect();
            if pos { pos_ray(nm, args) } else { neg_ray(nm, args) }
        }

        let mut rng = Lcg(0x9E37_79B9_7F4A_7C15);
        for _ in 0..400 {
            let n_stars = 2 + (rng.next() % 8) as usize;
            let phi: Constellation = (0..n_stars)
                .map(|_| {
                    let k = 1 + (rng.next() % 3) as usize;
                    (0..k).map(|_| gen_ray(&mut rng)).collect()
                })
                .collect();
            assert_disc_superset(&phi);
        }
    }
}
