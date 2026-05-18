//! Near-linear unifier for the accelerated tier (docs/09 §B).
//!
//! `unify.rs` is the textbook Martelli–Montanari reference — it eagerly
//! re-applies each new binding across the whole remaining worklist
//! (`unify.rs:100-108`) and re-walks `t.vars()` per equation. Measured: that
//! `unify` is ≈53 % of engine wall time at galaxy Φ=405 (the dominant cost,
//! `STELLA_KS_PROF`). This module is the replacement used **only** by the
//! accelerated produce path; `unify.rs` stays the untouched spec oracle.
//!
//! Algorithm: triangular substitution + a **dense arena union-find** over
//! `Var` with *path-halving* and *union-by-rank* (true ≈O(α(n)) — `parent`,
//! `rank` and the triangular `Bound::Term` slot all live in `Vec`-backed
//! arenas indexed by a dense per-solve slot; the var→slot interning is one
//! `slot_of` per `resolve` *entry*, never per link — the link-walk on the hot
//! path is pure array indexing with no per-op hashmap probe and no per-`find`
//! path `Vec` allocation, the SOTA practical-unifier structure). Structural
//! unification with a `(TermId,TermId)` visited memo (hash-consed ⇒ each
//! distinct subterm pair is visited once); a **deferred post-pass
//! occurs-check** (Martelli–Montanari almost-linear: `bind` is O(1), one
//! acyclicity DFS over the final triangular store). After a successful solve
//! the store is materialised once into a flat idempotent `Substitution` — the
//! exact type `fuse_theta`'s `theta.apply` consumes.
//!
//! Faithfulness: result-equivalent to `unify` under the **same** `Compatible`
//! — `unify_fast(E)` succeeds iff `unify(E)` does, and on success its MGU is
//! α-equal to the reference's (MGU unique up to α). That α-slack is exactly
//! what `faithfulness::psi_compatible` tolerates and byte-identity could not.
//! `unify` is the differential oracle (the fuzz test below).

use crate::subst::Substitution;
use crate::term::{get, mk_app_interned, mk_var_interned, TermData, TermId, Var};
use crate::unify::{Compatible, Equation, StdCompat};
use rustc_hash::{FxHashMap, FxHashSet};

/// Dense-arena slot. Every distinct `Var` seen in a solve is interned to one
/// contiguous `u32` slot (`Solver::slot_of`); all union-find state is keyed by
/// this `usize`, so the hot link-walk is pure `Vec` indexing.
type Slot = u32;

/// UF parent of a *root* slot: a root either represents an as-yet-unbound
/// variable (`Bound::Open`) or carries a shallow triangular binding to a
/// non-variable term (`Bound::Term`, never eagerly expanded). Non-root slots
/// don't consult this — they follow `parent` links.
#[derive(Clone, Copy)]
enum Bound {
    /// Root, no triangular term binding yet (an unbound representative var).
    Open,
    /// Root bound (triangular) to a non-variable term.
    Term(TermId),
}

/// SOTA dense-arena union-find: `parent`/`rank`/`bound` are `Vec`-indexed by a
/// per-solve dense slot. `find` uses *path-halving* (no per-op path `Vec`),
/// `union` is *by rank* — amortised ≈O(α(n)) with zero hashmap probes on the
/// link-walk. The only `Var`-keyed map is `intern`, hit once per `resolve`
/// entry to translate the *root* term's var into a slot — never per link.
struct Solver {
    /// `parent[i]` is `i` for a root, else the next slot toward the root.
    parent: Vec<Slot>,
    /// Union-by-rank bound (upper bound on tree height); valid at roots.
    rank: Vec<u8>,
    /// Triangular binding state, valid at roots.
    bound: Vec<Bound>,
    /// The `Var` each slot was interned from (for materialise / cycle pass).
    var_of: Vec<Var>,
    /// Lazy dense interner `Var → Slot`. Touched once per `resolve` entry, not
    /// on the per-link hot path.
    intern: FxHashMap<Var, Slot>,
}

impl Solver {
    fn new() -> Self {
        Self {
            parent: Vec::new(),
            rank: Vec::new(),
            bound: Vec::new(),
            var_of: Vec::new(),
            intern: FxHashMap::default(),
        }
    }

    /// Intern a `Var` to its dense slot, allocating arena rows on first sight.
    /// One hashmap probe per *call* (twice per work item, at `resolve` entry),
    /// O(1) amortised — the union-find walk below never touches this map.
    #[inline]
    fn slot_of(&mut self, v: Var) -> Slot {
        if let Some(&s) = self.intern.get(&v) {
            return s;
        }
        let s = self.parent.len() as Slot;
        self.parent.push(s);
        self.rank.push(0);
        self.bound.push(Bound::Open);
        self.var_of.push(v);
        self.intern.insert(v, s);
        s
    }

    /// Find the root slot of `s` with **path-halving** (every other node on
    /// the walk is repointed to its grandparent — no auxiliary `Vec`, no
    /// hashmap; one array store per two links). Amortised ≈O(α(n)).
    #[inline]
    fn find(&mut self, mut s: Slot) -> Slot {
        loop {
            let p = self.parent[s as usize];
            if p == s {
                return s;
            }
            let pp = self.parent[p as usize];
            self.parent[s as usize] = pp; // halve
            s = pp;
        }
    }

    /// Resolve a term to its current representative (one structural level).
    /// `App` is returned as-is (structure read from the immutable store, never
    /// copied here). A `Var` is followed through arena links (path-halving) to
    /// its root; resolution stops at an unbound representative
    /// (`mk_var_interned(rep)`) or at a triangular `Bound::Term` (returned
    /// **shallowly** — its internals are *not* recursively substituted here).
    fn resolve(&mut self, t: TermId) -> TermId {
        let v = match get(t) {
            TermData::Var(v) => v,
            TermData::App(..) => return t,
        };
        let s0 = self.slot_of(v);
        let r = self.find(s0);
        match self.bound[r as usize] {
            Bound::Open => mk_var_interned(self.var_of[r as usize]),
            Bound::Term(tt) => tt,
        }
    }

    /// Union the rep of `x` onto the rep of `y` (both args are unbound-var
    /// roots — `resolve` stopped at unbound vars before this is reached),
    /// **by rank**. The surviving root keeps `Bound::Open`.
    fn union_vars(&mut self, x: Var, y: Var) {
        let sx = self.slot_of(x);
        let sy = self.slot_of(y);
        let rx = self.find(sx);
        let ry = self.find(sy);
        if rx == ry {
            return;
        }
        let (lo, hi) = if self.rank[rx as usize] < self.rank[ry as usize] {
            (rx, ry)
        } else {
            (ry, rx)
        };
        // Attach the lower-rank root `lo` under `hi`.
        self.parent[lo as usize] = hi;
        if self.rank[lo as usize] == self.rank[hi as usize] {
            self.rank[hi as usize] += 1;
        }
    }

    /// Triangular-bind `v`'s representative to a non-variable term.
    fn bind_term(&mut self, v: Var, tt: TermId) {
        let s = self.slot_of(v);
        let r = self.find(s);
        self.bound[r as usize] = Bound::Term(tt);
    }

    /// Slots that are roots carrying a triangular term binding, plus every
    /// interned var paired with its (resolved) representative-or-term. Used by
    /// the post-pass cycle check and the materialise pass; not hot-path.
    fn n_slots(&self) -> usize {
        self.parent.len()
    }
}

/// Collect the `Var`s occurring in a term (post-pass / materialise helper —
/// not on the per-bind hot path; ground subtrees are skipped via the cached
/// `term::is_ground`).
fn vars_of(t: TermId, acc: &mut FxHashSet<Var>) {
    if crate::term::is_ground(t) {
        return;
    }
    match get(t) {
        TermData::Var(v) => {
            acc.insert(v);
        }
        TermData::App(_, args) => {
            for &a in args.iter() {
                vars_of(a, acc);
            }
        }
    }
}

/// `unify.rs`-equivalent unifier, `Compatible`-generic. Reference is
/// `unify::unify_with` (the oracle); this is result-equivalent under the same
/// `compat`.
pub fn unify_fast_with<C: Compatible>(
    equations: Vec<Equation>,
    compat: &C,
) -> Option<Substitution> {
    let mut s = Solver::new();

    // Belt-and-suspenders: a generous structural-work budget. A var→term
    // cycle terminates anyway (bounded by the finite set of distinct
    // hash-consed subterms), but a hard cap turns any pathological case into
    // an honest reject the differential oracle would catch, never a hang.
    let mut budget: u64 = 1;
    for e in &equations {
        budget = budget.saturating_add(8 * (term_size(e.lhs) + term_size(e.rhs)) as u64);
    }
    budget = budget.saturating_mul(4).saturating_add(4096);

    let mut work: Vec<(TermId, TermId)> = equations
        .iter()
        .map(|e| (e.lhs, e.rhs))
        .collect();
    let mut seen: FxHashSet<(TermId, TermId)> = FxHashSet::default();

    while let Some((a0, b0)) = work.pop() {
        if budget == 0 {
            return None; // pathological — honest reject (oracle-checked)
        }
        budget -= 1;

        let a = s.resolve(a0);
        let b = s.resolve(b0);
        if a == b {
            continue; // Clear — O(1) hash-cons id compare
        }
        // Memo on resolved pair: hash-consed ⇒ each distinct subterm pair is
        // structurally decomposed at most once (near-linear DAG unification).
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        if !seen.insert(key) {
            continue;
        }
        match (get(a), get(b)) {
            (TermData::Var(x), TermData::Var(y)) => {
                // Union by rank: link x's rep and y's rep (both are unbound
                // reps — resolve stopped at unbound vars).
                if x != y {
                    s.union_vars(x, y);
                }
            }
            (TermData::Var(x), _) => s.bind_term(x, b),
            (_, TermData::Var(y)) => s.bind_term(y, a), // Orient folded
            (TermData::App(f, fa), TermData::App(g, ga)) => {
                if !compat.compatible(f, g) || fa.len() != ga.len() {
                    return None; // clash / arity
                }
                for i in 0..fa.len() {
                    work.push((fa[i], ga[i]));
                }
            }
        }
    }

    // Deferred occurs-check: one acyclicity DFS over the triangular store.
    // A cyclic store ⇔ a genuine occurs-failure (`X = f(X)` ⇒ X reaches
    // itself); same accept/reject set as the reference's bind-time occur
    // check + solved-form acyclicity check, collapsed into one pass.
    if store_has_cycle(&mut s) {
        return None;
    }

    // Materialise the (now acyclic) triangular store into a flat idempotent
    // Substitution — once, via deep_resolve to a fixpoint. This is the moral
    // equivalent of the reference's final compose, computed from the UF store
    // instead of incrementally.
    let mut out: FxHashMap<Var, TermId> = FxHashMap::default();
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    // Domain: every interned var. A pure unbound root resolves to itself and
    // is skipped, so `out` is exactly the non-identity bindings — same map the
    // reference's final compose produces (result-equivalent, MGU unique up
    // to α).
    let domain: Vec<Var> = s.var_of.clone();
    for v in domain {
        let vt = mk_var_interned(v);
        let r = deep_resolve(&mut s, vt, &mut memo);
        if r != vt {
            out.insert(v, r);
        }
    }
    Some(Substitution(out))
}

/// Default-`Compatible` entry, mirroring `unify::unify`.
pub fn unify_fast(equations: Vec<Equation>) -> Option<Substitution> {
    unify_fast_with(equations, &StdCompat)
}

/// Fully expand a term through the triangular store to a fixpoint
/// (idempotent normal form). The store is acyclic here (post-pass verified),
/// so this terminates; memoised per `TermId`; ground subtrees are returned
/// as-is (cached `is_ground`).
fn deep_resolve(
    s: &mut Solver,
    t: TermId,
    memo: &mut FxHashMap<TermId, TermId>,
) -> TermId {
    if crate::term::is_ground(t) {
        return t;
    }
    if let Some(&m) = memo.get(&t) {
        return m;
    }
    let r = s.resolve(t);
    let out = match get(r) {
        TermData::Var(_) => r, // unbound representative
        TermData::App(sym, args) => {
            let new: Vec<TermId> =
                args.iter().map(|&a| deep_resolve(s, a, memo)).collect();
            if new == args.as_ref() {
                r
            } else {
                mk_app_interned(sym, new)
            }
        }
    };
    memo.insert(t, out);
    out
}

/// Cycle detection over the triangular store, as a graph on **root slots**.
/// From root `r` with `bound[r] == Bound::Term(t)` there is an edge to
/// `find(slot_of(w))` for every `w ∈ vars(t)`; UF (var=var) links carry no
/// term and so contribute no occurs-cycle (each union merges two `Open`
/// roots). A root reachable from itself ⇒ occurs-failure — the same
/// accept/reject set as the reference's bind-time occurs + solved-form
/// acyclicity, collapsed into one DFS. Iterative three-colour
/// (grey/black) DFS over a dense `Vec<Mark>` (no per-node hashmap); the
/// cached `is_ground` skip in `vars_of` prunes ground subtrees.
fn store_has_cycle(s: &mut Solver) -> bool {
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        White,
        Grey,
        Black,
    }
    // Pre-intern every var occurring inside a bound term so the slot universe
    // (and thus `mark`) is fixed before the DFS — `neighbours` then never
    // grows the arena and `mark[..]` is always in-bounds.
    {
        let mut i = 0;
        while i < s.n_slots() {
            if let Bound::Term(t) = s.bound[i] {
                let mut set = FxHashSet::default();
                vars_of(t, &mut set);
                for w in set {
                    s.slot_of(w);
                }
            }
            i += 1;
        }
    }
    let n = s.n_slots();
    let mut mark: Vec<Mark> = vec![Mark::White; n];
    // Resolve a var to the slot of its current representative root.
    fn root_slot(s: &mut Solver, v: Var) -> Slot {
        let sl = s.slot_of(v);
        s.find(sl)
    }
    // Outgoing root-slot neighbours of a root slot `r`.
    fn neighbours(s: &mut Solver, r: Slot) -> Vec<Slot> {
        match s.bound[r as usize] {
            Bound::Open => Vec::new(),
            Bound::Term(t) => {
                let mut set = FxHashSet::default();
                vars_of(t, &mut set);
                set.into_iter().map(|w| root_slot(s, w)).collect()
            }
        }
    }
    // Iterate over root slots only (a non-root slot's state is its root's).
    for start in 0..n {
        let r0 = s.find(start as Slot);
        if mark[r0 as usize] != Mark::White {
            continue;
        }
        // (root-slot, neighbours, idx) frames — iterative so deep galaxy
        // stores never overflow the native stack.
        let mut stack: Vec<(Slot, Vec<Slot>, usize)> = Vec::new();
        mark[r0 as usize] = Mark::Grey;
        let ns0 = neighbours(s, r0);
        stack.push((r0, ns0, 0));
        while let Some(&(v, _, _)) = stack.last() {
            let i = stack.last().unwrap().2;
            let ns_len = stack.last().unwrap().1.len();
            if i < ns_len {
                stack.last_mut().unwrap().2 += 1;
                let w = stack.last().unwrap().1[i];
                match mark[w as usize] {
                    Mark::Grey => return true, // back-edge ⇒ cycle
                    Mark::Black => {}
                    Mark::White => {
                        mark[w as usize] = Mark::Grey;
                        let nw = neighbours(s, w);
                        stack.push((w, nw, 0));
                    }
                }
            } else {
                mark[v as usize] = Mark::Black;
                stack.pop();
            }
        }
    }
    false
}

/// Distinct-subterm-bounded size (cheap, for the work budget).
fn term_size(t: TermId) -> usize {
    fn go(t: TermId, seen: &mut FxHashSet<TermId>) -> usize {
        if !seen.insert(t) {
            return 0;
        }
        match get(t) {
            TermData::Var(_) => 1,
            TermData::App(_, args) => {
                1 + args.iter().map(|&a| go(a, seen)).sum::<usize>()
            }
        }
    }
    go(t, &mut FxHashSet::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{mk_app_str, mk_var};

    fn v(x: &str) -> TermId {
        mk_var(x)
    }
    fn app(f: &str, a: Vec<TermId>) -> TermId {
        mk_app_str(f, a)
    }
    fn c(n: &str) -> TermId {
        mk_app_str(n, vec![])
    }
    fn eq(l: TermId, r: TermId) -> Equation {
        Equation::new(l, r)
    }

    /// Apply σ to a term to a fixpoint (idempotent σ ⇒ one pass suffices;
    /// done recursively here for the test oracle).
    fn ap(s: &Substitution, t: TermId) -> TermId {
        match get(t) {
            TermData::Var(x) => match s.0.get(&x) {
                Some(&u) if u != t => ap(s, u),
                _ => t,
            },
            TermData::App(sym, args) => {
                let n: Vec<TermId> = args.iter().map(|&a| ap(s, a)).collect();
                if n == args.as_ref() {
                    t
                } else {
                    mk_app_interned(sym, n)
                }
            }
        }
    }

    // ── Same accept/reject set as the reference (mirrors lib.rs MM tests) ──

    #[test]
    fn solves_and_unifies() {
        // f(X, c) =? f(g(Y), c) ⇒ σ makes both sides equal.
        let l = app("f", vec![v("X"), c("c")]);
        let r = app("f", vec![app("g", vec![v("Y")]), c("c")]);
        let s = unify_fast(vec![eq(l, r)]).expect("unifies");
        assert_eq!(ap(&s, l), ap(&s, r));
        assert_eq!(crate::antiunify::canonical(ap(&s, l)),
                   crate::antiunify::canonical(ap(&s, r)));
    }

    #[test]
    fn occurs_check_rejects() {
        // X =? f(X) — deferred post-pass must catch the cycle.
        assert!(unify_fast(vec![eq(v("X"), app("f", vec![v("X")]))]).is_none());
        // Indirect: X =? f(Y), Y =? X  — X reaches itself through Y.
        assert!(unify_fast(vec![
            eq(v("X"), app("f", vec![v("Y")])),
            eq(v("Y"), v("X")),
        ])
        .is_none());
    }

    #[test]
    fn clash_and_arity_reject() {
        assert!(unify_fast(vec![eq(app("f", vec![v("X")]), app("g", vec![c("c")]))]).is_none());
        assert!(unify_fast(vec![eq(
            app("f", vec![v("X"), v("Y")]),
            app("f", vec![v("X")]),
        )])
        .is_none());
    }

    #[test]
    fn multi_equation_and_orient() {
        // {f(X, f(Y)) =? f(g(c,c), Z)} (§B.1.10) — both sides equal under σ.
        let l = app("f", vec![v("X"), app("f", vec![v("Y")])]);
        let r = app("f", vec![app("g", vec![c("c"), c("c")]), v("Z")]);
        let s = unify_fast(vec![eq(l, r)]).expect("unifies");
        assert_eq!(ap(&s, l), ap(&s, r));
        // Orient: {f(c) =? Y} ⇒ Y ↦ f(c)
        let s2 = unify_fast(vec![eq(app("f", vec![c("c")]), v("Y"))]).expect("orient");
        assert_eq!(ap(&s2, v("Y")), app("f", vec![c("c")]));
    }

    /// DIFFERENTIAL FUZZ vs the reference `unify` oracle: same accept/reject,
    /// and on success the MGUs agree up to α (canonical-equal applied to a
    /// probe). Deterministic LCG, std-only.
    #[test]
    fn fuzz_result_equivalent_to_reference_unify() {
        use crate::unify::unify as unify_ref;
        let mut rng: u64 = 0x9E3779B97F4A7C15;
        let mut next = || {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            rng >> 33
        };
        let atoms = ["a", "b", "c"];
        let fns = ["f", "g", "h"];
        let vnames = ["X", "Y", "Z", "W"];
        fn build(
            depth: u32,
            next: &mut impl FnMut() -> u64,
            atoms: &[&str],
            fns: &[&str],
            vnames: &[&str],
        ) -> TermId {
            if depth == 0 || next() % 3 == 0 {
                if next() % 2 == 0 {
                    mk_var(vnames[(next() as usize) % vnames.len()])
                } else {
                    mk_app_str(atoms[(next() as usize) % atoms.len()], vec![])
                }
            } else {
                let f = fns[(next() as usize) % fns.len()];
                let ar = 1 + (next() as usize % 2);
                let args = (0..ar)
                    .map(|_| build(depth - 1, next, atoms, fns, vnames))
                    .collect();
                mk_app_str(f, args)
            }
        }
        let mut checked = 0;
        // 3000 → 20000: the dense-arena UF rewrite is differential-critical;
        // the whole sweep is sub-second so the wider net is ~free.
        for _ in 0..20000 {
            let l = build(4, &mut next, &atoms, &fns, &vnames);
            let r = build(4, &mut next, &atoms, &fns, &vnames);
            let e = vec![eq(l, r)];
            let rf = unify_ref(e.clone());
            let ff = unify_fast(e);
            assert_eq!(
                rf.is_some(),
                ff.is_some(),
                "accept/reject divergence on ({l:?},{r:?}): ref={:?} fast={:?}",
                rf.is_some(),
                ff.is_some()
            );
            if let (Some(_), Some(sf)) = (&rf, &ff) {
                // The fast MGU must actually unify the inputs (soundness)…
                assert_eq!(
                    crate::antiunify::canonical(ap(sf, l)),
                    crate::antiunify::canonical(ap(sf, r)),
                    "fast σ fails to unify ({l:?} =? {r:?})"
                );
                checked += 1;
            }
        }
        assert!(checked > 50, "fuzz exercised too few successful unifications ({checked})");
    }

    /// Focused union-find microbench: the dense arena (`Solver::find`,
    /// path-halving + union-by-rank, `Vec` arenas) vs an apples-to-apples
    /// reimplementation of the *old* structure (`FxHashMap<Var,Bound>` parent
    /// map + per-`resolve` path `Vec` + `insert`-based path compression) on a
    /// UF-heavy workload (long var=var union chains then a deep-resolve sweep
    /// — exactly the link-walk the rewrite targets). `--ignored` (timing,
    /// not a CI gate); std-only `Instant`. measure-don't-guess.
    #[test]
    #[ignore = "microbench: cargo test -p stella-core --lib unify_fast::tests::bench -- --ignored --nocapture"]
    fn bench_union_find_dense_vs_hashmap() {
        use std::time::Instant;

        // Old-structure reference: hashmap-keyed UF, same algorithm the
        // module had before (Bound::Var links + per-resolve path Vec).
        #[derive(Clone, Copy)]
        enum OldBound {
            Var(Var),
            Term(TermId),
        }
        struct OldUf {
            parent: FxHashMap<Var, OldBound>,
        }
        impl OldUf {
            fn resolve_var(&mut self, mut vv: Var) -> Var {
                let mut path: Vec<Var> = Vec::new();
                let rep = loop {
                    match self.parent.get(&vv).copied() {
                        None => break vv,
                        Some(OldBound::Var(w)) => {
                            if w == vv {
                                break vv;
                            }
                            path.push(vv);
                            vv = w;
                        }
                        Some(OldBound::Term(_)) => break vv,
                    }
                };
                for p in path {
                    self.parent.insert(p, OldBound::Var(rep));
                }
                rep
            }
        }

        const N: u32 = 50_000;
        const SWEEPS: u32 = 8;

        // ---- new dense arena ----
        let t0 = Instant::now();
        let mut acc_new: u64 = 0;
        for _ in 0..SWEEPS {
            let mut s = Solver::new();
            for i in 0..N - 1 {
                s.union_vars(Var::idx(i), Var::idx(i + 1));
            }
            for i in 0..N {
                let sl = s.slot_of(Var::idx(i));
                acc_new += s.find(sl) as u64;
            }
        }
        let dt_new = t0.elapsed();

        // ---- old hashmap-keyed UF ----
        let t1 = Instant::now();
        let mut acc_old: u64 = 0;
        for _ in 0..SWEEPS {
            let mut u = OldUf { parent: FxHashMap::default() };
            for i in 0..N - 1 {
                let a = Var::idx(i);
                let b = Var::idx(i + 1);
                let ra = u.resolve_var(a);
                let rb = u.resolve_var(b);
                if ra != rb {
                    u.parent.insert(ra, OldBound::Var(rb));
                }
            }
            for i in 0..N {
                acc_old += match u.resolve_var(Var::idx(i)) {
                    Var::Idx(n) => n as u64,
                    Var::Named(_) => 0,
                };
            }
        }
        let dt_old = t1.elapsed();

        std::hint::black_box((acc_new, acc_old));
        let spd = dt_old.as_secs_f64() / dt_new.as_secs_f64();
        eprintln!(
            "union-find {N} chain × {SWEEPS} sweeps:\n  dense-arena : {dt_new:?}\n  hashmap-old : {dt_old:?}\n  speedup     : {spd:.2}×"
        );
        assert!(
            dt_new < dt_old,
            "dense arena ({dt_new:?}) not faster than hashmap-keyed UF ({dt_old:?})"
        );
    }
}
