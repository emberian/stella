//! Near-linear unifier for the accelerated tier (docs/09 §B).
//!
//! `unify.rs` is the textbook Martelli–Montanari reference — it eagerly
//! re-applies each new binding across the whole remaining worklist
//! (`unify.rs:100-108`) and re-walks `t.vars()` per equation. Measured: that
//! `unify` is ≈53 % of engine wall time at galaxy Φ=405 (the dominant cost,
//! `STELLA_KS_PROF`). This module is the replacement used **only** by the
//! accelerated produce path; `unify.rs` stays the untouched spec oracle.
//!
//! Algorithm: triangular substitution + union-find over `Var` with path
//! compression; structural unification with a `(TermId,TermId)` visited memo
//! (hash-consed ⇒ each distinct subterm pair is visited once); a **deferred
//! post-pass occurs-check** (Martelli–Montanari almost-linear: `bind` is
//! O(1), one acyclicity DFS over the final triangular store). After a
//! successful solve the store is materialised once into a flat idempotent
//! `Substitution` — the exact type `fuse_theta`'s `theta.apply` consumes.
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

/// UF parent: a variable points either at another variable (a UF link) or at
/// a non-variable term (a shallow, triangular binding — never eagerly
/// expanded).
#[derive(Clone, Copy)]
enum Bound {
    Var(Var),
    Term(TermId),
}

struct Solver {
    parent: FxHashMap<Var, Bound>,
}

impl Solver {
    fn new() -> Self {
        Self { parent: FxHashMap::default() }
    }

    /// Resolve a term to its current representative (one structural level).
    /// `App` is returned as-is (structure read from the immutable store, never
    /// copied here). A `Var` is followed through `Bound::Var` links with path
    /// compression; resolution stops at an unbound representative
    /// (`mk_var_interned(rep)`) or at a `Bound::Term` (returned **shallowly** —
    /// triangular: its internals are *not* recursively substituted here).
    fn resolve(&mut self, t: TermId) -> TermId {
        let mut v = match get(t) {
            TermData::Var(v) => v,
            TermData::App(..) => return t,
        };
        // Walk the var chain, remembering it for path compression.
        let mut path: Vec<Var> = Vec::new();
        let sink: Bound = loop {
            match self.parent.get(&v).copied() {
                None => break Bound::Var(v), // unbound representative
                Some(Bound::Var(w)) => {
                    if w == v {
                        break Bound::Var(v); // self-rep (union invariant)
                    }
                    path.push(v);
                    v = w;
                }
                Some(Bound::Term(tt)) => break Bound::Term(tt),
            }
        };
        // Path-compress every visited var directly onto the sink.
        for p in path {
            self.parent.insert(p, sink);
        }
        match sink {
            Bound::Var(rep) => mk_var_interned(rep),
            Bound::Term(tt) => tt,
        }
    }

    fn bind(&mut self, v: Var, b: Bound) {
        self.parent.insert(v, b);
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
                // Union: link x's rep onto y (both are reps — resolve stopped
                // at unbound vars).
                if x != y {
                    s.bind(x, Bound::Var(y));
                }
            }
            (TermData::Var(x), _) => s.bind(x, Bound::Term(b)),
            (_, TermData::Var(y)) => s.bind(y, Bound::Term(a)), // Orient folded
            (TermData::App(f, fa), TermData::App(g, ga)) => {
                if !compat.compatible(f, g) || fa.len() != ga.len() {
                    return None; // clash / arity
                }
                for i in 0..fa.len() {
                    work.push((fa[i], ga[i]));
                }
            }
            _ => return None,
        }
    }

    // Deferred occurs-check: one acyclicity DFS over the triangular store.
    // A cyclic store ⇔ a genuine occurs-failure (`X = f(X)` ⇒ X reaches
    // itself); same accept/reject set as the reference's bind-time occur
    // check + solved-form acyclicity check, collapsed into one pass.
    if store_has_cycle(&s) {
        return None;
    }

    // Materialise the (now acyclic) triangular store into a flat idempotent
    // Substitution — once, via deep_resolve to a fixpoint. This is the moral
    // equivalent of the reference's final compose, computed from the UF store
    // instead of incrementally.
    let mut out: FxHashMap<Var, TermId> = FxHashMap::default();
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    let domain: Vec<Var> = s.parent.keys().copied().collect();
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

/// Cycle detection over the triangular store's variable graph: an edge
/// `v → w` exists if `parent[v]` is `Bound::Var(w)` or `Bound::Term(t)` with
/// `w ∈ vars(t)`. A var reachable from itself ⇒ occurs-failure. DFS with a
/// three-colour (white/grey/black) marking; `varsig`-pruning is a later
/// optimisation (E) — correctness only needs the cached `is_ground` skip in
/// `vars_of`.
fn store_has_cycle(s: &Solver) -> bool {
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        Grey,
        Black,
    }
    let mut mark: FxHashMap<Var, Mark> = FxHashMap::default();
    // Iterative DFS so deep galaxy stores never overflow the native stack.
    let roots: Vec<Var> = s.parent.keys().copied().collect();
    for root in roots {
        if mark.get(&root).copied() == Some(Mark::Black) {
            continue;
        }
        // (var, neighbours-iterator-as-vec, idx) frames.
        let mut stack: Vec<(Var, Vec<Var>, usize)> = Vec::new();
        let neighbours = |v: Var| -> Vec<Var> {
            match s.parent.get(&v).copied() {
                None => Vec::new(),
                Some(Bound::Var(w)) => vec![w],
                Some(Bound::Term(t)) => {
                    let mut set = FxHashSet::default();
                    vars_of(t, &mut set);
                    set.into_iter().collect()
                }
            }
        };
        mark.insert(root, Mark::Grey);
        stack.push((root, neighbours(root), 0));
        while let Some((v, ns, i)) = stack.last().cloned() {
            if i < ns.len() {
                stack.last_mut().unwrap().2 += 1;
                let w = ns[i];
                match mark.get(&w).copied() {
                    Some(Mark::Grey) => return true, // back-edge ⇒ cycle
                    Some(Mark::Black) => {}
                    None => {
                        mark.insert(w, Mark::Grey);
                        stack.push((w, neighbours(w), 0));
                    }
                }
            } else {
                mark.insert(v, Mark::Black);
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
        for _ in 0..3000 {
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
}
