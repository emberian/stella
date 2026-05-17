//! KA0 — recurrence-detector substrate (spec `docs/05` §9).
//!
//! Two pure, hash-cons-friendly primitives shared by KA1 (tabling /
//! variant-deletion) and KA2 (cycle acceleration):
//!
//! * [`canonical`] — renumber every variable to `Var::Idx(0,1,2,…)` in
//!   first-occurrence pre-order. α-equivalent terms ⇒ **identical `TermId`**
//!   (hash-consed) ⇒ "structurally-equivalent config seen before?" is an O(1)
//!   `TermId` compare. This is the variant check KA1 needs and the loop-state
//!   key KA2's tracer needs (cheap *because* de Bruijn `Var::Idx` landed).
//!
//! * [`lgg`] — least general generalization (anti-unification), the
//!   categorical dual of the unifier the engine already has. `lgg(prev,cur)`
//!   yields the common skeleton + the disagreement slots; for a recurring
//!   loop config that skeleton *is* the per-iteration context `C` and the
//!   slots are the iteration parameter (the KA2 detector primitive).
//!
//! KA0 is **observational only** — pure functions, no engine state changed,
//! faithful by construction. Wiring a trace history + witness into `iex_fast`
//! (still env-gated, still observational) is the next KA0 step; *applying*
//! acceleration is KA1/KA2 behind the pre-registered soundness contract.

use rustc_hash::FxHashMap;

use crate::term::{get, mk_app_interned, mk_var_interned, TermData, TermId, Var};

// ─────────────────────────────────────────────────────────────────────────────
// canonical — α-canonical form (first-occurrence Var::Idx renumbering)
// ─────────────────────────────────────────────────────────────────────────────

fn canon_rec(t: TermId, map: &mut FxHashMap<Var, u32>, next: &mut u32) -> TermId {
    match get(t) {
        TermData::Var(v) => {
            let idx = *map.entry(v).or_insert_with(|| {
                let n = *next;
                *next += 1;
                n
            });
            mk_var_interned(Var::Idx(idx))
        }
        TermData::App(sym, args) => {
            let new: Vec<TermId> = args.iter().map(|&a| canon_rec(a, map, next)).collect();
            mk_app_interned(sym, new)
        }
    }
}

/// α-canonical form: variables renumbered `Var::Idx(0,1,2,…)` by first
/// occurrence (pre-order). `canonical(s) == canonical(t)` **iff** `s` and `t`
/// are α-equivalent (variable-renaming-equal). O(1) comparison thereafter
/// (hash-consed `TermId` identity).
pub fn canonical(t: TermId) -> TermId {
    let mut map = FxHashMap::default();
    let mut next = 0u32;
    canon_rec(t, &mut map, &mut next)
}

/// `s` and `t` are α-equivalent (same up to consistent variable renaming).
pub fn alpha_eq(s: TermId, t: TermId) -> bool {
    canonical(s) == canonical(t)
}

// ─────────────────────────────────────────────────────────────────────────────
// lgg — least general generalization (anti-unification)
// ─────────────────────────────────────────────────────────────────────────────

/// The result of [`lgg`]: the anti-unifier `skeleton` plus, for each fresh
/// generalization variable, the `(s_subterm, t_subterm)` pair it abstracts.
/// `slots.len()` = number of distinct disagreement positions; a *single*
/// slot whose pair is a recursion-shaped (context-deeper) pair is the KA2
/// affine-recurrence witness.
#[derive(Debug, Clone)]
pub struct Lgg {
    pub skeleton: TermId,
    pub slots: Vec<(Var, TermId, TermId)>,
}

fn lgg_rec(
    s: TermId,
    t: TermId,
    table: &mut FxHashMap<(TermId, TermId), Var>,
    next: &mut u32,
    slots: &mut Vec<(Var, TermId, TermId)>,
) -> TermId {
    if s == t {
        return s; // identical subterm (hash-cons ⇒ pointer eq)
    }
    if let (TermData::App(f, sa), TermData::App(g, ta)) = (get(s), get(t)) {
        if f == g && sa.len() == ta.len() {
            let new: Vec<TermId> = sa
                .iter()
                .zip(ta.iter())
                .map(|(&a, &b)| lgg_rec(a, b, table, next, slots))
                .collect();
            return mk_app_interned(f, new);
        }
    }
    // Disagreement: one shared fresh variable per *distinct* (s,t) pair
    // (standard lgg sharing — repeated identical disagreements reuse the
    // same generalization variable, which is what makes lgg *least* general).
    if let Some(&v) = table.get(&(s, t)) {
        return mk_var_interned(v);
    }
    let v = Var::Idx(*next);
    *next += 1;
    table.insert((s, t), v);
    slots.push((v, s, t));
    mk_var_interned(v)
}

/// Least general generalization of `s` and `t`: the most specific term `g`
/// such that both `s` and `t` are substitution-instances of `g`. Fresh
/// generalization variables use `Var::Idx` from `0`.
pub fn lgg(s: TermId, t: TermId) -> Lgg {
    let mut table = FxHashMap::default();
    let mut next = 0u32;
    let mut slots = Vec::new();
    let skeleton = lgg_rec(s, t, &mut table, &mut next, &mut slots);
    Lgg { skeleton, slots }
}

// ─────────────────────────────────────────────────────────────────────────────
// recurrence witness (KA2 detector primitive — conservative first cut)
// ─────────────────────────────────────────────────────────────────────────────

/// Does `needle` (α) occur as a subterm of `hay`?  `proper` ⇒ require a
/// strictly-deeper occurrence (the whole-term match at depth 0 doesn't count).
pub fn occurs_alpha(needle: TermId, hay: TermId, proper: bool) -> bool {
    let nc = canonical(needle);
    fn go(h: TermId, nc: TermId, at_root: bool, proper: bool) -> bool {
        if !(at_root && proper) && canonical(h) == nc {
            return true;
        }
        match get(h) {
            TermData::App(_, args) => args.iter().any(|&a| go(a, nc, false, proper)),
            TermData::Var(_) => false,
        }
    }
    go(hay, nc, true, proper)
}

/// Is `t` the term `s` wrapped in a *fixed non-empty context*? (i.e. `s` (α)
/// occurs as a **proper** subterm of `t` — the per-iteration "grow by a
/// constant context" signature of a recursive loop parameter).
fn grows(s: TermId, t: TermId) -> bool {
    occurs_alpha(s, t, true)
}

/// A **conservative candidate filter** for an accelerable affine step between
/// two trace configs `prev` and `cur` (`cur` later in the trace). Returns the
/// `lgg` skeleton (the candidate per-iteration context `C`, with the varying
/// positions abstracted) when:
///
/// * `prev ≠α cur` (progress), and
/// * `lgg(prev,cur)` has a **non-trivial shared skeleton** (≥1 `App` node —
///   the loop-invariant context exists; not total disagreement), and
/// * **every** disagreement slot `(s_i,t_i)` is either α-invariant
///   (`s_i =α t_i`, a parameter passed through) **or** *grows* (`s_i` a
///   proper subterm of `t_i` — wrapped by a fixed context per iteration), and
/// * **≥1 slot grows** (there is actual iteration, not just renaming).
///
/// Soundness note: this only *nominates* candidates. No soundness rests on it
/// — KA2 still synthesises `Cᵏ`, **guards** it, and **differential-certifies**
/// against the unrolled reference `iex` (`N-KA-sound`). It is deliberately a
/// necessary-condition filter: it never fabricates a recurrence where the step
/// isn't "fixed skeleton + per-position fixed-context growth".
pub fn affine_recurrence(prev: TermId, cur: TermId) -> Option<TermId> {
    if alpha_eq(prev, cur) {
        return None;
    }
    let g = lgg(prev, cur);
    // Non-trivial shared skeleton: the root is a shared App (a bare Var
    // skeleton ⇒ prev/cur disagree at the root ⇒ no loop-invariant context).
    if !matches!(get(g.skeleton), TermData::App(..)) || g.slots.is_empty() {
        return None;
    }
    let mut any_growth = false;
    for (_, s_i, t_i) in &g.slots {
        if alpha_eq(*s_i, *t_i) {
            continue; // invariant parameter, fine
        }
        if grows(*s_i, *t_i) {
            any_growth = true;
            continue; // grown by a fixed context, fine
        }
        return None; // a slot that neither stays nor cleanly grows ⇒ reject
    }
    if any_growth {
        Some(g.skeleton)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{mk_app_str, mk_var};

    fn c(n: &str) -> TermId {
        mk_app_str(n, vec![])
    }
    fn app(h: &str, a: Vec<TermId>) -> TermId {
        mk_app_str(h, a)
    }
    fn v(n: &str) -> TermId {
        mk_var(n)
    }

    #[test]
    fn canonical_is_alpha_invariant() {
        // f(X, g(X, Y))  vs  f(A, g(A, B)) — α-equivalent ⇒ equal canonical.
        let t1 = app("f", vec![v("X"), app("g", vec![v("X"), v("Y")])]);
        let t2 = app("f", vec![v("A"), app("g", vec![v("A"), v("B")])]);
        assert_eq!(canonical(t1), canonical(t2));
        assert!(alpha_eq(t1, t2));
        // f(X,Y) vs f(X,X) are NOT α-equivalent (sharing differs).
        let t3 = app("f", vec![v("X"), v("Y")]);
        let t4 = app("f", vec![v("X"), v("X")]);
        assert_ne!(canonical(t3), canonical(t4));
        // ground terms: canonical is identity-ish (equal iff structurally equal).
        assert_eq!(canonical(c("a")), c("a"));
    }

    #[test]
    fn lgg_basic_and_sharing() {
        // lgg(f(a), f(b)) = f(Z)  — one slot.
        let g = lgg(app("f", vec![c("a")]), app("f", vec![c("b")]));
        assert_eq!(g.slots.len(), 1);
        assert_eq!(canonical(g.skeleton), canonical(app("f", vec![v("Z")])));
        // lgg sharing: f(a,a) vs f(b,b) → f(Z,Z) (ONE slot, reused), not f(Z,W).
        let g2 = lgg(
            app("f", vec![c("a"), c("a")]),
            app("f", vec![c("b"), c("b")]),
        );
        assert_eq!(g2.slots.len(), 1, "identical disagreements must share one var");
        assert_eq!(canonical(g2.skeleton), canonical(app("f", vec![v("Z"), v("Z")])));
        // distinct disagreements → two slots.
        let g3 = lgg(
            app("f", vec![c("a"), c("a")]),
            app("f", vec![c("b"), c("d")]),
        );
        assert_eq!(g3.slots.len(), 2);
        // identical terms → no slots, skeleton = the term.
        let same = app("f", vec![c("a")]);
        let g4 = lgg(same, same);
        assert!(g4.slots.is_empty());
        assert_eq!(g4.skeleton, same);
    }

    /// A Horn-`add`-style unfold pair: the loop wraps args 1 and 3 in `s`.
    /// `add(s(X),Y,s(Z))` vs `add(s(s(X')),Y',s(s(Z')))` — self-embedding,
    /// the canonical `prev` occurs inside `cur`; a single-parameter step.
    #[test]
    fn affine_recurrence_fires_on_add_unfold() {
        // add(s X, Y, s Z)  →  add(s(s X), Y, s(s Z)) : args 1,3 grow by a
        // fixed `s` context, arg 2 invariant (→ no slot, s==t short-circuits).
        let prev = app("add", vec![app("s", vec![v("X")]), v("Y"), app("s", vec![v("Z")])]);
        let cur = app(
            "add",
            vec![
                app("s", vec![app("s", vec![v("X")])]),
                v("Y"),
                app("s", vec![app("s", vec![v("Z")])]),
            ],
        );
        // X (α) is a *proper* subterm of s(X); not a proper subterm of itself.
        assert!(grows(v("X"), app("s", vec![v("X")])));
        assert!(!occurs_alpha(v("X"), v("X"), true));
        assert!(
            affine_recurrence(prev, cur).is_some(),
            "add-unfold is a textbook affine recurrence — detector must nominate it"
        );
        // α-equal configs ⇒ no progress ⇒ not a recurrence.
        let prev2 = app("add", vec![app("s", vec![v("A")]), v("B"), app("s", vec![v("Cc")])]);
        assert!(affine_recurrence(prev, prev2).is_none(), "α-equal ⇒ not a recurrence");
        // No false positive on unrelated / non-growing steps.
        assert!(affine_recurrence(c("foo"), app("bar", vec![c("baz")])).is_none());
        // Pure rename of a sub-position (no growth anywhere) ⇒ rejected.
        let r1 = app("g", vec![c("a"), v("P")]);
        let r2 = app("g", vec![c("b"), v("Q")]);
        assert!(
            affine_recurrence(r1, r2).is_none(),
            "no growing slot (only renames/swaps) ⇒ not an accelerable recurrence"
        );
    }
}
