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
// embeds — term homeomorphic embedding (Kruskal), the termination "whistle"
// ─────────────────────────────────────────────────────────────────────────────

/// Homeomorphic embedding `s ⊴ t` on finite-signature **terms** (Kruskal's
/// tree theorem). Decidable, and a *well-quasi-order*: in any infinite
/// sequence of terms `t₀,t₁,…` over a finite signature there exist `i<j` with
/// `tᵢ ⊴ tⱼ`. That is exactly what makes it a termination-safe **whistle** —
/// a "dangerous repetition" alarm that cannot be silenced forever, so a
/// supercompiler/recurrence detector that blows the whistle on `tᵢ ⊴ tⱼ`
/// (then generalizes) is guaranteed to stop.
///
/// Definition (term version — NOT the 1-ary Higman word special case):
/// `s ⊴ t` iff
///   (DIVE)    `s ⊴ tⱼ` for some argument `tⱼ` of `t`               — or
///   (COUPLE)  `s = f(s₁…sₙ)`, `t = f(t₁…tₙ)`, and `sᵢ ⊴ tᵢ` ∀i.
/// A variable embeds into any term of the *same variable identity* (we treat
/// `Var` as a nullary symbol keyed by its `Var` value, so `X ⊴ X` but
/// `X ⋬ Y`). DIVE is tried even when heads match, so e.g.
/// `f(a) ⊴ f(g(f(a)))` (dive into the inner `f(a)`).
pub fn embeds(s: TermId, t: TermId) -> bool {
    if s == t {
        return true; // hash-cons pointer eq ⇒ identical (incl. same Var)
    }
    // DIVE: s embeds into some proper subterm of t.
    if let TermData::App(_, targs) = get(t) {
        if targs.iter().any(|&tj| embeds(s, tj)) {
            return true;
        }
    }
    // COUPLE: same head & arity, embed argument-wise (zipped).
    match (get(s), get(t)) {
        (TermData::App(f, sa), TermData::App(g, ta)) => {
            f == g && sa.len() == ta.len() && sa.iter().zip(ta.iter()).all(|(&a, &b)| embeds(a, b))
        }
        // Var(s): only the s==t case above can match it (handled). Distinct
        // vars / var-vs-app do not couple and cannot be dived (no subterms).
        _ => false,
    }
}

/// Embedding *up to α* (variables compared by canonical first-occurrence
/// index, not raw identity). `affine_recurrence` uses this so a renamed
/// unfold (`add(s X,…)` ⊴ `add(s(s X'),…)`) trips the whistle: it is the
/// same structural growth modulo a consistent renaming.
fn embeds_alpha(s: TermId, t: TermId) -> bool {
    embeds(canonical(s), canonical(t))
}

// ─────────────────────────────────────────────────────────────────────────────
// rigid anti-unification — LCS-rigid generalizer (Kutsia)
// ─────────────────────────────────────────────────────────────────────────────

/// Rigid anti-unification (Kutsia & Pau). Unrestricted AU over sequence /
/// spine arguments is hopelessly nondeterministic (and — see the HARD
/// CAUTION below — AU *modulo unit* with ≥2 unital symbols is **NULLARY**:
/// there need be no minimal complete set of generalizers at all). We there-
/// fore stay **syntactic & rigid**: a *rigidity function* fixes a structured
/// common skeleton — here the **longest common subsequence (LCS)** of the
/// two `App` argument lists when heads agree but arities differ — and the
/// gaps (the non-LCS argument runs) are abstracted to one fresh variable
/// each. Recursion is rigid-AU on the aligned (LCS-matched) argument pairs.
///
/// HARD CAUTION — anti-unification *modulo unit* (one-unital case only):
/// anti-unification modulo the unit equation `e·x = x = x·e` is **finitary**
/// for **one** unital symbol but **NULLARY for two or more** unital symbols
/// (no minimal complete set of generalizers can be guaranteed to exist).
/// This module therefore **never** implements unrestricted AU-modulo-units.
/// It stays syntactic/rigid and treats *at most one* unit — the spine/stack
/// unit, the linear / one-unital case — via the LCS rigidity function only.
/// Do not extend this to a second unital symbol: the result set can be empty
/// and the generalizer would silently become incomplete.
#[derive(Debug, Clone)]
pub struct RigidGen {
    pub skeleton: TermId,
    pub slots: Vec<(Var, TermId, TermId)>,
}

/// Longest-common-subsequence alignment of two `TermId` slices, by hash-cons
/// identity (`==`). Returns the matched index pairs `(i,j)` in order. O(n·m)
/// DP — argument lists are tiny; this is a rigidity function, not a hot path.
fn lcs_align(a: &[TermId], b: &[TermId]) -> Vec<(usize, usize)> {
    let (n, m) = (a.len(), b.len());
    let mut dp = vec![vec![0u32; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            dp[i][j] = if a[i] == b[j] {
                dp[i + 1][j + 1] + 1
            } else {
                dp[i + 1][j].max(dp[i][j + 1])
            };
        }
    }
    let (mut i, mut j, mut out) = (0, 0, Vec::new());
    while i < n && j < m {
        if a[i] == b[j] {
            out.push((i, j));
            i += 1;
            j += 1;
        } else if dp[i + 1][j] >= dp[i][j + 1] {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

fn rigid_rec(
    s: TermId,
    t: TermId,
    table: &mut FxHashMap<(TermId, TermId), Var>,
    next: &mut u32,
    slots: &mut Vec<(Var, TermId, TermId)>,
) -> TermId {
    if s == t {
        return s; // identical subterm (hash-cons pointer eq)
    }
    if let (TermData::App(f, sa), TermData::App(g, ta)) = (get(s), get(t)) {
        if f == g {
            if sa.len() == ta.len() {
                // Same arity ⇒ positional rigid-AU (degenerate LCS = identity).
                let new: Vec<TermId> = sa
                    .iter()
                    .zip(ta.iter())
                    .map(|(&a, &b)| rigid_rec(a, b, table, next, slots))
                    .collect();
                return mk_app_interned(f, new);
            }
            // Same head, differing arity (a spine/sequence): RIGIDITY = LCS.
            // The LCS-matched argument pairs are kept (rigid-AU'd); each
            // maximal run of unmatched args (on either side) collapses to a
            // single shared fresh variable — deterministic & small.
            let pairs = lcs_align(&sa, &ta);
            if !pairs.is_empty() {
                let mut new = Vec::new();
                let (mut pi, mut pj) = (0usize, 0usize);
                let emit_gap =
                    |new: &mut Vec<TermId>,
                     gs: &[TermId],
                     gt: &[TermId],
                     table: &mut FxHashMap<(TermId, TermId), Var>,
                     next: &mut u32,
                     slots: &mut Vec<(Var, TermId, TermId)>| {
                        if gs.is_empty() && gt.is_empty() {
                            return;
                        }
                        let key = (mk_gap(gs), mk_gap(gt));
                        if let Some(&vv) = table.get(&key) {
                            new.push(mk_var_interned(vv));
                            return;
                        }
                        let vv = Var::Idx(*next);
                        *next += 1;
                        table.insert(key, vv);
                        slots.push((vv, key.0, key.1));
                        new.push(mk_var_interned(vv));
                    };
                for &(mi, mj) in &pairs {
                    emit_gap(&mut new, &sa[pi..mi], &ta[pj..mj], table, next, slots);
                    new.push(rigid_rec(sa[mi], ta[mj], table, next, slots));
                    pi = mi + 1;
                    pj = mj + 1;
                }
                emit_gap(&mut new, &sa[pi..], &ta[pj..], table, next, slots);
                return mk_app_interned(f, new);
            }
            // No common argument subsequence ⇒ fall through to a fresh var.
        }
    }
    // Disagreement (incl. head/arity mismatch with empty LCS): one shared
    // fresh variable per *distinct* (s,t) pair (lgg-style sharing ⇒ least).
    if let Some(&v) = table.get(&(s, t)) {
        return mk_var_interned(v);
    }
    let v = Var::Idx(*next);
    *next += 1;
    table.insert((s, t), v);
    slots.push((v, s, t));
    mk_var_interned(v)
}

/// Reify an argument-gap (a run of unmatched spine args) as a single term so
/// it can be a hash-cons key / slot payload. Empty ⇒ a reserved nullary
/// symbol; singleton ⇒ the arg itself; otherwise an `$gap(…)` wrapper. The
/// symbol name is internal and never escapes into a skeleton.
fn mk_gap(run: &[TermId]) -> TermId {
    match run {
        [] => crate::term::mk_app_str("$gap.ε", vec![]),
        [x] => *x,
        xs => crate::term::mk_app_str("$gap", xs.to_vec()),
    }
}

/// Rigid generalizer of `s` and `t`: like [`lgg`] on equal-arity structure,
/// but on a head-matched **arity mismatch** (a spine) it fixes the LCS of the
/// argument lists as the rigid skeleton and abstracts the gaps. Deterministic
/// and small by construction (the rigidity function removes AU's sequence
/// nondeterminism). Variables number from `Var::Idx(0)` like `lgg`.
pub fn rigid_generalize(s: TermId, t: TermId) -> RigidGen {
    let mut table = FxHashMap::default();
    let mut next = 0u32;
    let mut slots = Vec::new();
    let skeleton = rigid_rec(s, t, &mut table, &mut next, &mut slots);
    RigidGen { skeleton, slots }
}

// ─────────────────────────────────────────────────────────────────────────────
// recurrence witness (KA2 detector primitive — embedding-gated + rigid)
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
///
/// Superseded inside `affine_recurrence` by the homeomorphic-embedding
/// whistle (`embeds_alpha`), which is strictly stronger (embedding ⊇ "is a
/// proper subterm"); retained as a documented, test-exercised helper.
#[allow(dead_code)]
fn grows(s: TermId, t: TermId) -> bool {
    occurs_alpha(s, t, true)
}

/// A **conservative candidate filter** for an accelerable affine step between
/// two trace configs `prev` and `cur` (`cur` later in the trace). Returns the
/// **rigid** generalizer skeleton (the candidate per-iteration context `C`,
/// with the varying positions abstracted) when:
///
/// * `prev ≠α cur` (progress), and
/// * **the whistle blows**: `prev ⊴ cur` modulo α — `prev` is homeomorphically
///   embedded in `cur` (Kruskal). This is the wqo-backed "dangerous repetition
///   / this could grow forever" alarm; only *then* do we generalize. Replaces
///   the ad-hoc `occurs/grows` heuristic with the standard supercompiler
///   whistle, and
/// * the **rigid generalizer** `rigid_generalize(prev,cur)` has a non-trivial
///   shared skeleton (root is a shared `App` — the loop-invariant context
///   exists; not total disagreement), and ≥1 slot (there is variation), and
/// * **every** slot `(s_i,t_i)` is either α-invariant (`s_i =α t_i`, a
///   passed-through parameter) **or** itself embedding-progressing
///   (`s_i ⊴ t_i` modulo α with `s_i ≠α t_i` — that position grew under a
///   fixed context per iteration), and ≥1 slot progresses.
///
/// Soundness note: this only *nominates* candidates. No soundness rests on it
/// — KA2 still synthesises `Cᵏ`, **guards** it, and **differential-certifies**
/// against the unrolled reference `iex` (`N-KA-sound`). It is deliberately a
/// necessary-condition filter, now anchored on the homeomorphic-embedding
/// well-quasi-order (termination-safe) and a deterministic rigid generalizer.
pub fn affine_recurrence(prev: TermId, cur: TermId) -> Option<TermId> {
    if alpha_eq(prev, cur) {
        return None;
    }
    // WHISTLE: only nominate when prev is homeomorphically embedded in cur
    // (modulo α). wqo ⇒ this signal is termination-safe, and it strictly
    // characterises "cur is prev grown by some context", which is the only
    // shape an affine recurrence can take.
    if !embeds_alpha(prev, cur) {
        return None;
    }
    // Rigid (LCS) generalization — deterministic, small (see RigidGen doc &
    // the one-unital HARD CAUTION). The skeleton is the candidate context C.
    let g = rigid_generalize(prev, cur);
    // Non-trivial shared skeleton: the root is a shared App (a bare Var
    // skeleton ⇒ prev/cur disagree at the root ⇒ no loop-invariant context).
    if !matches!(get(g.skeleton), TermData::App(..)) || g.slots.is_empty() {
        return None;
    }
    let mut any_growth = false;
    for (_, s_i, t_i) in &g.slots {
        if alpha_eq(*s_i, *t_i) {
            continue; // invariant parameter passed through, fine
        }
        // Per-slot whistle: the position itself must be an embedding-step
        // (grew under a fixed context). Strictly stronger than the old
        // `grows` (proper-subterm) test and consistent with the root gate.
        if embeds_alpha(*s_i, *t_i) {
            any_growth = true;
            continue;
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

    // ── homeomorphic-embedding whistle (Kruskal wqo) ──────────────────────

    #[test]
    fn embeds_wqo_basics() {
        // Reflexive.
        let fa = app("f", vec![c("a")]);
        assert!(embeds(fa, fa));
        assert!(embeds(c("a"), c("a")));
        // DIVE: f(a) ⊴ f(g(a))  (embed into the inner arg run).
        assert!(embeds(fa, app("f", vec![app("g", vec![c("a")])])));
        // DIVE through a different head: f(a) ⊴ h(f(a)).
        assert!(embeds(fa, app("h", vec![fa])));
        // Deep dive: f(a) ⊴ f(g(f(a))) — dive beats same-head couple here.
        assert!(embeds(fa, app("f", vec![app("g", vec![fa])])));
        // COUPLE + DIVE mix: f(a,b) ⊴ h(f(a,c), f(d,b))? No single arg of h
        // embeds f(a,b) coupling-wise (a⋬c on left, d⋬a on right) so this is
        // FALSE — the textbook "needs different args" non-embedding.
        let fab = app("f", vec![c("a"), c("b")]);
        let outer = app("h", vec![app("f", vec![c("a"), c("c")]), app("f", vec![c("d"), c("b")])]);
        assert!(!embeds(fab, outer));
        // But f(a,b) ⊴ h(g, f(a, k(b))) by dive+couple (a⊴a, b⊴k(b)).
        let outer2 = app("h", vec![c("g"), app("f", vec![c("a"), app("k", vec![c("b")])])]);
        assert!(embeds(fab, outer2));
        // Non-embedding: g(a) ⋬ f(b) (head & content differ, no dive target).
        assert!(!embeds(app("g", vec![c("a")]), app("f", vec![c("b")])));
        // Distinct constants do not embed.
        assert!(!embeds(c("a"), c("b")));
        // Variable identity: X ⊴ X but X ⋬ Y (Var keyed by identity).
        assert!(embeds(v("X"), v("X")));
        assert!(!embeds(v("X"), v("Y")));
        // X ⊴ s(X) by dive (X is an arg of s(X)).
        assert!(embeds(v("X"), app("s", vec![v("X")])));
        // Arity-sensitive couple: f(a) ⋬ f(a,b) at the root, but DIVE finds
        // f(a) inside? args of f(a,b) are a,b — neither embeds f(a). FALSE.
        assert!(!embeds(fa, app("f", vec![c("a"), c("b")])));
    }

    // ── rigid (LCS) generalization over a spine ───────────────────────────

    #[test]
    fn rigid_generalize_picks_lcs_skeleton() {
        // Same-arity ⇒ behaves like lgg (positional).
        let g = rigid_generalize(app("f", vec![c("a")]), app("f", vec![c("b")]));
        assert_eq!(g.slots.len(), 1);
        assert_eq!(canonical(g.skeleton), canonical(app("f", vec![v("Z")])));

        // Spine: same head, differing arity. LCS of [a,b,c] vs [a,x,b,c] is
        // [a,b,c]; the single inserted `x` collapses to ONE fresh var. Rigid
        // skeleton (inspect-don't-trust via canonical):  f(a, W, b, c).
        let s = app("f", vec![c("a"), c("b"), c("c")]);
        let t = app("f", vec![c("a"), c("x"), c("b"), c("c")]);
        let rg = rigid_generalize(s, t);
        assert_eq!(
            canonical(rg.skeleton),
            canonical(app("f", vec![c("a"), v("W"), c("b"), c("c")])),
            "LCS-rigid skeleton must keep the common subsequence a,b,c verbatim"
        );
        assert_eq!(rg.slots.len(), 1, "the one unmatched gap ⇒ exactly one slot");

        // Spine with a gap on EACH side: [a,p,c] vs [a,q,c] — LCS [a,c],
        // middle differs ⇒ one shared gap var; skeleton f(a, V, c).
        let rg2 = rigid_generalize(
            app("f", vec![c("a"), c("p"), c("c")]),
            app("f", vec![c("a"), c("q"), c("c")]),
        );
        assert_eq!(
            canonical(rg2.skeleton),
            canonical(app("f", vec![c("a"), v("V"), c("c")]))
        );
    }

    // ── affine_recurrence: new embedding+rigid path, contract preserved ───

    #[test]
    fn affine_recurrence_embedding_rigid_path() {
        // add(s X, Y, s Z) → add(s(s X), Y, s(s Z)) : prev ⊴ cur (whistle),
        // rigid skeleton shared, slots embedding-progress. Still fires.
        let prev = app("add", vec![app("s", vec![v("X")]), v("Y"), app("s", vec![v("Z")])]);
        let cur = app(
            "add",
            vec![
                app("s", vec![app("s", vec![v("X")])]),
                v("Y"),
                app("s", vec![app("s", vec![v("Z")])]),
            ],
        );
        // The whistle blows on this pair (modulo α).
        assert!(embeds(canonical(prev), canonical(cur)));
        assert!(
            affine_recurrence(prev, cur).is_some(),
            "add-unfold: whistle blows + rigid skeleton ⇒ must still nominate"
        );

        // Negatives still rejected:
        // α-equal ⇒ no progress.
        let prev2 = app("add", vec![app("s", vec![v("A")]), v("B"), app("s", vec![v("Cc")])]);
        assert!(affine_recurrence(prev, prev2).is_none(), "α-equal ⇒ rejected");
        // Unrelated heads ⇒ no embedding ⇒ rejected.
        assert!(affine_recurrence(c("foo"), app("bar", vec![c("baz")])).is_none());
        // Pure rename/swap, no growth ⇒ prev ⋬ cur ⇒ rejected.
        let r1 = app("g", vec![c("a"), v("P")]);
        let r2 = app("g", vec![c("b"), v("Q")]);
        assert!(
            affine_recurrence(r1, r2).is_none(),
            "rename-only: no embedding step ⇒ not accelerable"
        );
        // Whistle gate specifically: cur does NOT embed prev (shrinks) ⇒ none.
        let big = app("s", vec![app("s", vec![v("X")])]);
        let small = app("s", vec![v("X")]);
        assert!(
            affine_recurrence(big, small).is_none(),
            "cur smaller than prev ⇒ no embedding ⇒ rejected"
        );
    }
}
