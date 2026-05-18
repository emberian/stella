//! Σ(Φ) — the first Futamura projection of the resolution interpreter w.r.t.
//! a FIXED constellation Φ (docs/14 design, docs/17 plan). **Σ0: the
//! compiled per-head transition table + its builder, no driver.**
//!
//! Every Φ star is the KAM rewrite shape `[ -P(st(Mn,πn)), +P(st(Mp,πp)) ]`
//! (`galaxy::{delta_star,prim_stars}`, `combinator::machine_stars`). Σ(Φ)
//! reads, once per fixed Φ, a closed [`Transition`] per resolvable head, so
//! a step becomes an O(1) head lookup + one node construction instead of
//! `psi_csyms` + O(|Φ|) scan + α-rename + unify + `theta.apply`.
//!
//! Classification is **structural, not name-heuristic**:
//! * `Mn = a(_,_)` (the Push star)                 → [`Transition::Unwind`]
//! * `Mn = H()` 0-ary atom, `πn` a *bare var* = πp → [`Transition::Delta`]
//!   (a δ-star: `:N ↦ body•`; `body` is closed, the MGU is definitionally
//!   `{π ↦ actual stack}` ⇒ no scan/rename/unify/apply)
//! * `Mn = H()` 0-ary atom, `πn = p1·…·pk·Var` (every frame a var)
//!                                                  → [`Transition::Splice`]
//!   (a combinator: pop `k` frames, instantiate the fixed contractum)
//! * anything else (e.g. `isnil`'s constructor-guarded stars, strict ops
//!   which have NO star and live on `drive_strict`) → **not in the table**;
//!   the future `iex_spec` driver delegates those to the generic/forced
//!   path (the §49.50 boundary stays exactly where docs/08 needs it).
//!
//! Σ(Φ) is a per-step-cost lever (the GraalVM "compiled tier = the
//! specialisation" move). It is sound *by construction* on the
//! δ/Push/combinator skeleton; the future driver is a sibling fast tier
//! gated by the proven `faithfulness::psi_compatible` + reference `iex`
//! oracle with deopt — never reachable from the reference path.

use crate::constellation::{Constellation, Star};
use crate::polarised::{ray_polarity, Polarity};
use crate::term::{get, Sym, SymName, TermData, TermId, Var};
use rustc_hash::{FxHashMap, FxHashSet};

/// A closed, head-keyed transition — the residual of one resolution step
/// specialised to a fixed Φ star.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transition {
    /// δ-star `:N ↦ body•`. Step: focus `:N` with stack π ⇒ `st(body, π)`.
    /// `body` is closed (`term::is_ground`); no scan/rename/unify/apply.
    Delta(TermId),
    /// Push (`a`-head): `a(M,N)⋆π ↦ M⋆(N·π)`. The verbatim KAM unwind rule.
    Unwind,
    /// Combinator: pop `params.len()` `dot`-frames off π, bind them
    /// positionally into `body` (the fixed contractum), continue with the
    /// substituted body on the residual π. `params` are the pattern vars in
    /// stack order; `body` is the `+P` focus term over those vars.
    Splice { params: Vec<Var>, body: TermId },
}

/// The compiled Σ(Φ): one [`Transition`] per specialisable head symbol
/// (keyed by head name; built once per fixed Φ — the partial-evaluation
/// residual). Heads absent from the table are NOT specialised (delegated).
#[derive(Clone, Debug, Default)]
pub struct SpecPhi {
    table: FxHashMap<String, Transition>,
}

/// `+P(st(M,π))` / `-P(st(M,π))` → `(M, π)`, structurally (head name `P`
/// polarity-agnostic; inner `st`/2). `None` if not that shape.
fn unwrap_st(ray: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(s, a) = get(ray) else { return None };
    if s.name.as_str() != "P" && s.name.as_str() != "+P" && s.name.as_str() != "-P" {
        return None;
    }
    if a.len() != 1 {
        return None;
    }
    let TermData::App(s2, a2) = get(a[0]) else { return None };
    if s2.name.as_str() != "st" || a2.len() != 2 {
        return None;
    }
    Some((a2[0], a2[1]))
}

/// If `t` is a `dot`-spine `p1 · p2 · … · pk · TAIL`, return
/// `(vec![p1..pk], TAIL)` with **every frame required to be a `Var`** and
/// `k ≥ 0`. A non-var frame (e.g. `isnil`'s `nil`/`cons _ _` pattern)
/// makes this return `None` for the whole star ⇒ it is not Spliceable.
fn dot_params(mut t: TermId) -> Option<(Vec<Var>, TermId)> {
    let mut params = Vec::new();
    loop {
        match get(t) {
            TermData::App(s, a) if s.name.as_str() == "dot" && a.len() == 2 => {
                match get(a[0]) {
                    TermData::Var(v) => params.push(v),
                    _ => return None, // constructor-guarded frame ⇒ not Splice
                }
                t = a[1];
            }
            _ => return Some((params, t)), // TAIL (the π var)
        }
    }
}

impl SpecPhi {
    /// Build the closed transition table from a fixed Φ. O(|Φ|), once.
    pub fn build(phi: &Constellation) -> Self {
        let mut table: FxHashMap<String, Transition> = FxHashMap::default();
        for star in phi {
            if let Some((head, tr)) = Self::classify(star) {
                // First star wins per head; Φ is deterministic per head in
                // the galaxy/combinator KAM (one rule per resolvable head).
                table.entry(head).or_insert(tr);
            }
        }
        Self { table }
    }

    /// Structurally classify a 2-ray KAM star into `(head_name, Transition)`.
    fn classify(star: &Star) -> Option<(String, Transition)> {
        if star.len() != 2 {
            return None;
        }
        // Pick the negative (pattern) ray and the positive (contractum) ray.
        let (mut neg, mut pos) = (None, None);
        for &r in star {
            match ray_polarity(r) {
                Polarity::Neg => neg = Some(r),
                Polarity::Pos => pos = Some(r),
                Polarity::Neutral => {}
            }
        }
        let (mn, pin) = unwrap_st(neg?)?;
        let (mp, pip) = unwrap_st(pos?)?;

        match get(mn) {
            // Push: focus is an application node a(_,_).
            TermData::App(s, args) if s.name.as_str() == "a" && args.len() == 2 => {
                Some(("a".to_string(), Transition::Unwind))
            }
            // 0-ary atom head H.
            TermData::App(s, args) if args.is_empty() => {
                let head = s.name.as_str().to_string();
                let (params, ntail) = dot_params(pin)?;
                // The negative stack tail and the positive stack must be the
                // same π var (the shared KAM stack) — the structural mark of
                // a faithful KAM rewrite star.
                let (TermData::Var(nv), TermData::Var(pv)) = (get(ntail), get(pip)) else {
                    return None;
                };
                if nv != pv {
                    return None;
                }
                if params.is_empty() {
                    // `-P(st(:N, π)) , +P(st(body, π))` — a δ-star.
                    Some((head, Transition::Delta(mp)))
                } else {
                    // `-P(st(H, p1·…·pk·π)) , +P(st(body, π))` — combinator.
                    Some((head, Transition::Splice { params, body: mp }))
                }
            }
            _ => None,
        }
    }

    /// The transition for a resolvable head, or `None` (⇒ delegate to the
    /// generic/forced path: `isnil`, strict numeric ops, anything unmapped).
    pub fn get(&self, head: &str) -> Option<&Transition> {
        self.table.get(head)
    }

    /// Number of specialised heads (diagnostics/tests).
    pub fn len(&self) -> usize {
        self.table.len()
    }
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }
}

/// Per-Φ-**star** specialisation (the in-loop `iex_spec` driver consults
/// this once per matched Φ-star, precomputed in `IexAccel`): the index of
/// the negative (pattern) ray + the closed [`Transition`], or `None` ⇒
/// delegate to the generic fast path. **Exact same structural
/// classification as [`SpecPhi::build`]** — this just additionally returns
/// *which* ray is the pattern (the realiser must only fire when the Ψ focus
/// matched that ray, i.e. the KAM `+Ψ`-vs-`-Φ-pattern` direction; a Ψ ray
/// matching the Φ *contractum* ray delegates).
pub fn spec_star(star: &Star) -> Option<(usize, Transition)> {
    if star.len() != 2 {
        return None;
    }
    let (mut neg, mut pos, mut neg_idx) = (None, None, 0usize);
    for (k, &r) in star.iter().enumerate() {
        match ray_polarity(r) {
            Polarity::Neg => {
                neg = Some(r);
                neg_idx = k;
            }
            Polarity::Pos => pos = Some(r),
            Polarity::Neutral => {}
        }
    }
    let (mn, pin) = unwrap_st(neg?)?;
    let (mp, pip) = unwrap_st(pos?)?;
    match get(mn) {
        TermData::App(s, args) if s.name.as_str() == "a" && args.len() == 2 => {
            Some((neg_idx, Transition::Unwind))
        }
        TermData::App(s, args) if args.is_empty() => {
            let _ = s;
            let (params, ntail) = dot_params(pin)?;
            let (TermData::Var(nv), TermData::Var(pv)) = (get(ntail), get(pip)) else {
                return None;
            };
            if nv != pv {
                return None;
            }
            if params.is_empty() {
                Some((neg_idx, Transition::Delta(mp)))
            } else {
                Some((neg_idx, Transition::Splice { params, body: mp }))
            }
        }
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Σ(Φ) — the SELECTION-side residual (thesis-audit 04 §2 Gap 2 / docs/14 §2)
//
// `iex_spec` already residualises the *realisation* of a step (`spec_realise`),
// but per-step *redex selection* — `any_match_accel`'s scan over the whole `-P`
// partner bucket of the fixed Φ — is still generic and is now (KS-PROF, the
// `iex_spec` tier) ~98–99 % of the per-step cost (realisation freshen/fuse → 0
// once residualised). `SelPhi` is the partial-evaluation residual of that scan:
// for the fixed Φ it precomputes, keyed on the focus term's *immediate*
// `(head-name, arity)`, whether a Φ pattern ray **provably** matches that focus
// **unconditionally** (independent of the rest of Ψ), so the per-step
// "is this ray a redex?" question collapses from an O(|Φ_{-P}|·matchable_fast)
// scan to one O(1) keyed lookup.
//
// FAITHFULNESS (non-negotiable; the project spine). `SelPhi::decide` is a
// **sound positive-only short-circuit**: it returns `Some(true)` *only* when a
// witness Φ-ray provably matches the focus AND `any_match_accel`'s colour gate
// provably passes — so `any_match_accel(...) == true` necessarily. It NEVER
// returns `Some(false)` and is consulted only as `decide(...) || generic`: a
// `None` falls through to the **unchanged** `any_match_accel`. Hence the
// boolean handed to the selection loop is *bit-for-bit* the one the generic
// scan returns for every ray, in scan order ⇒ the chosen `(i,j)` redex — and
// therefore the entire step stream and step count — is **identical** to
// `iex_fast`. The lever is purely the cost of *deciding* the same boolean.
//
// The unconditional witnesses (proved against `matchable_fast`'s reduction of
// `+P(st(M,π)) ⋈ -P(st(Mn,πn))`, where every KAM Φ star has `πn` a *bare var*
// ⇒ the stack conjunct is vacuously true, so matchability ≡ `M ⋈ Mn`):
//   * **Push** (`Mn = a(v,v)`, fresh vars): any focus `M = a(_,_)` unifies
//     with it regardless of its arguments — `(a, 2)` ⇒ AlwaysMatch.
//   * **δ** (`Mn = :N()` ground 0-ary, `πn` bare var): a focus whose `M` is
//     the 0-ary atom `:N()` unifies (same name, arity 0; the bare-var stack
//     never blocks) — `(name, 0)` ⇒ AlwaysMatch, *iff* Φ has no *other*
//     specialisable rule for `name` that would make the head ambiguous (the
//     `SpecPhi` "one rule per resolvable head" invariant guarantees it).
// **Splice** (`πn = p1·…·pk·var`, k>0) is *stack-arity conditional* (matches
// only if the focus stack has ≥k `dot` frames) ⇒ never an unconditional
// witness ⇒ its heads are deliberately NOT in the table (delegated, exact
// scan). Constructor-guarded patterns (`isnil`) and strict ops likewise never
// enter the table. The colour-gate side-condition is discharged at build time:
// an AlwaysMatch is only installed when the witness Φ-star contributes the
// `+P` positive colour itself ⇒ `(P,Pos) ∈ phi_csyms` ⇒ the gate passes for
// every focus process ray independent of Ψ.
// ─────────────────────────────────────────────────────────────────────────────

/// `+P(st(M,π))` / `-P(st(M,π))` → the polarity head `Sym` (`P`) and the inner
/// focus `M`, structurally. `None` if not a process ray of that exact shape.
fn process_focus(ray: TermId) -> Option<(Sym, TermId)> {
    let TermData::App(p, a) = get(ray) else { return None };
    if p.name.as_str() != "P" && p.name.as_str() != "+P" && p.name.as_str() != "-P" {
        return None;
    }
    if a.len() != 1 {
        return None;
    }
    let TermData::App(s2, a2) = get(a[0]) else { return None };
    if s2.name.as_str() != "st" || a2.len() != 2 {
        return None;
    }
    Some((p, a2[0]))
}

/// The compiled Σ(Φ) **selection** residual: the set of focus
/// `(immediate-head SymName, arity)` keys that **provably, unconditionally**
/// (independent of Ψ) have a matching Φ pattern ray, *and* the positive
/// process-ray colour `Sym` those witnesses carry (the discharged colour-gate
/// side-condition — `any_match_accel` returns early unless the focus colour is
/// in `phi_csyms ∪ psi_csyms`; every AlwaysMatch witness puts it in
/// `phi_csyms`, so the gate passes for any Ψ). Built once per fixed Φ.
#[derive(Clone, Debug, Default)]
pub struct SelPhi {
    /// `(head-name, arity)` of a focus `M` ⇒ AlwaysMatch witness exists.
    always: FxHashSet<(SymName, u32)>,
    /// The `+P` colour syms contributed by the AlwaysMatch witnesses. The
    /// focus ray's own polarity head must be one of these for the residual to
    /// fire (so the colour gate is provably already satisfied). In every KAM
    /// Φ this is the singleton `{+P}`; kept as a set for total generality.
    pos_csyms: FxHashSet<Sym>,
}

impl SelPhi {
    /// Build the closed selection residual from a fixed Φ. O(|Φ|), once.
    ///
    /// Mirrors [`spec_star`]'s classification *exactly* (same `unwrap_st` /
    /// `dot_params` structural tests) so the table can only ever name heads
    /// whose Φ rule the realisation residual also recognises — but admits a
    /// head only for the **π-unconditional** witnesses (Push, δ), never
    /// Splice. A head that has *any* non-AlwaysMatch specialisable rule, or
    /// appears at >1 distinct arity, is removed (forced to the exact scan):
    /// the residual is a sound *positive* over-approximation only when it is
    /// the *unique* unconditional witness for that key.
    pub fn build(phi: &Constellation) -> Self {
        // Provisional witnesses, plus heads we must blacklist because some
        // rule for them is *not* an unconditional match (⇒ key is ambiguous;
        // delegate to the exact scan to stay step-identical).
        let mut cand: FxHashMap<(SymName, u32), Sym> = FxHashMap::default();
        let mut blacklist: FxHashSet<(SymName, u32)> = FxHashSet::default();
        for star in phi {
            if star.len() != 2 {
                continue;
            }
            let (mut neg, mut pos) = (None, None);
            for &r in star {
                match ray_polarity(r) {
                    Polarity::Neg => neg = Some(r),
                    Polarity::Pos => pos = Some(r),
                    Polarity::Neutral => {}
                }
            }
            let (Some(neg), Some(pos)) = (neg, pos) else { continue };
            let (Some((mn, pin)), Some((pos_sym, _))) =
                (unwrap_st(neg), process_focus(pos))
            else {
                continue;
            };
            match get(mn) {
                // Push: `Mn = a(_,_)` (its args are fresh in every KAM Push
                // star) — a focus `a(_,_)` matches unconditionally. Key on
                // the structural shape `(a, 2)`.
                TermData::App(s, args)
                    if s.name.as_str() == "a" && args.len() == 2 =>
                {
                    let key = (s.name, 2u32);
                    cand.entry(key).or_insert(pos_sym);
                }
                // 0-ary atom head H. δ (empty `dot_params`, π a bare var) is
                // the only π-unconditional case; Splice (k>0) is stack-arity
                // conditional ⇒ blacklist its key so it delegates.
                TermData::App(s, args) if args.is_empty() => {
                    let key = (s.name, 0u32);
                    match dot_params(pin) {
                        Some((params, ntail)) => {
                            // Same KAM shared-π structural mark as `spec_star`.
                            let bare_pi = matches!(get(ntail), TermData::Var(_));
                            if params.is_empty() && bare_pi {
                                cand.entry(key).or_insert(pos_sym); // δ
                            } else {
                                blacklist.insert(key); // Splice / odd shape
                            }
                        }
                        None => {
                            blacklist.insert(key); // ctor-guarded ⇒ delegate
                        }
                    }
                }
                _ => {}
            }
        }
        let mut always = FxHashSet::default();
        let mut pos_csyms = FxHashSet::default();
        for (key, psym) in cand {
            if !blacklist.contains(&key) {
                always.insert(key);
                pos_csyms.insert(psym);
            }
        }
        Self { always, pos_csyms }
    }

    /// The sound positive-only selection decision for a Ψ ray `r`.
    ///
    /// `Some(true)`  ⇒ `any_match_accel(r)` is **provably** `true` (a witness
    ///                  Φ pattern matches AND the colour gate passes) — the
    ///                  caller may skip the generic scan for this ray.
    /// `None`        ⇒ no proof; caller MUST run the unchanged
    ///                  `any_match_accel` (Splice / ctor-guarded / strict /
    ///                  var-focus / non-process ray — exactly as before).
    ///
    /// It is *never* `Some(false)`: the residual only ever *replaces a
    /// `true`*, never decides absence. So `decide(r) == Some(true) ||
    /// generic(r)` is bit-identical to `generic(r)` for every `r`.
    #[inline]
    pub fn decide(&self, r: TermId) -> Option<bool> {
        let (pol, m) = process_focus(r)?;
        // Colour-gate side-condition: the focus colour must be one the
        // witnesses already put in `phi_csyms` (then `any_match_accel`'s
        // `phi_csyms.contains` is provably true, so it does not early-return).
        if !self.pos_csyms.contains(&pol) {
            return None;
        }
        let (name, arity) = match get(m) {
            TermData::App(s, args) => (s.name, args.len() as u32),
            // A bare-var focus would match *anything* generically; do not
            // attempt to prove that here — delegate (rare, non-hot).
            TermData::Var(_) => return None,
        };
        if self.always.contains(&(name, arity)) {
            Some(true)
        } else {
            None
        }
    }

    /// Number of unconditional-witness keys (diagnostics/tests).
    pub fn len(&self) -> usize {
        self.always.len()
    }
    pub fn is_empty(&self) -> bool {
        self.always.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pure combinator Φ (no δ): Push + S/B/C/I/T/F. Structural,
    /// hermetic (no external file).
    #[test]
    fn machine_stars_table_is_structurally_correct() {
        let phi = crate::combinator::machine_stars();
        let sp = SpecPhi::build(&phi);
        // Push present as Unwind.
        assert_eq!(sp.get("a"), Some(&Transition::Unwind), "Push → Unwind");
        // Each combinator letter is a Splice with the expected arity (pop).
        for (name, pop) in [("S", 3), ("B", 3), ("C", 3), ("I", 1), ("T", 2), ("F", 2)] {
            match sp.get(name) {
                Some(Transition::Splice { params, body }) => {
                    assert_eq!(params.len(), pop, "{name}: wrong pop");
                    assert!(!params.is_empty() && body.0 != u32::MAX, "{name}: body");
                }
                other => panic!("{name} expected Splice, got {other:?}"),
            }
        }
        // No δ in a pure combinator Φ.
        assert!(
            !sp.table.values().any(|t| matches!(t, Transition::Delta(_))),
            "combinator Φ must have no Delta"
        );
        // A head with no star is absent (delegated).
        assert_eq!(sp.get("nonexistent_head"), None);
    }

    /// Galaxy Φ (if the artifact is present): δ count = #defs, the lazy
    /// prims are Splice, Push is Unwind, isnil/strict are NOT specialised
    /// (delegated — the §49.50 boundary).
    #[test]
    fn galaxy_table_delta_count_and_boundary() {
        const P: &str = "/Users/ember/dev/embershot/src/galaxy.txt";
        let src = match std::fs::read_to_string(P) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("SKIP galaxy_table: {P}: {e}");
                return;
            }
        };
        let g = crate::galaxy::parse(&src).expect("galaxy parses");
        let n_defs = g.defs.len();
        let phi = crate::galaxy::constellation(&g);
        let sp = SpecPhi::build(&phi);

        let n_delta = sp.table.values().filter(|t| matches!(t, Transition::Delta(_))).count();
        assert_eq!(n_delta, n_defs, "one Delta per :N def ({n_defs})");
        assert_eq!(sp.get("a"), Some(&Transition::Unwind), "Push → Unwind");
        for (name, pop) in [("i", 1), ("t", 2), ("f", 2), ("s", 3), ("c", 3), ("b", 3),
                            ("cons", 3), ("car", 1), ("cdr", 1), ("nil", 1)] {
            match sp.get(name) {
                Some(Transition::Splice { params, .. }) => {
                    assert_eq!(params.len(), pop, "{name}: wrong pop")
                }
                other => panic!("galaxy {name} expected Splice, got {other:?}"),
            }
        }
        // isnil is constructor-guarded (value pattern, not a plain var
        // frame) ⇒ deliberately NOT specialised; strict numeric ops have
        // no star at all. Both delegate (the drive_strict / §49.50 path).
        assert_eq!(sp.get("isnil"), None, "isnil must NOT be specialised");
        for op in ["add", "mul", "eq", "lt", "div", "neg"] {
            assert_eq!(sp.get(op), None, "strict {op} must NOT be specialised");
        }
    }

    /// A δ body is closed (`is_ground`) — the invariant that makes the
    /// future Delta step sound with no α-rename/unify.
    #[test]
    fn delta_bodies_are_ground() {
        const P: &str = "/Users/ember/dev/embershot/src/galaxy.txt";
        let Ok(src) = std::fs::read_to_string(P) else {
            eprintln!("SKIP delta_bodies_are_ground: no galaxy.txt");
            return;
        };
        let g = crate::galaxy::parse(&src).unwrap();
        let phi = crate::galaxy::constellation(&g);
        let sp = SpecPhi::build(&phi);
        let mut checked = 0;
        for t in sp.table.values() {
            if let Transition::Delta(b) = t {
                assert!(
                    crate::term::is_ground(*b),
                    "δ body must be closed/ground (no α-rename/unify needed)"
                );
                checked += 1;
            }
        }
        assert!(checked > 100, "expected many δ bodies, got {checked}");
    }

    /// `SelPhi` structural correctness: combinator Φ admits the Push key
    /// `(a,2)` (unconditional) and **excludes every Splice head**
    /// (`S/B/C/I/T/F` — stack-arity conditional ⇒ delegated); galaxy Φ
    /// additionally admits every δ atom key `(:N,0)` and still excludes the
    /// lazy-prim Splice heads + the strict/ctor-guarded ones.
    #[test]
    fn sel_phi_admits_only_unconditional_witnesses() {
        // Combinator: Push only; no Splice head, no spurious atom key.
        let cphi = crate::combinator::machine_stars();
        let csel = SelPhi::build(&cphi);
        let a_name = crate::term::SymName::intern("a");
        assert!(
            csel.always.contains(&(a_name, 2)),
            "combinator: Push key (a,2) must be an unconditional witness"
        );
        for letter in ["S", "B", "C", "I", "T", "F"] {
            let n = crate::term::SymName::intern(letter);
            assert!(
                !csel.always.contains(&(n, 0)),
                "combinator: Splice head {letter} is stack-arity conditional \
                 — MUST be delegated (not in the selection residual)"
            );
        }

        // Galaxy: δ atoms in, Splice/strict/ctor-guarded out.
        const P: &str = "/Users/ember/dev/embershot/src/galaxy.txt";
        let Ok(src) = std::fs::read_to_string(P) else {
            eprintln!("SKIP sel_phi galaxy slice: no galaxy.txt");
            return;
        };
        let g = crate::galaxy::parse(&src).unwrap();
        let phi = crate::galaxy::constellation(&g);
        let sel = SelPhi::build(&phi);
        assert!(
            sel.always.contains(&(a_name, 2)),
            "galaxy: Push key (a,2) must be an unconditional witness"
        );
        // Every named def's :N atom is an unconditional δ witness.
        for d in &g.defs {
            let nm = crate::term::SymName::intern(&format!(":{}", d.name));
            assert!(
                sel.always.contains(&(nm, 0)),
                "galaxy: δ atom :{} must be an unconditional witness",
                d.name
            );
        }
        // Lazy-prim Splice heads + strict ops + isnil are NOT in the table.
        for h in [
            "i", "t", "f", "s", "c", "b", "cons", "car", "cdr", "nil", "isnil",
            "add", "mul", "eq", "lt", "div", "neg",
        ] {
            let n = crate::term::SymName::intern(h);
            assert!(
                !sel.always.contains(&(n, 0)) && !sel.always.contains(&(n, 1))
                    && !sel.always.contains(&(n, 2)) && !sel.always.contains(&(n, 3)),
                "galaxy: {h} is conditional/strict — MUST be delegated"
            );
        }
        assert!(
            sel.len() >= g.defs.len() + 1,
            "galaxy: expected ≥ (#defs + Push) unconditional keys"
        );
    }

    /// THE soundness gate (in-module): over every live Ψ state of a real
    /// galaxy reduction, `SelPhi::decide(r) == Some(true)` ⇒ the generic
    /// `-P`-bucket `matchable_fast` scan also finds a match for `r`. This is
    /// the property that makes the selection short-circuit step-identical:
    /// the residual only ever *replaces a true with a faster true*. (The
    /// end-to-end step-identity + α-equivalence is `iex_spec_result_eq_iex`;
    /// this checks the residual predicate itself, ray by ray, against the
    /// reference `matchable`.)
    #[test]
    fn sel_phi_decide_true_implies_generic_match() {
        use crate::polarised::matchable;
        const P: &str = "/Users/ember/dev/embershot/src/galaxy.txt";
        let Ok(src) = std::fs::read_to_string(P) else {
            eprintln!("SKIP sel_phi soundness: no galaxy.txt");
            return;
        };
        let g = crate::galaxy::parse(&src).unwrap();
        let phi = crate::galaxy::constellation(&g);
        let sel = SelPhi::build(&phi);

        // A bounded forced reduction of the [triple]-style entry (the
        // long δ/Push/Splice force the KS-PROF harness uses), sampling
        // every Ψ at every reference step.
        fn cst(n: &str) -> TermId {
            crate::term::mk_app_str(n, vec![])
        }
        fn ap(f: TermId, x: TermId) -> TermId {
            crate::term::mk_app_str("a", vec![f, x])
        }
        let entry = crate::galaxy::ref_atom(g.entry);
        let click = ap(ap(cst("cons"), crate::binarith::nat(0)), crate::binarith::nat(0));
        let prog = ap(ap(entry, cst("nil")), click);
        let mut psi = crate::galaxy::initial_psi(prog);
        let mut checked_true = 0usize;
        for _ in 0..1500 {
            // Check the residual predicate against the reference scan for
            // EVERY ray of the current Ψ.
            for star in &psi {
                for &r in star {
                    if sel.decide(r) == Some(true) {
                        // Reference: does ANY Φ ray `matchable` with `r`?
                        let any_ref = phi
                            .iter()
                            .flat_map(|s| s.iter())
                            .any(|&q| matchable(r, q));
                        assert!(
                            any_ref,
                            "UNSOUND: SelPhi::decide said Some(true) but the \
                             reference `matchable` scan finds no Φ partner — \
                             the selection residual would change the redex"
                        );
                        checked_true += 1;
                    }
                }
            }
            // Advance one reference step (oracle engine — independent of the
            // residual) to walk realistic Ψ shapes.
            let r = crate::interactive::iex(&phi, psi.clone(), 1);
            if r.is_normal_form {
                break;
            }
            psi = r.psi;
        }
        assert!(
            checked_true > 50,
            "expected the residual to fire on many rays (got {checked_true}) \
             — a vacuous test proves nothing"
        );
    }
}
