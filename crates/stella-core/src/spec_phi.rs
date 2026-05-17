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
use crate::term::{get, TermData, TermId, Var};
use rustc_hash::FxHashMap;

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
}
