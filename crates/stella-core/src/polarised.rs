//! Polarised signatures and rays (Eng §48.2–§48.7, §49.7).
//!
//! A *polarised signature* `P = (V, F, ar, ⊂, |·|)` partitions `F` into
//! `F₊ ⊎ F₋ ⊎ F₀`.  `Sym { name, pol }` in `term.rs` IS the polarised symbol;
//! no separate string-prefix scanning needed in hot paths.
//!
//! §48.7: A *ray* is a term in `Term(P)`.  `Ray = TermId`.
//!
//! §49.7: Two rays are *matchable* (`r ⋈ r′`) when they are α-unifiable
//! under the polarised compatibility relation.

pub use crate::term::{Polarity, Sym, TermId};
pub type Ray = TermId;

use crate::alpha::alpha_unify_with;
use crate::term::{get, mk_app, mk_app_str, mk_var, TermData};
use crate::unify::Compatible;

// ─────────────────────────────────────────────────────────────────────────────
// Re-export Polarity for compatibility with call sites
// ─────────────────────────────────────────────────────────────────────────────

// (Already `pub use`d above via `crate::term::Polarity`.)

// ─────────────────────────────────────────────────────────────────────────────
// PolarisedSymbol — compatibility shim (keeps call sites using old names green)
// ─────────────────────────────────────────────────────────────────────────────

/// A function symbol in a polarised signature (§48.2). Thin newtype over `Sym`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PolarisedSymbol {
    pub polarity: Polarity,
    pub neutral: String,
}

impl PolarisedSymbol {
    pub fn positive(neutral: impl Into<String>) -> Self {
        Self { polarity: Polarity::Pos, neutral: neutral.into() }
    }
    pub fn negative(neutral: impl Into<String>) -> Self {
        Self { polarity: Polarity::Neg, neutral: neutral.into() }
    }
    pub fn neutral(name: impl Into<String>) -> Self {
        Self { polarity: Polarity::Neutral, neutral: name.into() }
    }

    pub fn name(&self) -> String {
        match self.polarity {
            Polarity::Pos => format!("+{}", self.neutral),
            Polarity::Neg => format!("-{}", self.neutral),
            Polarity::Neutral => self.neutral.clone(),
        }
    }

    pub fn opposite(&self) -> Self {
        match self.polarity {
            Polarity::Neutral => self.clone(),
            Polarity::Pos => Self::negative(self.neutral.clone()),
            Polarity::Neg => Self::positive(self.neutral.clone()),
        }
    }
}

impl std::fmt::Display for PolarisedSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Parse a symbol name string into a `PolarisedSymbol`.
///
/// NOTE: this is now only used by legacy call sites (e.g. `viz.rs` DOT label
/// generation).  Hot paths use `Sym` directly.
pub fn parse_symbol(s: &str) -> PolarisedSymbol {
    if let Some(rest) = s.strip_prefix('+') {
        PolarisedSymbol::positive(rest)
    } else if let Some(rest) = s.strip_prefix('-') {
        PolarisedSymbol::negative(rest)
    } else {
        PolarisedSymbol::neutral(s)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// PolarisedCompat — the ⊂ relation on Sym (§48.2)
// ─────────────────────────────────────────────────────────────────────────────

/// The *polarised compatibility relation* `⊂` (§48.2):
///
/// ```text
/// c ⊂ d  ⟺  |c| = |d|  AND  (opposite polarities, or both neutral)
/// ```
///
/// Now operates on `Sym` (u32 name + enum polarity) — no string scanning.
pub struct PolarisedCompat;

impl Compatible for PolarisedCompat {
    fn compatible(&self, c: Sym, d: Sym) -> bool {
        // Same underlying neutral symbol?
        if c.name != d.name {
            return false;
        }
        // Polarity condition (§48.2).
        matches!(
            (c.pol, d.pol),
            (Polarity::Pos, Polarity::Neg)
                | (Polarity::Neg, Polarity::Pos)
                | (Polarity::Neutral, Polarity::Neutral)
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// underlying_term |·| (§48.7)
// ─────────────────────────────────────────────────────────────────────────────

/// The **underlying-term operator** `|·|` (§48.7):
///
/// - `|X| = X` (variable, unchanged)
/// - `|f(r₁,…,rₙ)| = |f|(|r₁|,…,|rₙ|)` where `|f|` is the neutral version
///
/// Strips polarity prefix recursively.
pub fn underlying_term(ray: Ray) -> Ray {
    match get(ray) {
        TermData::Var(_) => ray,
        TermData::App(sym, args) => {
            let neutral_sym = Sym::new(sym.name, Polarity::Neutral);
            let new_args: Vec<Ray> = args.iter().map(|&a| underlying_term(a)).collect();
            mk_app(neutral_sym, new_args)
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ray_polarity helper
// ─────────────────────────────────────────────────────────────────────────────

/// Extract the polarity of a ray's head symbol.
///
/// Variables are treated as neutral (no polarity).
pub fn ray_polarity(r: Ray) -> Polarity {
    match get(r) {
        TermData::Var(_) => Polarity::Neutral,
        TermData::App(sym, _) => sym.pol,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Ray constructors
// ─────────────────────────────────────────────────────────────────────────────

/// Build a ray `+sym(args)`.
pub fn pos_ray(neutral: &str, args: Vec<Ray>) -> Ray {
    mk_app_str(&format!("+{neutral}"), args)
}

/// Build a ray `−sym(args)`.
pub fn neg_ray(neutral: &str, args: Vec<Ray>) -> Ray {
    mk_app_str(&format!("-{neutral}"), args)
}

// ─────────────────────────────────────────────────────────────────────────────
// matchable ⋈ (§49.7)
// ─────────────────────────────────────────────────────────────────────────────

/// Matchability `r ⋈ r′` (§49.7).
///
/// Two rays are *dual* / *matchable* when they are α-unifiable under
/// the *polarised* compatibility relation `⊂` (§48.2).
///
/// Pre-check guards against Clear short-circuiting for ground rays (§49.8
/// anti-reflexivity).
pub fn matchable(r: Ray, r_prime: Ray) -> bool {
    match (get(r), get(r_prime)) {
        (TermData::App(f, _), TermData::App(g, _)) => {
            if !PolarisedCompat.compatible(f, g) {
                return false;
            }
        }
        _ => return false,
    }
    alpha_unify_with(r, r_prime, &PolarisedCompat).is_some()
}

// ─────────────────────────────────────────────────────────────────────────────
// matchable_fast — substitution-free boolean equivalent of `matchable` (KS B1)
//
// `matchable` decides only a yes/no, yet `alpha_unify_with` rebuilds BOTH terms
// via `freshen` (new nodes through the global term store + interned names) and
// runs full Martelli–Montanari building an mgu it discards — proven ~95 % of
// the engine's `find` cost. `matchable_fast` decides the *same boolean* with a
// recursive unifiability check over a `(Side, Var)` binding env: the two rays'
// variables live in disjoint side-tagged namespaces (≡ `alpha_unify_with`'s
// freshen), no term rebuild, no interning, allocation bounded by #bound vars.
//
// Rule-for-rule equivalent to `unify_with` + α-disjointness: var-bind with
// occurs-check (≡ Replace+occur), App ⇒ `compat.compatible` + equal arity +
// pairwise (≡ Open), identical side+var (≡ Clear), symmetric (≡ Orient).
// Gated by the differential fuzz `matchable_fast ≡ matchable` (tests) **and**
// the N-KS byte-identity gate; `matchable` stays the reference oracle.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Side {
    L,
    R,
}

type SideTerm = (Side, TermId);
type MfEnv = rustc_hash::FxHashMap<(Side, crate::term::Var), SideTerm>;

fn mf_walk(mut s: Side, mut t: TermId, env: &MfEnv) -> SideTerm {
    while let TermData::Var(v) = get(t) {
        match env.get(&(s, v)) {
            Some(&(s2, t2)) => {
                s = s2;
                t = t2;
            }
            None => break,
        }
    }
    (s, t)
}

fn mf_occurs(s: Side, v: crate::term::Var, ts: Side, tt: TermId, env: &MfEnv) -> bool {
    let (rs, rt) = mf_walk(ts, tt, env);
    match get(rt) {
        TermData::Var(w) => rs == s && w == v,
        TermData::App(_, args) => args.iter().any(|&a| mf_occurs(s, v, rs, a, env)),
    }
}

fn mf_unify(sa: Side, a: TermId, sb: Side, b: TermId, env: &mut MfEnv) -> bool {
    let (sa, a) = mf_walk(sa, a, env);
    let (sb, b) = mf_walk(sb, b, env);
    match (get(a), get(b)) {
        (TermData::Var(x), TermData::Var(y)) if sa == sb && x == y => true,
        (TermData::Var(x), _) => {
            if mf_occurs(sa, x, sb, b, env) {
                return false;
            }
            env.insert((sa, x), (sb, b));
            true
        }
        (_, TermData::Var(y)) => {
            if mf_occurs(sb, y, sa, a, env) {
                return false;
            }
            env.insert((sb, y), (sa, a));
            true
        }
        (TermData::App(f, fa), TermData::App(g, ga)) => {
            if !PolarisedCompat.compatible(f, g) || fa.len() != ga.len() {
                return false;
            }
            fa.iter()
                .zip(ga.iter())
                .all(|(&x, &y)| mf_unify(sa, x, sb, y, env))
        }
        _ => false,
    }
}

/// Substitution-free boolean equivalent of [`matchable`] (see section header).
pub fn matchable_fast(r: Ray, r_prime: Ray) -> bool {
    match (get(r), get(r_prime)) {
        (TermData::App(f, _), TermData::App(g, _)) => {
            if !PolarisedCompat.compatible(f, g) {
                return false;
            }
        }
        _ => return false,
    }
    let mut env: MfEnv = rustc_hash::FxHashMap::default();
    mf_unify(Side::L, r, Side::R, r_prime, &mut env)
}

#[cfg(test)]
mod matchable_fast_tests {
    use super::*;
    use crate::term::{mk_app_str, mk_var};

    /// Deterministic LCG — reproducible fuzz, no dev-deps.
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

    /// Random term: variable names are deliberately SHARED across the two rays
    /// (`X`/`Y`/`Z`) to stress α-disjointness — the exact thing the `(Side,Var)`
    /// namespacing must get right vs `alpha_unify_with`'s freshen.
    fn gen(rng: &mut Lcg, depth: u32) -> TermId {
        if depth == 0 || rng.next() % 3 == 0 {
            return *rng.pick(&[mk_var("X"), mk_var("Y"), mk_var("Z")]);
        }
        let head = *rng.pick(&["f", "g", "h"]); // neutral inner functors
        let ar = (rng.next() % 3) as usize; // 0..2
        let args: Vec<TermId> = (0..ar).map(|_| gen(rng, depth - 1)).collect();
        mk_app_str(head, args)
    }

    /// Top-level polarised ray (matchable requires App heads).
    fn gen_ray(rng: &mut Lcg) -> TermId {
        let head = *rng.pick(&["+p", "-p", "+q", "-q", "p", "q"]);
        let ar = 1 + (rng.next() % 3) as usize; // 1..3
        let args: Vec<TermId> = (0..ar).map(|_| gen(rng, 3)).collect();
        mk_app_str(head, args)
    }

    /// **B1 faithfulness gate**: `matchable_fast ≡ matchable` over a broad
    /// fuzz, including var-sharing across rays, nesting, and all polarity
    /// combinations. Any disagreement ⇒ B1 is unfaithful and must be reverted.
    #[test]
    fn matchable_fast_equiv_matchable_fuzz() {
        let mut rng = Lcg(0x5314_2718_2845_9045);
        let mut checked = 0u32;
        for _ in 0..20_000 {
            let a = gen_ray(&mut rng);
            let b = gen_ray(&mut rng);
            assert_eq!(
                matchable_fast(a, b),
                matchable(a, b),
                "matchable_fast disagrees with matchable on ({a:?}, {b:?})"
            );
            checked += 1;
        }
        assert_eq!(checked, 20_000);
    }

    /// Targeted: shared var must NOT couple across rays (α-disjointness).
    /// `+p(X)` vs `-p(g(X))`: with disjoint namespaces this unifies
    /// (Xᴸ ↦ g(Xᴿ)); a naive shared-var unifier would wrongly occurs-fail.
    #[test]
    fn shared_var_is_alpha_disjoint() {
        let a = mk_app_str("+p", vec![mk_var("X")]);
        let b = mk_app_str("-p", vec![mk_app_str("g", vec![mk_var("X")])]);
        assert_eq!(matchable_fast(a, b), matchable(a, b));
        assert!(matchable_fast(a, b), "α-disjoint: +p(Xᴸ) ⋈ -p(g(Xᴿ))");
    }
}
