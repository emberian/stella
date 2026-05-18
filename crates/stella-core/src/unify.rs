//! Martelli-Montanari unification algorithm.
//!
//! Eng §B.2.1 defines the algorithm as four rewrite rules over a *unification
//! problem* — a multiset of unordered equations `t =? u`.  The rules are:
//!
//! - **Clear**   `P ∪ {t =? t}  →  P`
//! - **Open**    `P ∪ {f(t₁..tₙ) =? g(u₁..uₙ)}  →  P ∪ {t₁=?u₁,…,tₙ=?uₙ}`
//!               when `f ⊂ g` (compatibility); for plain unification `f ⊂ g ⟺ f = g`
//!               and arities must agree.
//! - **Orient**  `P ∪ {t =? X}  →  P ∪ {X =? t}` when `t ∉ vars(·)` (not a var)
//! - **Replace** `P ∪ {X =? t}  →  {X↦t}P ∪ {X =? t}`
//!               when `X ∈ vars(P)` and `X ∉ vars(t)`  (occur check)
//!
//! A *solved form* (§B.1.23) is a problem where every equation is `Xᵢ =? tᵢ`
//! with distinct `Xᵢ` none of which appears in any `tⱼ`.  The underlying
//! substitution is then the most general unifier (unique up to α, §B.2.6).
//!
//! Returns `None` when the problem is unsolvable (clash or occur-check failure).

use rustc_hash::FxHashSet;
use std::collections::VecDeque;

use crate::subst::Substitution;
use crate::term::{get, Sym, TermData, TermId, Var};

/// An equation `lhs =? rhs` in a unification problem (§B.1.9).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Equation {
    pub lhs: TermId,
    pub rhs: TermId,
}

impl Equation {
    pub fn new(lhs: TermId, rhs: TermId) -> Self {
        Self { lhs, rhs }
    }
}

/// The compatibility relation `⊂` (§B.1.2, §B.1.3).
///
/// Now operates on `Sym` (interned name + polarity), not raw strings.
pub trait Compatible {
    /// Returns `true` iff `c ⊂ d`.
    fn compatible(&self, c: Sym, d: Sym) -> bool;
}

/// The standard compatibility relation: `f ⊂ g ⟺ f = g` (§B.1.3).
pub struct StdCompat;

impl Compatible for StdCompat {
    fn compatible(&self, c: Sym, d: Sym) -> bool {
        c == d
    }
}

/// Drive the Martelli-Montanari rewrite system to normal form.
///
/// Returns `Some(θ)` where `θ` is the mgu when the problem is solvable,
/// `None` otherwise.
///
/// The `compat` parameter supplies the compatibility relation `⊂`.
pub fn unify_with<C: Compatible>(equations: Vec<Equation>, compat: &C) -> Option<Substitution> {
    let mut work: VecDeque<Equation> = equations.into();
    let mut sigma = Substitution::identity();

    'outer: loop {
        let mut i = 0;
        while i < work.len() {
            let eq = &work[i];

            // ── Clear ────────────────────────────────────────────────────────
            if eq.lhs == eq.rhs {
                work.remove(i);
                continue 'outer;
            }

            // ── Orient ───────────────────────────────────────────────────────
            if !eq.lhs.is_var() && eq.rhs.is_var() {
                let eq = work.remove(i).unwrap();
                work.insert(i, Equation::new(eq.rhs, eq.lhs));
                continue 'outer;
            }

            // ── Replace ──────────────────────────────────────────────────────
            if let TermData::Var(x) = get(eq.lhs) {
                let t = eq.rhs;
                let t_vars = t.vars();

                // Occur check.
                if t_vars.contains(&x) {
                    return None;
                }

                // Check whether x appears in any other equation.
                let x_in_p = work.iter().enumerate().any(|(j, e)| {
                    j != i
                        && (e.lhs.vars().contains(&x) || e.rhs.vars().contains(&x))
                });

                if x_in_p {
                    let binding = Substitution::from_var_pairs([(x, t)]);
                    for (j, e) in work.iter_mut().enumerate() {
                        if j != i {
                            e.lhs = binding.apply(e.lhs);
                            e.rhs = binding.apply(e.rhs);
                        }
                    }
                    sigma = Substitution::compose(&binding, &sigma);
                    continue 'outer;
                }
            }

            // ── Open ─────────────────────────────────────────────────────────
            if let (TermData::App(f, ts), TermData::App(g, us)) = (get(eq.lhs), get(eq.rhs)) {
                if !compat.compatible(f, g) {
                    return None;
                }
                if ts.len() != us.len() {
                    return None;
                }
                let pairs: Vec<Equation> = ts
                    .iter()
                    .zip(us.iter())
                    .map(|(&t, &u)| Equation::new(t, u))
                    .collect();
                work.remove(i);
                for eq in pairs.into_iter().rev() {
                    work.insert(i, eq);
                }
                continue 'outer;
            }

            i += 1;
        }

        break;
    }

    // Check solved form (§B.1.23).
    let mut seen_vars: FxHashSet<Var> = FxHashSet::default();
    let mut rhs_vars: FxHashSet<Var> = FxHashSet::default();
    for eq in &work {
        match get(eq.lhs) {
            TermData::Var(x) => {
                if !seen_vars.insert(x) {
                    return None;
                }
            }
            _ => return None,
        }
        rhs_vars.extend(eq.rhs.vars());
    }
    for x in &seen_vars {
        if rhs_vars.contains(x) {
            return None;
        }
    }

    // Build the final substitution from the solved form + accumulated sigma.
    let solved_subst = Substitution::from_var_pairs(
        work.into_iter().map(|eq| match get(eq.lhs) {
            TermData::Var(x) => (x, eq.rhs),
            _ => unreachable!(),
        }),
    );

    Some(Substitution::compose(&solved_subst, &sigma))
}

/// Plain first-order unification using standard compatibility `f ⊂ g ⟺ f = g`.
pub fn unify(equations: Vec<Equation>) -> Option<Substitution> {
    unify_with(equations, &StdCompat)
}
