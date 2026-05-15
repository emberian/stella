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
//! Returns `None` when the problem is unsolvable (clash or occur-check
//! failure).

use crate::subst::Substitution;
use crate::term::Term;
use std::collections::{HashSet, VecDeque};

/// An equation `lhs =? rhs` in a unification problem (§B.1.9).
///
/// Equations are *unordered* (§B.1.9 says "unordered pair"), but we store
/// them directed for algorithmic convenience; the Orient rule swaps them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Equation {
    pub lhs: Term,
    pub rhs: Term,
}

impl Equation {
    pub fn new(lhs: Term, rhs: Term) -> Self {
        Self { lhs, rhs }
    }
}

/// The compatibility relation `⊂` (§B.1.2, §B.1.3).
///
/// In plain first-order unification `f ⊂ g ⟺ f = g`.  The polarised
/// variant (§48.2) uses a different notion; see [`crate::polarised`].
pub trait Compatible {
    /// Returns `true` iff `c ⊂ d`.
    fn compatible(&self, c: &str, d: &str) -> bool;
}

/// The standard compatibility relation: `f ⊂ g ⟺ f = g` (§B.1.3).
pub struct StdCompat;

impl Compatible for StdCompat {
    fn compatible(&self, c: &str, d: &str) -> bool {
        c == d
    }
}

/// Drive the Martelli-Montanari rewrite system to normal form.
///
/// Returns `Some(θ)` where `θ` is the mgu when the problem is solvable,
/// `None` otherwise.
///
/// The `compat` parameter supplies the compatibility relation `⊂`.
pub fn unify_with<C: Compatible>(
    equations: Vec<Equation>,
    compat: &C,
) -> Option<Substitution> {
    // We work with a deque so we can process equations FIFO and easily push
    // new equations to the front (after decomposition) or back.
    let mut work: VecDeque<Equation> = equations.into();

    // The partial substitution we accumulate.  When Replace fires for X ↦ t,
    // we record it here and apply it to the remaining problem.
    let mut sigma = Substitution::identity();

    'outer: loop {
        // Find the first equation to which a rule applies.
        let mut i = 0;
        while i < work.len() {
            let eq = &work[i];

            // ── Clear (§B.2.1) ───────────────────────────────────────────
            // P ∪ {t =? t} → P
            if eq.lhs == eq.rhs {
                work.remove(i);
                continue 'outer;
            }

            // ── Orient (§B.2.1) ──────────────────────────────────────────
            // P ∪ {t =? X} → P ∪ {X =? t}   when t is not a variable
            if !eq.lhs.is_var() && eq.rhs.is_var() {
                let eq = work.remove(i).unwrap();
                work.insert(i, Equation::new(eq.rhs, eq.lhs));
                continue 'outer;
            }

            // ── Replace (§B.2.1) ─────────────────────────────────────────
            // P ∪ {X =? t} → {X↦t}P ∪ {X =? t}
            //   when X ∈ vars(P) and X ∉ vars(t)  (the X ∉ vars(t) IS the occur check)
            if let Term::Var(ref x) = eq.lhs.clone() {
                let t = eq.rhs.clone();
                let t_vars = t.vars();

                // Occur check: if X ∈ vars(t) and lhs ≠ rhs, fail.
                if t_vars.contains(x) {
                    // lhs = rhs was already handled by Clear; here lhs ≠ rhs.
                    return None;
                }

                // Check whether X appears in any *other* equation.
                let x_in_p = work.iter().enumerate().any(|(j, e)| {
                    j != i && (e.lhs.vars().contains(x) || e.rhs.vars().contains(x))
                });

                if x_in_p {
                    // Apply the substitution {X ↦ t} to all other equations.
                    let binding = Substitution::from_pairs([(x.clone(), t.clone())]);
                    for (j, e) in work.iter_mut().enumerate() {
                        if j != i {
                            e.lhs = binding.apply(&e.lhs);
                            e.rhs = binding.apply(&e.rhs);
                        }
                    }
                    // Accumulate into sigma: new_sigma = binding ∘ sigma
                    sigma = Substitution::compose(&binding, &sigma);
                    // Also apply binding to sigma's existing range values.
                    // (compose already handles this via the theta1.apply(theta2_val) step)
                    continue 'outer;
                }
            }

            // ── Open (§B.2.1) ────────────────────────────────────────────
            // P ∪ {f(t₁..tₙ) =? g(u₁..uₙ)} → P ∪ {t₁=?u₁,…,tₙ=?uₙ}
            //   when f ⊂ g
            if let (Term::App(f, ts), Term::App(g, us)) = (eq.lhs.clone(), eq.rhs.clone()) {
                if !compat.compatible(&f, &g) {
                    // Clash (§B.2.3 termination: unsuccessful).
                    return None;
                }
                if ts.len() != us.len() {
                    // Arity mismatch: also a clash.
                    return None;
                }
                work.remove(i);
                // Push decomposed equations at position i (preserve order).
                for (t, u) in ts.into_iter().zip(us).rev() {
                    work.insert(i, Equation::new(t, u));
                }
                continue 'outer;
            }

            i += 1;
        }

        // No rule applied: either solved form or unsolvable.
        break;
    }

    // Check that we reached a solved form (§B.1.23):
    // - every lhs is a distinct variable
    // - no lhs variable appears in any rhs
    let mut seen_vars: HashSet<String> = HashSet::new();
    let mut rhs_vars: HashSet<String> = HashSet::new();
    for eq in &work {
        match &eq.lhs {
            Term::Var(x) => {
                if !seen_vars.insert(x.clone()) {
                    // Duplicate lhs variable: not solved form (shouldn't
                    // happen after full Replace, but guard anyway).
                    return None;
                }
            }
            _ => {
                // lhs is not a variable: not solved form ⟹ unsolvable.
                return None;
            }
        }
        rhs_vars.extend(eq.rhs.vars());
    }
    for x in &seen_vars {
        if rhs_vars.contains(x) {
            return None;
        }
    }

    // Build the final substitution from the solved form + accumulated sigma.
    let solved_subst = Substitution::from_pairs(
        work.into_iter()
            .map(|eq| match eq.lhs {
                Term::Var(x) => (x, eq.rhs),
                _ => unreachable!(),
            }),
    );

    // The mgu is: apply solved_subst on top of sigma.
    // Because sigma may contain variables that solved_subst further instantiates,
    // we compose: result(x) = solved_subst(sigma(x)).
    Some(Substitution::compose(&solved_subst, &sigma))
}

/// Plain first-order unification using standard compatibility `f ⊂ g ⟺ f = g`
/// (§B.1.3, §B.2.1).
pub fn unify(equations: Vec<Equation>) -> Option<Substitution> {
    unify_with(equations, &StdCompat)
}
