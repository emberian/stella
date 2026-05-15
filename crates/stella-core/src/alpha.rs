//! α-unification.
//!
//! Eng §B.1.11: Two terms `t` and `u` are *α-equivalent* (`t ≈_α u`) if
//! there is a renaming `α` with `t = α(u)`.
//!
//! §B.1.12: An *α-unifier* for `{t₁ =? t₂}` is a pair `(θ, α)` where `θ` is
//! a substitution and `α` is a renaming such that `θ` is a solution for
//! `{t₁ =? α t₂}`.  Two terms are *α-unifiable* if such a pair exists.
//!
//! §B.1.19 (Proposition): `t₁` and `t₂` are α-unifiable iff there exist
//! renamings `α₁, α₂` such that:
//! 1. `α₁ t₁` and `α₂ t₂` are (plainly) unifiable, and
//! 2. `vars(α₁ t₁) ∩ vars(α₂ t₂) = ∅`.
//!
//! We implement the constructive direction of §B.1.19: rename the two terms
//! to make their variable sets disjoint, then attempt plain unification.  This
//! is the standard approach and Eng's proposition guarantees it is equivalent
//! to the definition.

use crate::subst::{freshen, Substitution};
use crate::term::Term;
use crate::unify::{unify_with, Compatible, Equation};

/// α-unify two terms using a given compatibility relation.
///
/// Implements §B.1.19: rename `t1` and `t2` to disjoint variable sets, then
/// run unification.  Returns the mgu on the renamed terms if one exists.
pub fn alpha_unify_with<C: Compatible>(t1: &Term, t2: &Term, compat: &C) -> Option<Substitution> {
    let mut counter = 0u32;

    // Rename t1 with prefix "a" so its variables are fresh.
    let (renamed1, _alpha1) = freshen(t1, "a", &mut counter);
    // Rename t2 with prefix "b" so its variables are fresh and disjoint from t1's.
    let (renamed2, _alpha2) = freshen(t2, "b", &mut counter);

    // Disjointness guaranteed by distinct prefixes + monotone counter.
    debug_assert!(
        renamed1.vars().is_disjoint(&renamed2.vars()),
        "freshen produced overlapping variable sets"
    );

    let eqs = vec![Equation::new(renamed1, renamed2)];
    unify_with(eqs, compat)
}

/// α-unify two terms under the standard compatibility relation `f ⊂ g ⟺ f = g`.
pub fn alpha_unify(t1: &Term, t2: &Term) -> Option<Substitution> {
    use crate::unify::StdCompat;
    alpha_unify_with(t1, t2, &StdCompat)
}
