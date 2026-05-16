//! α-unification.
//!
//! Eng §B.1.11–§B.1.19.  Implements §B.1.19: rename the two terms to
//! disjoint variable sets, then attempt plain unification.

use crate::subst::{freshen, Substitution};
use crate::term::TermId;
use crate::unify::{unify_with, Compatible, Equation};

/// α-unify two terms using a given compatibility relation (§B.1.19).
pub fn alpha_unify_with<C: Compatible>(t1: TermId, t2: TermId, compat: &C) -> Option<Substitution> {
    let mut counter = 0u32;
    let (renamed1, _alpha1) = freshen(t1, "a", &mut counter);
    let (renamed2, _alpha2) = freshen(t2, "b", &mut counter);

    debug_assert!(
        renamed1.vars().is_disjoint(&renamed2.vars()),
        "freshen produced overlapping variable sets"
    );

    unify_with(vec![Equation::new(renamed1, renamed2)], compat)
}

/// α-unify two terms under the standard compatibility relation `f ⊂ g ⟺ f = g`.
pub fn alpha_unify(t1: TermId, t2: TermId) -> Option<Substitution> {
    use crate::unify::StdCompat;
    alpha_unify_with(t1, t2, &StdCompat)
}
