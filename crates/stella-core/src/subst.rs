//! Substitutions and renamings.
//!
//! Eng §B.1.7: A *substitution* is a function `θ : V → Term(S)` extended
//! homomorphically to terms:
//!
//! ```text
//! θ(X)          = θ(X)            (look up, default: identity)
//! θ(f(u₁,…,uₖ)) = f(θ(u₁),…,θ(uₖ))
//! ```
//!
//! Composition is defined so that `(θ₁ ∘ θ₂)(t) = θ₁(θ₂(t))`.
//!
//! A *renaming* is a bijective substitution `α` with `α(X) ∈ V` for all `X`.
//! Its inverse `α⁻¹` is well-defined.

use crate::term::Term;
use std::collections::HashMap;

/// A substitution `θ : V → Term(S)` (§B.1.7).
///
/// Variables not in the map are mapped to themselves (identity on free
/// variables).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Substitution(pub HashMap<String, Term>);

impl Substitution {
    /// The identity substitution (empty map).
    pub fn identity() -> Self {
        Self(HashMap::new())
    }

    /// Build a substitution from a list of `(variable, term)` pairs.
    pub fn from_pairs(pairs: impl IntoIterator<Item = (String, Term)>) -> Self {
        Self(pairs.into_iter().collect())
    }

    /// Apply `θ` to a term (§B.1.7).
    pub fn apply(&self, t: &Term) -> Term {
        match t {
            Term::Var(x) => self.0.get(x).cloned().unwrap_or_else(|| t.clone()),
            Term::App(f, args) => {
                Term::App(f.clone(), args.iter().map(|a| self.apply(a)).collect())
            }
        }
    }

    /// Composition `θ₁ ∘ θ₂` such that `(θ₁ ∘ θ₂)(t) = θ₁(θ₂(t))` (§B.1.7).
    ///
    /// The composition is: for each variable `x`, the result maps `x` to
    /// `θ₁(θ₂(x))`.  Any variable in `θ₁` but not `θ₂` maps to `θ₁(x)`.
    pub fn compose(theta1: &Self, theta2: &Self) -> Self {
        let mut map: HashMap<String, Term> = HashMap::new();
        // Apply theta1 to all values of theta2.
        for (x, t) in &theta2.0 {
            let result = theta1.apply(t);
            // Drop identity mappings.
            if result != Term::Var(x.clone()) {
                map.insert(x.clone(), result);
            }
        }
        // Include bindings from theta1 whose domain variable is not in theta2.
        for (x, t) in &theta1.0 {
            if !theta2.0.contains_key(x) {
                map.insert(x.clone(), t.clone());
            }
        }
        Self(map)
    }

    /// Insert or overwrite a single binding.
    pub fn bind(&mut self, var: String, term: Term) {
        self.0.insert(var, term);
    }
}

/// A renaming is a bijective substitution `α` with `α(X) ∈ V` (§B.1.7).
///
/// Internally stored as a forward map `V → V`; the inverse is computed on
/// demand.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Renaming(pub HashMap<String, String>);

impl Renaming {
    /// Build from an explicit map.
    pub fn from_map(map: HashMap<String, String>) -> Self {
        Self(map)
    }

    /// Lift to a `Substitution`.
    pub fn to_substitution(&self) -> Substitution {
        Substitution(
            self.0
                .iter()
                .map(|(k, v)| (k.clone(), Term::Var(v.clone())))
                .collect(),
        )
    }

    /// Apply the renaming to a term.
    pub fn apply(&self, t: &Term) -> Term {
        self.to_substitution().apply(t)
    }

    /// Compute the inverse renaming `α⁻¹` (§B.1.7).
    ///
    /// Panics in debug mode if the map is not injective (i.e. not a bijection).
    pub fn inverse(&self) -> Self {
        let mut inv = HashMap::new();
        for (k, v) in &self.0 {
            debug_assert!(
                !inv.contains_key(v),
                "renaming is not injective: {v} has two preimages"
            );
            inv.insert(v.clone(), k.clone());
        }
        Self(inv)
    }

    /// Compose two renamings: `(α₁ ∘ α₂)(x) = α₁(α₂(x))`.
    pub fn compose(alpha1: &Self, alpha2: &Self) -> Self {
        let mut map = HashMap::new();
        for (x, y) in &alpha2.0 {
            let z = alpha1.0.get(y).cloned().unwrap_or_else(|| y.clone());
            if z != *x {
                map.insert(x.clone(), z);
            }
        }
        for (x, z) in &alpha1.0 {
            if !alpha2.0.contains_key(x) {
                map.insert(x.clone(), z.clone());
            }
        }
        Self(map)
    }
}

/// Generate a fresh variable name with a given prefix and counter.
pub fn fresh_var(prefix: &str, counter: &mut u32) -> String {
    let name = format!("{prefix}{counter}");
    *counter += 1;
    name
}

/// Rename all variables in `t` to fresh names, returning the renamed term and
/// the renaming used.  Used for producing variable-disjoint copies (§B.1.19).
pub fn freshen(t: &Term, prefix: &str, counter: &mut u32) -> (Term, Renaming) {
    let vars: Vec<String> = t.vars().into_iter().collect();
    let mut map = HashMap::new();
    for v in vars {
        let fresh = fresh_var(prefix, counter);
        map.insert(v, fresh);
    }
    let renaming = Renaming::from_map(map);
    (renaming.apply(t), renaming)
}
