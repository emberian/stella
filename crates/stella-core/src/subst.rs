//! Substitutions and renamings over hash-consed terms.
//!
//! Eng §B.1.7: A *substitution* is a function `θ : V → Term(S)` extended
//! homomorphically to terms.
//!
//! Keys are interned `Var` (u32), not `String`.  Values are `TermId`.
//! `Renaming` maps `Var → Var`.  `FxHashMap` replaces `std::HashMap`.

use rustc_hash::FxHashMap;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::term::{get, mk_app_interned, mk_var_interned, TermData, TermId, Var};

// ─────────────────────────────────────────────────────────────────────────────
// Substitution: Var → TermId
// ─────────────────────────────────────────────────────────────────────────────

/// A substitution `θ : V → Term(S)` (§B.1.7).
///
/// Variables not in the map are mapped to themselves (identity on free variables).
/// Keyed on interned `Var` (u32 compare, no string allocation).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Substitution(pub FxHashMap<Var, TermId>);

impl Substitution {
    /// The identity substitution (empty map).
    pub fn identity() -> Self {
        Self(FxHashMap::default())
    }

    /// Build from `(variable_name_str, TermId)` pairs.
    pub fn from_pairs(pairs: impl IntoIterator<Item = (String, TermId)>) -> Self {
        Self(
            pairs
                .into_iter()
                .map(|(s, t)| (Var::intern(&s), t))
                .collect(),
        )
    }

    /// Build from `(Var, TermId)` pairs.
    pub fn from_var_pairs(pairs: impl IntoIterator<Item = (Var, TermId)>) -> Self {
        Self(pairs.into_iter().collect())
    }

    /// Apply `θ` to a term (§B.1.7).
    pub fn apply(&self, id: TermId) -> TermId {
        // A variable-free term is unaffected by any θ — return it in O(1)
        // instead of re-walking/​rebuilding it. Galaxy δ-bodies are huge
        // ground terms fused on every step; this is the dominant `fuse`
        // cost (KS-PROF: fuse ≈ 82% at Φ=405). Behaviour-identical.
        if crate::term::is_ground(id) {
            return id;
        }
        match get(id) {
            TermData::Var(v) => self.0.get(&v).copied().unwrap_or(id),
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args.iter().map(|&a| self.apply(a)).collect();
                // Only allocate a new node if args actually changed.
                if new_args == args.as_ref() {
                    id
                } else {
                    mk_app_interned(sym, new_args)
                }
            }
        }
    }

    /// Composition `θ₁ ∘ θ₂` such that `(θ₁ ∘ θ₂)(t) = θ₁(θ₂(t))` (§B.1.7).
    pub fn compose(theta1: &Self, theta2: &Self) -> Self {
        let mut map: FxHashMap<Var, TermId> = FxHashMap::default();
        // Apply theta1 to all values of theta2.
        for (&x, &t) in &theta2.0 {
            let result = theta1.apply(t);
            // Drop identity mappings (Var x maps to mk_var_interned(x)).
            if result != mk_var_interned(x) {
                map.insert(x, result);
            }
        }
        // Include bindings from theta1 whose domain variable is not in theta2.
        for (&x, &t) in &theta1.0 {
            if !theta2.0.contains_key(&x) {
                map.insert(x, t);
            }
        }
        Self(map)
    }

    /// Insert or overwrite a single binding.
    pub fn bind(&mut self, var: Var, term: TermId) {
        self.0.insert(var, term);
    }

    /// Insert by variable name string.
    pub fn bind_str(&mut self, var: &str, term: TermId) {
        self.0.insert(Var::intern(var), term);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Renaming: Var → Var
// ─────────────────────────────────────────────────────────────────────────────

/// A bijective substitution `α` with `α(X) ∈ V` (§B.1.7).
///
/// Stored as a forward map `Var → Var`; no String allocation in the hot path.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Renaming(pub FxHashMap<Var, Var>);

impl Renaming {
    /// Build from an explicit map.
    pub fn from_map(map: FxHashMap<Var, Var>) -> Self {
        Self(map)
    }

    /// Lift to a `Substitution`.
    pub fn to_substitution(&self) -> Substitution {
        Substitution(
            self.0
                .iter()
                .map(|(&k, &v)| (k, mk_var_interned(v)))
                .collect(),
        )
    }

    /// Apply the renaming to a term.
    pub fn apply(&self, t: TermId) -> TermId {
        self.to_substitution().apply(t)
    }

    /// Compute the inverse renaming `α⁻¹` (§B.1.7).
    pub fn inverse(&self) -> Self {
        let mut inv = FxHashMap::default();
        for (&k, &v) in &self.0 {
            debug_assert!(
                !inv.contains_key(&v),
                "renaming is not injective: {v:?} has two preimages"
            );
            inv.insert(v, k);
        }
        Self(inv)
    }

    /// Compose two renamings: `(α₁ ∘ α₂)(x) = α₁(α₂(x))`.
    pub fn compose(alpha1: &Self, alpha2: &Self) -> Self {
        let mut map = FxHashMap::default();
        for (&x, &y) in &alpha2.0 {
            let z = alpha1.0.get(&y).copied().unwrap_or(y);
            if z != x {
                map.insert(x, z);
            }
        }
        for (&x, &z) in &alpha1.0 {
            if !alpha2.0.contains_key(&x) {
                map.insert(x, z);
            }
        }
        Self(map)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Fresh variable generation — u32 counter, NO String allocation in engine
// ─────────────────────────────────────────────────────────────────────────────

static FRESH_COUNTER: AtomicU32 = AtomicU32::new(0);

/// Generate a fresh `Var` from a u32 counter.
///
/// The `prefix` is retained only for API compatibility with the historical
/// string scheme; it is **ignored** — the result is a canonical-index
/// [`Var::Idx`] consuming one slot of `counter`.  No `format!`, no global
/// interner lock: `Var::Idx(n)` is disjoint from every `Var::Named` (different
/// enum variant) and from any other `Idx` with a different `n`, so a
/// monotone `counter` is exactly the freshness guarantee the old
/// `"{prefix}{counter}"` string scheme provided.
#[inline]
pub fn fresh_var(_prefix: &str, counter: &mut u32) -> Var {
    let n = *counter;
    *counter += 1;
    Var::Idx(n)
}

/// Generate a globally-unique fresh `Var` (for use when no local counter is
/// available).  Pulls one slot from a process-global atomic generation; the
/// `prefix` is ignored for the same reason as [`fresh_var`].
pub fn fresh_var_global(_prefix: &str) -> Var {
    let n = FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
    Var::Idx(n)
}

/// Rename all variables in `t` to fresh names, returning the renamed term and
/// the renaming used.  Used for producing variable-disjoint copies (§B.1.19).
///
/// O(#distinct vars) integer work: each source var is mapped to a fresh
/// `Var::Idx` consuming one `counter` slot — **no string formatting, no
/// global-interner lock** (the cost the KS profiler attributed to
/// `freshen`/`Var::intern`).  The resulting term is variable-disjoint from
/// anything carrying `Named` vars or `Idx` vars of a lower generation.
pub fn freshen(t: TermId, prefix: &str, counter: &mut u32) -> (TermId, Renaming) {
    let vars: Vec<Var> = t.vars().into_iter().collect();
    let mut map = FxHashMap::default();
    for v in vars {
        let fresh = fresh_var(prefix, counter);
        map.insert(v, fresh);
    }
    let renaming = Renaming::from_map(map);
    (renaming.apply(t), renaming)
}
