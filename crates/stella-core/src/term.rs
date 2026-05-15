//! First-order terms over a signature.
//!
//! Eng §B.1.2 defines a *signature* `S = (V, F, ar, ⊂)` where `V` is a
//! countable set of variables, `F` a countable set of function symbols with
//! arity function `ar : F → N`, and `⊂` a compatibility relation on `F`.
//!
//! §B.1.4 defines the set of (first-order) **terms** `Term(S)` inductively:
//!
//! ```text
//! t ::= X          (variable, X ∈ V)
//!     | f(t₁,…,tₙ) (function application, f ∈ F, ar(f) = n)
//! ```
//!
//! **Representation choice**: variables and function-symbol names are
//! represented as owned `String`s.  This keeps the code self-contained (no
//! interner dependency) and makes debug output readable.  Arity is derived
//! implicitly from the argument vector length.

use std::collections::HashSet;

/// A first-order term (§B.1.4).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A variable `X ∈ V`.
    Var(String),
    /// A function application `f(t₁, …, tₙ)`.  The arity is `args.len()`.
    App(String, Vec<Term>),
}

impl Term {
    /// Convenience constructor for a zero-arity (constant) function symbol.
    pub fn constant(name: impl Into<String>) -> Self {
        Term::App(name.into(), vec![])
    }

    /// Convenience constructor for a variable.
    pub fn var(name: impl Into<String>) -> Self {
        Term::Var(name.into())
    }

    /// Returns `true` iff this term is a variable (§B.1.4).
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_))
    }

    /// The set of variables appearing in a term (§B.1.5):
    ///
    /// ```text
    /// vars(X)          = {X}
    /// vars(f(t₁,…,tₙ)) = ⋃ vars(tᵢ)
    /// ```
    pub fn vars(&self) -> HashSet<String> {
        match self {
            Term::Var(x) => {
                let mut s = HashSet::new();
                s.insert(x.clone());
                s
            }
            Term::App(_, args) => args.iter().flat_map(|t| t.vars()).collect(),
        }
    }

    /// The head function symbol, if this term is an application.
    pub fn head(&self) -> Option<&str> {
        match self {
            Term::App(f, _) => Some(f.as_str()),
            Term::Var(_) => None,
        }
    }

    /// The arity of this term: 0 for variables, `args.len()` for applications.
    pub fn arity(&self) -> usize {
        match self {
            Term::Var(_) => 0,
            Term::App(_, args) => args.len(),
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{x}"),
            Term::App(sym, args) if args.is_empty() => write!(f, "{sym}"),
            Term::App(sym, args) => {
                write!(f, "{sym}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}
