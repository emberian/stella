//! Polarised signatures and rays.
//!
//! Eng §48.2 defines a *polarised signature* as a tuple
//!
//! ```text
//! P = (V, F, ar, ⊂, |·|)
//! ```
//!
//! where `(V, F, ar, ⊂)` is a signature (§B.1.2) and `F` is partitioned as
//! `F₊ ⊎ F₋ ⊎ F₀` encoding polarity: positive (`+`), negative (`−`), or
//! neutral/uncoloured (`0`).
//!
//! The *underlying symbol* function `|·| : F → F₀` satisfies:
//! - `|f| = f` for `f ∈ F₀`
//! - the restrictions `|·|↾F₊` and `|·|↾F₋` are both bijections onto `F₀`
//!   (so every neutral symbol has exactly one positive and one negative version).
//!
//! §48.2 defines `+, − : F₀ → F₊/F₋` as the inverses of `|·|`.
//!
//! The compatibility relation `⊂` on polarised symbols (§48.2):
//!
//! ```text
//! c ⊂ d  ⟺  |c| = |d|  AND  one of:
//!              • c ∈ F₊, d ∈ F₋
//!              • c ∈ F₋, d ∈ F₊
//!              • c ∈ F₀, d ∈ F₀
//! ```
//!
//! §48.3 defines the *opposite* `op(f)`:
//!
//! ```text
//! op(f) = f        if f ∈ F₀
//! op(f) = −|f|     if f ∈ F₊
//! op(f) = +|f|     if f ∈ F₋
//! ```
//!
//! §48.7 defines a *ray* as a term in `Term(P)`.
//!
//! §49.7 defines *matchability* (`⋈`): two rays `r` and `r′` are *dual* /
//! *matchable* when they are α-unifiable with respect to the polarised
//! compatibility relation.

use crate::alpha::alpha_unify_with;
use crate::term::Term;
use crate::unify::Compatible;

/// The polarity of a function symbol (§48.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Polarity {
    /// Positive (+).
    Pos,
    /// Negative (−).
    Neg,
    /// Neutral / uncoloured (F₀).
    Neutral,
}

/// A function symbol in a polarised signature (§48.2).
///
/// We represent a polarised symbol as `(polarity, neutral_name)`.  The full
/// name is the neutral name prefixed with `+` (positive) or `−` (negative);
/// neutral symbols carry no prefix.
///
/// This avoids separate `F₊`, `F₋`, `F₀` name tables: the neutral name *is*
/// the shared underlying name, and polarity is a tag.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PolarisedSymbol {
    /// The polarity of this symbol.
    pub polarity: Polarity,
    /// The underlying neutral symbol name `|f|` (§48.2).
    pub neutral: String,
}

impl PolarisedSymbol {
    /// Construct a positive symbol `+c` from a neutral name `c`.
    pub fn positive(neutral: impl Into<String>) -> Self {
        Self { polarity: Polarity::Pos, neutral: neutral.into() }
    }

    /// Construct a negative symbol `−c` from a neutral name `c`.
    pub fn negative(neutral: impl Into<String>) -> Self {
        Self { polarity: Polarity::Neg, neutral: neutral.into() }
    }

    /// Construct a neutral symbol.
    pub fn neutral(name: impl Into<String>) -> Self {
        Self { polarity: Polarity::Neutral, neutral: name.into() }
    }

    /// The *opposite* `op(f)` (§48.3):
    /// - `op(f) = f`    if `f ∈ F₀`
    /// - `op(f) = −|f|` if `f ∈ F₊`
    /// - `op(f) = +|f|` if `f ∈ F₋`
    pub fn opposite(&self) -> Self {
        match self.polarity {
            Polarity::Neutral => self.clone(),
            Polarity::Pos => Self::negative(self.neutral.clone()),
            Polarity::Neg => Self::positive(self.neutral.clone()),
        }
    }

    /// The displayed name of this symbol (e.g. `"+c"`, `"-d"`, `"f"`).
    pub fn name(&self) -> String {
        match self.polarity {
            Polarity::Pos => format!("+{}", self.neutral),
            Polarity::Neg => format!("-{}", self.neutral),
            Polarity::Neutral => self.neutral.clone(),
        }
    }
}

impl std::fmt::Display for PolarisedSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Parse a symbol name into a `PolarisedSymbol`.
///
/// A name starting with `+` is positive, `−` (or `-`) is negative, otherwise
/// neutral.
pub fn parse_symbol(s: &str) -> PolarisedSymbol {
    if let Some(rest) = s.strip_prefix('+') {
        PolarisedSymbol::positive(rest)
    } else if let Some(rest) = s.strip_prefix('-') {
        PolarisedSymbol::negative(rest)
    } else {
        PolarisedSymbol::neutral(s)
    }
}

/// The *polarised compatibility relation* `⊂` for the unification algorithm
/// (§48.2):
///
/// ```text
/// c ⊂ d  ⟺  |c| = |d|  AND  (c and d have opposite polarity, or both neutral)
/// ```
pub struct PolarisedCompat;

impl Compatible for PolarisedCompat {
    fn compatible(&self, c_name: &str, d_name: &str) -> bool {
        let c = parse_symbol(c_name);
        let d = parse_symbol(d_name);

        // Same underlying symbol?
        if c.neutral != d.neutral {
            return false;
        }

        // Polarity condition (§48.2):
        matches!(
            (c.polarity, d.polarity),
            (Polarity::Pos, Polarity::Neg)
                | (Polarity::Neg, Polarity::Pos)
                | (Polarity::Neutral, Polarity::Neutral)
        )
    }
}

/// A *ray* is a term in `Term(P)` over a polarised signature (§48.7).
///
/// We use the same `Term` type with the symbol names encoded as strings
/// (e.g. `"+c"`, `"-d"`, `"f"`).  This is a type alias to make the
/// distinction explicit in APIs.
pub type Ray = Term;

/// The **underlying-term operator** `|·|` (§48.7, §48.2).
///
/// Strips colour (polarity prefix) from every application head recursively:
///
/// ```text
/// |X|                 = X                (variables unchanged)
/// |c(r₁,…,rₙ)|       = |c|(|r₁|,…,|rₙ|)  (strip head; recurse into args)
/// ```
///
/// where `|c|` is the *neutral underlying symbol* — i.e. the neutral name
/// with polarity prefix removed (`"+c"` → `"c"`, `"-d"` → `"d"`, `"f"` → `"f"`).
///
/// This is used by §49.27 to form the underlying unification problem `Prob(δ)`:
/// equations must be over underlying terms, not polarised rays.
pub fn underlying_term(ray: &Ray) -> Term {
    match ray {
        Term::Var(x) => Term::Var(x.clone()),
        Term::App(head, args) => {
            // Strip the polarity prefix from the head symbol (reuse parse_symbol).
            let sym = parse_symbol(head);
            let neutral_head = sym.neutral; // |head| is just the neutral name
            let underlying_args: Vec<Term> = args.iter().map(underlying_term).collect();
            Term::App(neutral_head, underlying_args)
        }
    }
}

/// Build a ray term `+sym(args)`.
pub fn pos_ray(neutral: &str, args: Vec<Term>) -> Ray {
    Term::App(PolarisedSymbol::positive(neutral).name(), args)
}

/// Build a ray term `−sym(args)`.
pub fn neg_ray(neutral: &str, args: Vec<Term>) -> Ray {
    Term::App(PolarisedSymbol::negative(neutral).name(), args)
}

/// Matchability `r ⋈ r′` (§49.7):
///
/// Two rays are *dual* / *matchable* when they are α-unifiable with respect
/// to the *polarised* compatibility relation `⊂` (§48.2).
///
/// §49.8: the relation is symmetric (follows from §B.1.14), anti-reflexive and
/// anti-transitive.
///
/// **Implementation note**: We pre-check head-symbol compatibility before calling
/// `alpha_unify_with`.  This guards against the Martelli-Montanari **Clear** rule
/// `{t =? t} → {}` short-circuiting compatibility checks for ground terms: when
/// two rays are syntactically identical, `alpha_unify_with` succeeds via Clear
/// before `PolarisedCompat` is consulted, which would falsely admit same-polarity
/// ground atoms.  The pre-check ensures §49.8 anti-reflexivity even for ground rays.
pub fn matchable(r: &Ray, r_prime: &Ray) -> bool {
    // Both rays must be applications (not variables) — §49.9: matchability
    // requires application terms with an underlying (neutral) symbol.
    // Pre-check: heads must be compatible under the polarised relation.
    // This also guards against the Clear rule short-circuiting compatibility for
    // syntactically-equal ground rays (see implementation note above).
    match (r, r_prime) {
        (Term::App(f, _), Term::App(g, _)) => {
            if !PolarisedCompat.compatible(f, g) {
                return false;
            }
        }
        _ => {
            // One or both rays are variables: not matchable.
            return false;
        }
    }
    alpha_unify_with(r, r_prime, &PolarisedCompat).is_some()
}
