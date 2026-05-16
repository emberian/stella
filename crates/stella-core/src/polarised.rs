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
