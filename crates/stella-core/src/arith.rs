//! Arithmetic module — §58-style label/Horn stars (subproject spec
//! `docs/05-combinator-core-and-the-kam-escape.md`, phase **K2a**).
//!
//! embershot's strict numeric primitives (`add mul div neg eq lt`, `inc dec`)
//! cannot be combinator-rewritten — they consume *evaluated* numerals. Eng's
//! own pattern for "labels that denote functions" is the §58 module
//! constellation `M★ = Σ l★` (`circuits.rs`). For arithmetic over an infinite
//! domain the per-label star is not a finite truth table but Eng's §55 Horn
//! definition — recursive constellations over unary numerals `n̄ = sⁿ(z)`
//! (verbatim `[+add(z,Y,Y)] + [−add(X,Y,Z),+add(s(X),Y,s(Z))]`, the milestone
//! already in `concrete.rs`/`ch9.rs`).
//!
//! Run under **IEx** (Eng §55: `IEx(Φ⁺_N, [−add(2̄,2̄,R),R]) ↝ [4̄]`): the Horn
//! program is the reference constellation `Φ` (recursive star reused every
//! step — the reason IEx, not copy-bounded AEx, is the faithful mode here, as
//! in K1).
//!
//! ## Scope / disclosed risk (spec §3, nulls N-K2 / N-K4)
//!
//! - **K2a (this module): the arithmetic module standalone, faithful.** Oracle
//!   = ground arithmetic + Eng §55. Numerals are **unary** — exact and
//!   Eng-faithful, but `O(n)` in the integer, so galaxy-scale bignums are
//!   infeasible here (**N-K4**, acknowledged, not hidden; binary/scale =
//!   later phase). This phase proves the *module mechanism* correct on small
//!   numbers; it deliberately does **not** touch the combinator spine.
//! - **K2b (next): the strict-primitive bridge.** Wiring `op` into the K1
//!   combinator IEx thread requires forcing argument subterms to numerals
//!   before the module fires — exactly embershot's `ForceArgs` and exactly
//!   Eng's §58/§87.2 "nothing specifies this synchronised flow" punt. The
//!   **N-K2** experiment (does it work without hand-ordered arg evaluation)
//!   lives there, inspect-don't-trust. Nothing here is a v1 "win" until K2b
//!   is run honestly.
//! - Signed/negative integers (galaxy uses them) are **out of K2a**: unary
//!   `ℕ` only. `neg`/`div` deferred with the binary representation.

use crate::constellation::{Constellation, Star};
use crate::interactive::iex_fast_concealed as iex_concealed;
use crate::polarised::{neg_ray, pos_ray};
use crate::term::{self, Term, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// Unary numerals  n̄ = sⁿ(z)   (Eng 0̄ ↦ the constant `z`, to keep a namespace
// disjoint from combinator atoms when K2b fuses the constellations)
// ─────────────────────────────────────────────────────────────────────────────

fn zero() -> Term {
    term::mk_app_str("z", vec![])
}
fn succ(t: Term) -> Term {
    term::mk_app_str("s", vec![t])
}
fn var(x: &str) -> Term {
    term::mk_var(x)
}

/// `n̄ = sⁿ(z)`.
pub fn nat(n: u64) -> Term {
    let mut t = zero();
    for _ in 0..n {
        t = succ(t);
    }
    t
}

/// Decode a ground unary numeral back to `u64` (None if it is not `sⁿ(z)`).
pub fn denat(t: TermId) -> Option<u64> {
    let mut n = 0u64;
    let mut cur = t;
    loop {
        match term::get(cur) {
            term::TermData::App(sym, args) if sym.name.as_str() == "z" && args.is_empty() => {
                return Some(n)
            }
            term::TermData::App(sym, args) if sym.name.as_str() == "s" && args.len() == 1 => {
                n += 1;
                cur = args[0];
            }
            _ => return None,
        }
    }
}

/// Boolean codomain for `eq`/`lt`: Eng's truth constants. Mapped to the
/// combinator `T`/`F` selectors in K2b (embershot `Primitive::{T,F}`).
fn tt() -> Term {
    term::mk_app_str("tt", vec![])
}
fn ff() -> Term {
    term::mk_app_str("ff", vec![])
}

// ─────────────────────────────────────────────────────────────────────────────
// The arithmetic module  M★ = Σ l★   (Eng §55 Horn definitions)
// ─────────────────────────────────────────────────────────────────────────────

/// `add` — Eng §55 verbatim: `[+add(z,Y,Y)] + [−add(X,Y,Z),+add(s(X),Y,s(Z))]`.
pub fn add_stars() -> Vec<Star> {
    vec![
        vec![pos_ray("add", vec![zero(), var("Y"), var("Y")])],
        vec![
            neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
            pos_ray("add", vec![succ(var("X")), var("Y"), succ(var("Z"))]),
        ],
    ]
}

/// `mul` — `mul(z,Y,z)`; `mul(s X,Y,W) ⇐ mul(X,Y,Z), add(Y,Z,W)`.
/// Reuses `add` in the same constellation (module is closed under its ops).
pub fn mul_stars() -> Vec<Star> {
    vec![
        vec![pos_ray("mul", vec![zero(), var("Y"), zero()])],
        vec![
            neg_ray("mul", vec![var("X"), var("Y"), var("Z")]),
            neg_ray("add", vec![var("Y"), var("Z"), var("W")]),
            pos_ray("mul", vec![succ(var("X")), var("Y"), var("W")]),
        ],
    ]
}

/// `inc`/`dec` — embershot `Primitive::{Inc,Dec}`. `dec(z)=z` (saturating, ℕ).
pub fn incdec_stars() -> Vec<Star> {
    vec![
        vec![pos_ray("inc", vec![var("X"), succ(var("X"))])],
        vec![pos_ray("dec", vec![zero(), zero()])],
        vec![pos_ray("dec", vec![succ(var("X")), var("X")])],
    ]
}

/// `eq` — structural equality on numerals → `tt`/`ff`.
pub fn eq_stars() -> Vec<Star> {
    vec![
        vec![pos_ray("eq", vec![zero(), zero(), tt()])],
        vec![pos_ray("eq", vec![succ(var("X")), zero(), ff()])],
        vec![pos_ray("eq", vec![zero(), succ(var("Y")), ff()])],
        vec![
            neg_ray("eq", vec![var("X"), var("Y"), var("R")]),
            pos_ray("eq", vec![succ(var("X")), succ(var("Y")), var("R")]),
        ],
    ]
}

/// `lt` — strict less-than on numerals → `tt`/`ff`.
pub fn lt_stars() -> Vec<Star> {
    vec![
        vec![pos_ray("lt", vec![zero(), succ(var("Y")), tt()])],
        vec![pos_ray("lt", vec![var("X"), zero(), ff()])],
        vec![
            neg_ray("lt", vec![var("X"), var("Y"), var("R")]),
            pos_ray("lt", vec![succ(var("X")), succ(var("Y")), var("R")]),
        ],
    ]
}

/// `M★` — the full arithmetic module constellation (`Σ l★`, §58.9 pattern).
pub fn arith_module() -> Constellation {
    let mut m = Vec::new();
    m.extend(add_stars());
    m.extend(mul_stars());
    m.extend(incdec_stars());
    m.extend(eq_stars());
    m.extend(lt_stars());
    m
}

// ─────────────────────────────────────────────────────────────────────────────
// Module-internal evaluation:  IEx(M★, [−op(args, R), R]) ↝ [result]
// (§58.8 criterion shape; §55 IEx-with-query for the recursive cases)
// ─────────────────────────────────────────────────────────────────────────────

/// Run `op` on ground numeral inputs through the module under IEx, returning
/// the single concealed result term, or `None` if no `[result]` is produced.
///
/// Query star `[−op(a⃗, R), R]` (Eng §55/§58.8): the negative ray drives
/// resolution against the module; the trailing unpolarised `R` is the readout
/// that survives `↨♭` once bound.
pub fn eval(op: &str, inputs: &[Term], fuel: usize) -> Option<TermId> {
    let phi = arith_module();
    let mut q: Vec<Term> = inputs.to_vec();
    q.push(var("R"));
    let query: Star = vec![neg_ray(op, q), var("R")];
    let (visible, _normal) = iex_concealed(&phi, vec![query], fuel);
    // Exactly one concealed star, the bound readout `[result]`.
    visible.iter().find_map(|s| match s.as_slice() {
        [only] => Some(*only),
        _ => None,
    })
}

/// Convenience: evaluate a numeric binary op to `u64`.
pub fn eval_nat(op: &str, a: u64, b: u64, fuel: usize) -> Option<u64> {
    eval(op, &[nat(a), nat(b)], fuel).and_then(denat)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — oracle = ground arithmetic + Eng §55 (spec §4). Inspect-don't-trust:
// every result is decoded back to a number and checked, never "a star exists".
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    const FUEL: usize = 4000;

    /// Eng §55 milestone, verbatim: `IEx(Φ⁺_N, [−add(2̄,2̄,R),R]) ↝ [4̄]`.
    #[test]
    fn add_2_plus_2_is_4() {
        assert_eq!(eval_nat("add", 2, 2, FUEL), Some(4));
    }

    #[test]
    fn add_table_small() {
        for a in 0..5 {
            for b in 0..5 {
                assert_eq!(
                    eval_nat("add", a, b, FUEL),
                    Some(a + b),
                    "add({a},{b})"
                );
            }
        }
    }

    #[test]
    fn mul_table_small() {
        for a in 0..4 {
            for b in 0..4 {
                assert_eq!(
                    eval_nat("mul", a, b, FUEL),
                    Some(a * b),
                    "mul({a},{b})"
                );
            }
        }
    }

    #[test]
    fn inc_dec() {
        assert_eq!(eval("inc", &[nat(3)], FUEL).and_then(denat), Some(4));
        assert_eq!(eval("dec", &[nat(3)], FUEL).and_then(denat), Some(2));
        assert_eq!(eval("dec", &[nat(0)], FUEL).and_then(denat), Some(0));
    }

    #[test]
    fn eq_is_decidable() {
        assert_eq!(eval("eq", &[nat(3), nat(3)], FUEL), Some(tt()));
        assert_eq!(eval("eq", &[nat(3), nat(2)], FUEL), Some(ff()));
        assert_eq!(eval("eq", &[nat(0), nat(0)], FUEL), Some(tt()));
        assert_eq!(eval("eq", &[nat(0), nat(1)], FUEL), Some(ff()));
    }

    #[test]
    fn lt_is_decidable() {
        assert_eq!(eval("lt", &[nat(2), nat(5)], FUEL), Some(tt()));
        assert_eq!(eval("lt", &[nat(5), nat(2)], FUEL), Some(ff()));
        assert_eq!(eval("lt", &[nat(3), nat(3)], FUEL), Some(ff()));
        assert_eq!(eval("lt", &[nat(0), nat(1)], FUEL), Some(tt()));
    }

    /// N-K4 marker (acknowledged, not hidden): unary cost is O(n). A modest
    /// number still works; galaxy-scale bignums do not — that is the binary
    /// representation's job in a later phase, recorded as a known boundary.
    #[test]
    fn unary_cost_is_linear_but_modest_works() {
        assert_eq!(eval_nat("add", 12, 7, FUEL), Some(19));
    }
}
