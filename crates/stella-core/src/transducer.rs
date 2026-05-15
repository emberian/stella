//! NFST-to-constellation encoding (Eng §56.15–56.18).
//!
//! ## Encoding summary (§56.17)
//!
//! Given `T = (Σ, Γ, Q, Q₀, Δ, F)` and input word `w = c₁…cₙ`:
//!
//! * **Word star** (§56.2): `[+i(c₁ · … · cₙ · ε)]`
//!
//! * **Initial stars**: for each `q₀ ∈ Q₀`:
//!   `[−i(W), +f(W, q₀, ε)]`
//!   (output stack starts empty = `ε`)
//!
//! * **Final stars**: for each `q_f ∈ F`:
//!   `[−f(ε, q_f, S), S]`
//!   (`S` is the unpolarised accumulated output stack)
//!
//! * **Transition stars**: for `(q', c') ∈ Δ(q, c)`:
//!   `[−f(c·W, q, S), +f(W, q', c'·S)]`   (`c ≠ ε, c' ≠ ε`)
//!   `c = ε`  ⇒ `[−f(W, q, S), +f(W, q', c'·S)]`
//!   `c' = ε` ⇒ `[−f(c·W, q, S), +f(W, q', S)]`
//!   (both ε: `[−f(W, q, S), +f(W, q', S)]`)
//!
//! ## Output-order note
//!
//! Eng's stack accumulates output symbols left-to-right via `c'·S` (prepend).
//! So the stack at the final state is `cₙ'·(cₙ₋₁'·(…·(c₁'·ε)…))`.
//! The final star `[−f(ε, q_f, S), S]` emits `S` unpolarised; decoding
//! `S = cₙ'·cₙ₋₁'·…·c₁'·ε` yields the output word in **reverse** of
//! application order.  Concretely: the first transition's output symbol
//! appears last in the decoded stack.  `nfst_transduce` returns the decoded
//! vector; callers should be aware that the order is reversed relative to
//! the input-symbol order (last input processed = first in result).

use crate::automata::encode_word;
use crate::constellation::{Constellation, Star};
use crate::interactive::{iex, iex_concealed};
use crate::polarised::Polarity;
use crate::constellation::ray_polarity;
use crate::term::Term;

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn constant(name: &str) -> Term {
    Term::App(name.into(), vec![])
}

fn pos(neutral: &str, args: Vec<Term>) -> Term {
    Term::App(format!("+{neutral}"), args)
}

fn neg(neutral: &str, args: Vec<Term>) -> Term {
    Term::App(format!("-{neutral}"), args)
}

fn var(name: &str) -> Term {
    Term::Var(name.into())
}

fn cons(c: Term, s: Term) -> Term {
    Term::App("cons".into(), vec![c, s])
}

// ─────────────────────────────────────────────────────────────────────────────
// NFST data type
// ─────────────────────────────────────────────────────────────────────────────

/// A non-deterministic finite-state transducer (Eng §56.15).
///
/// `T = (Σ, Γ, Q, Q₀, Δ, F)` where `Δ : Q × Σ_ε → P(Q × Γ_ε)`.
///
/// Transitions: `(q, c_opt, q', c'_opt)`:
/// - `c_opt  = None` → ε-input (no input consumed)
/// - `c'_opt = None` → ε-output (no output symbol emitted)
#[derive(Debug, Clone)]
pub struct Nfst {
    /// All states Q.
    pub states: Vec<String>,
    /// Input alphabet Σ.
    pub alphabet: Vec<String>,
    /// Output alphabet Γ.
    pub output_alphabet: Vec<String>,
    /// Initial states Q₀.
    pub initial: Vec<String>,
    /// Accepting states F.
    pub finals: Vec<String>,
    /// Transition relation: `(from, input_or_ε, to, output_or_ε)`.
    pub transitions: Vec<(
        String,          // q
        Option<String>,  // c  (None = ε)
        String,          // q'
        Option<String>,  // c' (None = ε)
    )>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Encoding (§56.17)
// ─────────────────────────────────────────────────────────────────────────────

/// Build a single transition star per §56.17.
fn build_transition_star(
    q: &str,
    c_opt: Option<&str>,
    q_prime: &str,
    c_prime_opt: Option<&str>,
) -> Star {
    let w = var("W");
    let s = var("S");

    // Negative side: consume `c·W` or bare `W`.
    let input_neg = match c_opt {
        None => w.clone(),
        Some(c) => cons(constant(c), w.clone()),
    };

    // Positive output stack: prepend `c'` to `S` or leave `S` unchanged.
    let stack_pos = match c_prime_opt {
        None => s.clone(),
        Some(c_prime) => cons(constant(c_prime), s.clone()),
    };

    vec![
        neg("f", vec![input_neg, constant(q), s.clone()]),
        pos("f", vec![w.clone(), constant(q_prime), stack_pos]),
    ]
}

/// Encode an NFST as the base constellation `T★` (without word star).
///
/// `n_copies`: number of copies of each transition star (to cover repeated firings).
pub fn encode_nfst(fst: &Nfst, n_copies: usize) -> Constellation {
    let mut c: Constellation = Vec::new();

    // Initial stars: [−i(W), +f(W, q₀, ε)]
    for q0 in &fst.initial {
        let w = var("W");
        c.push(vec![
            neg("i", vec![w.clone()]),
            pos("f", vec![w.clone(), constant(q0), constant("eps")]),
        ]);
    }

    // Final stars: [−f(ε, q_f, S), S]  — S is unpolarised
    for qf in &fst.finals {
        let s = var("S");
        c.push(vec![
            neg("f", vec![constant("eps"), constant(qf), s.clone()]),
            s.clone(), // unpolarised output
        ]);
    }

    // Transition stars: n_copies copies each.
    for _ in 0..n_copies {
        for (q, c_opt, q_prime, c_prime_opt) in &fst.transitions {
            c.push(build_transition_star(
                q,
                c_opt.as_deref(),
                q_prime,
                c_prime_opt.as_deref(),
            ));
        }
    }

    c
}

/// Full constellation `w★ + T★` for NFST execution.
pub fn nfst_constellation(fst: &Nfst, word: &[&str], n_copies: usize) -> Constellation {
    let mut phi: Constellation = Vec::new();
    phi.push(encode_word(word));
    phi.extend(encode_nfst(fst, n_copies));
    phi
}

// ─────────────────────────────────────────────────────────────────────────────
// Output decoding
// ─────────────────────────────────────────────────────────────────────────────

/// Decode a `cons`-chain term back to a symbol vector.
///
/// `cons(c₁, cons(c₂, … cons(cₙ, eps) …))` → `["c₁", "c₂", …, "cₙ"]`.
fn decode_stack(term: &Term) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = term;
    loop {
        match cur {
            Term::App(head, args) if head == "cons" && args.len() == 2 => {
                if let Term::App(sym, sym_args) = &args[0] {
                    if sym_args.is_empty() {
                        out.push(sym.clone());
                    } else {
                        // Compound symbol — stringify.
                        out.push(format!("{}", args[0]));
                    }
                } else {
                    out.push(format!("{}", args[0]));
                }
                cur = &args[1];
            }
            Term::App(head, args) if head == "eps" && args.is_empty() => break,
            _ => {
                // Non-standard tail; stop.
                break;
            }
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Transduction (§56.18)
// ─────────────────────────────────────────────────────────────────────────────

/// Transduce `word` via `fst` using IEx + ↨♭ (§56.18).
///
/// Returns all possible output words found in the ↨♭-result (one per
/// unpolarised star `[S]` in the concealed normal form).
///
/// ## Output order
///
/// The NFST encoding accumulates output by prepending: each transition
/// `[−f(c·W,q,S), +f(W,q',c'·S)]` prepends `c'` to the running stack `S`.
/// The final star emits the accumulated stack `S` unpolarised.  Decoding
/// the `cons`-chain gives symbols in the order they were prepended, which is
/// **reverse input order**: the output symbol corresponding to the *last*
/// input character appears *first* in the decoded list.
///
/// This is faithful to Eng's construction.  Callers that need "natural" order
/// (output symbol for first input character first) should reverse the result.
///
/// `n_copies`: copies of each transition star in the reference constellation.
/// `fuel`: IEx step limit.
pub fn nfst_transduce(fst: &Nfst, word: &[&str], n_copies: usize, fuel: usize) -> Vec<Vec<String>> {
    let word_star = encode_word(word);
    let phi = encode_nfst(fst, n_copies);
    let (concealed, _) = iex_concealed(&phi, vec![word_star], fuel);

    // Collect all unpolarised single-term stars [S] where S is a cons-chain.
    // The final star emits `S` as a bare unpolarised term (not wrapped in any functor).
    let mut results = Vec::new();
    for star in &concealed {
        if star.len() == 1 {
            let ray = &star[0];
            // Must be neutral (unpolarised).
            if ray_polarity(ray) != Polarity::Neutral {
                continue;
            }
            // Must look like a cons-chain or eps.
            match ray {
                Term::App(head, _) if head == "cons" || head == "eps" => {
                    results.push(decode_stack(ray));
                }
                Term::Var(_) => {
                    // A bare variable — the stack was unconstrained, skip.
                }
                _ => {
                    // Other neutral term — not an output stack.
                }
            }
        }
    }
    results
}

// ─────────────────────────────────────────────────────────────────────────────
// Example machines
// ─────────────────────────────────────────────────────────────────────────────

/// Build a simple "copy" transducer: output = input, over alphabet {a, b}.
///
/// One state `q₀` (initial and accepting), transitions:
///   `Δ(q₀, a) = {(q₀, a)}`
///   `Δ(q₀, b) = {(q₀, b)}`
///
/// This exercises the basic construction and lets us verify transduction
/// gives back the input (but in reversed stack order — see module note).
pub fn copy_transducer() -> Nfst {
    Nfst {
        states: vec!["q0".into()],
        alphabet: vec!["a".into(), "b".into()],
        output_alphabet: vec!["a".into(), "b".into()],
        initial: vec!["q0".into()],
        finals: vec!["q0".into()],
        transitions: vec![
            ("q0".into(), Some("a".into()), "q0".into(), Some("a".into())),
            ("q0".into(), Some("b".into()), "q0".into(), Some("b".into())),
        ],
    }
}

/// Build an "a→bb" transducer: replaces each `a` with `bb`, keeps `b` as `b`.
///
/// One state `q₀` (initial and accepting), transitions:
///   `Δ(q₀, a) = {(q₁, b)}`   (emit first b, go to q₁)
///   `Δ(q₁, ε) = {(q₀, b)}`   (emit second b, return to q₀)
///   `Δ(q₀, b) = {(q₀, b)}`   (copy b)
///
/// Note: because the stack accumulates by prepending, the two `b` outputs
/// for each `a` arrive in the stack in reverse order (the ε-step's `b`
/// is on top).
pub fn a_to_bb_transducer() -> Nfst {
    Nfst {
        states: vec!["q0".into(), "q1".into()],
        alphabet: vec!["a".into(), "b".into()],
        output_alphabet: vec!["b".into()],
        initial: vec!["q0".into()],
        finals: vec!["q0".into()],
        transitions: vec![
            // read a → go q₁, emit b
            ("q0".into(), Some("a".into()), "q1".into(), Some("b".into())),
            // ε → back to q₀, emit b  (second b for each a)
            ("q1".into(), None, "q0".into(), Some("b".into())),
            // read b → stay q₀, emit b
            ("q0".into(), Some("b".into()), "q0".into(), Some("b".into())),
        ],
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn copies_for(word: &[&str]) -> usize {
        // Each symbol may trigger up to 2 transitions (e.g. a→bb uses 2 steps per a).
        word.len() * 2 + 2
    }

    // ── Copy transducer ───────────────────────────────────────────────────────

    /// The copy transducer on "ab" should produce ["b","a"] in stack order.
    ///
    /// Explanation: processing "a" then "b":
    ///   stack after "a": cons(a, eps)
    ///   stack after "b": cons(b, cons(a, eps))
    /// Decoded: ["b", "a"].  This is reversed from input order, as documented.
    #[test]
    fn copy_transducer_ab() {
        let fst = copy_transducer();
        let word = &["a", "b"];
        let results = nfst_transduce(&fst, word, copies_for(word), 4000);
        assert!(
            !results.is_empty(),
            "copy transducer on 'ab' should produce output; got {:?}", results
        );
        // The stack is accumulated by prepending, so decoded order = ["b","a"].
        assert!(
            results.contains(&vec!["b".to_string(), "a".to_string()]),
            "copy transducer 'ab' → stack ['b','a'] (reversed); got {:?}", results
        );
    }

    /// The copy transducer on "a" should produce ["a"] (single symbol, order unchanged).
    #[test]
    fn copy_transducer_a() {
        let fst = copy_transducer();
        let word = &["a"];
        let results = nfst_transduce(&fst, word, copies_for(word), 2000);
        assert!(
            results.contains(&vec!["a".to_string()]),
            "copy transducer 'a' → ['a']; got {:?}", results
        );
    }

    // ── Structural test ───────────────────────────────────────────────────────

    /// The copy transducer's base constellation (n_copies=1) has the right shape.
    ///
    /// encode_nfst gives:
    ///   1 initial star  (q₀)
    ///   1 final star    (q₀)
    ///   2 transition stars × 1 copy = 2
    /// Total: 4 stars (no word star in encode_nfst).
    #[test]
    fn nfst_constellation_structure() {
        let fst = copy_transducer();
        let phi = encode_nfst(&fst, 1);
        assert_eq!(phi.len(), 4, "encode_nfst(copy,1) should have 4 stars");

        // Initial star: [−i(W), +f(W, q₀, ε)]
        let init = &phi[0];
        assert_eq!(init.len(), 2);
        assert_eq!(init[0].head(), Some("-i"), "initial star first ray is -i");
        assert_eq!(init[1].head(), Some("+f"), "initial star second ray is +f");

        // Final star: [−f(ε, q₀, S), S]
        let fin = &phi[1];
        assert_eq!(fin.len(), 2);
        assert_eq!(fin[0].head(), Some("-f"), "final star first ray is -f");
        // Second ray is unpolarised (bare variable S).
        assert!(
            matches!(&fin[1], Term::Var(_)),
            "final star second ray is neutral variable S; got {:?}", fin[1]
        );
    }

    // ── a→bb transducer ───────────────────────────────────────────────────────

    /// The a→bb transducer on "a" should produce ["b","b"] (in some order in stack).
    ///
    /// The two b's are emitted in sequence; the stack is built by prepending,
    /// so the result stack encodes them in reverse emission order.
    /// Emission order: first b (from q0→q1), then b (from q1→q0 ε-step).
    /// Stack order: second-b on top = cons(b, cons(b, eps)) = ["b","b"].
    #[test]
    fn a_to_bb_transducer_a() {
        let fst = a_to_bb_transducer();
        let word = &["a"];
        let results = nfst_transduce(&fst, word, copies_for(word), 4000);
        assert!(
            !results.is_empty(),
            "a→bb transducer on 'a' should produce output; got {:?}", results
        );
        assert!(
            results.contains(&vec!["b".to_string(), "b".to_string()]),
            "a→bb transducer 'a' → ['b','b']; got {:?}", results
        );
    }

    /// The a→bb transducer on "b" should produce ["b"].
    #[test]
    fn a_to_bb_transducer_b() {
        let fst = a_to_bb_transducer();
        let word = &["b"];
        let results = nfst_transduce(&fst, word, copies_for(word), 4000);
        assert!(
            results.contains(&vec!["b".to_string()]),
            "a→bb transducer 'b' → ['b']; got {:?}", results
        );
    }
}
