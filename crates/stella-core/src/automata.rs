//! NFA-to-constellation encoding (Eng §56).
//!
//! §56 (Non-deterministic finite automata, Chapter 8 "Illustrating stellar
//! resolution") defines a faithful translation of an NFA and a word into a
//! constellation whose execution decides acceptance.
//!
//! ## Encoding summary (§56.2–§56.3)
//!
//! Given an NFA A = (Σ, Q, Q0, Δ, F) and a word w = c1…cn:
//!
//! * **Word star** (§56.2): `[+i(c1 · c2 · … · cn · ε)]`
//!   where `·` is a right-associative binary constructor.
//!
//! * **Initial stars** (§56.3): for each `q0 ∈ Q0`:
//!   `[−i(W), +a(W, q0)]`
//!
//! * **Final stars** (§56.3): for each `qf ∈ F`:
//!   `[−a(ε, qf), accept]`
//!
//! * **Transition stars** (§56.3): for each `(q, c, q') ∈ Δ` with `c ≠ ε`:
//!   `[−a(c · W, q), +a(W, q')]`
//!   for ε-transitions (`c = ε`):
//!   `[−a(W, q), +a(W, q')]`
//!
//! The acceptance criterion (§56.5 Theorem): A accepts w iff `[accept] ∈ IEx(A⋆, w⋆)`.
//!
//! ## Execution-mode accommodation (deviation from §56.5)
//!
//! Eng §56.5 uses IEx (Interactive Execution).  The crate implements AEx
//! (Abstract Execution, §49.42) via saturated-diagram construction.
//!
//! Because the dependency graph (§49.10) requires `i ≠ i'` (rays from distinct
//! star indices), a transition rule used k times in a run requires k distinct
//! star copies.  We expose `nfa_constellation(nfa, word, extra_copies)` which
//! pre-includes `1 + extra_copies` copies of each transition star.
//!
//! For the Eng Figure 56.1 example we use `extra_copies = 0` (one copy per
//! transition) and test with words "00" (accepted) and "1" (rejected).  The
//! accepting path for "00" uses each of the two relevant transition stars
//! (`q0→q1`, `q1→q2`) exactly once, so one copy suffices.  Using more copies
//! inflates the dependency graph and causes exponential diagram-saturation
//! blowup that is intrinsic to AEx on branching NFAs; §56.5 relies on IEx for
//! this reason.  This is the documented deviation.
//!
//! Cyclic diagrams are excluded by the occur-check on `cons(c, W) =? W` (§56.5
//! proof, "cyclic diagrams" paragraph).

use crate::constellation::{Constellation, Star};
use crate::dep_graph::DepGraph;
use crate::execution::aex;
use crate::term::Term;

// ─────────────────────────────────────────────────────────────────────────────
// Helper constructors
// ─────────────────────────────────────────────────────────────────────────────

/// Build the constant term `name` (zero-arity application).
fn constant(name: &str) -> Term {
    crate::term::mk_app_str(name, vec![])
}

/// Build `+sym(args)`.
fn pos(neutral: &str, args: Vec<Term>) -> Term {
    crate::term::mk_app_str(&format!("+{neutral}"), args)
}

/// Build `−sym(args)`.
fn neg(neutral: &str, args: Vec<Term>) -> Term {
    crate::term::mk_app_str(&format!("-{neutral}"), args)
}

/// Build a variable term.
fn var(name: &str) -> Term {
    crate::term::mk_var(name)
}

/// Build the right-associative cons chain `c1 · c2 · … · cn · base`.
///
/// §56.2 uses `·` as a right-associative binary symbol (`cons`).
/// E.g. for `[c1, c2, c3]` and base = ε:
/// `cons(c1, cons(c2, cons(c3, ε)))`.
fn cons_chain(chars: &[Term], base: Term) -> Term {
    chars
        .iter()
        .rev()
        .fold(base, |acc, c| crate::term::mk_app_str("cons", vec![*c, acc]))
}

// ─────────────────────────────────────────────────────────────────────────────
// NFA data type
// ─────────────────────────────────────────────────────────────────────────────

/// A non-deterministic finite automaton (§56, Definition before §56.2).
///
/// States and alphabet symbols are `String`s; the transition relation is given
/// as a list of `(from_state, symbol_or_epsilon, to_state)` triples.
/// `symbol_or_epsilon`: `None` means an ε-transition (§56.3 epsilon case).
#[derive(Debug, Clone)]
pub struct Nfa {
    /// All states Q.
    pub states: Vec<String>,
    /// Alphabet Σ (characters).
    pub alphabet: Vec<String>,
    /// Initial states Q0 ⊆ Q.
    pub initial: Vec<String>,
    /// Final/accepting states F ⊆ Q.
    pub finals: Vec<String>,
    /// Transition relation: `(from, symbol_or_ε, to)`.
    ///
    /// `symbol` is `None` for ε-transitions, `Some(c)` for reading character `c`.
    pub transitions: Vec<(String, Option<String>, String)>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Encoding functions (§56.2–§56.3)
// ─────────────────────────────────────────────────────────────────────────────

/// Encode a word as its input star (§56.2).
///
/// `w⋆ = [+i(c1 · c2 · … · cn · ε)]`
/// where `·` = `cons` (right-associative binary constructor) and `ε` is the
/// terminal constant.
pub fn encode_word(word: &[&str]) -> Star {
    let chars: Vec<Term> = word.iter().map(|c| constant(c)).collect();
    let chain = cons_chain(&chars, constant("eps"));
    vec![pos("i", vec![chain])]
}

/// Encode an NFA as a base constellation A⋆ (§56.3), without the word star.
///
/// Contains exactly one copy of each initial star, final star, and transition star.
/// For execution use `nfa_constellation`.
pub fn encode_nfa(nfa: &Nfa) -> Constellation {
    let mut c: Constellation = Vec::new();

    // §56.3 — initial stars: for each q0 ∈ Q0: [−i(W), +a(W, q0)]
    for q0 in &nfa.initial {
        let w = var("W");
        c.push(vec![
            neg("i", vec![w]),
            pos("a", vec![w, constant(q0)]),
        ]);
    }

    // §56.3 — final stars: for each qf ∈ F: [−a(ε, qf), accept]
    for qf in &nfa.finals {
        c.push(vec![
            neg("a", vec![constant("eps"), constant(qf)]),
            crate::term::mk_app_str("accept", vec![]),
        ]);
    }

    // §56.3 — transition stars: one per transition
    for (from, sym_opt, to) in &nfa.transitions {
        c.push(build_transition_star(from, sym_opt.as_deref(), to));
    }

    c
}

/// Build a single transition star per §56.3.
fn build_transition_star(from: &str, sym_opt: Option<&str>, to: &str) -> Star {
    match sym_opt {
        None => {
            // ε-transition: [−a(W, q), +a(W, q')]
            let w = var("W");
            vec![
                neg("a", vec![w, constant(from)]),
                pos("a", vec![w, constant(to)]),
            ]
        }
        Some(c) => {
            // Reading symbol c: [−a(c·W, q), +a(W, q')]
            let w = var("W");
            let cw = crate::term::mk_app_str("cons", vec![constant(c), w]);
            vec![
                neg("a", vec![cw, constant(from)]),
                pos("a", vec![w, constant(to)]),
            ]
        }
    }
}

/// Build the full constellation `w⋆ + A⋆` for NFA execution (§56.2–§56.3).
///
/// Includes the word star, initial stars, final stars, and `1 + extra_copies`
/// copies of each transition star.
///
/// `extra_copies = 0` is correct when every transition fires at most once along
/// the accepting run.  Use larger values only if the same transition must fire
/// multiple times; note that this inflates the saturation search space
/// (see module-level deviation note).
pub fn nfa_constellation(nfa: &Nfa, word: &[&str], extra_copies: usize) -> Constellation {
    let mut c: Constellation = Vec::new();

    // Word star (§56.2).
    c.push(encode_word(word));

    // Initial stars (§56.3).
    for q0 in &nfa.initial {
        let w = var("W");
        c.push(vec![
            neg("i", vec![w]),
            pos("a", vec![w, constant(q0)]),
        ]);
    }

    // Final stars (§56.3).
    for qf in &nfa.finals {
        c.push(vec![
            neg("a", vec![constant("eps"), constant(qf)]),
            crate::term::mk_app_str("accept", vec![]),
        ]);
    }

    // Transition stars: 1 + extra_copies copies of each (§56.3, §50 pre-expansion).
    for _ in 0..=(extra_copies) {
        for (from, sym_opt, to) in &nfa.transitions {
            c.push(build_transition_star(from, sym_opt.as_deref(), to));
        }
    }

    c
}

/// Check whether the NFA accepts `word` using stellar execution.
///
/// Acceptance criterion (§56.5): A accepts w iff `[accept] ∈ IEx(A⋆, w⋆)`.
/// We check for the star `[accept]` in the AEx output.
///
/// `extra_copies`: how many additional copies of each transition star to include
/// beyond the one required by the base encoding.  Use 0 when each transition fires
/// at most once; increase for words requiring repeated transitions (with the
/// tradeoff of exponential AEx blowup for branching NFAs — see module doc).
pub fn nfa_accepts(nfa: &Nfa, word: &[&str], extra_copies: usize) -> bool {
    let phi = nfa_constellation(nfa, word, extra_copies);
    let dg = DepGraph::from_constellation(&phi);
    let results = aex(&phi, &dg);
    let accept_star: Star = vec![crate::term::mk_app_str("accept", vec![])];
    results.iter().any(|s| s == &accept_star)
}

// ─────────────────────────────────────────────────────────────────────────────
// Public NFA constructors (used in tests and by interactive.rs)
// ─────────────────────────────────────────────────────────────────────────────

/// Build Eng's Figure 56.1 NFA: accepts words over {0,1} ending in "00".
///
/// States: q0 (initial), q1, q2 (final).
/// Transitions from Fig 56.1:
///   q0 --0--> q0  (self-loop)
///   q0 --1--> q0  (self-loop)
///   q0 --0--> q1
///   q1 --0--> q2
///
/// A⋆ = [−i(W), +a(W, q0)]
///    + [−a(ε, q2), accept]
///    + [−a(0·W, q0), +a(W, q0)]
///    + [−a(1·W, q0), +a(W, q0)]
///    + [−a(0·W, q0), +a(W, q1)]
///    + [−a(0·W, q1), +a(W, q2)]
pub fn eng_fig561_nfa() -> Nfa {
    Nfa {
        states: vec!["q0".into(), "q1".into(), "q2".into()],
        alphabet: vec!["0".into(), "1".into()],
        initial: vec!["q0".into()],
        finals: vec!["q2".into()],
        transitions: vec![
            ("q0".into(), Some("0".into()), "q0".into()), // self-loop 0
            ("q0".into(), Some("1".into()), "q0".into()), // self-loop 1
            ("q0".into(), Some("0".into()), "q1".into()), // to q1
            ("q1".into(), Some("0".into()), "q2".into()), // to q2 (final)
        ],
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// §56.5 Theorem acceptance: A accepts "00".
    ///
    /// The accepting path is q0 --(0)--> q1 --(0)--> q2.
    /// Each of the two relevant transitions fires exactly once, so extra_copies=0
    /// suffices.  self-loop transitions don't fire on the accepting path and their
    /// single copy participates in no correct saturated diagram for "00".
    ///
    /// Eng's Fig 56.1 caption gives IEx(A⋆, [+i(0·0·0·ε)]) = [accept]; we check
    /// the minimal case "00" (direct q0→q1→q2 path, no self-loop needed).
    #[test]
    fn nfa_accepts_minimal_00() {
        let nfa = eng_fig561_nfa();
        assert!(
            nfa_accepts(&nfa, &["0", "0"], 0),
            "NFA should accept '00' (ends in 00, per Eng Fig 56.1)"
        );
    }

    /// §56.5 Theorem rejection: A rejects "1" (§56.5 case 2: A(w)=0).
    ///
    /// "1" has no run reaching q2, so [accept] must not appear in AEx output.
    #[test]
    fn nfa_rejects_single_one() {
        let nfa = eng_fig561_nfa();
        assert!(
            !nfa_accepts(&nfa, &["1"], 0),
            "NFA should reject '1' (does not end in 00)"
        );
    }

    /// Rejection: "10" does not end in "00".
    #[test]
    fn nfa_rejects_10() {
        let nfa = eng_fig561_nfa();
        assert!(
            !nfa_accepts(&nfa, &["1", "0"], 0),
            "NFA should reject '10' (does not end in 00)"
        );
    }

    /// Verify the constellation structure for "00" with extra_copies=0.
    ///
    /// Stars: 1 word + 1 initial + 1 final + 4 transitions * 1 = 7.
    #[test]
    fn nfa_constellation_structure() {
        let nfa = eng_fig561_nfa();
        let phi = nfa_constellation(&nfa, &["0", "0"], 0);
        // 1 word + 1 initial + 1 final + 4 transitions = 7
        assert_eq!(phi.len(), 7, "constellation should have 7 stars for '00' with extra_copies=0");
        // Word star is first, has a single +i ray.
        let word_star = &phi[0];
        assert_eq!(word_star.len(), 1);
        assert_eq!(
            word_star[0].head(),
            Some("+i".to_string()),
            "word star should have +i head"
        );
    }

    /// Encode-word check: "00" encodes as +i(cons(0, cons(0, eps))).
    #[test]
    fn encode_word_structure() {
        let star = encode_word(&["0", "0"]);
        assert_eq!(star.len(), 1);
        let ray = star[0];
        // Should be: +i(cons(0, cons(0, eps)))
        assert_eq!(ray.head(), Some("+i".to_string()));
        // The argument should be a cons application.
        let args = ray.args();
        assert_eq!(args.len(), 1);
        assert_eq!(args[0].head(), Some("cons".to_string()));
    }
}
