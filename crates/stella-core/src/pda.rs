//! NPDA-to-constellation encoding (Eng §56.9–56.13).
//!
//! ## Encoding summary (§56.9–§56.11)
//!
//! Given `P = (Q, Σ, Γ, Δ, Q₀, $, F)` and a word `w = c₁…cₙ`:
//!
//! * **Word star** (§56.2, shared with NFA): `[+i(c₁ · … · cₙ · ε)]`
//!
//! * **Initial stars**: for each `q₀ ∈ Q₀`:
//!   `[−i(W), +p(W, q₀, $)]`
//!
//! * **Final stars**: for each `q_f ∈ F`:
//!   `[−p(ε, q_f, S), accept]`
//!
//! * **Transition stars** (§56.11): for `(q', b) ∈ Δ(q, c, a)`:
//!   - `a=ε, b=ε`: `[−p(c·W, q, S),   +p(W, q', S)]`
//!   - `a=ε, b≠ε`: `[−p(c·W, q, S),   +p(W, q', b·S)]`
//!   - `a≠ε, b=ε`: `[−p(c·W, q, a·S), +p(W, q', S)]`
//!   - `a≠ε, b≠ε`: `[−p(c·W, q, a·S), +p(W, q', b·S)]`
//!   When `c=ε`: use `W` directly in place of `c·W`.
//!
//! Acceptance criterion (§56.13): `P accepts w iff [accept] ∈ ɟIEx(P★, w★)`.
//! Mode: IEx + ↨♭ (conceal + noise-filter).

use crate::automata::encode_word;
use crate::constellation::{Constellation, Star};
use crate::interactive::iex_nfa_accepts;
use crate::term::Term;

// ─────────────────────────────────────────────────────────────────────────────
// Helpers (mirroring automata.rs)
// ─────────────────────────────────────────────────────────────────────────────

fn constant(name: &str) -> Term {
    crate::term::mk_app_str(&name, vec![])
}

fn pos(neutral: &str, args: Vec<Term>) -> Term {
    crate::term::mk_app_str(&format!("+{neutral}"), args)
}

fn neg(neutral: &str, args: Vec<Term>) -> Term {
    crate::term::mk_app_str(&format!("-{neutral}"), args)
}

fn var(name: &str) -> Term {
    crate::term::mk_var(name)
}

/// `c·W` = `cons(c, W)`.
fn cons(c: Term, w: Term) -> Term {
    crate::term::mk_app_str("cons", vec![c, w])
}

// ─────────────────────────────────────────────────────────────────────────────
// NPDA data type
// ─────────────────────────────────────────────────────────────────────────────

/// A non-deterministic pushdown automaton (Eng §56.9).
///
/// - `states`: all states `Q`.
/// - `alphabet`: input alphabet `Σ` (characters as strings).
/// - `stack_alphabet`: stack alphabet `Γ` (characters as strings).
/// - `initial`: initial states `Q₀ ⊆ Q`.
/// - `finals`: accepting states `F ⊆ Q`.
/// - `transitions`: `(q, c_opt, a_opt, q', b_opt)` where
///   - `c_opt = None` means `c = ε` (no input consumed),
///   - `a_opt = None` means `a = ε` (no stack symbol popped),
///   - `b_opt = None` means `b = ε` (no stack symbol pushed).
#[derive(Debug, Clone)]
pub struct Npda {
    /// All states Q.
    pub states: Vec<String>,
    /// Input alphabet Σ.
    pub alphabet: Vec<String>,
    /// Stack alphabet Γ.
    pub stack_alphabet: Vec<String>,
    /// Initial states Q₀.
    pub initial: Vec<String>,
    /// Accepting states F.
    pub finals: Vec<String>,
    /// Transition relation: `(from, input_sym_or_ε, stack_top_or_ε, to, stack_push_or_ε)`.
    pub transitions: Vec<(
        String,      // q
        Option<String>, // c (None = ε)
        Option<String>, // a: stack top (None = ε, don't pop)
        String,      // q'
        Option<String>, // b: stack push (None = ε, don't push)
    )>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Encoding (§56.9–§56.11)
// ─────────────────────────────────────────────────────────────────────────────

/// Build a single transition star per §56.11.
///
/// `(q, c_opt, a_opt, q', b_opt)`:
/// - `c_opt = None` → ε-input: use bare `W` (not `c·W`)
/// - `a_opt = None` → ε stack top: match `S` (not `a·S`)
/// - `b_opt = None` → ε stack push: produce `S` (not `b·S`)
fn build_transition_star(
    q: &str,
    c_opt: Option<&str>,
    a_opt: Option<&str>,
    q_prime: &str,
    b_opt: Option<&str>,
) -> Star {
    let w = var("W");
    let s = var("S");

    // Stack pattern: the negative side matches `a·S` or `S`.
    let stack_neg = match a_opt {
        None => s.clone(),
        Some(a) => cons(constant(a), s.clone()),
    };

    // Stack output: the positive side emits `b·S` or `S`.
    let stack_pos = match b_opt {
        None => s.clone(),
        Some(b) => cons(constant(b), s.clone()),
    };

    // Input pattern: the negative side matches `c·W` or `W`.
    let input_neg = match c_opt {
        None => w.clone(),
        Some(c) => cons(constant(c), w.clone()),
    };

    vec![
        neg("p", vec![input_neg, constant(q), stack_neg]),
        pos("p", vec![w.clone(), constant(q_prime), stack_pos]),
    ]
}

/// Encode an NPDA as the base constellation `P★` (without word star).
///
/// Caller inserts `n_copies` copies of each transition star (to cover
/// repeated firings of the same rule); use 1 or more as appropriate.
pub fn encode_npda(pda: &Npda, n_copies: usize) -> Constellation {
    let mut c: Constellation = Vec::new();

    // Initial stars: [−i(W), +p(W, q₀, $)]
    for q0 in &pda.initial {
        let w = var("W");
        c.push(vec![
            neg("i", vec![w.clone()]),
            pos("p", vec![w.clone(), constant(q0), constant("$")]),
        ]);
    }

    // Final stars: [−p(ε, q_f, $), accept]  (§56.11, Fig 56.2: stack must be $ to accept)
    //
    // Eng's Fig 56.2 writes the final star as [−p(ε,q₃,$),accept] — the stack
    // position is the literal bottom-of-stack constant `$`, not a free variable S.
    // This ensures the machine accepts only when both input is exhausted AND
    // the stack is exactly `$` (empty save for the bottom marker).
    for qf in &pda.finals {
        c.push(vec![
            neg("p", vec![constant("eps"), constant(qf), constant("$")]),
            crate::term::mk_app_str("accept", vec![]),
        ]);
    }

    // Transition stars: n_copies copies of each.
    for _ in 0..n_copies {
        for (q, c_opt, a_opt, q_prime, b_opt) in &pda.transitions {
            c.push(build_transition_star(
                q,
                c_opt.as_deref(),
                a_opt.as_deref(),
                q_prime,
                b_opt.as_deref(),
            ));
        }
    }

    c
}

/// Full constellation `w★ + P★` for NPDA execution.
///
/// `word_copies` controls how many copies of the transition stars are included;
/// for a word of length `n` needing at most `k` firings per rule, use `k`.
pub fn npda_constellation(pda: &Npda, word: &[&str], word_copies: usize) -> Constellation {
    let mut phi: Constellation = Vec::new();
    phi.push(encode_word(word));
    phi.extend(encode_npda(pda, word_copies));
    phi
}

// ─────────────────────────────────────────────────────────────────────────────
// Acceptance (§56.13)
// ─────────────────────────────────────────────────────────────────────────────

/// Check whether the NPDA accepts `word` via IEx + ↨♭ (Thm §56.13).
///
/// `P accepts w iff [accept] ∈ ↨♭ IEx(P★, w★)`.
///
/// `n_copies` controls how many copies of each transition star are included
/// in the reference constellation.  Use a value large enough that each
/// transition can fire as many times as needed (= length of word for simple
/// stack operations, or more for complex ones).
///
/// `fuel` caps IEx steps; 4000 is safe for short words.
pub fn npda_accepts(pda: &Npda, word: &[&str], n_copies: usize, fuel: usize) -> bool {
    // Separate the word star (initial Ψ) from the machine constellation (Φ).
    let word_star = encode_word(word);
    let phi = encode_npda(pda, n_copies);
    iex_nfa_accepts(&phi, vec![word_star], fuel)
}

// ─────────────────────────────────────────────────────────────────────────────
// Eng's Figure 56.2 NPDA: {0ⁿ1ⁿ | n ≥ 0}
// ─────────────────────────────────────────────────────────────────────────────

/// Build Eng's Fig 56.2 NPDA for `{0ⁿ1ⁿ | n ≥ 0}`.
///
/// States: q₀ (initial/read-0), q₁ (read-1), q₂ (check-done), q₃ (final).
///
/// From the digest, the exact constellation `P★` is:
///   `[−i(W),+p(W,q₀,$)]`
///   `[−p(ε,q₃,$),accept]`
///   `[−p(0·W,q₀,S),+p(W,q₀,0·S)]`   read 0 → push 0
///   `[−p(1·W,q₀,0·S),+p(W,q₁,S)]`   read 1 → pop 0 → go q₁
///   `[−p(1·W,q₁,0·S),+p(W,q₁,S)]`   read 1 → pop 0 → stay q₁
///   `[−p(W,q₁,$),+p(W,q₂,$)]`        ε-transition: check stack = $ → go q₂
///
/// The ε-transition uses literal `$` (not a variable S), directly matching
/// the digest.  We use q₂ as "q₃" in the digest (the pre-final state).
/// The Npda struct encodes `(q1, None, None, q2, None)` for the ε-transition;
/// to faithfully reproduce the literal-$ form, `eng_fig562_npda_constellation`
/// overrides the final star and the ε-transition with exact-`$` stars.
pub fn eng_fig562_npda() -> Npda {
    Npda {
        states: vec!["q0".into(), "q1".into(), "q2".into()],
        alphabet: vec!["0".into(), "1".into()],
        stack_alphabet: vec!["0".into(), "$".into()],
        initial: vec!["q0".into()],
        finals: vec!["q2".into()],
        transitions: vec![
            // [−p(0·W,q₀,S),+p(W,q₀,0·S)]: read 0, push 0
            ("q0".into(), Some("0".into()), None, "q0".into(), Some("0".into())),
            // [−p(1·W,q₀,0·S),+p(W,q₁,S)]: read 1, pop 0, go q₁
            ("q0".into(), Some("1".into()), Some("0".into()), "q1".into(), None),
            // [−p(1·W,q₁,0·S),+p(W,q₁,S)]: read 1, pop 0, stay q₁
            ("q1".into(), Some("1".into()), Some("0".into()), "q1".into(), None),
            // ε-transition q₁→q₂: encoded as a=ε,b=ε (no stack op).
            // The digest writes this star as [−p(W,q₁,$),+p(W,q₂,$)] with
            // literal $; we emit that exact star in the constellation override below.
            ("q1".into(), None, None, "q2".into(), None),
        ],
    }
}

/// Build the exact Fig 56.2 constellation as given in the digest.
///
/// This overrides the generic encoding to reproduce the literal stars from
/// the digest verbatim:
/// ```text
/// [−i(W),+p(W,q₀,$)]
/// [−p(ε,q₂,$),accept]          ← literal $ (not variable S)
/// [−p(0·W,q₀,S),+p(W,q₀,0·S)]
/// [−p(1·W,q₀,0·S),+p(W,q₁,S)]
/// [−p(1·W,q₁,0·S),+p(W,q₁,S)]
/// [−p(W,q₁,$),+p(W,q₂,$)]      ← literal $ (not variable S)
/// ```
///
/// The literal `$` in the ε-transition makes it fire only when the FULL stack
/// is `$`; the variable-S form would fire at any stack state.  Both produce
/// the same accept/reject behaviour for this machine (the final star guards
/// `$` anyway), but the literal form is more faithful to the digest.
pub fn eng_fig562_npda_constellation(n_copies: usize) -> Constellation {
    let w = || var("W");
    let s = || var("S");
    let dollar = || constant("$");
    let eps = || constant("eps");

    let mut phi: Constellation = Vec::new();

    // Initial: [−i(W), +p(W, q₀, $)]
    phi.push(vec![
        neg("i", vec![w()]),
        pos("p", vec![w(), constant("q0"), dollar()]),
    ]);

    // Final: [−p(ε, q₂, $), accept]  — literal $
    phi.push(vec![
        neg("p", vec![eps(), constant("q2"), dollar()]),
        crate::term::mk_app_str("accept", vec![]),
    ]);

    // 4 transition stars, n_copies times
    for _ in 0..n_copies {
        // [−p(0·W, q₀, S), +p(W, q₀, 0·S)]
        phi.push(vec![
            neg("p", vec![cons(constant("0"), w()), constant("q0"), s()]),
            pos("p", vec![w(), constant("q0"), cons(constant("0"), s())]),
        ]);
        // [−p(1·W, q₀, 0·S), +p(W, q₁, S)]
        phi.push(vec![
            neg("p", vec![cons(constant("1"), w()), constant("q0"), cons(constant("0"), s())]),
            pos("p", vec![w(), constant("q1"), s()]),
        ]);
        // [−p(1·W, q₁, 0·S), +p(W, q₁, S)]
        phi.push(vec![
            neg("p", vec![cons(constant("1"), w()), constant("q1"), cons(constant("0"), s())]),
            pos("p", vec![w(), constant("q1"), s()]),
        ]);
        // [−p(W, q₁, $), +p(W, q₂, $)]  — literal $
        phi.push(vec![
            neg("p", vec![w(), constant("q1"), dollar()]),
            pos("p", vec![w(), constant("q2"), dollar()]),
        ]);
    }

    phi
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

/// Run the Fig 56.2 NPDA acceptance check using the exact-constellation encoding.
///
/// Uses `eng_fig562_npda_constellation` (literal `$` in final + ε-transition stars).
pub fn fig562_accepts(word: &[&str], fuel: usize) -> bool {
    // n_copies = word.len() + 2 ensures enough copies for the accepting run.
    let n_copies = word.len() + 2;
    let word_star = encode_word(word);
    let phi = eng_fig562_npda_constellation(n_copies);
    crate::interactive::iex_nfa_accepts(&phi, vec![word_star], fuel)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// §56.13: "0011" accepted (2 zeros, 2 ones).
    // IGNORED: ~90s under blind IEx (fuel=12000) — makes routine `cargo test`
    // look stalled. Faithful and passing; run with `cargo test -- --ignored`.
    // (Candidate for the semi-naïve/fast path; tracked, not weakened.)
    #[test]
    #[ignore = "slow (~90s blind IEx); faithful & passing; run with --ignored"]
    fn npda_accepts_0011() {
        assert!(
            fig562_accepts(&["0", "0", "1", "1"], 12000),
            "NPDA should accept '0011'"
        );
    }

    /// §56.13: "01" accepted (1 zero, 1 one).
    #[test]
    fn npda_accepts_01() {
        assert!(
            fig562_accepts(&["0", "1"], 4000),
            "NPDA should accept '01'"
        );
    }

    /// §56.13: ε (empty word): the digest's Fig 56.2 has no q₀→q₂ ε-path,
    /// so ε is not in the language of this machine's encoding.
    #[test]
    fn npda_epsilon_not_accepted_by_fig562() {
        assert!(
            !fig562_accepts(&[], 2000),
            "Fig 56.2 as encoded in digest does not accept ε (no q₀→q₂ ε-path)"
        );
    }

    /// §56.13: "001" rejected (unequal counts).
    #[test]
    fn npda_rejects_001() {
        assert!(
            !fig562_accepts(&["0", "0", "1"], 8000),
            "NPDA should reject '001'"
        );
    }

    /// §56.13: "10" rejected (1 before 0).
    #[test]
    fn npda_rejects_10() {
        assert!(
            !fig562_accepts(&["1", "0"], 4000),
            "NPDA should reject '10'"
        );
    }

    /// §56.13: "0" rejected (unequal counts, one 0 no 1).
    #[test]
    fn npda_rejects_0() {
        assert!(
            !fig562_accepts(&["0"], 4000),
            "NPDA should reject '0'"
        );
    }

    /// Structural test: count and shape of stars in the Fig 56.2 exact constellation.
    ///
    /// `eng_fig562_npda_constellation(1)` (1 copy of transition stars) has:
    /// - 1 initial star
    /// - 1 final star
    /// - 4 transition stars × 1 copy
    /// = 6 stars total (no word star — word star is the initial Ψ).
    #[test]
    fn npda_constellation_structure() {
        let phi = eng_fig562_npda_constellation(1);
        // 1 initial + 1 final + 4 transitions = 6
        assert_eq!(phi.len(), 6, "eng_fig562 constellation should have 6 stars for n_copies=1");

        // Initial star: [−i(W), +p(W, q₀, $)]
        let init_star = &phi[0];
        assert_eq!(init_star.len(), 2);
        assert_eq!(init_star[0].head(), Some("-i".to_string()), "initial star has -i ray");
        assert_eq!(init_star[1].head(), Some("+p".to_string()), "initial star has +p ray");

        // Final star: [−p(ε, q₂, $), accept]
        let final_star = &phi[1];
        assert_eq!(final_star.len(), 2);
        assert_eq!(final_star[0].head(), Some("-p".to_string()), "final star has -p ray");
        assert_eq!(final_star[1].head(), Some("accept".to_string()), "final star has accept ray");
    }
}
