//! Non-deterministic Turing machine (NTM) encoding (Eng §56.19–§56.25).
//!
//! ## Two-stack tape representation (§56.19)
//!
//! The tape configuration is encoded as `m(L, Q, X, R)` where:
//! - `L`: left portion of tape to the left of the head, encoded with `●`
//!   **left-associatively** (`lcons`): `□`, `□ ● a`, `(□ ● a) ● b`, …
//! - `Q`: current state
//! - `X`: symbol currently under the head
//! - `R`: right portion of tape to the right of the head, encoded with `○`
//!   **right-associatively** (`rcons`): `□`, `a ○ □`, `a ○ (b ○ □)`, …
//!
//! ## Symbol choices
//!
//! | Eng notation | This implementation | Rationale |
//! |---|---|---|
//! | `●` (left-tape cons, left-assoc) | function symbol `"lcons"` | distinct from right cons |
//! | `○` (right-tape cons, right-assoc) | function symbol `"rcons"` | mirrors NFA `cons` style |
//! | `□` (blank) | constant `"blank"` | printable, unique |
//! | `m(L,Q,X,R)` | `+m(…)` / `−m(…)` | follows polarised signature convention |
//! | `i(W)` | `+i(…)` / `−i(…)` | matches NFA `i` symbol for input |
//! | `accept` | constant `"accept"` | matches NFA convention |
//! | `reject` | constant `"reject"` | new constant for TM rejection |
//!
//! ## Encoding M★ (§56.22)
//!
//! Given `M = (Q, Γ, Δ, q₀, q_a, q_r)`:
//!
//! **q₀ stars** (non-empty and empty word):
//! ```text
//! [−i(C ○ W), +m(□, q₀, C, W)]     (non-empty input)
//! [−i(□),     +m(□, q₀, □, □)]     (empty input / blank tape)
//! ```
//!
//! **Accept/reject stars:**
//! ```text
//! [−m(L, q_a, X, R), accept]
//! [−m(L, q_r, X, R), reject]
//! ```
//!
//! **Transition stars** for each `(q', c', d) ∈ Δ(q, c)`:
//! - `d=L` (left):  `[−m(L ● X, q, c, R), +m(L, q', X, c' ○ R)]`
//! - `d=R` (right): `[−m(L, q, c, X ○ R), +m(L ● c', q', X, R)]`
//! - `d=S` (stay):  `[−m(L, q, c, R),     +m(L, q', c', R)]`
//!
//! **Memory-allocation (malloc) stars** (dynamic blank extension):
//! ```text
//! [−m(□, Q, C, R),     +m(□ ● □, Q, C, R)]   (extend left with new blank)
//! [−m(L, Q, C, □),     +m(L, Q, C, □ ○ □)]   (extend right with new blank)
//! ```
//!
//! **Word encoding** (§56.21):
//! ```text
//! non-empty w = c₁…cₙ: [+i(c₁ ○ (c₂ ○ (… ○ cₙ ○ □) …))]   (right-assoc ○-chain ending in □)
//! empty word:           [+i(□)]
//! ```
//!
//! ## Acceptance criterion (Thm §56.25)
//!
//! Mode: IEx (§51.10, not AEx).  Let `Ψ = ↨♭ IEx(M★ ⊢ w★)`.
//! - `M(w) = 1` (accept)  ⇒  `[accept] ∈ Ψ`
//! - `M(w) = 0` (reject)  ⇒  `[reject] ∈ Ψ`
//! - `M(w) = ∞` (diverge) ⇒  neither (fuel exhausted without `[accept]`/`[reject]`)

use crate::constellation::{Constellation, Star};
use crate::interactive::iex_concealed;
use crate::term::Term;

// ─────────────────────────────────────────────────────────────────────────────
// Alphabet / state / direction types
// ─────────────────────────────────────────────────────────────────────────────

/// A tape symbol from Γ (including blank `□`).
///
/// We represent symbols as plain strings.  The blank is the special string
/// `"blank"` (Eng `□`).
pub type Sym = String;

/// The blank symbol `□` (§56.19).
pub const BLANK: &str = "blank";

/// Head movement direction (§56.22).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dir {
    /// Move head left.
    L,
    /// Move head right.
    R,
    /// Stay (no movement).
    S,
}

// ─────────────────────────────────────────────────────────────────────────────
// NTM data type
// ─────────────────────────────────────────────────────────────────────────────

/// A non-deterministic Turing machine `M = (Q, Γ, Δ, q₀, q_a, q_r)` (§56.19).
///
/// - `states`: all states Q (including q0, q_accept, q_reject)
/// - `gamma`: tape alphabet Γ (excluding blank; blank is always implicitly present)
/// - `delta`: transition relation as a list of `(from_state, read_sym, to_state, write_sym, dir)`
///   quintuples; `read_sym` ∈ Γ ∪ {blank}; `write_sym` ∈ Γ ∪ {blank}
/// - `q0`: initial state
/// - `q_accept`: accepting state q_a
/// - `q_reject`: rejecting state q_r
#[derive(Debug, Clone)]
pub struct Ntm {
    /// All states Q.
    pub states: Vec<String>,
    /// Tape alphabet Γ (symbols other than blank).
    pub gamma: Vec<String>,
    /// Transition relation: `(from, read_sym, to, write_sym, dir)`.
    ///
    /// `read_sym` / `write_sym` are tape symbols; use `BLANK` for `□`.
    pub delta: Vec<(String, String, String, String, Dir)>,
    /// Initial state q₀.
    pub q0: String,
    /// Accepting state q_a.
    pub q_accept: String,
    /// Rejecting state q_r.
    pub q_reject: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper constructors (mirrors automata.rs style)
// ─────────────────────────────────────────────────────────────────────────────

/// Build a zero-arity constant term.
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

/// Build a right-associative `○` chain (§56.21 `rcons`):
/// `rcons_chain([c1, c2, c3], base)` = `rcons(c1, rcons(c2, rcons(c3, base)))`.
///
/// This encodes the right portion of the tape and the input word.
fn rcons_chain(items: &[Term], base: Term) -> Term {
    items
        .iter()
        .rev()
        .fold(base, |acc, c| crate::term::mk_app_str("rcons", vec![*c, acc]))
}

/// Build a left-associative `●` application (`lcons`):
/// `lcons(lcons(base, a), b)`.
///
/// This is used only for the `L ● X` pattern in transitions (one level deep).
/// `lcons_app(left, right)` = `lcons(left, right)`.
fn lcons_app(left: Term, right: Term) -> Term {
    crate::term::mk_app_str("lcons", vec![left, right])
}

/// Encode a state name as a constant term.
fn state(q: &str) -> Term {
    constant(q)
}

/// Encode a tape symbol string as a constant term.
/// `BLANK` → constant `"blank"`.
fn sym_term(s: &str) -> Term {
    constant(s) // "blank" maps to itself; other symbols are their own constants
}

/// `+m(L, Q, X, R)` — positive memory ray.
fn pos_m(l: Term, q: Term, x: Term, r: Term) -> Term {
    pos("m", vec![l, q, x, r])
}

/// `−m(L, Q, X, R)` — negative memory ray.
fn neg_m(l: Term, q: Term, x: Term, r: Term) -> Term {
    neg("m", vec![l, q, x, r])
}

// ─────────────────────────────────────────────────────────────────────────────
// Word encoding (§56.21)
// ─────────────────────────────────────────────────────────────────────────────

/// Encode the input word `w` as the input star `w★` (§56.21).
///
/// - Non-empty `w = c₁…cₙ`:
///   `[+i(rcons(c₁, rcons(c₂, … rcons(cₙ, blank) …)))]`
/// - Empty word: `[+i(blank)]`
///
/// Note: `○` is right-associative and the chain terminates with `□` (blank).
/// This differs from the NFA encoding (which uses `cons`/`eps`):
/// here the terminal sentinel IS blank (§56.21: "tape is blank beyond the input").
pub fn encode_word_ntm(word: &[Sym]) -> Star {
    if word.is_empty() {
        // Empty word → [+i(□)]
        vec![pos("i", vec![constant(BLANK)])]
    } else {
        // Non-empty w = c₁…cₙ → +i(c₁ ○ (c₂ ○ (… ○ (cₙ ○ □) …)))
        let syms: Vec<Term> = word.iter().map(|s| sym_term(s)).collect();
        let chain = rcons_chain(&syms, constant(BLANK));
        vec![pos("i", vec![chain])]
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Constellation encoding (§56.22)
// ─────────────────────────────────────────────────────────────────────────────

/// Build `M★` — the machine constellation for NTM `M` — WITHOUT the word star.
///
/// This is the reference constellation Φ passed to `iex`.
/// The word star `w★` is the initial interaction space Ψ (see `ntm_constellation`).
///
/// Structure (§56.22):
/// 1. Two q₀ stars (non-empty input / empty input).
/// 2. One q_a star (accept).
/// 3. One q_r star (reject).
/// 4. One transition star per `(q, c, q', c', d) ∈ Δ`.
/// 5. Two malloc (memory-allocation) stars.
pub fn encode_ntm(ntm: &Ntm) -> Constellation {
    let mut c: Constellation = Vec::new();

    // ── (1) q₀ stars ──────────────────────────────────────────────────────────
    //
    // §56.22:
    //   [−i(C ○ W), +m(□, q₀, C, W)]   ← non-empty input: C is first symbol, W is rest
    //   [−i(□),     +m(□, q₀, □, □)]   ← empty input: blank tape

    // Non-empty: read `C ○ W` from input, start with blank left tape, head on C.
    {
        let c_var = var("C");
        let w_var = var("W");
        let input = crate::term::mk_app_str("rcons", vec![c_var, w_var]);
        c.push(vec![
            neg("i", vec![input]),
            pos_m(
                constant(BLANK),      // L = □ (left tape initially blank)
                state(&ntm.q0),       // Q = q₀
                c_var,                // X = C (head symbol = first input char)
                w_var,                // R = W (rest of input goes right)
            ),
        ]);
    }

    // Empty: read blank from input, blank tape.
    {
        c.push(vec![
            neg("i", vec![constant(BLANK)]),
            pos_m(
                constant(BLANK), // L = □
                state(&ntm.q0),  // Q = q₀
                constant(BLANK), // X = □ (head on blank)
                constant(BLANK), // R = □ (right tape blank)
            ),
        ]);
    }

    // ── (2) Accept star ────────────────────────────────────────────────────────
    //
    // §56.22: [−m(L, q_a, X, R), accept]
    {
        let l = var("L");
        let x = var("X");
        let r = var("R");
        c.push(vec![
            neg_m(l, state(&ntm.q_accept), x, r),
            constant("accept"),
        ]);
    }

    // ── (3) Reject star ────────────────────────────────────────────────────────
    //
    // §56.22: [−m(L, q_r, X, R), reject]
    {
        let l = var("L");
        let x = var("X");
        let r = var("R");
        c.push(vec![
            neg_m(l, state(&ntm.q_reject), x, r),
            constant("reject"),
        ]);
    }

    // ── (4) Transition stars ───────────────────────────────────────────────────
    //
    // §56.22 per `(q', c', d) ∈ Δ(q, c)`, c ∈ Γ_□:
    //   d=L: [−m(L ● X, q, c, R), +m(L,  q', X, c' ○ R)]
    //   d=R: [−m(L, q, c, X ○ R), +m(L ● c', q', X, R)]
    //   d=S: [−m(L, q, c, R),     +m(L,  q', c', R)]

    for (from, read, to, write, dir) in &ntm.delta {
        let c_sym = sym_term(read);   // c (read symbol)
        let cp = sym_term(write);     // c' (write symbol)
        let star = match dir {
            Dir::L => {
                // d=L: −m(L ● X, q, c, R) and +m(L, q', X, c' ○ R)
                let l = var("L");
                let x = var("X");
                let r = var("R");
                let lx = lcons_app(l, x); // L ● X
                let cpr = crate::term::mk_app_str("rcons", vec![cp, r]); // c' ○ R
                vec![
                    neg_m(lx, state(from), c_sym, r),
                    pos_m(l, state(to), x, cpr),
                ]
            }
            Dir::R => {
                // d=R: −m(L, q, c, X ○ R) and +m(L ● c', q', X, R)
                let l = var("L");
                let x = var("X");
                let r = var("R");
                let xr = crate::term::mk_app_str("rcons", vec![x, r]); // X ○ R
                let lcp = lcons_app(l, cp);                             // L ● c'
                vec![
                    neg_m(l, state(from), c_sym, xr),
                    pos_m(lcp, state(to), x, r),
                ]
            }
            Dir::S => {
                // d=S: −m(L, q, c, R) and +m(L, q', c', R)
                let l = var("L");
                let r = var("R");
                vec![
                    neg_m(l, state(from), c_sym, r),
                    pos_m(l, state(to), cp, r),
                ]
            }
        };
        c.push(star);
    }

    // ── (5) Memory-allocation (malloc) stars ───────────────────────────────────
    //
    // §56.22:
    //   [−m(□, Q, C, R), +m(□ ● □, Q, C, R)]   ← extend left: add blank to left spine
    //   [−m(L, Q, C, □), +m(L, Q, C, □ ○ □)]   ← extend right: add blank to right spine

    // Left malloc: when L = □ (bare blank, not lcons), we can extend with lcons(□, □).
    {
        let q = var("Q");
        let cv = var("C");
        let r = var("R");
        let lhs = constant(BLANK);                               // □
        let rhs = lcons_app(constant(BLANK), constant(BLANK));   // □ ● □
        c.push(vec![
            neg_m(lhs, q, cv, r),
            pos_m(rhs, q, cv, r),
        ]);
    }

    // Right malloc: when R = □ (bare blank), extend with rcons(□, □).
    {
        let q = var("Q");
        let cv = var("C");
        let l = var("L");
        let lhs = constant(BLANK);                                                   // □
        let rhs = crate::term::mk_app_str("rcons", vec![constant(BLANK), constant(BLANK)]); // □ ○ □
        c.push(vec![
            neg_m(l, q, cv, lhs),
            pos_m(l, q, cv, rhs),
        ]);
    }

    c
}

// ─────────────────────────────────────────────────────────────────────────────
// Full constellation (machine + word)
// ─────────────────────────────────────────────────────────────────────────────

/// Build the full constellation `M★ ⊢ w★` for NTM execution.
///
/// Per §56.22 and §56.21:
/// - The machine constellation `M★` is the reference Φ (infinite supply via IEx).
/// - The word star `w★` is the initial interaction space Ψ.
///
/// Returns the REFERENCE constellation (M★) and the word star separately;
/// callers pass them to `iex(phi, psi, fuel)`.
///
/// The returned `Constellation` is M★ with the word star PREPENDED (index 0).
/// This is a convenience for structural tests; `ntm_accepts` uses them separately.
pub fn ntm_constellation(ntm: &Ntm, input: &[Sym]) -> Constellation {
    let mut phi = encode_ntm(ntm);
    // Prepend the word star so tests can inspect `phi[0]` = word star.
    let word = encode_word_ntm(input);
    phi.insert(0, word);
    phi
}

// ─────────────────────────────────────────────────────────────────────────────
// Acceptance (Thm §56.25)
// ─────────────────────────────────────────────────────────────────────────────

/// Decide acceptance of `input` by NTM `M` via stellar IEx (Thm §56.25).
///
/// Mode: IEx (not AEx/CEx).
///
/// - Reference constellation Φ = M★ (encode_ntm)
/// - Initial interaction space Ψ = w★ (encode_word_ntm)
/// - Run `↨♭ IEx(M★, w★)` for up to `fuel` steps.
/// - Return `Some(true)` if `[accept] ∈ Ψ`, `Some(false)` if `[reject] ∈ Ψ`.
/// - Return `None` if neither (fuel exhausted or diverges).
pub fn ntm_run(ntm: &Ntm, input: &[Sym], fuel: usize) -> Option<bool> {
    let phi = encode_ntm(ntm);
    let psi = encode_word_ntm(input);
    let (visible, _normal) = iex_concealed(&phi, vec![psi], fuel);
    let accept_star: Star = vec![constant("accept")];
    let reject_star: Star = vec![constant("reject")];
    if visible.iter().any(|s| s == &accept_star) {
        Some(true)
    } else if visible.iter().any(|s| s == &reject_star) {
        Some(false)
    } else {
        None
    }
}

/// Convenience wrapper: `ntm_accepts` returns `true` iff `[accept]` appears
/// in `↨♭ IEx(M★, w★)` within `fuel` steps (Thm §56.25).
pub fn ntm_accepts(ntm: &Ntm, input: &[Sym], fuel: usize) -> bool {
    ntm_run(ntm, input, fuel) == Some(true)
}

// ─────────────────────────────────────────────────────────────────────────────
// Example NTMs
// ─────────────────────────────────────────────────────────────────────────────

/// Build a simple deterministic TM over `{a, b}` that accepts the empty word only.
///
/// This is the simplest TM exercising the initial stars:
/// - q0 on empty input → accept immediately
/// - q0 on non-empty input → reject immediately
///
/// Transitions: q0 on 'a' → q_r (write a, stay); q0 on 'b' → q_r (write b, stay).
/// q0 on blank → q_a (write blank, stay).
pub fn trivial_accept_empty_tm() -> Ntm {
    Ntm {
        states: vec!["q0".into(), "qa".into(), "qr".into()],
        gamma: vec!["a".into(), "b".into()],
        delta: vec![
            // On blank (empty word): accept
            ("q0".into(), BLANK.into(), "qa".into(), BLANK.into(), Dir::S),
            // On 'a': reject
            ("q0".into(), "a".into(), "qr".into(), "a".into(), Dir::S),
            // On 'b': reject
            ("q0".into(), "b".into(), "qr".into(), "b".into(), Dir::S),
        ],
        q0: "q0".into(),
        q_accept: "qa".into(),
        q_reject: "qr".into(),
    }
}

/// Build a deterministic TM that accepts words of the form `a^n b^n` (n ≥ 0).
///
/// This is a classic TM that exercises head movement in both directions.
///
/// Algorithm:
/// - q0: scan for leftmost 'a'; mark it as 'X' and move right to find matching 'b'.
/// - q1: move right past a's and X's to find 'b'; mark it as 'Y', go back left.
/// - q2: move left past a's and X's back to the left end.
/// - q3: check if all a's are consumed (all X's at start).
///       If blank found on left → scan right past Y's → if blank → accept; else reject.
/// - q4: scanning right past Y's.
///
/// Alphabet: {a, b, X, Y, blank}
///
/// State transitions (simplified, deterministic):
/// ```text
/// q0, a → q1, X, R  (mark a, go find b)
/// q0, Y → q3, Y, R  (all a's done, check b's)
/// q0, □ → qa, □, S  (empty tape: n=0 → accept)
/// q1, a → q1, a, R  (skip a's going right)
/// q1, Y → q1, Y, R  (skip Y's going right)
/// q1, b → q2, Y, L  (mark b, go back left)
/// q2, a → q2, a, L  (skip a's going left)
/// q2, X → q0, X, R  (back at left: find next unmarked a)
/// q3, Y → q3, Y, R  (skip Y's)
/// q3, □ → qa, □, S  (all matched: accept)
/// q3, b → qr, b, S  (unmatched b: reject)
/// q0, b → qr, b, S  (b before any a: reject)
/// q1, □ → qr, □, S  (no matching b: reject)
/// ```
pub fn anbn_tm() -> Ntm {
    Ntm {
        states: vec![
            "q0".into(), "q1".into(), "q2".into(), "q3".into(),
            "qa".into(), "qr".into(),
        ],
        gamma: vec!["a".into(), "b".into(), "X".into(), "Y".into()],
        delta: vec![
            // q0: looking for next 'a' to mark
            ("q0".into(), "a".into(), "q1".into(), "X".into(), Dir::R),
            ("q0".into(), "Y".into(), "q3".into(), "Y".into(), Dir::R),
            ("q0".into(), BLANK.into(), "qa".into(), BLANK.into(), Dir::S),
            ("q0".into(), "b".into(), "qr".into(), "b".into(), Dir::S),
            // q1: moving right to find 'b'
            ("q1".into(), "a".into(), "q1".into(), "a".into(), Dir::R),
            ("q1".into(), "Y".into(), "q1".into(), "Y".into(), Dir::R),
            ("q1".into(), "b".into(), "q2".into(), "Y".into(), Dir::L),
            ("q1".into(), BLANK.into(), "qr".into(), BLANK.into(), Dir::S),
            // q2: moving left back to start
            ("q2".into(), "a".into(), "q2".into(), "a".into(), Dir::L),
            ("q2".into(), "Y".into(), "q2".into(), "Y".into(), Dir::L),
            ("q2".into(), "X".into(), "q0".into(), "X".into(), Dir::R),
            // q3: scanning right past Y's to verify all b's matched
            ("q3".into(), "Y".into(), "q3".into(), "Y".into(), Dir::R),
            ("q3".into(), BLANK.into(), "qa".into(), BLANK.into(), Dir::S),
            ("q3".into(), "b".into(), "qr".into(), "b".into(), Dir::S),
        ],
        q0: "q0".into(),
        q_accept: "qa".into(),
        q_reject: "qr".into(),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(s: &str) -> Sym { s.to_string() }
    fn word(v: &[&str]) -> Vec<Sym> { v.iter().map(|s| sym(s)).collect() }

    // ── Structural tests ──────────────────────────────────────────────────────

    /// Verify the q₀ pair of stars, q_a/q_r stars, malloc stars, and transition
    /// count appear in the constellation (§56.22).
    ///
    /// For `trivial_accept_empty_tm` with 3 transitions:
    ///   - index 0: word star (prepended by ntm_constellation)
    ///   - index 1: q₀ non-empty star
    ///   - index 2: q₀ empty star
    ///   - index 3: q_a accept star
    ///   - index 4: q_r reject star
    ///   - indices 5..7: 3 transition stars (one per Δ entry)
    ///   - index 8: left malloc star
    ///   - index 9: right malloc star
    ///   Total: 10 stars
    #[test]
    fn ntm_constellation_structure() {
        let ntm = trivial_accept_empty_tm();
        // Test on the empty word (word star = [+i(blank)])
        let phi = ntm_constellation(&ntm, &[]);
        // 1 word + 2 q0 + 2 halting + 3 transitions + 2 malloc = 10
        assert_eq!(phi.len(), 10, "trivial TM constellation should have 10 stars; got {}", phi.len());

        // Star 0: word star — a single +i ray
        let word_star = &phi[0];
        assert_eq!(word_star.len(), 1, "word star should have 1 ray");
        assert_eq!(word_star[0].head(), Some("+i".to_string()), "word star ray should be +i");

        // Star 1: q₀ non-empty — [−i(rcons(C,W)), +m(blank, q0, C, W)]
        let q0_nonempty = &phi[1];
        assert_eq!(q0_nonempty.len(), 2, "q0 non-empty star should have 2 rays");
        assert_eq!(q0_nonempty[0].head(), Some("-i".to_string()), "first ray of q0 non-empty star should be -i");
        assert_eq!(q0_nonempty[1].head(), Some("+m".to_string()), "second ray of q0 non-empty star should be +m");

        // Star 2: q₀ empty — [−i(blank), +m(blank, q0, blank, blank)]
        let q0_empty = &phi[2];
        assert_eq!(q0_empty.len(), 2, "q0 empty star should have 2 rays");
        assert_eq!(q0_empty[0].head(), Some("-i".to_string()), "first ray of q0 empty star should be -i");
        assert_eq!(q0_empty[1].head(), Some("+m".to_string()), "second ray of q0 empty star should be +m");

        // Stars 3,4: accept/reject halting stars — each has 2 rays: -m and a constant
        let q_a_star = &phi[3];
        assert_eq!(q_a_star.len(), 2);
        assert_eq!(q_a_star[0].head(), Some("-m".to_string()), "accept star should start with -m");
        assert_eq!(q_a_star[1], constant("accept"), "accept star should end with [accept]");

        let q_r_star = &phi[4];
        assert_eq!(q_r_star.len(), 2);
        assert_eq!(q_r_star[0].head(), Some("-m".to_string()), "reject star should start with -m");
        assert_eq!(q_r_star[1], constant("reject"), "reject star should end with [reject]");

        // Transition stars (indices 5..7): each has 2 rays (-m, +m)
        for idx in 5..8 {
            let ts = &phi[idx];
            assert_eq!(ts.len(), 2, "transition star {} should have 2 rays", idx);
            assert_eq!(ts[0].head(), Some("-m".to_string()), "transition star {} ray 0 should be -m", idx);
            assert_eq!(ts[1].head(), Some("+m".to_string()), "transition star {} ray 1 should be +m", idx);
        }

        // Malloc stars (indices 8, 9): each has 2 rays (-m, +m)
        let malloc_l = &phi[8];
        assert_eq!(malloc_l.len(), 2, "left malloc star should have 2 rays");
        assert_eq!(malloc_l[0].head(), Some("-m".to_string()));
        assert_eq!(malloc_l[1].head(), Some("+m".to_string()));

        let malloc_r = &phi[9];
        assert_eq!(malloc_r.len(), 2, "right malloc star should have 2 rays");
        assert_eq!(malloc_r[0].head(), Some("-m".to_string()));
        assert_eq!(malloc_r[1].head(), Some("+m".to_string()));
    }

    /// Verify transition star count for the anbn TM (14 transitions).
    #[test]
    fn ntm_constellation_transition_count() {
        let ntm = anbn_tm();
        let phi = encode_ntm(&ntm);
        // 2 q0 + 1 q_a + 1 q_r + 14 transitions + 2 malloc = 20
        assert_eq!(phi.len(), 20, "anbn TM machine constellation should have 20 stars; got {}", phi.len());
    }

    // ── Trivial TM (accept empty only) ───────────────────────────────────────

    /// Trivial TM accepts the empty word.
    #[test]
    fn trivial_tm_accepts_empty() {
        let ntm = trivial_accept_empty_tm();
        let result = ntm_run(&ntm, &[], 200);
        assert_eq!(
            result, Some(true),
            "trivial TM should accept empty word; got {:?}", result
        );
    }

    /// Trivial TM rejects "a".
    #[test]
    fn trivial_tm_rejects_a() {
        let ntm = trivial_accept_empty_tm();
        let result = ntm_run(&ntm, &word(&["a"]), 200);
        assert_eq!(
            result, Some(false),
            "trivial TM should reject 'a'; got {:?}", result
        );
    }

    /// Trivial TM rejects "b".
    #[test]
    fn trivial_tm_rejects_b() {
        let ntm = trivial_accept_empty_tm();
        let result = ntm_run(&ntm, &word(&["b"]), 200);
        assert_eq!(
            result, Some(false),
            "trivial TM should reject 'b'; got {:?}", result
        );
    }

    // ── aⁿbⁿ TM ─────────────────────────────────────────────────────────────

    /// aⁿbⁿ TM accepts empty word (n=0).
    #[test]
    fn anbn_accepts_empty() {
        let ntm = anbn_tm();
        let result = ntm_run(&ntm, &[], 500);
        assert_eq!(
            result, Some(true),
            "anbn TM should accept empty word (n=0); got {:?}", result
        );
    }

    /// aⁿbⁿ TM accepts "ab" (n=1).
    #[test]
    fn anbn_accepts_ab() {
        let ntm = anbn_tm();
        let result = ntm_run(&ntm, &word(&["a", "b"]), 2000);
        assert_eq!(
            result, Some(true),
            "anbn TM should accept 'ab' (n=1); got {:?}", result
        );
    }

    /// aⁿbⁿ TM rejects "a" (no matching b).
    #[test]
    fn anbn_rejects_a() {
        let ntm = anbn_tm();
        let result = ntm_run(&ntm, &word(&["a"]), 500);
        assert_eq!(
            result, Some(false),
            "anbn TM should reject 'a'; got {:?}", result
        );
    }

    /// aⁿbⁿ TM rejects "b" (b before any a).
    #[test]
    fn anbn_rejects_b() {
        let ntm = anbn_tm();
        let result = ntm_run(&ntm, &word(&["b"]), 500);
        assert_eq!(
            result, Some(false),
            "anbn TM should reject 'b'; got {:?}", result
        );
    }

    /// aⁿbⁿ TM rejects "ba" (wrong order).
    #[test]
    fn anbn_rejects_ba() {
        let ntm = anbn_tm();
        let result = ntm_run(&ntm, &word(&["b", "a"]), 500);
        assert_eq!(
            result, Some(false),
            "anbn TM should reject 'ba'; got {:?}", result
        );
    }

    /// aⁿbⁿ TM rejects "aab" (unequal counts).
    #[test]
    fn anbn_rejects_aab() {
        let ntm = anbn_tm();
        let result = ntm_run(&ntm, &word(&["a", "a", "b"]), 500);
        assert_eq!(
            result, Some(false),
            "anbn TM should reject 'aab'; got {:?}", result
        );
    }

    // ── Word encoding ─────────────────────────────────────────────────────────

    /// Empty word encodes as [+i(blank)] (§56.21).
    #[test]
    fn encode_word_empty() {
        let star = encode_word_ntm(&[]);
        assert_eq!(star.len(), 1, "empty word star should have 1 ray");
        assert_eq!(star[0].head(), Some("+i".to_string()));
        let args0 = star[0].args();
        assert_eq!(args0.len(), 1);
        assert_eq!(args0[0], constant(BLANK), "empty word star arg should be blank");
    }

    /// Non-empty word "ab" encodes as [+i(rcons(a, rcons(b, blank)))] (§56.21).
    #[test]
    fn encode_word_ab() {
        let star = encode_word_ntm(&word(&["a", "b"]));
        assert_eq!(star.len(), 1);
        assert_eq!(star[0].head(), Some("+i".to_string()));
        let args0 = star[0].args();
        assert_eq!(args0.len(), 1);
        assert_eq!(args0[0].head(), Some("rcons".to_string()), "word should be rcons-encoded");
    }
}
