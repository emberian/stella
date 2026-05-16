//! Alternating Turing machine (ATM) encoding (Eng §57.1–§57.6).
//!
//! ## Overview (§57.1)
//!
//! An ATM extends the NTM by equipping every state with a *class*:
//! `class : Q → {∨, ∧}`.  Existential (`∨`) states behave exactly like NTM
//! states — one of the possible successors is chosen.  Universal (`∧`) states
//! require ALL successors to succeed simultaneously, represented here by a
//! single star that emits **k positive** `+m(…)` rays — one per branch — from
//! a single negative `−m(…)` head.
//!
//! ## Two-stack tape (inherited from §56.19)
//!
//! Same as `tm.rs`: `m(L, Q, X, R)` with `lcons`/`rcons`/`blank`.
//!
//! ## Encoding M★ (§57.4)
//!
//! Given `M = (Q, Γ, Δ, q₀, q_a, q_r, class)`:
//!
//! **q₀ / q_a / q_r stars** — identical to §56.22 (NTM):
//! ```text
//! [−i(C ○ W), +m(□, q₀, C, W)]   (non-empty input)
//! [−i(□),     +m(□, q₀, □, □)]   (empty input)
//! [−m(L, q_a, X, R), accept]
//! [−m(L, q_r, X, R), reject]
//! ```
//!
//! **∨-successor transition** (existential, §57.4): same shape as NTM —
//! one star, one positive `+m(…)` output:
//! ```text
//! d=L: [−m(L ● X, q, c, R), +m(L,  q', X, c' ○ R)]
//! d=R: [−m(L, q, c, X ○ R), +m(L ● c', q', X, R)]
//! d=S: [−m(L, q, c, R),     +m(L,  q', c', R)]
//! ```
//!
//! **∧-successor with k branches** `(q₁,c₁,d₁), …, (qₖ,cₖ,dₖ)` for the SAME
//! `(q, c)` pair (§57.4): ONE star with k positive `+m(…)` outputs.  For `d=L`:
//! ```text
//! [−m(L ● X, q, c, R), +m(L, q₁, X, c₁ ○ R), …, +m(L, qₖ, X, cₖ ○ R)]
//! ```
//! For `d=R`:
//! ```text
//! [−m(L, q, c, X ○ R), +m(L ● c₁, q₁, X, R), …, +m(L ● cₖ, qₖ, X, R)]
//! ```
//! For `d=S`:
//! ```text
//! [−m(L, q, c, R), +m(L, q₁, c₁, R), …, +m(L, qₖ, cₖ, R)]
//! ```
//! Note: Eng §57.4 presents the left-move case; the right and stay cases follow
//! by analogy with NTM §56.22, using the same variable placeholders.
//!
//! **malloc stars** — identical to NTM §56.22:
//! ```text
//! [−m(□, Q, C, R), +m(□ ● □, Q, C, R)]
//! [−m(L, Q, C, □), +m(L, Q, C, □ ○ □)]
//! ```
//!
//! ## Acceptance criterion (Thm §57.5)
//!
//! Mode: IEx (same as NTM, §51.10).  Let `Ψ = ↨♭ IEx(M★ ⊢ w★)`.
//! - `M(w) = 1` ⇒ `[accept, k., accept] ∈ Ψ` for some k ≥ 1 (a star of k copies
//!   of `accept`, all unpolarised constants).
//! - Reject: none such star appears.
//!
//! Mechanically: the ∧-star emits k parallel `+m(…)` rays; each will eventually
//! fuse along its own accept path, depositing one `accept` constant per branch
//! in the same fused star, yielding `[accept, accept, …, accept]` (k entries).
//! An ∨-step yields exactly `[accept]` (k=1), so `[accept]` also satisfies the
//! criterion (it is a k=1 accept star).

use std::collections::HashMap;

use crate::constellation::{Constellation, Star};
use crate::interactive::iex_concealed;
use crate::term::Term;

// Re-export direction and blank from tm so ATM is consistent.
pub use crate::tm::{Dir, Sym, BLANK};

// ─────────────────────────────────────────────────────────────────────────────
// State class
// ─────────────────────────────────────────────────────────────────────────────

/// The *class* (§57.1) assigned to each state: existential (`∨`) or universal (`∧`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Class {
    /// Existential (`∨`) — non-deterministic choice, same star shape as NTM.
    Existential,
    /// Universal (`∧`) — all branches must succeed; encoded as one star with
    /// k positive outputs.
    Universal,
}

// ─────────────────────────────────────────────────────────────────────────────
// ATM data type
// ─────────────────────────────────────────────────────────────────────────────

/// An alternating Turing machine `M = (Q, Γ, Δ, q₀, q_a, q_r, class)` (§57.1).
///
/// Δ is given as a list of quintuples `(from, read, to, write, dir)`.
/// The `class` map assigns each state in Q a `Class` value.
/// States `q0`, `q_accept`, and `q_reject` may be assigned any class (Eng makes
/// no restriction); in practice q_accept/q_reject are trivial and their class
/// does not affect the encoding of their halting stars.
#[derive(Debug, Clone)]
pub struct Atm {
    /// All states Q.
    pub states: Vec<String>,
    /// Tape alphabet Γ (excluding blank; blank is always implicitly present).
    pub gamma: Vec<String>,
    /// Transition relation: `(from, read_sym, to, write_sym, dir)`.
    pub delta: Vec<(String, String, String, String, Dir)>,
    /// Initial state q₀.
    pub q0: String,
    /// Accepting state q_a.
    pub q_accept: String,
    /// Rejecting state q_r.
    pub q_reject: String,
    /// Class assignment `class : Q → {∨, ∧}` (§57.1).
    pub class: HashMap<String, Class>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Term helpers (mirror tm.rs exactly)
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

fn rcons(left: Term, right: Term) -> Term {
    crate::term::mk_app_str("rcons", vec![left, right])
}

fn lcons_app(left: Term, right: Term) -> Term {
    crate::term::mk_app_str("lcons", vec![left, right])
}

fn state(q: &str) -> Term {
    constant(q)
}

fn sym_term(s: &str) -> Term {
    constant(s)
}

fn pos_m(l: Term, q: Term, x: Term, r: Term) -> Term {
    pos("m", vec![l, q, x, r])
}

fn neg_m(l: Term, q: Term, x: Term, r: Term) -> Term {
    neg("m", vec![l, q, x, r])
}

// ─────────────────────────────────────────────────────────────────────────────
// Word encoding (§56.21 — identical to NTM)
// ─────────────────────────────────────────────────────────────────────────────

/// Encode input word `w` as `w★` (§56.21), using `○`-chaining (`rcons`).
///
/// ```text
/// non-empty w = c₁…cₙ: [+i(c₁ ○ (c₂ ○ (… ○ cₙ ○ □) …))]
/// empty word:           [+i(□)]
/// ```
pub fn encode_word_atm(word: &[Sym]) -> Star {
    if word.is_empty() {
        vec![pos("i", vec![constant(BLANK)])]
    } else {
        let chain = word
            .iter()
            .rev()
            .fold(constant(BLANK), |acc, c| rcons(sym_term(c), acc));
        vec![pos("i", vec![chain])]
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ∧-transition grouping
// ─────────────────────────────────────────────────────────────────────────────

/// Group `∧`-transitions by `(from_state, read_sym, direction)`.
///
/// For each such key, we collect all `(to_state, write_sym)` targets.
/// Eng §57.4: all branches for the same `(q, c, d)` go into ONE star with
/// k positive outputs.
///
/// Note: Eng's presentation in §57.4 uses a single direction for the whole
/// ∧-group (the star has one `−m(…)` matching `(q,c)` in a specific direction).
/// This implementation requires that all successors of a universal state on the
/// same symbol share the SAME direction. If they do not, they are treated as
/// separate groups (keyed by direction). This is the natural faithful encoding.
type AndGroupKey = (String, String, Dir); // (from, read, dir)

fn group_and_transitions(
    atm: &Atm,
) -> HashMap<AndGroupKey, Vec<(String, String)>> {
    let mut groups: HashMap<AndGroupKey, Vec<(String, String)>> = HashMap::new();
    for (from, read, to, write, dir) in &atm.delta {
        let cls = atm.class.get(from).copied().unwrap_or(Class::Existential);
        if cls == Class::Universal {
            groups
                .entry((from.clone(), read.clone(), *dir))
                .or_default()
                .push((to.clone(), write.clone()));
        }
    }
    groups
}

// ─────────────────────────────────────────────────────────────────────────────
// Constellation encoding (§57.4)
// ─────────────────────────────────────────────────────────────────────────────

/// Build `M★` — the ATM machine constellation — WITHOUT the word star.
///
/// Structure (§57.4):
/// 1. Two q₀ stars (non-empty / empty input) — identical to NTM §56.22.
/// 2. One q_a star (accept) — identical to NTM.
/// 3. One q_r star (reject) — identical to NTM.
/// 4. Transition stars:
///    - For each `∨`-state transition `(q, c, q', c', d)`: ONE star, ONE positive `+m`.
///    - For each `∧`-state group `(q, c, d)` with k successors: ONE star, k positive `+m`.
/// 5. Two malloc stars — identical to NTM §56.22.
pub fn encode_atm(atm: &Atm) -> Constellation {
    let mut c: Constellation = Vec::new();

    // ── (1) q₀ stars (§56.22, §57.4 reuses) ──────────────────────────────────

    // Non-empty input: [−i(C ○ W), +m(□, q₀, C, W)]
    {
        let cv = var("C");
        let w = var("W");
        let input = rcons(cv.clone(), w.clone());
        c.push(vec![
            neg("i", vec![input]),
            pos_m(constant(BLANK), state(&atm.q0), cv, w),
        ]);
    }

    // Empty input: [−i(□), +m(□, q₀, □, □)]
    {
        c.push(vec![
            neg("i", vec![constant(BLANK)]),
            pos_m(constant(BLANK), state(&atm.q0), constant(BLANK), constant(BLANK)),
        ]);
    }

    // ── (2) Accept star ────────────────────────────────────────────────────────

    // [−m(L, q_a, X, R), accept]
    {
        let l = var("L");
        let x = var("X");
        let r = var("R");
        c.push(vec![neg_m(l, state(&atm.q_accept), x, r), constant("accept")]);
    }

    // ── (3) Reject star ────────────────────────────────────────────────────────

    // [−m(L, q_r, X, R), reject]
    {
        let l = var("L");
        let x = var("X");
        let r = var("R");
        c.push(vec![neg_m(l, state(&atm.q_reject), x, r), constant("reject")]);
    }

    // ── (4) Transition stars ───────────────────────────────────────────────────

    // Pre-compute the ∧-groups so we can skip those entries below.
    let and_groups = group_and_transitions(atm);
    // Track which (from, read, dir) ∧ groups have already been emitted.
    let mut emitted_and: std::collections::HashSet<AndGroupKey> = std::collections::HashSet::new();

    for (from, read, to, write, dir) in &atm.delta {
        let cls = atm.class.get(from).copied().unwrap_or(Class::Existential);

        match cls {
            // ── ∨ transition: same shape as NTM (§57.4 para 1) ──────────────
            Class::Existential => {
                let c_sym = sym_term(read);
                let cp = sym_term(write);
                let star = match dir {
                    Dir::L => {
                        let l = var("L");
                        let x = var("X");
                        let r = var("R");
                        let lx = lcons_app(l.clone(), x.clone()); // L ● X
                        let cpr = rcons(cp, r.clone());            // c' ○ R
                        vec![
                            neg_m(lx, state(from), c_sym, r),
                            pos_m(l, state(to), x, cpr),
                        ]
                    }
                    Dir::R => {
                        let l = var("L");
                        let x = var("X");
                        let r = var("R");
                        let xr = rcons(x.clone(), r.clone()); // X ○ R
                        let lcp = lcons_app(l.clone(), cp);   // L ● c'
                        vec![
                            neg_m(l, state(from), c_sym, xr),
                            pos_m(lcp, state(to), x, r),
                        ]
                    }
                    Dir::S => {
                        let l = var("L");
                        let r = var("R");
                        vec![
                            neg_m(l.clone(), state(from), c_sym, r.clone()),
                            pos_m(l, state(to), cp, r),
                        ]
                    }
                };
                c.push(star);
            }

            // ── ∧ transition: ONE star with k positive outputs (§57.4) ───────
            Class::Universal => {
                let key: AndGroupKey = (from.clone(), read.clone(), *dir);
                if emitted_and.contains(&key) {
                    // Already emitted this group.
                    continue;
                }
                emitted_and.insert(key.clone());

                let branches = &and_groups[&key]; // Vec<(to, write)>
                let c_sym = sym_term(read);

                let star = match dir {
                    // §57.4 left case:
                    // [−m(L ● X, q, c, R), +m(L,q₁,X,c₁○R), …, +m(L,qₖ,X,cₖ○R)]
                    Dir::L => {
                        let l = var("L");
                        let x = var("X");
                        let r = var("R");
                        let lx = lcons_app(l.clone(), x.clone());
                        let mut rays = vec![neg_m(lx, state(from), c_sym, r.clone())];
                        for (qi, ci) in branches {
                            let cir = rcons(sym_term(ci), r.clone()); // cᵢ ○ R
                            rays.push(pos_m(l.clone(), state(qi), x.clone(), cir));
                        }
                        rays
                    }
                    // Right case (§57.4 right analogue with L●cᵢ):
                    // [−m(L, q, c, X ○ R), +m(L●c₁,q₁,X,R), …, +m(L●cₖ,qₖ,X,R)]
                    Dir::R => {
                        let l = var("L");
                        let x = var("X");
                        let r = var("R");
                        let xr = rcons(x.clone(), r.clone());
                        let mut rays = vec![neg_m(l.clone(), state(from), c_sym, xr)];
                        for (qi, ci) in branches {
                            let lci = lcons_app(l.clone(), sym_term(ci)); // L ● cᵢ
                            rays.push(pos_m(lci, state(qi), x.clone(), r.clone()));
                        }
                        rays
                    }
                    // Stay case:
                    // [−m(L, q, c, R), +m(L,q₁,c₁,R), …, +m(L,qₖ,cₖ,R)]
                    Dir::S => {
                        let l = var("L");
                        let r = var("R");
                        let mut rays = vec![neg_m(l.clone(), state(from), c_sym, r.clone())];
                        for (qi, ci) in branches {
                            rays.push(pos_m(l.clone(), state(qi), sym_term(ci), r.clone()));
                        }
                        rays
                    }
                };
                c.push(star);
            }
        }
    }

    // ── (5) malloc stars (§56.22) ─────────────────────────────────────────────

    // Left malloc: [−m(□, Q, C, R), +m(□ ● □, Q, C, R)]
    {
        let q = var("Q");
        let cv = var("C");
        let r = var("R");
        let lhs = constant(BLANK);
        let rhs = lcons_app(constant(BLANK), constant(BLANK));
        c.push(vec![
            neg_m(lhs, q.clone(), cv.clone(), r.clone()),
            pos_m(rhs, q, cv, r),
        ]);
    }

    // Right malloc: [−m(L, Q, C, □), +m(L, Q, C, □ ○ □)]
    {
        let q = var("Q");
        let cv = var("C");
        let l = var("L");
        let lhs = constant(BLANK);
        let rhs = rcons(constant(BLANK), constant(BLANK));
        c.push(vec![
            neg_m(l.clone(), q.clone(), cv.clone(), lhs),
            pos_m(l, q, cv, rhs),
        ]);
    }

    c
}

// ─────────────────────────────────────────────────────────────────────────────
// Full constellation (machine + word)
// ─────────────────────────────────────────────────────────────────────────────

/// Build the convenience constellation `M★ + w★` with the word star at index 0.
///
/// Structural tests inspect specific indices; `atm_accepts` uses `encode_atm`
/// and `encode_word_atm` directly.
pub fn atm_constellation(atm: &Atm, input: &[Sym]) -> Constellation {
    let mut phi = encode_atm(atm);
    let word = encode_word_atm(input);
    phi.insert(0, word);
    phi
}

// ─────────────────────────────────────────────────────────────────────────────
// Acceptance (Thm §57.5)
// ─────────────────────────────────────────────────────────────────────────────

/// Check whether `[accept, …, accept]` (k ≥ 1 copies) appears in `↨♭ IEx(M★, w★)`.
///
/// Per Thm §57.5: `M(w) = 1 ⇒ ∃k≥1. [accept, k., accept] ∈ Ψ`.
fn is_accept_star(star: &Star) -> bool {
    !star.is_empty() && star.iter().all(|r| *r == constant("accept"))
}

/// Decide acceptance of `input` by ATM `M` (Thm §57.5).
///
/// Mode: IEx + `↨♭`.
///
/// Returns `true` if some `[accept, …, accept]` (k ≥ 1) star appears in the
/// final interaction space.
pub fn atm_accepts(atm: &Atm, input: &[Sym], fuel: usize) -> bool {
    let phi = encode_atm(atm);
    let psi = encode_word_atm(input);
    let (visible, _) = iex_concealed(&phi, vec![psi], fuel);
    visible.iter().any(is_accept_star)
}

// ─────────────────────────────────────────────────────────────────────────────
// Example ATM
// ─────────────────────────────────────────────────────────────────────────────

/// Build a small ATM that exercises at least one ∧ and one ∨ state.
///
/// Language: words over `{a}` where every prefix position is "approved" by
/// a universal (∧) check.  Concretely this ATM accepts `{a}` (a single `a`)
/// and rejects the empty word and `{aa}`.
///
/// States:
/// - `q0` (∨): read `a` on blank-left tape → go to `qcheck` (∧); read blank → reject.
/// - `qcheck` (∧): universal split.  Needs BOTH:
///   - branch 1: go to `q_end` (∨, stay, write blank): must see blank to accept.
///   - branch 2: go to `q_pos` (∨, stay, write `a`): must also confirm consumed.
/// - `q_end` (∨): on blank → accept.  On `a` → reject.
/// - `q_pos` (∨): on `a` → reject; on blank → accept (confirms tape consumed).
/// - `qa`: accept.
/// - `qr`: reject.
///
/// Transitions (after reading the first `a`; head is now over the remaining input):
/// ```text
/// q0,   a    → (∨) qcheck, a, S    (stay, keep a; delegate to ∧ node)
/// q0,   blank→ (∨) qr,    blank, S (empty input → reject)
/// qcheck, a  → (∧, S) branches: (q_end, blank) AND (q_pos, a)
/// q_end, blank→ (∨) qa, blank, S  (accept: tape is blank)
/// q_end, a   → (∨) qr, a, S       (reject: tape not blank)
/// q_pos, blank→ (∨) qa, blank, S  (accept)
/// q_pos, a   → (∨) qr, a, S       (reject)
/// ```
///
/// On input `[a]`:
/// - q0 reads `rcons(a, blank)` → C=a, W=blank; head on `a`.
/// - q0,a → (∨) go to `qcheck`, write `a`, stay; tape: (blank, qcheck, a, blank).
/// - qcheck, a (∧,S) → two branches:
///   - Branch 1: (q_end, blank, S): tape (blank, q_end, blank, blank).
///   - Branch 2: (q_pos, a, S): tape (blank, q_pos, a, blank).
/// - q_end, blank → qa → accept (contributes 1 `accept`).
/// - q_pos, a → qr → reject (contributes 1 `reject`).
///   But per §57.5 the ∧-star collects ALL branch results into one combined
///   star only when ALL branches accept; here one branch rejects so the overall
///   word is rejected (no all-accept star).
///
/// Hmm — this means `[a]` is REJECTED.  Let's redesign for a cleaner example.
///
/// Simpler ATM: accepts the singleton language `{""}` (empty word) always via
/// a trivial ∧ check.  Empty word → q0 on blank:
/// - `q0, blank → (∧, S) branch 1: (q_mid1, blank), branch 2: (q_mid2, blank)`.
/// - Both `q_mid1` and `q_mid2` are ∨ states: on blank → qa.
/// On empty input, `qcheck` fires, both `q_mid1` and `q_mid2` go to qa, so
/// the fused star has two `accept` rays: `[accept, accept]`.
///
/// On non-empty input `[a]`: `q0` reads `rcons(a, blank)`; no transition fires
/// for `q0` on `a` (we add a reject transition for `q0, a`), so `[reject]` appears.
pub fn example_atm() -> Atm {
    // States: q0 (∧), q_mid1 (∨), q_mid2 (∨), qa, qr.
    let states = vec![
        "q0".into(),
        "q_mid1".into(),
        "q_mid2".into(),
        "qa".into(),
        "qr".into(),
    ];

    let mut class = HashMap::new();
    class.insert("q0".into(), Class::Universal);
    class.insert("q_mid1".into(), Class::Existential);
    class.insert("q_mid2".into(), Class::Existential);
    class.insert("qa".into(), Class::Existential); // unused
    class.insert("qr".into(), Class::Existential); // unused

    // Transitions:
    // q0 (∧) on blank → two branches: (q_mid1, blank, S) AND (q_mid2, blank, S)
    // q0 (∧) on a → reject (single ∧ branch to qr; but all must succeed → rejection)
    // Actually for a single ∧ branch to qr: the result star has one `reject`,
    // no `accept`-only star, so rejection. Correct.
    // q_mid1 (∨) on blank → qa (accept)
    // q_mid2 (∨) on blank → qa (accept)
    // q_mid1 (∨) on a → qr (reject, for robustness)
    // q_mid2 (∨) on a → qr (reject)
    let delta = vec![
        // ∧ branches for q0 on blank: both go to q_mid1/q_mid2
        ("q0".into(), BLANK.into(), "q_mid1".into(), BLANK.into(), Dir::S),
        ("q0".into(), BLANK.into(), "q_mid2".into(), BLANK.into(), Dir::S),
        // ∧ branch for q0 on 'a': go to qr (universal → if any branch rejects, word rejected)
        ("q0".into(), "a".into(), "qr".into(), "a".into(), Dir::S),
        // ∨ transitions for q_mid1
        ("q_mid1".into(), BLANK.into(), "qa".into(), BLANK.into(), Dir::S),
        ("q_mid1".into(), "a".into(), "qr".into(), "a".into(), Dir::S),
        // ∨ transitions for q_mid2
        ("q_mid2".into(), BLANK.into(), "qa".into(), BLANK.into(), Dir::S),
        ("q_mid2".into(), "a".into(), "qr".into(), "a".into(), Dir::S),
    ];

    Atm {
        states,
        gamma: vec!["a".into()],
        delta,
        q0: "q0".into(),
        q_accept: "qa".into(),
        q_reject: "qr".into(),
        class,
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

    // ── Structural test ───────────────────────────────────────────────────────

    /// Verify the structure of `atm_constellation` for `example_atm`.
    ///
    /// The example ATM has:
    ///   - 7 Δ entries: 3 for q0 (∧, but grouped: blank→2 branches = 1 ∧-star,
    ///     a→1 branch = 1 ∧-star), 2 for q_mid1 (∨), 2 for q_mid2 (∨).
    ///   - Stars produced:
    ///     * 1  word star (prepended)
    ///     * 2  q0 stars (non-empty + empty)
    ///     * 1  q_a accept star
    ///     * 1  q_r reject star
    ///     * 1  ∧-star for (q0, blank, S) — 2 positive outputs
    ///     * 1  ∧-star for (q0, a, S)     — 1 positive output (qr branch)
    ///     * 2  ∨-stars for q_mid1 (blank→qa, a→qr)
    ///     * 2  ∨-stars for q_mid2 (blank→qa, a→qr)
    ///     * 2  malloc stars
    ///   Total = 1+2+2+1+1+2+2+2 = 13 stars
    #[test]
    fn atm_constellation_structure() {
        let atm = example_atm();
        let phi = atm_constellation(&atm, &[]);

        // Index 0: word star (1 ray: +i(blank))
        let word_star = &phi[0];
        assert_eq!(word_star.len(), 1, "word star should have 1 ray");
        assert_eq!(word_star[0].head(), Some("+i".to_string()), "word star ray should be +i");

        // Index 1: q₀ non-empty — 2 rays: -i, +m
        let q0_ne = &phi[1];
        assert_eq!(q0_ne.len(), 2);
        assert_eq!(q0_ne[0].head(), Some("-i".to_string()));
        assert_eq!(q0_ne[1].head(), Some("+m".to_string()));

        // Index 2: q₀ empty — 2 rays: -i, +m
        let q0_e = &phi[2];
        assert_eq!(q0_e.len(), 2);
        assert_eq!(q0_e[0].head(), Some("-i".to_string()));
        assert_eq!(q0_e[1].head(), Some("+m".to_string()));

        // Index 3: accept star — 2 rays: -m, accept
        let acc = &phi[3];
        assert_eq!(acc.len(), 2);
        assert_eq!(acc[0].head(), Some("-m".to_string()));
        assert_eq!(acc[1], constant("accept"));

        // Index 4: reject star — 2 rays: -m, reject
        let rej = &phi[4];
        assert_eq!(rej.len(), 2);
        assert_eq!(rej[0].head(), Some("-m".to_string()));
        assert_eq!(rej[1], constant("reject"));

        // Find the ∧-star for (q0, blank, S) — should have 3 rays: 1 neg + 2 pos
        let and_blank = phi.iter().skip(5).find(|star| {
            star.len() == 3
                && star[0].head() == Some("-m".to_string())
                && star[1].head() == Some("+m".to_string())
                && star[2].head() == Some("+m".to_string())
        });
        assert!(
            and_blank.is_some(),
            "should find ∧-star for (q0, blank, S) with 3 rays; phi={:?}",
            &phi[5..]
        );

        // Malloc stars: the last two stars each have 2 rays (-m, +m)
        let n = phi.len();
        assert!(n >= 2, "should have at least 2 stars for malloc");
        let ml = &phi[n - 2];
        let mr = &phi[n - 1];
        assert_eq!(ml.len(), 2);
        assert_eq!(ml[0].head(), Some("-m".to_string()));
        assert_eq!(ml[1].head(), Some("+m".to_string()));
        assert_eq!(mr.len(), 2);
        assert_eq!(mr[0].head(), Some("-m".to_string()));
        assert_eq!(mr[1].head(), Some("+m".to_string()));
    }

    // ── Acceptance tests ──────────────────────────────────────────────────────

    /// Example ATM accepts the empty word: the ∧-star on blank emits 2 branches
    /// that both converge to `accept`, yielding `[accept, accept]` (Thm §57.5, k=2).
    #[test]
    fn example_atm_accepts_empty() {
        let atm = example_atm();
        let result = atm_accepts(&atm, &[], 500);
        assert!(
            result,
            "example ATM should accept empty word (∧ yields [accept,accept])"
        );
    }

    /// Example ATM rejects `[a]`: the ∧-star on `a` leads to `qr` → `[reject]`,
    /// no all-accept star appears.
    #[test]
    fn example_atm_rejects_a() {
        let atm = example_atm();
        let result = atm_accepts(&atm, &word(&["a"]), 500);
        assert!(
            !result,
            "example ATM should reject 'a' (∧ branch goes to qr)"
        );
    }

    /// The `[accept, accept]` star satisfies `is_accept_star` (k=2).
    #[test]
    fn is_accept_star_k2() {
        let star: Star = vec![constant("accept"), constant("accept")];
        assert!(is_accept_star(&star), "[accept, accept] should be an accept star");
    }

    /// A single `[accept]` also satisfies `is_accept_star` (k=1, ∨ case).
    #[test]
    fn is_accept_star_k1() {
        let star: Star = vec![constant("accept")];
        assert!(is_accept_star(&star), "[accept] should be an accept star (k=1)");
    }

    /// `[reject]` does NOT satisfy `is_accept_star`.
    #[test]
    fn is_accept_star_reject() {
        let star: Star = vec![constant("reject")];
        assert!(!is_accept_star(&star), "[reject] should not be an accept star");
    }

    /// A mixed star `[accept, reject]` does NOT satisfy `is_accept_star`.
    #[test]
    fn is_accept_star_mixed() {
        let star: Star = vec![constant("accept"), constant("reject")];
        assert!(!is_accept_star(&star), "[accept, reject] should not be an accept star");
    }

    // ── Word encoding ─────────────────────────────────────────────────────────

    /// Empty word encodes as `[+i(blank)]`.
    #[test]
    fn encode_word_empty() {
        let star = encode_word_atm(&[]);
        assert_eq!(star.len(), 1);
        assert_eq!(star[0].head(), Some("+i".to_string()));
    }

    /// Non-empty word `[a]` encodes as `[+i(rcons(a, blank))]`.
    #[test]
    fn encode_word_a() {
        let star = encode_word_atm(&word(&["a"]));
        assert_eq!(star.len(), 1);
        assert_eq!(star[0].head(), Some("+i".to_string()));
        if let crate::term::TermData::App(_, args) = crate::term::get(star[0]) {
            assert_eq!(args[0].head(), Some("rcons".to_string()), "should be rcons-encoded");
        }
    }
}
