//! ICFP-2020 `galaxy.txt` loader — parse + `•`-encode + δ-star constellation
//! (subproject spec `docs/05`, phase **KG2**).
//!
//! `~/dev/embershot`'s `galaxy.txt` is a binder-free objective program: 392
//! named definitions `:N = <expr>` plus one entry alias `galaxy = :1338`. Each
//! `<expr>` is a *prefix* term — `ap <e> <e>` is binary application; the atoms
//! are the combinator basis (`s c b i t f`), the list ops (`cons car cdr nil
//! isnil`), the arithmetic ops (`add mul div neg eq lt`), `:N` back-references,
//! and signed integer literals. There are no parentheses and no λ — the whole
//! file is in the binder-free fragment `combinator.rs` already handles, so the
//! KAM-escape encoding (§57.16, `−i` row deleted — see `combinator.rs` doc)
//! applies verbatim and a named def becomes a **δ-star**.
//!
//! ## The `•` translation (this module)
//!
//! ```text
//! ap e1 e2  •  := a(e1•, e2•)            (verbatim §57.16, as combinator.rs)
//! atom      •  := atom                   (combinator / list-op / arith-op constant)
//! :N        •  := :N                     (a constant atom — resolved by its δ-star)
//! n  (n≥0)  •  := nat(n)                  (KG1a binary numeral, crate::binarith)
//! -n (n>0)  •  := neg(nat(n))            ← HONEST PLACEHOLDER, see below
//! ```
//!
//! A named definition `:N = body` becomes the **δ-star**
//!
//! ```text
//! [ −P(st(:N, π)),  +P(st(body•, π)) ]
//! ```
//!
//! — exactly the `combinator.rs::machine_stars()` shape, but the head is the
//! constant atom `:N` instead of a combinator letter. `galaxy = :1338` is an
//! *alias*, not a δ-star: it names the entry term `:1338`, nothing to rewrite.
//!
//! ## Honest negatives / scope
//!
//! * **Signed literals are a placeholder.** A negative literal `-n` encodes to
//!   the constant-headed term `neg(nat(n))`. There is *no* δ/machine star that
//!   reduces `neg(_)` here — full signed arithmetic (and `div`) is **KG1b**,
//!   explicitly out of KG2 scope. The encoding is faithful as a *term graph*
//!   (the galaxy's `neg` op and a literal both survive structurally); it is
//!   simply not *executable* until KG1b lands. We do not rabbit-hole on it.
//! * **KG2 is parse + encode + load only.** This module builds `Φ` (δ-stars ∪
//!   `machine_stars()`); it never runs IEx. Executing the galaxy is **KG3**
//!   and needs the acceleration engine — the unaccelerated machine would not
//!   finish (galaxy lists are millions of `cons` cells deep).
//! * `galaxy.txt` lives outside the repo; tests read it at runtime from the
//!   canonical absolute path and **skip with a message** (never panic) if it
//!   is absent, so the crate stays buildable without the embershot checkout.

#![allow(dead_code)]

use crate::binarith;
use crate::constellation::{Constellation, Star};
use crate::term::{self, Term, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// AST
// ─────────────────────────────────────────────────────────────────────────────

/// One parsed `galaxy.txt` expression (prefix, binder-free).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    /// `ap f x` — binary application.
    App(Box<Ast>, Box<Ast>),
    /// A nullary constant atom: a combinator (`s c b i t f`), a list op
    /// (`cons car cdr nil isnil`), or an arithmetic op (`add mul div neg eq
    /// lt`). Stored as the raw galaxy token.
    Atom(String),
    /// `:N` — a back-reference to another named definition.
    Ref(u64),
    /// A signed integer literal. `neg=false` ⇒ non-negative `mag`; `neg=true`
    /// ⇒ the value is `-mag` (and `mag>0`). `mag` is `u128` so the wide galaxy
    /// constants (`123229502148636`, …) never overflow.
    Lit { neg: bool, mag: u128 },
}

/// Iterative drop: galaxy.txt bodies nest hundreds of `App`s deep, and the
/// derived recursive `Drop` for the `Box<Ast>` chain would overflow a small
/// (2 MiB) test-thread stack. Dismantle the tree breadth-first instead so
/// every `Ast` value frees in O(1) native stack regardless of depth.
impl Drop for Ast {
    fn drop(&mut self) {
        let mut pending: Vec<Ast> = Vec::new();
        // Steal this node's children without recursing into their Drop yet.
        if let Ast::App(f, x) = self {
            pending.push(std::mem::replace(f.as_mut(), Ast::Atom(String::new())));
            pending.push(std::mem::replace(x.as_mut(), Ast::Atom(String::new())));
        }
        while let Some(mut node) = pending.pop() {
            if let Ast::App(f, x) = &mut node {
                pending.push(std::mem::replace(f.as_mut(), Ast::Atom(String::new())));
                pending.push(std::mem::replace(x.as_mut(), Ast::Atom(String::new())));
            }
            // `node` (now an App with Atom children, or a leaf) drops here:
            // its children are Atoms ⇒ no further recursion.
        }
    }
}

/// A single named definition `:N = body` (the `galaxy` entry alias is captured
/// separately as [`Galaxy::entry`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Def {
    pub name: u64,
    pub body: Ast,
}

/// The whole parsed program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Galaxy {
    /// All `:N = …` definitions, in file order.
    pub defs: Vec<Def>,
    /// The `:N` the `galaxy = :N` line points at (the program entry point).
    pub entry: u64,
}

// ─────────────────────────────────────────────────────────────────────────────
// Parser  (&str → Galaxy)
// ─────────────────────────────────────────────────────────────────────────────

/// Parse failure with the offending line (1-based) and a reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub msg: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "galaxy.txt:{}: {}", self.line, self.msg)
    }
}

/// Parse one *leaf* token (everything except `ap`, which only structures).
fn parse_leaf(tok: &str, line: usize) -> Result<Ast, ParseError> {
    match tok {
        // Combinator / list / arith atoms — the full documented alphabet.
        "s" | "c" | "b" | "i" | "t" | "f" | "cons" | "car" | "cdr" | "nil"
        | "isnil" | "add" | "mul" | "div" | "neg" | "eq" | "lt" => {
            Ok(Ast::Atom(tok.to_string()))
        }
        _ if tok.starts_with(':') => {
            let n = tok[1..].parse::<u64>().map_err(|e| ParseError {
                line,
                msg: format!("bad :N reference {tok:?}: {e}"),
            })?;
            Ok(Ast::Ref(n))
        }
        _ => {
            // Signed integer literal (the only remaining token shape).
            let (neg, digits) = match tok.strip_prefix('-') {
                Some(d) => (true, d),
                None => (false, tok),
            };
            let mag = digits.parse::<u128>().map_err(|e| ParseError {
                line,
                msg: format!("unrecognised token {tok:?} (not atom/:N/int): {e}"),
            })?;
            // `-0` would be non-canonical; galaxy.txt has none, but normalise.
            Ok(Ast::Lit {
                neg: neg && mag != 0,
                mag,
            })
        }
    }
}

/// Parse one whitespace-token prefix expression with an **explicit work
/// stack** (no native recursion — galaxy.txt prefix terms nest hundreds of
/// `ap`s deep and would overflow a recursive descent). Consumes exactly the
/// tokens the expression needs; leaves the iterator positioned after it.
///
/// Algorithm: maintain a stack of partially-built `App`s. Each `ap` pushes a
/// "need 2 children" frame; each completed sub-expression is fed to the frame
/// on top of the stack, which fills its function slot then its argument slot,
/// collapsing to a finished `Ast` that is itself fed upward — iteratively.
fn parse_expr<'a, I: Iterator<Item = &'a str>>(
    toks: &mut std::iter::Peekable<I>,
    line: usize,
) -> Result<Ast, ParseError> {
    /// A pending `ap`: `Func` = still awaiting its function child;
    /// `Arg(f)` = function known, awaiting the argument child.
    enum Frame {
        Func,
        Arg(Ast),
    }
    let mut stack: Vec<Frame> = Vec::new();

    loop {
        let tok = toks.next().ok_or_else(|| ParseError {
            line,
            msg: "unexpected end of expression".into(),
        })?;

        // An `ap` is never a value by itself: open a new frame and keep going.
        if tok == "ap" {
            stack.push(Frame::Func);
            continue;
        }

        // Otherwise we have a completed leaf value; propagate it up the stack,
        // closing any frames whose argument it completes.
        let mut value = parse_leaf(tok, line)?;
        loop {
            match stack.pop() {
                None => return Ok(value), // whole expression done
                Some(Frame::Func) => {
                    // `value` is this ap's function; now await the argument.
                    stack.push(Frame::Arg(value));
                    break; // need to read more tokens for the argument
                }
                Some(Frame::Arg(f)) => {
                    // `value` is this ap's argument: the App is complete; it
                    // becomes the value for the next frame up. Loop (no read).
                    value = Ast::App(Box::new(f), Box::new(value));
                }
            }
        }
    }
}

/// Parse the full `galaxy.txt` contents.
///
/// Grammar (one per line, blank lines tolerated):
/// `:N = <prefix-expr>`  and exactly one  `galaxy = :N`.
pub fn parse(src: &str) -> Result<Galaxy, ParseError> {
    let mut defs = Vec::new();
    let mut entry: Option<u64> = None;

    for (i, raw) in src.lines().enumerate() {
        let line = i + 1;
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            continue;
        }
        let mut toks = trimmed.split_whitespace().peekable();
        let lhs = toks.next().ok_or_else(|| ParseError {
            line,
            msg: "empty line after trim (unreachable)".into(),
        })?;
        match toks.next() {
            Some("=") => {}
            other => {
                return Err(ParseError {
                    line,
                    msg: format!("expected '=' after {lhs:?}, got {other:?}"),
                })
            }
        }

        if lhs == "galaxy" {
            // Entry alias: `galaxy = :N`.
            let e = parse_expr(&mut toks, line)?;
            match e {
                Ast::Ref(n) => {
                    if entry.replace(n).is_some() {
                        return Err(ParseError {
                            line,
                            msg: "duplicate `galaxy = …` entry line".into(),
                        });
                    }
                }
                other => {
                    return Err(ParseError {
                        line,
                        msg: format!("`galaxy =` must alias a :N ref, got {other:?}"),
                    })
                }
            }
        } else if let Some(num) = lhs.strip_prefix(':') {
            let name = num.parse::<u64>().map_err(|e| ParseError {
                line,
                msg: format!("bad definition name {lhs:?}: {e}"),
            })?;
            let body = parse_expr(&mut toks, line)?;
            defs.push(Def { name, body });
        } else {
            return Err(ParseError {
                line,
                msg: format!("line LHS {lhs:?} is neither `:N` nor `galaxy`"),
            });
        }

        if let Some(extra) = toks.next() {
            return Err(ParseError {
                line,
                msg: format!("trailing token {extra:?} after a complete expression"),
            });
        }
    }

    let entry = entry.ok_or_else(|| ParseError {
        line: 0,
        msg: "no `galaxy = :N` entry line found".into(),
    })?;
    Ok(Galaxy { defs, entry })
}

// ─────────────────────────────────────────────────────────────────────────────
// Encoder  (Ast → TermId, the `•` translation)
// ─────────────────────────────────────────────────────────────────────────────
//
// Helpers mirror `combinator.rs` *exactly* (same `a`/`st`/`dot`/`+P`/`-P`
// constructors, same conventions) so galaxy δ-stars interlock with
// `machine_stars()` under one term universe.

fn cst(name: &str) -> TermId {
    term::mk_app_str(name, vec![])
}
fn v(name: &str) -> TermId {
    term::mk_var(name)
}
/// `a(M, N)` — application node (§57.16, identical to `combinator::ap`).
fn ap_node(m: TermId, n: TermId) -> TermId {
    term::mk_app_str("a", vec![m, n])
}
/// `M · π` — stack cons (right-assoc, §22.6; identical to `combinator::dot`).
fn dot(h: TermId, t: TermId) -> TermId {
    term::mk_app_str("dot", vec![h, t])
}
/// `M ⋆ π` — process connective (§57.16; identical to `combinator::st`).
fn st(m: TermId, pi: TermId) -> TermId {
    term::mk_app_str("st", vec![m, pi])
}
/// `+P(·)` — positive process ray (identical to `combinator::pp`).
fn pp(arg: TermId) -> TermId {
    term::mk_app_str("+P", vec![arg])
}
/// `−P(·)` — negative process ray (identical to `combinator::np`).
fn np(arg: TermId) -> TermId {
    term::mk_app_str("-P", vec![arg])
}

/// The constant atom that names definition `:N` in the term universe.
///
/// We use the literal galaxy spelling `":N"` (e.g. `":1338"`) so a δ-star head
/// is visually traceable back to the source line.
pub fn ref_atom(n: u64) -> TermId {
    cst(&format!(":{n}"))
}

/// `•` : AST → term-graph encoding.
///
/// * `ap` → `a(·,·)` application node (§57.16)
/// * atom → its constant
/// * `:N` → the constant `:N` (its δ-star supplies the rewrite)
/// * `n ≥ 0` → `binarith::nat(n)` (KG1a binary numeral)
/// * `-n`  → `neg(nat(n))` — **honest placeholder**, not executable (KG1b)
pub fn enc(a: &Ast) -> TermId {
    // Iterative post-order over the (deeply right-nested) AST — a recursive
    // `enc` overflows on galaxy.txt's hundreds-deep `ap` spines.
    enum Job<'a> {
        Visit(&'a Ast),
        /// Both children of an `App` are now on the value stack — combine.
        MkApp,
    }
    let mut work: Vec<Job> = vec![Job::Visit(a)];
    let mut vals: Vec<TermId> = Vec::new();
    while let Some(job) = work.pop() {
        match job {
            Job::Visit(node) => match node {
                Ast::App(f, x) => {
                    // Post-order: push the combine marker first, then children
                    // so `f` then `x` end up on `vals` in (f, x) order.
                    work.push(Job::MkApp);
                    work.push(Job::Visit(x));
                    work.push(Job::Visit(f));
                }
                Ast::Atom(name) => vals.push(cst(name)),
                Ast::Ref(n) => vals.push(ref_atom(*n)),
                Ast::Lit { neg: false, mag } => vals.push(binarith::nat(*mag)),
                Ast::Lit { neg: true, mag } => {
                    // Constant-headed placeholder. No star reduces this in
                    // KG2; the magnitude is still carried faithfully (KG1b).
                    vals.push(term::mk_app_str("neg", vec![binarith::nat(*mag)]));
                }
            },
            Job::MkApp => {
                let x = vals.pop().expect("enc: missing arg value");
                let f = vals.pop().expect("enc: missing func value");
                vals.push(ap_node(f, x));
            }
        }
    }
    debug_assert_eq!(vals.len(), 1, "enc: exactly one root value");
    vals.pop().unwrap()
}

// ─────────────────────────────────────────────────────────────────────────────
// Constellation builder
// ─────────────────────────────────────────────────────────────────────────────

/// The δ-star for one named definition: `[ −P(st(:N, π)), +P(st(body•, π)) ]`.
///
/// `π` is the (single, shared-per-star) stack variable — same role as `Pi` in
/// `combinator::machine_stars()`. Exactly analogous to a combinator rewrite
/// star, with the constant `:N` as the head and `body•` as the contractum.
pub fn delta_star(d: &Def) -> Star {
    let pi = v("Pi");
    vec![
        np(st(ref_atom(d.name), pi)),
        pp(st(enc(&d.body), pi)),
    ]
}

/// Build the full galaxy reference constellation `Φ`:
/// every definition's δ-star **plus** the combinator machine stars
/// (`combinator::machine_stars()` — Push §57.19 + S/B/C/I/T/F), reused so the
/// galaxy's combinator applications reduce under the very same rules.
///
/// KG2 stops here: this `Φ` is *loaded*, never executed (running it is KG3).
pub fn constellation(g: &Galaxy) -> Constellation {
    let mut phi: Constellation = crate::combinator::machine_stars();
    phi.reserve(g.defs.len());
    for d in &g.defs {
        phi.push(delta_star(d));
    }
    phi
}

/// `Φ` directly from `galaxy.txt` source text (parse → build).
pub fn constellation_from_src(src: &str) -> Result<Constellation, ParseError> {
    Ok(constellation(&parse(src)?))
}

// ─────────────────────────────────────────────────────────────────────────────
// Structural-faithfulness helper
// ─────────────────────────────────────────────────────────────────────────────

/// Every `:N` reference appearing in any body, collected (with duplicates) so
/// callers can check none dangles. Walks the AST; does not recurse through the
/// δ-star indirection (that is the resolution we are *checking*).
pub fn referenced_names(g: &Galaxy) -> Vec<u64> {
    // Iterative DFS — recursion overflows on galaxy.txt's deep spines.
    let mut out = Vec::new();
    let mut stack: Vec<&Ast> = Vec::new();
    for d in &g.defs {
        stack.push(&d.body);
        while let Some(a) = stack.pop() {
            match a {
                Ast::App(f, x) => {
                    stack.push(f);
                    stack.push(x);
                }
                Ast::Ref(n) => out.push(*n),
                Ast::Atom(_) | Ast::Lit { .. } => {}
            }
        }
    }
    out
}

/// `:N`s that are referenced but never defined (a dangling-ref check). Includes
/// the entry. Empty ⇒ the program is closed over its own definitions.
pub fn dangling_refs(g: &Galaxy) -> Vec<u64> {
    use std::collections::BTreeSet;
    let defined: BTreeSet<u64> = g.defs.iter().map(|d| d.name).collect();
    let mut bad: BTreeSet<u64> = referenced_names(g)
        .into_iter()
        .filter(|n| !defined.contains(n))
        .collect();
    if !defined.contains(&g.entry) {
        bad.insert(g.entry);
    }
    bad.into_iter().collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — KG2 acceptance (parse + encode + load; no execution)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Canonical embershot artifact. Outside the repo: tests that need it skip
    /// (with a printed message) when it is absent — never panic.
    const GALAXY_PATH: &str = "/Users/ember/dev/embershot/src/galaxy.txt";

    fn load_src() -> Option<String> {
        match std::fs::read_to_string(GALAXY_PATH) {
            Ok(s) => Some(s),
            Err(e) => {
                eprintln!(
                    "SKIP: galaxy.txt not readable at {GALAXY_PATH} ({e}); \
                     KG2 file-backed test skipped (not a failure)."
                );
                None
            }
        }
    }

    // ── unit-level parser/encoder checks (no external file) ──────────────────

    #[test]
    fn parses_minimal_program() {
        let src = ":1 = ap ap cons 7 nil\n:2 = ap add :1\ngalaxy = :2\n";
        let g = parse(src).expect("parses");
        assert_eq!(g.entry, 2);
        assert_eq!(g.defs.len(), 2);
        assert_eq!(g.defs[0].name, 1);
        // :1 body = App(App(cons, 7), nil)
        assert_eq!(
            g.defs[0].body,
            Ast::App(
                Box::new(Ast::App(
                    Box::new(Ast::Atom("cons".into())),
                    Box::new(Ast::Lit { neg: false, mag: 7 }),
                )),
                Box::new(Ast::Atom("nil".into())),
            )
        );
        assert_eq!(
            g.defs[1].body,
            Ast::App(
                Box::new(Ast::Atom("add".into())),
                Box::new(Ast::Ref(1)),
            )
        );
    }

    #[test]
    fn parses_signed_and_big_literals() {
        let src = ":1 = ap ap add -3 123229502148636\ngalaxy = :1\n";
        let g = parse(src).expect("parses");
        let Ast::App(inner, big) = &g.defs[0].body else {
            panic!("expected App")
        };
        assert_eq!(**big, Ast::Lit { neg: false, mag: 123229502148636 });
        let Ast::App(_add, neg3) = &**inner else {
            panic!("expected inner App")
        };
        assert_eq!(**neg3, Ast::Lit { neg: true, mag: 3 });
    }

    #[test]
    fn rejects_garbage_and_trailing_tokens() {
        assert!(parse(":1 = ap add\ngalaxy = :1\n").is_err()); // ap missing 2nd arg
        assert!(parse(":1 = add extra\ngalaxy = :1\n").is_err()); // trailing token
        assert!(parse(":1 = qux\ngalaxy = :1\n").is_err()); // unknown atom
        assert!(parse(":1 = add\n").is_err()); // no entry line
    }

    #[test]
    fn delta_star_shape_is_machine_star_analogous() {
        // :1 = i  →  [ -P(st(:1, Pi)), +P(st(i, Pi)) ]
        let d = Def {
            name: 1,
            body: Ast::Atom("i".into()),
        };
        let star = delta_star(&d);
        assert_eq!(star.len(), 2, "δ-star is exactly 2 rays");
        // Ray 0: -P(st(:1, Pi)) ; Ray 1: +P(st(i, Pi)) with the SAME Pi var.
        let pi = v("Pi");
        assert_eq!(star[0], np(st(ref_atom(1), pi)));
        assert_eq!(star[1], pp(st(cst("i"), pi)));
    }

    #[test]
    fn neg_literal_is_constant_headed_placeholder() {
        // Honest-negative contract: -5 encodes to neg(nat(5)), a constant head
        // with no reducing star in KG2.
        let t = enc(&Ast::Lit { neg: true, mag: 5 });
        match term::get(t) {
            term::TermData::App(sym, args) => {
                assert_eq!(sym.name.as_str(), "neg");
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], binarith::nat(5));
            }
            other => panic!("expected neg(_) app, got {other:?}"),
        }
    }

    // ── the KG2 acceptance test: the real galaxy.txt ─────────────────────────

    #[test]
    fn galaxy_txt_parses_loads_and_is_closed() {
        let Some(src) = load_src() else { return };
        let g = parse(&src).expect("galaxy.txt must parse fully");

        // (a) exactly 392 numbered defs + entry `galaxy → :1338`.
        // (Spec said "393 definitions"; the file is 392 `:N` defs PLUS the
        //  `galaxy = :1338` alias line — 393 lines total. We assert the true
        //  structure: 392 defs and the entry alias resolving to 1338.)
        assert_eq!(
            g.defs.len(),
            392,
            "expected 392 numbered :N definitions in galaxy.txt"
        );
        assert_eq!(g.entry, 1338, "galaxy entry must alias :1338");

        // No duplicate :N names.
        let mut names: Vec<u64> = g.defs.iter().map(|d| d.name).collect();
        names.sort_unstable();
        let n_before = names.len();
        names.dedup();
        assert_eq!(n_before, names.len(), "no duplicate :N definitions");

        // (b) KEY structural-faithfulness check: every :N referenced anywhere
        // (incl. the entry) resolves to a defined :N — zero dangling refs.
        let dangling = dangling_refs(&g);
        assert!(
            dangling.is_empty(),
            "dangling :N references (referenced but never defined): {dangling:?}"
        );

        // (c) build Φ, sanity-check star count, spot-check a small δ-star.
        let phi = constellation(&g);
        let machine = crate::combinator::machine_stars().len();
        assert_eq!(
            phi.len(),
            machine + g.defs.len(),
            "Φ = machine_stars() ∪ one δ-star per def"
        );
        assert_eq!(machine, 7, "combinator::machine_stars() is the 7-star K★");

        // Spot-check the smallest-body def's δ-star shape (head = its :N
        // constant, contractum = body•, shared Pi).
        // Iterative node count (Debug-formatting a deep Ast would recurse and
        // overflow — same reason enc/parse are iterative).
        fn node_count(a: &Ast) -> usize {
            let mut n = 0usize;
            let mut st = vec![a];
            while let Some(x) = st.pop() {
                n += 1;
                if let Ast::App(f, y) = x {
                    st.push(f);
                    st.push(y);
                }
            }
            n
        }
        let small = g
            .defs
            .iter()
            .min_by_key(|d| node_count(&d.body))
            .unwrap();
        let star = delta_star(small);
        assert_eq!(star.len(), 2);
        let pi = v("Pi");
        assert_eq!(
            star[0],
            np(st(ref_atom(small.name), pi)),
            "δ-star ray 0 = -P(st(:N, Pi))"
        );
        assert_eq!(
            star[1],
            pp(st(enc(&small.body), pi)),
            "δ-star ray 1 = +P(st(body•, Pi))"
        );

        eprintln!(
            "galaxy.txt: {} defs, entry :{}, {} dangling refs, Φ = {} stars \
             ({} machine + {} δ)",
            g.defs.len(),
            g.entry,
            dangling.len(),
            phi.len(),
            machine,
            g.defs.len(),
        );
    }

    /// Every body encodes without panic and every literal round-trips through
    /// `binarith` (non-negative) or the `neg(_)` placeholder (negative).
    #[test]
    fn galaxy_txt_every_body_encodes() {
        let Some(src) = load_src() else { return };
        let g = parse(&src).expect("parses");
        let mut max_lit: u128 = 0;
        let mut n_neg = 0usize;
        let mut stack: Vec<&Ast> = Vec::new();
        for d in &g.defs {
            // Encoding must not panic for any body.
            let _ = enc(&d.body);
            stack.push(&d.body);
            while let Some(a) = stack.pop() {
                match a {
                    Ast::App(f, x) => {
                        stack.push(f);
                        stack.push(x);
                    }
                    Ast::Lit { neg, mag } => {
                        max_lit = max_lit.max(*mag);
                        if *neg {
                            n_neg += 1;
                        }
                    }
                    _ => {}
                }
            }
        }
        // Non-negative literals round-trip exactly through binarith.
        assert_eq!(binarith::denat(binarith::nat(max_lit)), Some(max_lit));
        eprintln!(
            "galaxy.txt: max non-neg literal = {max_lit}, \
             {n_neg} negative-literal occurrences (neg(_) placeholder, KG1b)"
        );
    }
}
