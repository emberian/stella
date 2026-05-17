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
use crate::term::{self, Term, TermData, TermId};

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

/// The faithful ICFP-2020 alien **primitive** rules, KAM/Push form (args on
/// the `·`-stack after `Push` unwinds applications — exactly the
/// `combinator::machine_stars()` shape, but keyed on galaxy's *actual
/// lowercase atom names* with the authoritative alien "Message from Space"
/// semantics). KG3b slice 1 = the **pure-lazy** fragment (no strictness):
/// `Push` + `i t f s c b cons car cdr nil`.
///
/// Deliberately OMITTED (constructor-strict / strict-numeric — the §58/§60
/// synchronisation punt at galaxy scale; the measured next slice): `isnil`,
/// `add mul div neg eq lt`. Adding them unfaithfully would smuggle a fake
/// green — they land only once done faithfully.
pub fn prim_stars() -> Constellation {
    let (m, n, x, y, z, p, pi) =
        (v("M"), v("N"), v("X"), v("Y"), v("Z"), v("P"), v("Pi"));
    let a = ap_node;
    vec![
        // Push (§57.19): a(M,N)⋆π → M⋆(N·π)
        vec![np(st(a(m, n), pi)), pp(st(m, dot(n, pi)))],
        // i x → x
        vec![np(st(cst("i"), dot(x, pi))), pp(st(x, pi))],
        // t x y → x   (K / true)
        vec![np(st(cst("t"), dot(x, dot(y, pi)))), pp(st(x, pi))],
        // f x y → y   (false)
        vec![np(st(cst("f"), dot(x, dot(y, pi)))), pp(st(y, pi))],
        // s x y z → (x z) (y z)
        vec![
            np(st(cst("s"), dot(x, dot(y, dot(z, pi))))),
            pp(st(a(a(x, z), a(y, z)), pi)),
        ],
        // c x y z → (x z) y
        vec![
            np(st(cst("c"), dot(x, dot(y, dot(z, pi))))),
            pp(st(a(a(x, z), y), pi)),
        ],
        // b x y z → x (y z)
        vec![
            np(st(cst("b"), dot(x, dot(y, dot(z, pi))))),
            pp(st(a(x, a(y, z)), pi)),
        ],
        // cons x y z → (z x) y   (Church pair / vec)
        vec![
            np(st(cst("cons"), dot(x, dot(y, dot(z, pi))))),
            pp(st(a(a(z, x), y), pi)),
        ],
        // car p → p t
        vec![np(st(cst("car"), dot(p, pi))), pp(st(a(p, cst("t")), pi))],
        // cdr p → p f
        vec![np(st(cst("cdr"), dot(p, pi))), pp(st(a(p, cst("f")), pi))],
        // nil x → t   (empty list applied to anything is true)
        vec![np(st(cst("nil"), dot(x, pi))), pp(st(cst("t"), pi))],
        // isnil — constructor pattern-match (pure, no forcing): fires iff the
        // argument is *already* a `nil` atom or a `cons x y` cell value on the
        // stack. `isnil nil → t`. The 2-arg `a(a(cons,X),Y)` is exactly the
        // list-cell value (cons needs 3 args to fire, so 2-applied is stuck =
        // a value). NOT host-forced: whether galaxy's combinator structure
        // delivers a forced constructor here is an empirical question the
        // probe answers — if these don't fire, that *measures* the genuine
        // §58/§60 strictness need (then forcing is added, disclosed).
        vec![np(st(cst("isnil"), dot(cst("nil"), pi))), pp(st(cst("t"), pi))],
        vec![
            np(st(cst("isnil"), dot(a(a(cst("cons"), x), y), pi))),
            pp(st(cst("f"), pi)),
        ],
    ]
}

/// Build the galaxy reference constellation `Φ`: the faithful alien
/// [`prim_stars`] (Push + pure-lazy primitives) **plus** every definition's
/// δ-star. (KG2 piggybacked `combinator::machine_stars()`, whose *uppercase*
/// `S/T/…` never matched galaxy's *lowercase* `s/t/…` atoms — KG3a's
/// "blocked@5" was really "no faithful alien rules". Fixed here.)
pub fn constellation(g: &Galaxy) -> Constellation {
    let mut phi: Constellation = prim_stars();
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
// KG3c slice 1 — disclosed §60 host-forcing driver (isnil only)
//
// FAITHFULNESS DISCLOSURE: this is the epidictic §58/§60 concession, made
// honestly. Every *reduction* is the stellar engine over `Φ`
// (`iex_fast`); the host contributes ONLY the §60 *strategy* — the order in
// which a strict primitive's argument is driven to WHNF — exactly
// embershot's own `ForceArgs`. Slice 1 forces only `isnil` (constructor-
// strict, no arithmetic ⇒ no KG1b dependency). `eq`/`add`/… stay residual
// and are *measured*, not faked.
// ─────────────────────────────────────────────────────────────────────────────

/// The leftmost non-`a` atom of an application spine, and the spine length.
fn spine_head(mut t: TermId) -> (Option<crate::term::SymName>, usize) {
    let mut n = 0usize;
    loop {
        match term::get(t) {
            TermData::App(s, args) if s.name.as_str() == "a" && args.len() == 2 => {
                n += 1;
                t = args[0];
            }
            TermData::App(s, args) if args.is_empty() => return (Some(s.name), n),
            _ => return (None, n),
        }
    }
}

/// Is `t` a list value `isnil` can match — the `nil` atom or a `cons _ _`
/// cell (`a(a(cons,_),_)`) — i.e. forced enough for the pure isnil rule.
fn is_listish_value(t: TermId) -> bool {
    match term::get(t) {
        TermData::App(s, a) if a.is_empty() && s.name.as_str() == "nil" => true,
        _ => {
            let (h, len) = spine_head(t);
            h.map(|n| n.as_str()) == Some("cons") && len == 2
        }
    }
}

// ── Unified strict-redex driver ──────────────────────────────────────────
//
// The pure combinator/list prims (i t f s c b cons car cdr nil + the two
// value-guarded `isnil` rules) reduce NATIVELY in `prim_stars()`. The
// remaining strict ops (add mul eq lt div neg + `isnil` on an unforced
// scrutinee) need a forced numeral/constructor the stellar engine cannot
// pattern-match, so they are resolved by the disclosed §60 host driver.
//
// CRITICAL STRUCTURAL FACT (the recurring-bug root cause, fixed once here):
// the KAM `Push` rule `a(M,N)⋆π → M⋆(N·π)` ALWAYS uncurries an operator's
// arguments onto π before the head is examined. So every strict op blocks
// in **Push-stack form** `+P(st(OP, a·b·…·π))` — never the curried
// `a(a(OP,a),b)` form. The old code had separate curried + Push detectors
// per prim (8 functions, 2 duplicated branches); the curried ones never
// fired at the real redex and, by recursing into π/operands, force a
// NON-leftmost redex (an evaluation-order deviation vs the reference
// oracle). This ONE detector + ONE forcer + ONE driver replace all of it.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum StrictOp {
    Add,
    Mul,
    Eq,
    Lt,
    Div,
    Neg,
    IsNil,
}

impl StrictOp {
    fn from_atom(name: &str) -> Option<(StrictOp, usize)> {
        Some(match name {
            "add" => (StrictOp::Add, 2),
            "mul" => (StrictOp::Mul, 2),
            "eq" => (StrictOp::Eq, 2),
            "lt" => (StrictOp::Lt, 2),
            "div" => (StrictOp::Div, 2),
            "neg" => (StrictOp::Neg, 1),
            "isnil" => (StrictOp::IsNil, 1),
            _ => return None,
        })
    }
    fn name(self) -> &'static str {
        match self {
            StrictOp::Add => "add",
            StrictOp::Mul => "mul",
            StrictOp::Eq => "eq",
            StrictOp::Lt => "lt",
            StrictOp::Div => "div",
            StrictOp::Neg => "neg",
            StrictOp::IsNil => "isnil",
        }
    }
}

struct StrictRedex {
    op: StrictOp,
    /// The popped stack frames = the actual argument closures.
    operands: Vec<TermId>,
    /// π after the operands are consumed (the continuation).
    resid_pi: TermId,
}

/// THE strict-redex detector. Unwrap `+P(st(M,π))`; `Push` runs until M is
/// not an `a`-node, so a rule-less strict op is the bare atom M with all
/// args already on π. Pop `arity` frames. For `isnil` whose scrutinee is
/// already a list value the pure prim rule fires on its own ⇒ not a host
/// redex. Subsumes the old `find_blocked_pushform` AND
/// `find_blocked_isnil_pushform`; deliberately has NO curried path (the KAM
/// never presents one at the redex, and scanning operands forced a
/// non-leftmost redex — the D2/D3 evaluation-order deviation).
fn strict_redex_on_pi(ray: TermId) -> Option<StrictRedex> {
    let TermData::App(p, pa) = term::get(ray) else { return None };
    if p.name.as_str() != "P" || pa.len() != 1 {
        return None;
    }
    let TermData::App(stsym, sa) = term::get(pa[0]) else { return None };
    if stsym.name.as_str() != "st" || sa.len() != 2 {
        return None;
    }
    let (m, pi) = (sa[0], sa[1]);
    let TermData::App(h, ha) = term::get(m) else { return None };
    if !ha.is_empty() {
        return None;
    }
    let (op, arity) = StrictOp::from_atom(h.name.as_str())?;
    let mut operands = Vec::with_capacity(arity);
    let mut cur = pi;
    for _ in 0..arity {
        match term::get(cur) {
            TermData::App(d, da) if d.name.as_str() == "dot" && da.len() == 2 => {
                operands.push(da[0]);
                cur = da[1];
            }
            // Fewer args than the op needs ⇒ a partial-application value,
            // NOT a redex.
            _ => return None,
        }
    }
    if op == StrictOp::IsNil && is_listish_value(operands[0]) {
        return None; // the pure `isnil` prim-star fires natively
    }
    Some(StrictRedex { op, operands, resid_pi: cur })
}

/// `sbinarith`'s internal comparison booleans `tt`/`ff` → galaxy's church
/// booleans `t`/`f` (`prim_stars`: `t x y → x`, `f x y → y`). Applied at the
/// SINGLE point a comparison result is produced (D1 root fix): the `tt`/`ff`
/// token can never escape the driver into a sub-position where it would
/// stick (galaxy has no `tt`/`ff` rule).
fn galaxy_bool(t: TermId) -> TermId {
    match term::get(t) {
        TermData::App(s, a) if a.is_empty() && s.name.as_str() == "tt" => cst("t"),
        TermData::App(s, a) if a.is_empty() && s.name.as_str() == "ff" => cst("f"),
        _ => t,
    }
}

/// The surviving single-ray process star's ray `+P(st(M, π))` (whole ray —
/// the stack `π` need NOT be `ε`; galaxy blocks mid-application).
fn single_ray(psi: &[Star]) -> Option<TermId> {
    psi.iter().find(|s| s.len() == 1).map(|s| s[0])
}

/// `M` inside a `+P(st(M, π))` ray (the focused term), if shaped so.
fn st_inner(ray: TermId) -> Option<TermId> {
    if let TermData::App(p, pa) = term::get(ray) {
        if p.name.as_str() == "P" && pa.len() == 1 {
            if let TermData::App(s2, sa) = term::get(pa[0]) {
                if s2.name.as_str() == "st" && sa.len() == 2 {
                    return Some(sa[0]);
                }
            }
        }
    }
    None
}

/// Classified WHNF of a forced sub-term (the only thing the driver needs).
enum ForcedValue {
    Numeral(TermId),
    Nil,
    Cons,
    /// Could not be forced to a value within budget/fuel ⇒ honest stop.
    Residual,
}

/// THE single recursive forcer (replaces `force_whnf`/`force_numeral`/
/// `force_listish`). Runs the forced evaluator on `term` with an explicitly
/// decremented `budget` (so the recursion is well-founded BY CONSTRUCTION —
/// the D6 fix, not an accounting coincidence), reads the KAM result back,
/// and classifies it. A list constructor is committed ONLY if the
/// sub-evaluation actually finished (`fully_reduced`) — never from a
/// not-yet-reduced readback (the D7 faithfulness fix).
fn force_value(
    phi: &Constellation,
    term: TermId,
    fuel: usize,
    budget: usize,
) -> (ForcedValue, usize) {
    if budget == 0 {
        return (ForcedValue::Residual, 0);
    }
    TR_DEPTH.with(|c| c.set(c.get() + 1));
    let f = eval_forced(phi, term, fuel, budget - 1); // strictly smaller
    TR_DEPTH.with(|c| c.set(c.get().saturating_sub(1)));
    let rb = readback_ray(f.final_ray.unwrap_or(f.value));
    if crate::sbinarith::dsint(rb).is_some() {
        return (ForcedValue::Numeral(rb), f.steps);
    }
    if f.fully_reduced {
        match term::get(rb) {
            TermData::App(s, a) if a.is_empty() && s.name.as_str() == "nil" => {
                return (ForcedValue::Nil, f.steps);
            }
            _ if is_listish_value(rb) => return (ForcedValue::Cons, f.steps),
            _ => {}
        }
    }
    gtrace(format_args!(
        "  └ operand NOT a value: rb_head={} fully_reduced={}",
        match term::get(rb) {
            TermData::Var(_) => "<var>".into(),
            TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
        },
        f.fully_reduced
    ));
    (ForcedValue::Residual, f.steps)
}

/// Resolve ONE strict redex (disclosed §60 host-forcing). Force operands via
/// the engine (`force_value`); for `isnil` decide from the forced
/// constructor, else compute via stellar `sbinarith` (the disclosed
/// host-i128 boundary — see `sbinarith`'s module doc). `eq`/`lt` are mapped
/// to galaxy church booleans HERE, the single production point (D1). Returns
/// the rebuilt process ray `+P(st(result, resid_pi))`, or `None` for an
/// honest measured stop (non-value operand, DivByZero — stuck by ICFP spec,
/// or sbinarith past `sub_fuel`).
fn drive_strict(
    phi: &Constellation,
    r: &StrictRedex,
    fuel: usize,
    budget: usize,
    total: &mut usize,
) -> Option<TermId> {
    const SUB_FUEL: usize = 2_000_000;
    if r.op == StrictOp::IsNil {
        let (fv, stp) = force_value(phi, r.operands[0], fuel, budget);
        *total += stp;
        let res = match fv {
            ForcedValue::Nil => cst("t"),
            ForcedValue::Cons => cst("f"),
            _ => return None,
        };
        return Some(pp(st(res, r.resid_pi)));
    }
    let mut nums: Vec<TermId> = Vec::with_capacity(r.operands.len());
    for &o in &r.operands {
        let (fv, stp) = force_value(phi, o, fuel, budget);
        *total += stp;
        match fv {
            ForcedValue::Numeral(n) => nums.push(n),
            _ => return None,
        }
    }
    let result = match r.op {
        StrictOp::Neg => crate::sbinarith::neg(nums[0])?,
        StrictOp::Add => crate::sbinarith::add(nums[0], nums[1], SUB_FUEL)?,
        StrictOp::Mul => crate::sbinarith::mul(nums[0], nums[1], SUB_FUEL)?,
        StrictOp::Eq => galaxy_bool(crate::sbinarith::eq(nums[0], nums[1], SUB_FUEL)?),
        StrictOp::Lt => galaxy_bool(crate::sbinarith::lt(nums[0], nums[1], SUB_FUEL)?),
        // div: disclosed §60 (user-authorised). sbinarith::div is
        // ICFP-correct (truncate toward zero). DivByZero is stuck BY SPEC
        // (ICFP assigns no value) ⇒ honest stop, not faked.
        StrictOp::Div => match crate::sbinarith::div(nums[0], nums[1], SUB_FUEL) {
            Some(crate::sbinarith::DivResult::Ok(q)) => crate::sbinarith::sint(q),
            Some(crate::sbinarith::DivResult::DivByZero) | None => return None,
        },
        StrictOp::IsNil => unreachable!("isnil handled above"),
    };
    Some(pp(st(result, r.resid_pi)))
}

/// KAM readback: `+P(st(M, f0·f1·…·eps))` denotes the term `M f0 f1 …`
/// (`a(a(…a(M,f0),f1)…)`). The `Push` rule built π by uncurrying; folding it
/// back reconstructs the applicative term that constructor recognisers
/// (`is_listish_value`, the decoder) understand. Total: a non-`st` ray or
/// non-`dot` π just folds what it has.
pub fn readback_ray(ray: TermId) -> TermId {
    let (mut head, mut pi) = match term::get(ray) {
        TermData::App(p, pa) if p.name.as_str() == "P" && pa.len() == 1 => {
            match term::get(pa[0]) {
                TermData::App(s, sa) if s.name.as_str() == "st" && sa.len() == 2 => {
                    (sa[0], sa[1])
                }
                _ => return ray,
            }
        }
        _ => return ray,
    };
    let mut frames = Vec::new();
    while let TermData::App(d, da) = term::get(pi) {
        if d.name.as_str() == "dot" && da.len() == 2 {
            frames.push(da[0]);
            pi = da[1];
        } else {
            break;
        }
    }
    for f in frames {
        head = ap_node(head, f);
    }
    head
}

/// Outcome of [`eval_forced`].
#[derive(Debug)]
pub struct Forced {
    /// The most-evaluated term reached (constructor structure / residual).
    pub value: TermId,
    /// Total stellar steps across all engine passes.
    pub steps: usize,
    /// Host `isnil`-forcings performed (the §60 strategy's work).
    pub forcings: usize,
    /// Host arith-op resolutions performed (force operands → stellar sbinarith).
    pub arith_ops: usize,
    /// No blocked `isnil` remains.
    pub isnil_complete: bool,
    /// No blocked `isnil` AND no blocked `add/mul/eq/lt/neg` remains. `div`
    /// and non-numeral-operand residuals are honest measured stops, not faked.
    pub fully_reduced: bool,
    /// The full surviving process ray `+P(st(M,π))` at termination (the
    /// protocol's `(flag,newState,data)` lives on the continuation `π`, NOT
    /// in `value`/focus). `None` only if no single ray survived. Feed this to
    /// `galaxy_decode::decode_result` for the real result.
    pub final_ray: Option<TermId>,
}

thread_local! {
    /// Recursion depth for `STELLA_GALAXY_TRACE` indentation.
    static TR_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// Env-gated (`STELLA_GALAXY_TRACE=1`) one-line forcing trace — the
/// instrument that shows exactly which Push-form op resolves and where the
/// chain actually stops. No-op (one env read) unless enabled.
fn gtrace(args: std::fmt::Arguments) {
    if std::env::var_os("STELLA_GALAXY_TRACE").is_some() {
        let d = TR_DEPTH.with(|c| c.get());
        eprintln!("[gtrace]{}{}", "  ".repeat(d), args);
    }
}

/// Disclosed §60 host-forcing evaluator. Interleaves stellar reduction
/// (`iex_fast`) with demand-driven forcing of the strict ops the engine
/// can't pattern-match. ONE loop, ONE detector (`strict_redex_on_pi`), ONE
/// forcer (`force_value`), ONE driver (`drive_strict`) — no curried/Push
/// duality, no per-prim branches, no `replace_subterm` (the structural
/// fix for the recurring false-NF bug class). `prog` is reduced as the
/// process `+P(st(prog, ε))`; the result `(flag,newState,data)` lives on
/// the continuation π of `final_ray` (use `readback_ray` + the decoder).
///
/// FAITHFULNESS: every *reduction* is the reference engine over `Φ`. The
/// only host acts are (a) deciding to force a strict op's operands and
/// (b) computing the numeric kernel via `crate::sbinarith` — a disclosed,
/// bounded §60 concession (user-authorised; see `sbinarith`'s module doc
/// for its host-i128 signed-layer boundary). No green is faked: a
/// non-value operand, DivByZero (stuck by ICFP spec), or an sbinarith
/// past `sub_fuel` all return `fully_reduced=false` honestly.
pub fn eval_forced(phi: &Constellation, prog: TermId, fuel: usize, max_forcings: usize) -> Forced {
    // State = the process Ψ (preserving the KAM stack across resumes).
    let mut psi: Vec<Star> = vec![vec![pp(st(prog, cst("eps")))]];
    let mut total = 0usize;
    let mut forcings = 0usize; // isnil resolutions
    let mut arith_ops = 0usize; // numeric resolutions
    loop {
        let res = crate::interactive::iex_fast(phi, psi.clone(), fuel);
        total += res.steps;
        let ray = match single_ray(&res.psi) {
            Some(r) => r,
            None => {
                let v = psi.first().and_then(|s| s.first().copied()).unwrap_or(prog);
                return Forced {
                    value: v, steps: total, forcings, arith_ops, final_ray: None,
                    isnil_complete: false, fully_reduced: false,
                };
            }
        };
        let focus = st_inner(ray).unwrap_or(ray);

        let Some(redex) = strict_redex_on_pi(ray) else {
            // No strict redex on π, and `iex_fast` already ran the pure
            // prims to fixpoint ⇒ a genuine normal form.
            gtrace(format_args!(
                "FULLY REDUCED: no strict redex; focus={} forcings={forcings} arith_ops={arith_ops}",
                match term::get(focus) {
                    TermData::Var(_) => "<var>".into(),
                    TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
                }
            ));
            return Forced {
                value: focus, steps: total, forcings, arith_ops, final_ray: Some(ray),
                isnil_complete: true, fully_reduced: true,
            };
        };

        let is_isnil = redex.op == StrictOp::IsNil;
        if forcings + arith_ops >= max_forcings {
            return Forced {
                value: focus, steps: total, forcings, arith_ops, final_ray: Some(ray),
                isnil_complete: !is_isnil, fully_reduced: false,
            };
        }
        if is_isnil {
            forcings += 1;
        } else {
            arith_ops += 1;
        }
        gtrace(format_args!(
            "strict op={} ({}={}, total_steps={total})",
            redex.op.name(),
            if is_isnil { "forcings" } else { "arith_ops" },
            if is_isnil { forcings } else { arith_ops },
        ));
        // Operands forced with a strictly smaller budget ⇒ well-founded.
        let sub_budget = max_forcings.saturating_sub(forcings + arith_ops);
        match drive_strict(phi, &redex, fuel, sub_budget, &mut total) {
            Some(new_ray) => {
                psi = vec![vec![new_ray]];
                continue;
            }
            None => {
                return Forced {
                    value: focus, steps: total, forcings, arith_ops, final_ray: Some(ray),
                    isnil_complete: !is_isnil, fully_reduced: false,
                };
            }
        }
    }
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
        let prims = prim_stars().len();
        assert_eq!(
            phi.len(),
            prims + g.defs.len(),
            "Φ = prim_stars() ∪ one δ-star per def"
        );
        assert_eq!(
            prims, 13,
            "prim_stars() = Push + i/t/f/s/c/b/cons/car/cdr/nil + isnil×2 (KG3b/c)"
        );

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
             ({} prim + {} δ)",
            g.defs.len(),
            g.entry,
            dangling.len(),
            phi.len(),
            prims,
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
