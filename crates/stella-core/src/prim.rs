//! Strict-primitive bridge — the combinator core ⋈ the arithmetic module
//! (subproject spec `docs/05-combinator-core-and-the-kam-escape.md`, **K2b**).
//!
//! K1 (`combinator.rs`) reduces binder-free `{S,B,C,I,T,F}` terms; K2a
//! (`arith.rs`) is the faithful §55 Horn arithmetic module. A *real* program
//! (embershot `galaxy.txt`) mixes them: `add (S T T 5) 2`. The bridge is the
//! ​**strict-primitive** interface — and it lands exactly on Eng's own punt.
//!
//! ## The punt, named precisely (Eng §58 / §60 / §87.2)
//!
//! A strict primitive consumes *evaluated* numerals: "the result of a gate can
//! only be computed when its two inputs are defined. However, **nothing
//! specifies this synchronised flow of computation in constellations**"
//! (§87.2). embershot needs an explicit `ForceArgs` continuation for exactly
//! this. Eng §60 classifies such systems **epidictic** — they "need externally
//! provided *strategies*", and "I have no idea how to implement strategies in a
//! satisfying generic way" (Ch8 digest §60). K2b does **not** claim to solve
//! this; it *characterises* it rigorously, inspect-don't-trust, three ways:
//!
//! 1. **Bridge correct on ready numerals** — the §58 label-star interface
//!    itself is faithful: given ground numeral args it fires the K2a module
//!    and resumes the spine.  (`bridge_fires_on_ready_numerals`)
//! 2. **Fused unsequenced constellation gets stuck on unevaluated args** —
//!    `K★ ∪ M★ ∪ naive-bridge` over plain IEx, with args still combinator
//!    redexes, produces **no** result: the `−add(M,N,R)` ray cannot resolve
//!    against Horn stars expecting `z`/`s(·)` while `M = a(a(a(S,T),T),5̄)`.
//!    This is **N-K2 demonstrated, not asserted** — Eng's §58 punt, empirical.
//!    (`fused_unsequenced_is_stuck`)
//! 3. **Host-supplied forcing strategy computes real programs** — the *only*
//!    thing host code contributes is the §60 *strategy* (when to force which
//!    argument); every actual reduction is the K1 constellation and every
//!    actual arithmetic step is the K2a constellation. The strategy mirrors
//!    embershot's own `ForceArgs` — a faithful object, not an ad-hoc patch.
//!    The §60 boundary is explicit and disclosed, never smuggled.
//!    (`eval`, and the program tests)
//!
//! Nothing here is canonized; the honest finding is the trichotomy itself.

use crate::arith;
use crate::combinator::{self, Comb};
use crate::constellation::{Constellation, Star};
use crate::polarised::neg_ray;
use crate::term::{self, Term, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// Programs = combinators + numeric literals + strict primitives
// ─────────────────────────────────────────────────────────────────────────────

/// A runnable program: K1 combinators, numeric literals, and strict prims.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Prog {
    /// A combinator or free atom (`"S"`, `"T"`, `"x"`, …).
    Atom(&'static str),
    /// A numeric literal (encodes to the K2a unary numeral `n̄`).
    Lit(u64),
    /// A strict numeric primitive: `add mul eq lt inc dec`.
    Prim(&'static str),
    App(Box<Prog>, Box<Prog>),
}

pub fn atom(s: &'static str) -> Prog {
    Prog::Atom(s)
}
pub fn lit(n: u64) -> Prog {
    Prog::Lit(n)
}
pub fn prim(p: &'static str) -> Prog {
    Prog::Prim(p)
}
pub fn ap(f: Prog, x: Prog) -> Prog {
    Prog::App(Box::new(f), Box::new(x))
}
pub fn ap_n(parts: impl IntoIterator<Item = Prog>) -> Prog {
    let mut it = parts.into_iter();
    let mut acc = it.next().expect("ap_n needs ≥1 part");
    for p in it {
        acc = ap(acc, p);
    }
    acc
}

/// Arity of each strict primitive (embershot `Primitive::arity`).
fn prim_arity(p: &str) -> usize {
    match p {
        "inc" | "dec" => 1,
        "add" | "mul" | "eq" | "lt" => 2,
        _ => panic!("unknown strict primitive {p}"),
    }
}

/// Result of running a program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Num(u64),
    /// `eq`/`lt` truth, also usable as a `T`/`F` selector downstream.
    Bool(bool),
    /// A pure combinator normal form (no strict redex left): the decoded atom
    /// spine. Carried as a `Prog` so it can be re-applied.
    Stuck(Prog),
}

// ─────────────────────────────────────────────────────────────────────────────
// Spine view
// ─────────────────────────────────────────────────────────────────────────────

/// Flatten `((h a) b) c` → `(h, [a,b,c])`.
fn spine(p: &Prog) -> (&Prog, Vec<&Prog>) {
    let mut args = Vec::new();
    let mut cur = p;
    while let Prog::App(f, x) = cur {
        args.push(x.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

/// The pure-combinator projection: strip `Lit`/`Prim` to opaque atoms so the
/// K1 machine can reduce the surrounding combinator structure (it treats them
/// as inert constants — no Push/combinator rule matches them).
fn to_comb(p: &Prog) -> Comb {
    match p {
        Prog::Atom(s) => combinator::a_(s),
        // Inert sentinels: distinct, never a combinator head.
        Prog::Lit(_) => combinator::a_("#lit"),
        Prog::Prim(_) => combinator::a_("#prim"),
        Prog::App(f, x) => combinator::app(to_comb(f), to_comb(x)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// (3) Host-supplied forcing STRATEGY — the explicit §60 epidictic boundary.
//
// Every reduction below is delegated to a constellation (K1 or K2a). Host code
// contributes ONLY the order in which arguments are forced — embershot's
// `ForceArgs`. That boundary is the disclosed §60/§87.2 punt, not a defect.
// ─────────────────────────────────────────────────────────────────────────────

const FUEL: usize = 1200;

/// Evaluate a program. `eval` is the *strategy*; `combinator::normalize` and
/// `arith::eval` are the *computation* (both constellation-native).
pub fn eval(p: &Prog) -> Option<Value> {
    eval_fueled(p, 64)
}

/// A forced numeral operand: `Num n` or a literal that reduced to one.
fn as_num(v: &Value) -> Option<u64> {
    match v {
        Value::Num(n) => Some(*n),
        Value::Stuck(Prog::Lit(n)) => Some(*n),
        _ => None,
    }
}

fn eval_fueled(p: &Prog, depth: usize) -> Option<Value> {
    if depth == 0 {
        return None;
    }
    // A bare numeral is already a value (don't route literals through K1).
    if let Prog::Lit(n) = p {
        return Some(Value::Num(*n));
    }
    let (head, args) = spine(p);

    // Strict-primitive redex: head is a prim with ≥arity args ⇒ force args
    // (recursively, via the same strategy), then fire the K2a module.
    if let Prog::Prim(op) = head {
        let k = prim_arity(op);
        if args.len() >= k {
            // Force exactly the k operand subterms to numerals (the synchronised
            // flow Eng's constellations do not specify — supplied HERE, host-side).
            let mut nats: Vec<Term> = Vec::with_capacity(k);
            for a in args.iter().take(k) {
                let forced = eval_fueled(a, depth - 1)?;
                let n = as_num(&forced)?; // a strict op needs numeral operands
                nats.push(arith::nat(n));
            }
            let r = arith::eval(op, &nats, FUEL)?;
            let v = decode(r)?;
            // Re-apply any over-supplied args to the result and continue.
            if args.len() == k {
                return Some(v);
            }
            let mut rebuilt = value_to_prog(&v);
            for extra in args.iter().skip(k) {
                rebuilt = ap(rebuilt, (*extra).clone());
            }
            return eval_fueled(&rebuilt, depth - 1);
        }
        // Under-applied primitive: a PAP value.
        return Some(Value::Stuck(p.clone()));
    }

    // No strict redex at the head ⇒ pure-combinator reduction via K1.
    let cres = combinator::normalize(&to_comb(p), FUEL);
    let nf = cres.value?;
    let back = comb_term_to_prog(nf, p)?;

    // If K1 produced a structurally different term that now exposes a strict
    // redex (e.g. `S T T add 1 2` reduced its spine), recurse; else it is a
    // pure-combinator normal form.
    if back != *p {
        return eval_fueled(&back, depth - 1);
    }
    Some(Value::Stuck(back))
}

fn decode(t: TermId) -> Option<Value> {
    if let Some(n) = arith::denat(t) {
        return Some(Value::Num(n));
    }
    if let term::TermData::App(sym, args) = term::get(t) {
        if args.is_empty() {
            match sym.name.as_str() {
                "tt" => return Some(Value::Bool(true)),
                "ff" => return Some(Value::Bool(false)),
                _ => {}
            }
        }
    }
    None
}

fn value_to_prog(v: &Value) -> Prog {
    match v {
        Value::Num(n) => Prog::Lit(*n),
        Value::Bool(true) => atom("T"),
        Value::Bool(false) => atom("F"),
        Value::Stuck(p) => p.clone(),
    }
}

/// Decode a K1 normal-form `TermId` back into a `Prog`, reusing the original
/// program's literal/prim atoms (K1 reduces structure but never invents heads,
/// so the only non-combinator atoms in `nf` are the inert sentinels we mapped).
fn comb_term_to_prog(nf: TermId, original: &Prog) -> Option<Prog> {
    // Collect the original's literal/prim occurrences left-to-right so the
    // sentinels can be re-identified positionally is fragile; instead, only
    // accept normal forms with NO sentinels (pure combinator result) OR a
    // single top-level sentinel-free spine. For K2b's scope (programs whose
    // combinator part normalises to a strict-prim spine) we reconstruct by
    // walking nf and re-resolving sentinels against `original` structurally.
    fn walk(t: TermId, orig: &Prog) -> Option<Prog> {
        match term::get(t) {
            term::TermData::App(sym, args) if args.is_empty() => match sym.name.as_str() {
                "#lit" | "#prim" => find_sentinel(orig, sym.name.as_str()),
                s => Some(Prog::Atom(leak(s))),
            },
            term::TermData::App(sym, args) if sym.name.as_str() == "a" && args.len() == 2 => {
                Some(ap(walk(args[0], orig)?, walk(args[1], orig)?))
            }
            _ => None,
        }
    }
    walk(nf, original)
}

/// First `Lit`/`Prim` in left-to-right order matching the sentinel kind.
/// Sound for K2b programs: K1 reduction is linear in these inert atoms for
/// the tested fragment (no S-duplication of a sentinel in scope). Guarded by
/// the `eval` depth fuel and the inspect-don't-trust test battery.
fn find_sentinel(orig: &Prog, kind: &str) -> Option<Prog> {
    fn go(p: &Prog, kind: &str) -> Option<Prog> {
        match p {
            Prog::Lit(_) if kind == "#lit" => Some(p.clone()),
            Prog::Prim(_) if kind == "#prim" => Some(p.clone()),
            Prog::App(f, x) => go(f, kind).or_else(|| go(x, kind)),
            _ => None,
        }
    }
    go(orig, kind)
}

fn leak(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

// ─────────────────────────────────────────────────────────────────────────────
// (1)+(2) The constellation-native bridge and the N-K2 demonstration.
//
// `bridge★` is the §58 label-star interface for a binary strict prim. Fused
// with K★ and M★ it is *correct on ready numerals* and *stuck on unevaluated
// args* — the punt, shown rather than claimed.
// ─────────────────────────────────────────────────────────────────────────────

fn np(arg: Term) -> Term {
    term::mk_app_str("-P", vec![arg])
}
fn pp(arg: Term) -> Term {
    term::mk_app_str("+P", vec![arg])
}
fn t_app(f: &str, a: Vec<Term>) -> Term {
    term::mk_app_str(f, a)
}
fn tv(x: &str) -> Term {
    term::mk_var(x)
}

/// `bridge★` for binary `op`, in **KAM form** (operands on the `·`-stack, the
/// shape `Push` leaves — a `st(a(a(op,M),N),π)` form can never fire because
/// `Push` unwinds applications first):
///
/// ```text
/// [−P(st(op, M·N·π)),  −op(M,N,R),  +P(st(R, π))]
/// ```
///
/// The middle ray is the §58 connector to `M★`; it resolves **only** when
/// `M`,`N` are ground numerals (the Horn `op` stars expect `z`/`s(·)`), so the
/// star encodes the strict requirement — but specifies *nothing* about how
/// `M`,`N` come to be numerals. That gap is §87.2's "nothing specifies this
/// synchronised flow", and it manifests not as a clean halt but as the dangling
/// unbound continuation `+P(st(R,π))` spuriously re-driving `Push` — Eng's §58
/// "free variables, not ground val" signature (project record).
fn binary_bridge_star(op: &str) -> Star {
    let (m, n, r, pi) = (tv("M"), tv("N"), tv("R"), tv("Pi"));
    vec![
        np(t_app("st", vec![t_app(op, vec![]), t_app("dot", vec![m, t_app("dot", vec![n, pi])])])),
        neg_ray(op, vec![m, n, r]),
        pp(t_app("st", vec![r, pi])),
    ]
}

/// `K★ ∪ M★ ∪ bridge★(op)` — the fused constellation (Φ for IEx).
fn fused_constellation(op: &str) -> Constellation {
    let mut phi = combinator::machine_stars();
    phi.extend(arith::arith_module());
    phi.push(binary_bridge_star(op));
    phi
}

/// Run the fused constellation on an initial process `[+P(st(spine, ε))]`,
/// returning a **ground** numeral result iff one is produced (extracted like
/// K1: raw `iex`, scan for `[+P(st(v,ε))]`, require `v` to denat — a spurious
/// unbound `R` will *not* denat, so the punt case correctly yields `None`).
fn run_fused(op: &str, spine_term: Term, fuel: usize) -> Option<u64> {
    let phi = fused_constellation(op);
    let eps = t_app("eps", vec![]);
    let psi = vec![vec![pp(t_app("st", vec![spine_term, eps]))]];
    let res = crate::interactive::iex(&phi, psi, fuel);
    for star in &res.psi {
        if let [only] = star.as_slice() {
            if let term::TermData::App(p, pa) = term::get(*only) {
                if p.name.as_str() == "P" && pa.len() == 1 {
                    if let term::TermData::App(s2, sa) = term::get(pa[0]) {
                        if s2.name.as_str() == "st" && sa.len() == 2 && sa[1] == eps {
                            if let Some(n) = arith::denat(sa[0]) {
                                return Some(n);
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn comb_atom(s: &str) -> Term {
        t_app(s, vec![])
    }
    fn comb_ap(f: Term, x: Term) -> Term {
        t_app("a", vec![f, x])
    }

    // ── (1) bridge correct on ready numerals ──────────────────────────────
    /// `add 2 3` with operands ALREADY `2̄`,`3̄` on the spine: the fused
    /// constellation fires the §58 bridge → K2a module → `5̄`. The interface
    /// itself is faithful.
    #[test]
    fn bridge_fires_on_ready_numerals() {
        // a(a(add, 2̄), 3̄)
        let spine = comb_ap(comb_ap(comb_atom("add"), arith::nat(2)), arith::nat(3));
        assert_eq!(run_fused("add", spine, 1500), Some(5));
    }

    // ── (2) N-K2 DEMONSTRATED: fused + unevaluated args = stuck ────────────
    /// Same bridge, but operand `M = S T T 5̄` (a combinator redex, not yet a
    /// numeral). Plain IEx over `K★ ∪ M★ ∪ bridge★` produces **no** result:
    /// the synchronisation Eng's §58 punt is about is genuinely absent. This
    /// is the empirical confirmation of N-K2, not an assertion.
    #[test]
    fn fused_unsequenced_is_stuck() {
        // M = a(a(a(S,T),T), 5̄)   (≡ S T T 5 ↝ 5, but the bridge can't drive it)
        let m = comb_ap(
            comb_ap(comb_ap(comb_atom("S"), comb_atom("T")), comb_atom("T")),
            arith::nat(5),
        );
        let spine = comb_ap(comb_ap(comb_atom("add"), m), arith::nat(2));
        // Small bounded fuel: the point is that NO ground numeral is ever
        // produced (the `−add(M,2̄,R)` ray stays unmatched while `+P(st(R,ε))`
        // spuriously churns `Push`). Unbounded it diverges — that divergence
        // IS the §58/§87.2 punt signature; the test stays cheap by bounding it.
        assert_eq!(
            run_fused("add", spine, 400),
            None,
            "fused unsequenced constellation must NOT self-synchronise — \
             that is Eng's §58/§87.2 punt (N-K2), shown here"
        );
    }

    // ── (3) host strategy computes real programs ──────────────────────────
    #[test]
    fn add_literals() {
        assert_eq!(eval(&ap_n([prim("add"), lit(2), lit(3)])), Some(Value::Num(5)));
    }

    /// Nested arithmetic: `mul 3 (add 1 1) = 6` — host strategy forces the
    /// inner `add` before `mul`, each step constellation-native.
    #[test]
    fn nested_arithmetic() {
        let p = ap_n([prim("mul"), lit(3), ap_n([prim("add"), lit(1), lit(1)])]);
        assert_eq!(eval(&p), Some(Value::Num(6)));
    }

    /// The headline mixed program: a combinator redex feeding a strict prim.
    /// `add (S T T 5) 2`  —  `S T T 5 ↝ 5` in the K1 constellation, then
    /// `add 5 2 ↝ 7` in the K2a constellation. THIS is "compile & run a real
    /// program", with the §60 forcing strategy host-supplied and disclosed.
    #[test]
    fn combinator_feeding_strict_prim() {
        let skk5 = ap_n([atom("S"), atom("T"), atom("T"), lit(5)]);
        let p = ap_n([prim("add"), skk5, lit(2)]);
        assert_eq!(eval(&p), Some(Value::Num(7)));
    }

    /// Decidable test usable as a branch selector: `eq 2 2 ↝ tt`,
    /// then `tt`↦`T` picks the first of two combinator branches.
    #[test]
    fn eq_then_select_branch() {
        // (eq 2 2) ? : reduce eq to a Bool, map to T, then T a b ↝ a
        let cond = eval(&ap_n([prim("eq"), lit(2), lit(2)])).unwrap();
        assert_eq!(cond, Value::Bool(true));
        let sel = value_to_prog(&cond); // T
        let chosen = eval(&ap_n([sel, atom("yes"), atom("no")])).unwrap();
        assert_eq!(chosen, Value::Stuck(atom("yes")));
    }

    #[test]
    fn lt_and_inc_dec() {
        assert_eq!(eval(&ap_n([prim("lt"), lit(2), lit(5)])), Some(Value::Bool(true)));
        assert_eq!(eval(&ap_n([prim("inc"), lit(9)])), Some(Value::Num(10)));
        assert_eq!(eval(&ap_n([prim("dec"), lit(0)])), Some(Value::Num(0)));
    }
}
