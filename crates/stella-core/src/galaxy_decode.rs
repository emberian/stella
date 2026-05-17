//! Faithful structural decoder for the galaxy program's evaluated output.
//!
//! `crate::galaxy` loads ICFP-2020 `galaxy.txt`, `•`-encodes it, and runs it
//! as a *process* `[+P(st(M, π))]` under the interaction engine
//! (`crate::interactive::iex_fast`). When IEx finishes, the ICFP value the
//! galaxy produced is somewhere inside the surviving process star — but the
//! value-bearing term `M` is *not* always the whole answer: the real list
//! structure frequently lives further down the continuation `π`. This module
//! turns whatever term is there into a *total, faithful* tree (`GValue`) that
//! the next session can read with their eyes.
//!
//! ## Value encoding (the term universe of `crate::term`)
//!
//! ICFP values, as `crate::galaxy::enc` / `crate::combinator` build them:
//!
//! * `nil`        → `App("nil", [])`                       (a 0-ary atom)
//! * cons-cell    → `a(a(cons, HEAD), TAIL)`, i.e.
//!                  `App("a",[ App("a",[ App("cons",[]), HEAD ]), TAIL ])`.
//!                  `cons` needs 3 args to fire; 2-applied it is a stuck
//!                  **value** (a pair / list node).
//! * number ≥ 0   → a `crate::binarith` numeral (head atoms `bz`/`o0`/`o1`),
//!                  decoded by [`crate::binarith::denat`].
//! * number < 0   → `App("neg",[ <nat> ])` — galaxy's honest negative-literal
//!                  placeholder (`crate::galaxy`, KG1b).
//! * `t` / `f`    → `App("t", [])` / `App("f", [])`        (truth atoms).
//!
//! Anything that is *not* one of the clean shapes above is reported as
//! [`GValue::Opaque`] carrying a short `head/arity` tag — decoding never lies
//! by coercing a non-cons into a [`GValue::Cons`].
//!
//! ## Honest scope
//!
//! This module only decodes *structure*. It does not validate that the
//! galaxy's normal form is the *correct* ICFP interaction result — that
//! judgement is left to a human reading [`pretty`] output. The decoder is
//! deliberately conservative: an `Opaque`-heavy dump is a true signal that the
//! engine did not reduce the program to a clean list value.

use crate::term::{get, TermData, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// GValue
// ─────────────────────────────────────────────────────────────────────────────

/// A faithfully-decoded galaxy value. Total: every `TermId` maps to exactly
/// one of these, and `Opaque` is the honest catch-all (never a fabricated
/// `Cons`/`Num`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GValue {
    /// The `nil` atom — empty list / list terminator.
    Nil,
    /// A galaxy numeral (`binarith` non-negative, or `neg(_)` negative).
    Num(i128),
    /// A 0-ary atom that is neither `nil` nor a numeral (e.g. `t`, `f`, a
    /// combinator letter, a `:N` ref that never resolved).
    Atom(String),
    /// A cons-cell `a(a(cons, HEAD), TAIL)` — decoded head and tail.
    Cons(Box<GValue>, Box<GValue>),
    /// Any subterm that is *not* a clean nil / numeral / cons-cell / 0-ary
    /// atom. Carries a short `"head/arity"` tag (or `"Var"`), so the decode is
    /// total and self-describing without ever fabricating structure.
    Opaque(String),
}

// ─────────────────────────────────────────────────────────────────────────────
// Numeral decode (signed) — delegate to the canonical sbinarith codec
// ─────────────────────────────────────────────────────────────────────────────

/// Decode a galaxy signed numeral. Delegates to [`crate::sbinarith::dsint`],
/// the single canonical signed codec, so the decoder accepts exactly what the
/// engine produces — including nested `neg(neg(..))` (parity-folded) and
/// `neg(nat 0)` canonicalised to `0`. (A previous local copy only handled a
/// single `neg` layer and so mis-decoded those as `Opaque`.) Shares the
/// documented host-`i128` ceiling of `sbinarith` — see that module's
/// faithfulness-boundary note.
fn dsint(t: TermId) -> Option<i128> {
    crate::sbinarith::dsint(t)
}

/// Encode a signed integer the way galaxy does (the canonical
/// [`crate::sbinarith::sint`]): non-negative → `binarith::nat`, negative →
/// `neg(nat(mag))`. Test/round-trip helper.
pub fn sint(n: i128) -> TermId {
    crate::sbinarith::sint(n)
}

// ─────────────────────────────────────────────────────────────────────────────
// Structural recognisers
// ─────────────────────────────────────────────────────────────────────────────

/// `true` iff `t == App("nil", [])`.
fn is_nil(t: TermId) -> bool {
    matches!(get(t), TermData::App(s, a) if a.is_empty() && s.name.as_str() == "nil")
}

/// If `t` is a cons-cell `a(a(cons, HEAD), TAIL)`, return `(HEAD, TAIL)`.
///
/// Recognises the exact stuck-value shape: an `a`-node whose function side is
/// itself an `a`-node applying the 0-ary `cons` atom to `HEAD`, and whose
/// argument side is `TAIL`. (`cons` fires at arity 3; 2-applied it is a
/// value.) Polarity-agnostic on the `a`/`cons` head *name* for robustness.
fn as_cons_cell(t: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(s, a) = get(t) else { return None };
    if s.name.as_str() != "a" || a.len() != 2 {
        return None;
    }
    let (inner, tail) = (a[0], a[1]);
    let TermData::App(s2, a2) = get(inner) else { return None };
    if s2.name.as_str() != "a" || a2.len() != 2 {
        return None;
    }
    let (consatom, head) = (a2[0], a2[1]);
    match get(consatom) {
        TermData::App(s3, a3) if a3.is_empty() && s3.name.as_str() == "cons" => {
            Some((head, tail))
        }
        _ => None,
    }
}

/// A short `"head/arity"` (or `"Var"`) tag for the `Opaque` catch-all.
fn head_tag(t: TermId) -> String {
    match get(t) {
        TermData::Var(_) => "Var".to_string(),
        TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// decode
// ─────────────────────────────────────────────────────────────────────────────

/// Decode one term, recursively and totally.
///
/// Order matters (and is faithful):
/// 0. **readback-aware**: if `t` is a Push-form process ray
///    `+P(st(M,π))`, fold π back into applicative form first
///    ([`crate::galaxy::readback_ray`]) — the KAM leaves results in
///    Push-stack form and the cons recognisers below are applicative.
///    Idempotent on a plain applicative term (readback returns it
///    unchanged), so it is safe in the recursive head/tail calls too.
/// 1. numeral (signed) — try first, so a `neg(nat n)` never looks like an atom;
/// 2. `nil` atom → [`GValue::Nil`];
/// 3. cons-cell shape → [`GValue::Cons`] of decoded head/tail;
/// 4. any other 0-ary atom → [`GValue::Atom`];
/// 5. anything else → [`GValue::Opaque`] (`head/arity` tag) — never coerced.
pub fn decode(t: TermId) -> GValue {
    let t = crate::galaxy::readback_ray(t);
    if let Some(n) = dsint(t) {
        return GValue::Num(n);
    }
    if is_nil(t) {
        return GValue::Nil;
    }
    if let Some((h, tl)) = as_cons_cell(t) {
        return GValue::Cons(Box::new(decode(h)), Box::new(decode(tl)));
    }
    match get(t) {
        TermData::App(s, a) if a.is_empty() => GValue::Atom(s.name.as_str().to_string()),
        _ => GValue::Opaque(head_tag(t)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// decode_result — from a finished process Ψ
// ─────────────────────────────────────────────────────────────────────────────

/// If `r == App("P", [ App("st", [M, π]) ])` (the `+P(st(M,π))` process ray,
/// matched polarity-agnostically on the head *name* `P`, exactly as
/// `combinator::read_value` does), return `(M, π)`.
fn unwrap_process_ray(r: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(s, a) = get(r) else { return None };
    if s.name.as_str() != "P" || a.len() != 1 {
        return None;
    }
    let TermData::App(s2, a2) = get(a[0]) else { return None };
    if s2.name.as_str() != "st" || a2.len() != 2 {
        return None;
    }
    Some((a2[0], a2[1]))
}

/// Decode a process ray directly: KAM-readback (`+P(st(M,π))` ≡ the term
/// `M` applied to π's frames) then [`decode`]. This is the correct
/// extraction now that the KAM leaves the result `(flag,newState,data)` in
/// Push-stack form on π — it replaces the old "largest cons subtree"
/// heuristic, which demonstrably selected a spurious tiny island
/// (`[0,[]]`) inside the frozen continuation. No search, no guessing: the
/// KAM denotation IS the readback.
pub fn decode_ray(ray: TermId) -> GValue {
    decode(crate::galaxy::readback_ray(ray))
}

/// Decode the value produced by a finished process Ψ. Locate the single
/// process ray `+P(st(M,π))` ([`unwrap_process_ray`], polarity-agnostic on
/// head name `P`, first in Ψ order; multi-ray stars tolerated), then
/// [`decode_ray`] it. Total: no ray ⇒ `Opaque`.
///
/// This is a *shallow* decode — it does NOT force lazy/Push-form
/// sub-structure, so a lazily-unbuilt payload field shows as `Opaque`.
/// For the fully-forced protocol triple use [`decode_forced`].
pub fn decode_result(psi: &[crate::constellation::Star]) -> GValue {
    let mut ray: Option<TermId> = None;
    'find: for star in psi {
        if star.len() == 1 {
            if let Some(_) = unwrap_process_ray(star[0]) {
                ray = Some(star[0]);
                break 'find;
            }
        }
    }
    if ray.is_none() {
        'find2: for star in psi {
            for &r in star {
                if unwrap_process_ray(r).is_some() {
                    ray = Some(r);
                    break 'find2;
                }
            }
        }
    }
    match ray.or_else(|| psi.first().and_then(|s| s.first()).copied()) {
        Some(r) => decode_ray(r),
        None => GValue::Opaque("empty-psi".to_string()),
    }
}

/// Decode the FULLY-FORCED protocol result. The galaxy result spine is
/// lazy: `eval_forced` yields only the outer WHNF cons; `newState`/`data`
/// fields stay as unforced thunks (Push-form). This recursively forces +
/// reads back each cons field to normal form before decoding — the
/// trustworthy `(flag,newState,data)` oracle.
///
/// Honest bounds (never hangs, never lies): `depth` caps recursion and
/// `*budget` caps total forced sub-evaluations; a field not resolvable
/// within the bound (or a genuine non-value residual) decodes as
/// `Opaque("unforced:…")` — an honest "not reached", never a fabricated
/// value. Per-field forcing uses the disclosed §60 `eval_forced`
/// (`fuel`/`max_forcings`), so the sbinarith host-i128 boundary applies.
pub fn decode_forced(
    phi: &crate::constellation::Constellation,
    f: &crate::galaxy::Forced,
    fuel: usize,
    max_forcings: usize,
) -> GValue {
    let root = f.final_ray.unwrap_or(f.value);
    let mut budget = 50_000usize;
    deep_decode(phi, root, fuel, max_forcings, 4096, &mut budget)
}

/// One node of [`decode_forced`]: force `t` to NF, read it back, and if it
/// is a cons cell recurse into head/tail (re-forcing each). Numerals / nil
/// / atoms terminate; a non-value or budget/depth exhaustion ⇒
/// `Opaque("unforced:…")` (honest, never coerced).
fn deep_decode(
    phi: &crate::constellation::Constellation,
    t: TermId,
    fuel: usize,
    max_forcings: usize,
    depth: usize,
    budget: &mut usize,
) -> GValue {
    if *budget == 0 || depth == 0 {
        return GValue::Opaque(format!("unforced:{}", head_tag(t)));
    }
    *budget -= 1;
    let f = crate::galaxy::eval_forced(phi, t, fuel, max_forcings);
    let rb = crate::galaxy::readback_ray(f.final_ray.unwrap_or(f.value));
    if let Some(n) = dsint(rb) {
        return GValue::Num(n);
    }
    if is_nil(rb) {
        return GValue::Nil;
    }
    if let Some((h, tl)) = as_cons_cell(rb) {
        return GValue::Cons(
            Box::new(deep_decode(phi, h, fuel, max_forcings, depth - 1, budget)),
            Box::new(deep_decode(phi, tl, fuel, max_forcings, depth - 1, budget)),
        );
    }
    match get(rb) {
        TermData::App(s, a) if a.is_empty() => GValue::Atom(s.name.as_str().to_string()),
        // Honest "engine did not reduce this to a value", NOT a coerced
        // Cons/Num — distinguished from a clean Opaque by the prefix.
        _ => GValue::Opaque(format!("unforced:{}", head_tag(rb))),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// pretty
// ─────────────────────────────────────────────────────────────────────────────

/// Render a [`GValue`] for human eyes.
///
/// * `Nil`               → `[]`
/// * `Num` / `Atom`      → the literal value
/// * `Opaque(s)`         → `<s>`
/// * `Cons` chain        → `[a, b, c]` when nil-terminated, else
///                          `[a, b, c | tail]` (improper list / pair).
pub fn pretty(v: &GValue) -> String {
    match v {
        GValue::Nil => "[]".to_string(),
        GValue::Num(n) => n.to_string(),
        GValue::Atom(a) => a.clone(),
        GValue::Opaque(s) => format!("<{s}>"),
        GValue::Cons(_, _) => {
            let mut elems: Vec<String> = Vec::new();
            let mut cur = v;
            loop {
                match cur {
                    GValue::Cons(h, tl) => {
                        elems.push(pretty(h));
                        cur = tl;
                    }
                    GValue::Nil => {
                        return format!("[{}]", elems.join(", "));
                    }
                    other => {
                        return format!("[{} | {}]", elems.join(", "), pretty(other));
                    }
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Convenience: list_to_vec / as_pair
// ─────────────────────────────────────────────────────────────────────────────

/// Best-effort cons-list → `Vec<GValue>`.
///
/// Walks the `Cons` spine collecting heads. Returns `Some(vec)` iff the spine
/// is **proper** (nil-terminated). An improper list (e.g. a bare pair
/// `Cons(a,b)` with non-nil `b`) ⇒ `None` (use [`as_pair`] for those).
/// `Nil` ⇒ `Some(vec![])`.
pub fn list_to_vec(v: &GValue) -> Option<Vec<GValue>> {
    let mut out = Vec::new();
    let mut cur = v;
    loop {
        match cur {
            GValue::Nil => return Some(out),
            GValue::Cons(h, tl) => {
                out.push((**h).clone());
                cur = tl;
            }
            _ => return None,
        }
    }
}

/// Best-effort "this value is a pair" view, for vectors `cons X Y` and
/// 2-element lists.
///
/// * `Cons(a, b)` → `Some((a, b))` (covers a raw vector `cons X Y` whose tail
///   `Y` is *not* nil, and also the head of any longer list).
/// * a proper 2-element list `[a, b]` (i.e. `Cons(a, Cons(b, Nil))`) →
///   `Some((a, b))` — the common "decoded 2-list is logically a pair" case.
/// * anything else → `None`.
pub fn as_pair(v: &GValue) -> Option<(GValue, GValue)> {
    if let GValue::Cons(a, b) = v {
        // Proper 2-list [a, b] ⇒ (a, b).
        if let GValue::Cons(b0, b1) = &**b {
            if matches!(&**b1, GValue::Nil) {
                return Some(((**a).clone(), (**b0).clone()));
            }
        }
        // Raw pair / vector cons X Y.
        return Some(((**a).clone(), (**b).clone()));
    }
    None
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — hermetic (hand-built terms; no galaxy.txt dependency)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::mk_app_str;

    /// A cons-cell `a(a(cons, HEAD), TAIL)` — galaxy's stuck-value shape.
    fn cell(head: TermId, tail: TermId) -> TermId {
        let cons = mk_app_str("cons", vec![]);
        let inner = mk_app_str("a", vec![cons, head]);
        mk_app_str("a", vec![inner, tail])
    }
    fn nil_t() -> TermId {
        mk_app_str("nil", vec![])
    }

    #[test]
    fn nil_decodes_to_nil() {
        assert_eq!(decode(nil_t()), GValue::Nil);
        assert_eq!(pretty(&GValue::Nil), "[]");
    }

    #[test]
    fn numeral_round_trips() {
        for n in [0i128, 1, 2, 42, 12345, -1, -3, -98765] {
            assert_eq!(decode(sint(n)), GValue::Num(n), "n={n}");
        }
        // A negative is `neg(nat)`, decoded as Num — never an Atom/Opaque.
        assert_eq!(decode(sint(-3)), GValue::Num(-3));
    }

    #[test]
    fn proper_list_decodes_and_flattens() {
        // cons 1 (cons -2 nil)  →  [1, -2]
        let t = cell(sint(1), cell(sint(-2), nil_t()));
        let d = decode(t);
        assert_eq!(pretty(&d), "[1, -2]");
        let v = list_to_vec(&d).expect("proper list");
        assert_eq!(v, vec![GValue::Num(1), GValue::Num(-2)]);
    }

    #[test]
    fn vector_as_pair() {
        // A vector cons 3 4  →  Cons(3,4)  →  as_pair = (3,4)
        let t = cell(sint(3), sint(4));
        let d = decode(t);
        let (x, y) = as_pair(&d).expect("pair");
        assert_eq!((x, y), (GValue::Num(3), GValue::Num(4)));
        // Improper list ⇒ list_to_vec is None (faithful).
        assert_eq!(list_to_vec(&d), None);
        assert_eq!(pretty(&d), "[3 | 4]");
    }

    #[test]
    fn two_list_is_also_a_pair() {
        // [a, b] reads as a pair too.
        let t = cell(sint(7), cell(sint(8), nil_t()));
        let (x, y) = as_pair(&decode(t)).expect("2-list pair");
        assert_eq!((x, y), (GValue::Num(7), GValue::Num(8)));
    }

    #[test]
    fn non_cons_is_opaque_not_cons() {
        // a(foo, bar): an `a`-node but NOT the cons-cell shape (no `cons`
        // atom inside) ⇒ Opaque, never a fabricated Cons (faithfulness).
        let foo = mk_app_str("foo", vec![]);
        let bar = mk_app_str("bar", vec![]);
        let t = mk_app_str("a", vec![foo, bar]);
        let d = decode(t);
        assert!(matches!(d, GValue::Opaque(_)), "got {d:?}");
        assert!(!matches!(d, GValue::Cons(_, _)));
        assert_eq!(pretty(&d), "<a/2>");
    }

    #[test]
    fn truth_and_unknown_atoms() {
        assert_eq!(decode(mk_app_str("t", vec![])), GValue::Atom("t".into()));
        assert_eq!(decode(mk_app_str("f", vec![])), GValue::Atom("f".into()));
        assert_eq!(decode(mk_app_str(":1338", vec![])), GValue::Atom(":1338".into()));
        assert_eq!(pretty(&GValue::Atom("t".into())), "t");
    }

    #[test]
    fn decode_result_readback_pushform_cons() {
        // The KAM leaves a cons RESULT in Push-stack form: head `cons`, its
        // args on π. `+P(st(cons, 9 · [8] · eps))` denotes `cons 9 [8]` =
        // the cons value `[9, 8]`. decode_result must KAM-read-back π (not
        // dig a spurious island out of it — the deleted heuristic's bug).
        let eps = mk_app_str("eps", vec![]);
        let pi = mk_app_str(
            "dot",
            vec![sint(9), mk_app_str("dot", vec![cell(sint(8), nil_t()), eps])],
        );
        let st = mk_app_str("st", vec![mk_app_str("cons", vec![]), pi]);
        let ray = mk_app_str("+P", vec![st]);
        let psi: Vec<crate::constellation::Star> = vec![vec![ray]];
        assert_eq!(pretty(&decode_result(&psi)), "[9, 8]");
    }

    #[test]
    fn decode_result_no_island_lie() {
        // M is genuinely `garbage(x)` applied to a parked list. The OLD
        // heuristic lied by surfacing the buried `[9,8]` as "the result";
        // readback faithfully denotes `garbage(x) [9,8]` ⇒ NOT a clean
        // list (Opaque), which is the honest answer.
        let list = cell(sint(9), cell(sint(8), nil_t()));
        let m = mk_app_str("garbage", vec![mk_app_str("x", vec![])]);
        let eps = mk_app_str("eps", vec![]);
        let pi = mk_app_str("dot", vec![list, eps]);
        let st = mk_app_str("st", vec![m, pi]);
        let ray = mk_app_str("+P", vec![st]);
        let psi: Vec<crate::constellation::Star> = vec![vec![ray]];
        match decode_result(&psi) {
            GValue::Opaque(_) => {}
            other => panic!("readback must NOT fabricate a list; got {other:?}"),
        }
    }

    #[test]
    fn decode_result_prefers_clean_m() {
        // When M is itself a clean list, decode_result returns it directly.
        let list = cell(sint(1), nil_t());
        let eps = mk_app_str("eps", vec![]);
        let st = mk_app_str("st", vec![list, eps]);
        let ray = mk_app_str("+P", vec![st]);
        let psi: Vec<crate::constellation::Star> = vec![vec![ray]];
        assert_eq!(pretty(&decode_result(&psi)), "[1]");
    }

    // ── DIAGNOSTIC (output, NOT assertion) ───────────────────────────────────

    /// Make galaxy's *actual* normal form legible. Reads the embershot
    /// `galaxy.txt` if present (else eprintln-skips, never panics), builds Φ,
    /// runs the engine on the standard entry interaction, and prints the
    /// decoded NF + engine counters. Asserts NOTHING about correctness — it
    /// exists so the next session can *see* what the galaxy reduced to.
    #[test]
    #[ignore = "diagnostic: long-running, reads external galaxy.txt; run with --ignored --nocapture"]
    fn dump_galaxy_nf() {
        const GALAXY_PATH: &str = "/Users/ember/dev/embershot/src/galaxy.txt";
        let src = match std::fs::read_to_string(GALAXY_PATH) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "SKIP dump_galaxy_nf: galaxy.txt not readable at \
                     {GALAXY_PATH} ({e}) — diagnostic skipped, not a failure."
                );
                return;
            }
        };
        let g = match crate::galaxy::parse(&src) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("SKIP dump_galaxy_nf: galaxy.txt parse error: {e}");
                return;
            }
        };
        let phi = crate::galaxy::constellation(&g);

        // Entry interaction term: `ap ap :entry nil (ap ap cons 0 0)`
        //   = a( a(:entry, nil), a(a(cons, 0), 0) )
        // built via galaxy's own AST→term encoder so it interlocks with Φ.
        use crate::galaxy::Ast;
        let zero = || Ast::Lit { neg: false, mag: 0 };
        let entry_ast = Ast::App(
            Box::new(Ast::App(
                Box::new(Ast::Ref(g.entry)),
                Box::new(Ast::Atom("nil".to_string())),
            )),
            Box::new(Ast::App(
                Box::new(Ast::App(
                    Box::new(Ast::Atom("cons".to_string())),
                    Box::new(zero()),
                )),
                Box::new(zero()),
            )),
        );
        let m = crate::galaxy::enc(&entry_ast);

        // Initial process `[+P(st(M, ε))]` — same constructors galaxy uses.
        let eps = crate::term::mk_app_str("eps", vec![]);
        let st = crate::term::mk_app_str("st", vec![m, eps]);
        let ray = crate::term::mk_app_str("+P", vec![st]);
        let psi_init: Vec<crate::constellation::Star> = vec![vec![ray]];

        const FUEL: usize = 200_000;
        let res = crate::interactive::iex_fast(&phi, psi_init, FUEL);

        let decoded = decode_result(&res.psi);
        let rendered = pretty(&decoded);
        let preview: String = rendered.chars().take(4000).collect();

        eprintln!("─── dump_galaxy_nf ─────────────────────────────────────────");
        eprintln!("galaxy.txt: {} defs, entry :{}", g.defs.len(), g.entry);
        eprintln!("Φ stars         : {}", phi.len());
        eprintln!("IEx fuel        : {FUEL}");
        eprintln!("IEx steps       : {}", res.steps);
        eprintln!("normal form?    : {}", res.is_normal_form);
        eprintln!("surviving Ψ size: {} star(s)", res.psi.len());
        eprintln!(
            "decoded NF head : {}",
            match &decoded {
                GValue::Nil => "Nil".into(),
                GValue::Num(n) => format!("Num({n})"),
                GValue::Atom(a) => format!("Atom({a})"),
                GValue::Cons(_, _) => "Cons(…)".into(),
                GValue::Opaque(s) => format!("Opaque({s})"),
            }
        );
        if let Some(v) = list_to_vec(&decoded) {
            eprintln!("decoded NF len  : {} element(s) (proper list)", v.len());
        } else {
            eprintln!("decoded NF      : NOT a proper nil-terminated list");
        }
        eprintln!(
            "pretty(decoded) [{}{}]:",
            preview.len(),
            if rendered.len() > preview.len() { " chars, TRUNCATED" } else { " chars" }
        );
        eprintln!("{preview}");
        eprintln!("────────────────────────────────────────────────────────────");
    }
}
