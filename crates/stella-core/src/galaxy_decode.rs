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
// Numeral decode (signed) — local; there is no `sbinarith` in this tree.
// ─────────────────────────────────────────────────────────────────────────────

/// Decode a galaxy signed numeral. Tries [`crate::binarith::denat`]
/// (non-negative `bz`/`o0`/`o1`) first; otherwise an `App("neg",[ <nat> ])`
/// placeholder ⇒ `-nat`. Returns `None` if the term is not a numeral shape.
///
/// (The originating spec named this `sbinarith::dsint`; no such module exists
/// in this tree — galaxy encodes non-negatives via `binarith::nat` and
/// negatives via the `neg(_)` placeholder, so the signed decode is composed
/// here from `binarith::denat`.)
fn dsint(t: TermId) -> Option<i128> {
    if let Some(n) = crate::binarith::denat(t) {
        return i128::try_from(n).ok();
    }
    if let TermData::App(sym, args) = get(t) {
        if sym.name.as_str() == "neg" && args.len() == 1 {
            let mag = crate::binarith::denat(args[0])?;
            let mag = i128::try_from(mag).ok()?;
            return Some(-mag);
        }
    }
    None
}

/// Encode a signed integer the way galaxy does — non-negative via
/// [`crate::binarith::nat`], negative via the `neg(nat(mag))` placeholder.
/// Test/round-trip helper (the spec's `sbinarith::sint`).
pub fn sint(n: i128) -> TermId {
    if n >= 0 {
        crate::binarith::nat(n as u128)
    } else {
        crate::term::mk_app_str("neg", vec![crate::binarith::nat((-n) as u128)])
    }
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
/// 1. numeral (signed) — try first, so a `neg(nat n)` never looks like an atom;
/// 2. `nil` atom → [`GValue::Nil`];
/// 3. cons-cell shape → [`GValue::Cons`] of decoded head/tail;
/// 4. any other 0-ary atom → [`GValue::Atom`];
/// 5. anything else → [`GValue::Opaque`] (`head/arity` tag) — never coerced.
pub fn decode(t: TermId) -> GValue {
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

/// Score: size of the largest list-ish (nil / cons-cell) structure rooted at
/// `t`, scanning *all* subterms. `nil` and a non-list leaf both score 0/…;
/// a cons-cell scores `1 + max(child scores)` so the *outermost, deepest*
/// list wins. Used purely to pick the best decode root — never asserts.
fn list_score(t: TermId) -> usize {
    // Iterative; galaxy continuations can nest very deep.
    fn cell_depth(t: TermId) -> usize {
        let mut best = 0usize;
        let mut stack = vec![(t, 0usize)];
        while let Some((cur, _d)) = stack.pop() {
            if is_nil(cur) {
                continue;
            }
            if let Some((h, tl)) = as_cons_cell(cur) {
                best += 1; // count every reachable cons-cell on any path
                stack.push((h, 0));
                stack.push((tl, 0));
            }
        }
        best
    }
    cell_depth(t)
}

/// Walk every subterm of `root`; return the subterm with the highest
/// [`list_score`] (ties → the first encountered in pre-order, i.e. the
/// outermost). Always returns *some* term (worst case `root` itself).
fn best_list_subterm(root: TermId) -> TermId {
    let mut best = root;
    let mut best_score = 0usize;
    let mut stack = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let sc = if is_nil(t) {
            1 // a bare nil still beats a non-list root
        } else if as_cons_cell(t).is_some() {
            1 + list_score(t)
        } else {
            0
        };
        if sc > best_score {
            best_score = sc;
            best = t;
        }
        if let TermData::App(_, args) = get(t) {
            for &a in args.iter() {
                stack.push(a);
            }
        }
    }
    best
}

/// Decode the value produced by a finished process Ψ.
///
/// # Heuristic (documented precisely; the decode itself never lies)
///
/// 1. Find the single-ray star whose lone ray is `+P(st(M, π))`
///    (via [`unwrap_process_ray`], polarity-agnostic on head name `P`,
///    matching `combinator::read_value`). If several exist, the **first** in
///    Ψ order is taken. If none exists, fall back to the first ray of the
///    first star in Ψ (so the function is still total).
/// 2. Prefer `M`: if `M` is itself list-ish (`nil` or a cons-cell), decode
///    `M` directly — that is the clean, expected case.
/// 3. Otherwise the answer is on the continuation: scan **the whole ray**
///    (`App("P",[App("st",[M,π])])`, i.e. both `M` and `π` and everything
///    nested) for the subterm with the largest reachable nil/cons-cell
///    structure ([`best_list_subterm`] / [`list_score`]) and decode that.
///    Ties resolve to the outermost (pre-order-first) subterm.
/// 4. If no star matched at all in step 1, decode the chosen fallback ray
///    whole via the same step-3 search.
///
/// This is a *best-effort legibility* heuristic, not a correctness oracle: it
/// surfaces the biggest list-shaped thing the engine left behind so a human
/// can judge whether the galaxy actually produced a sensible value.
pub fn decode_result(psi: &[crate::constellation::Star]) -> GValue {
    // Step 1: locate the process ray.
    let mut process: Option<(TermId, TermId, TermId)> = None; // (ray, M, π)
    'find: for star in psi {
        if star.len() != 1 {
            continue;
        }
        if let Some((m, pi)) = unwrap_process_ray(star[0]) {
            process = Some((star[0], m, pi));
            break 'find;
        }
    }
    // Also tolerate multi-ray stars containing a process ray (defensive).
    if process.is_none() {
        'find2: for star in psi {
            for &r in star {
                if let Some((m, pi)) = unwrap_process_ray(r) {
                    process = Some((r, m, pi));
                    break 'find2;
                }
            }
        }
    }

    match process {
        Some((ray, m, _pi)) => {
            // Step 2: M itself is a clean list value ⇒ decode it directly.
            if is_nil(m) || as_cons_cell(m).is_some() {
                return decode(m);
            }
            // Step 3: the value is on the continuation — search the whole ray.
            decode(best_list_subterm(ray))
        }
        None => {
            // Step 4: no process ray at all — be total: search the first ray.
            match psi.first().and_then(|s| s.first()).copied() {
                Some(r) => decode(best_list_subterm(r)),
                None => GValue::Opaque("empty-psi".to_string()),
            }
        }
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
    fn decode_result_finds_value_in_continuation() {
        // Build a finished process whose M is NOT a list but π carries the
        // real list — decode_result must find it on the continuation.
        let list = cell(sint(9), cell(sint(8), nil_t())); // [9, 8]
        let m = mk_app_str("garbage", vec![mk_app_str("x", vec![])]); // non-list M
        let eps = mk_app_str("eps", vec![]);
        let pi = mk_app_str("dot", vec![list, eps]); // value parked on π
        let st = mk_app_str("st", vec![m, pi]);
        let ray = mk_app_str("+P", vec![st]);
        let psi: Vec<crate::constellation::Star> = vec![vec![ray]];
        let d = decode_result(&psi);
        assert_eq!(pretty(&d), "[9, 8]");
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
