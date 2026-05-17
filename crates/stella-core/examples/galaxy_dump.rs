//! KG3e — galaxy TERMINAL-STATE dump (why is the NF shallow?).
//!
//!   cargo run -q --release --example galaxy_dump
//!
//! `galaxy_probe` established: galaxy reaches `is_normal_form=true` in 371
//! steps with a 342-`a`-node surviving ray, and the decoder collapses it to a
//! tiny `[0,[]]`. That left the real question open: is `[0,[]]` a genuine
//! small value, or is the machine stuck in a `+P(st(M,π))` state with a VALUE
//! in `M` and a huge un-consumed continuation `π` (a Krivine/Push "value
//! applied to leftover stack" — i.e. an entry/protocol-shape mismatch, not an
//! arithmetic stall)? This dumps the exact terminal `(M, π)` so we can SEE it
//! instead of guessing: M's raw head/shape, whether M is a value, the depth
//! and per-frame heads of the `dot`-spine continuation π, and where π ends.

use stella_core::galaxy;
use stella_core::interactive::iex_fast;
use stella_core::term::{self, TermData, TermId};

fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}
fn cst(n: &str) -> TermId {
    term::mk_app_str(n, vec![])
}

/// `head/arity` (or `Var`) tag for one node.
fn tag(t: TermId) -> String {
    match term::get(t) {
        TermData::Var(_) => "Var".into(),
        TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
    }
}

/// Bounded raw-tree print (depth-capped, child-count-capped).
fn tree(t: TermId, depth: usize, max_depth: usize, out: &mut String) {
    let pad = "  ".repeat(depth);
    if depth >= max_depth {
        out.push_str(&format!("{pad}{} …\n", tag(t)));
        return;
    }
    match term::get(t) {
        TermData::Var(_) => out.push_str(&format!("{pad}{}\n", tag(t))),
        TermData::App(s, a) => {
            out.push_str(&format!("{pad}{}/{}\n", s.name.as_str(), a.len()));
            for (i, &c) in a.iter().enumerate() {
                if i >= 6 {
                    out.push_str(&format!("{pad}  …(+{} more)\n", a.len() - 6));
                    break;
                }
                tree(c, depth + 1, max_depth, out);
            }
        }
    }
}

/// Total node count (capped) — to size M vs π honestly.
fn count(t: TermId, budget: &mut i64) -> i64 {
    if *budget <= 0 {
        return 0;
    }
    *budget -= 1;
    let mut n = 1;
    if let TermData::App(_, a) = term::get(t) {
        for &c in a.iter() {
            n += count(c, budget);
        }
    }
    n
}

/// Unwrap `+P(st(M, π))` (polarity-agnostic on the `P` head name).
fn unwrap(ray: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(p, pa) = term::get(ray) else { return None };
    if p.name.as_str() != "P" || pa.len() != 1 {
        return None;
    }
    let TermData::App(s, sa) = term::get(pa[0]) else { return None };
    if s.name.as_str() != "st" || sa.len() != 2 {
        return None;
    }
    Some((sa[0], sa[1]))
}

fn main() {
    let path = "/Users/ember/dev/embershot/src/galaxy.txt";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[galaxy_dump] SKIP — {path}: {e}");
            return;
        }
    };
    let g = galaxy::parse(&src).expect("galaxy.txt must parse");
    let phi = galaxy::constellation(&g);

    // Canonical first interaction: ap ap :entry nil (ap ap cons 0 0).
    let entry = galaxy::ref_atom(g.entry);
    let point = ap(ap(cst("cons"), stella_core::binarith::nat(0)), stella_core::binarith::nat(0));
    let prog = ap(ap(entry, cst("nil")), point);
    let proc0 = term::mk_app_str("+P", vec![term::mk_app_str("st", vec![prog, cst("eps")])]);

    let res = iex_fast(&phi, vec![vec![proc0]], 500_000);
    println!(
        "entry :{}  Φ={}  steps={}  normal_form={}  Ψ stars={}",
        g.entry, phi.len(), res.steps, res.is_normal_form, res.psi.len()
    );

    let ray = match res.psi.iter().find(|s| s.len() == 1) {
        Some(s) => s[0],
        None => {
            println!("no single-ray process star — Ψ shape unexpected");
            return;
        }
    };
    let (m, pi) = match unwrap(ray) {
        Some(x) => x,
        None => {
            println!("surviving ray is not +P(st(M,π)); raw:");
            let mut s = String::new();
            tree(ray, 0, 5, &mut s);
            print!("{s}");
            return;
        }
    };

    let (mut bm, mut bp) = (200_000i64, 200_000i64);
    let (nm, np) = (count(m, &mut bm), count(pi, &mut bp));
    println!("\n── M (focused term) ──  nodes≈{nm}  head={}", tag(m));
    let mut sm = String::new();
    tree(m, 0, 6, &mut sm);
    print!("{sm}");
    println!(
        "  decoded(M) = {}",
        stella_core::galaxy_decode::pretty(&stella_core::galaxy_decode::decode(m))
    );
    println!(
        "  decode_result(Ψ) = {}",
        stella_core::galaxy_decode::pretty(&stella_core::galaxy_decode::decode_result(&res.psi))
    );

    // Walk the continuation π: it is a right-nested `dot(frame, π')` spine
    // terminated by `eps`. Report depth + each frame's head (this is the
    // KAM argument stack the final value is being applied against).
    println!("\n── π (continuation / KAM arg stack) ──  nodes≈{np}");
    let mut cur = pi;
    let mut frames: Vec<String> = Vec::new();
    let mut depth = 0usize;
    let term_end;
    loop {
        match term::get(cur) {
            TermData::App(s, a) if s.name.as_str() == "dot" && a.len() == 2 => {
                if frames.len() < 20 {
                    frames.push(tag(a[0]));
                }
                cur = a[1];
                depth += 1;
                if depth > 100_000 {
                    term_end = "…(π spine > 100k; aborted)".to_string();
                    break;
                }
            }
            _ => {
                term_end = tag(cur);
                break;
            }
        }
    }
    println!("  π spine depth (frames) = {depth}   terminator = {term_end}");
    println!("  first frames (head/arity, outermost first):");
    for (i, f) in frames.iter().enumerate() {
        println!("    [{i}] {f}");
    }

    // If the head is a strict op, the first frames ARE its operands — dump
    // them so we can see WHY they don't force to numerals.
    if let TermData::App(hs, ha) = term::get(m) {
        if ha.is_empty()
            && matches!(hs.name.as_str(), "add" | "mul" | "eq" | "lt" | "neg")
        {
            let arity = if hs.name.as_str() == "neg" { 1 } else { 2 };
            println!("\n── operands of `{}` (the stalled strict op) ──", hs.name.as_str());
            let mut cur = pi;
            for k in 0..arity {
                let TermData::App(d, da) = term::get(cur) else { break };
                if d.name.as_str() != "dot" || da.len() != 2 {
                    break;
                }
                let opnd = da[0];
                let mut b = 200_000i64;
                let n = count(opnd, &mut b);
                let (sh, sn) = {
                    // local spine-head
                    let mut t = opnd;
                    let mut na = 0;
                    loop {
                        match term::get(t) {
                            TermData::App(s, a) if s.name.as_str() == "a" && a.len() == 2 => {
                                na += 1;
                                t = a[0];
                            }
                            TermData::App(s, a) if a.is_empty() => break (Some(s.name.as_str().to_string()), na),
                            _ => break (None, na),
                        }
                    }
                };
                println!(
                    "  operand[{k}]: nodes≈{n}  head={}  spine_head={:?}/{}  decoded={}",
                    tag(opnd),
                    sh,
                    sn,
                    stella_core::galaxy_decode::pretty(&stella_core::galaxy_decode::decode(opnd))
                );
                let mut so = String::new();
                tree(opnd, 0, 4, &mut so);
                print!("{so}");
                // Force THIS operand alone via the full forced evaluator and
                // report exactly where it stalls.
                let fo = galaxy::eval_forced(&phi, opnd, 500_000, 5000);
                let mut b2 = 200_000i64;
                println!(
                    "    └ eval_forced(operand[{k}]): value_head={} value_nodes≈{} arith_ops={} fully_reduced={} decoded={}",
                    tag(fo.value),
                    count(fo.value, &mut b2),
                    fo.arith_ops,
                    fo.fully_reduced,
                    stella_core::galaxy_decode::pretty(&stella_core::galaxy_decode::decode(fo.value))
                );
                let mut sv = String::new();
                tree(fo.value, 0, 4, &mut sv);
                for l in sv.lines() {
                    println!("      {l}");
                }
                cur = da[1];
            }
        }
    }

    println!("\n── verdict inputs ──");
    println!(
        "  M is value? {}   π empty (eps)? {}   π depth {}",
        matches!(term::get(m), TermData::App(s,a) if a.is_empty()
            && matches!(s.name.as_str(), "nil"|"t"|"f")) ,
        term_end == "eps/0",
        depth
    );
    println!(
        "  ⇒ if M is a value AND π is non-empty: the Push/Krivine machine HALTED\n     applying a value to leftover stack frames — an entry/protocol-shape\n     mismatch (galaxy expects a different interaction call), NOT an arith\n     stall. If M is itself a partial cons-spine: lazy-WHNF under-forcing."
    );
}
