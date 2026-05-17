//! KG3g — recursively chase galaxy's strict-op operand tree to the leaf
//! that actually blocks.
//!
//!   cargo run -q --release --example galaxy_chase
//!
//! `eval_forced` returns only its focus, hiding WHERE deep in the recursive
//! operand tree the chain bottoms out. This walks it explicitly: run the
//! stellar engine to NF, find the Push-form strict-op redex
//! (`galaxy::find_blocked_pushform`), and recurse into each operand until we
//! reach either a numeral (resolved) or a genuine non-numeral, non-redex
//! dead-end — which it prints (head, arity, decoded), with the op path that
//! led there. That dead-end is the real remaining gap.

use stella_core::galaxy;
use stella_core::interactive::iex_fast;
use stella_core::sbinarith::dsint;
use stella_core::term::{self, TermData, TermId};

fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}
fn cst(n: &str) -> TermId {
    term::mk_app_str(n, vec![])
}
fn tag(t: TermId) -> String {
    match term::get(t) {
        TermData::Var(_) => "<var>".into(),
        TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
    }
}

/// Reduce `t` to engine NF (fresh `+P(st(t,eps))`), return the surviving ray.
fn nf_ray(phi: &stella_core::constellation::Constellation, t: TermId, fuel: usize) -> Option<TermId> {
    let proc0 = term::mk_app_str("+P", vec![term::mk_app_str("st", vec![t, cst("eps")])]);
    let res = iex_fast(phi, vec![vec![proc0]], fuel);
    res.psi.iter().find(|s| s.len() == 1).map(|s| s[0])
}

/// `M` of `+P(st(M,π))`.
fn focus(ray: TermId) -> TermId {
    if let TermData::App(p, pa) = term::get(ray) {
        if p.name.as_str() == "P" && pa.len() == 1 {
            if let TermData::App(s, sa) = term::get(pa[0]) {
                if s.name.as_str() == "st" && sa.len() == 2 {
                    return sa[0];
                }
            }
        }
    }
    ray
}

const FUEL: usize = 2_000_000;

/// Returns `Some(n)` if `t` resolves to numeral `n`; else prints the dead-end
/// (with the op path) and returns `None`. `depth` caps the walk.
fn chase(
    phi: &stella_core::constellation::Constellation,
    t: TermId,
    path: &mut Vec<&'static str>,
    depth: usize,
    hits: &mut usize,
) -> Option<i128> {
    *hits += 1;
    if *hits > 200_000 {
        println!("  [{}] …(chase node budget exhausted)", path.join(">"));
        return None;
    }
    if depth == 0 {
        println!("  [{}] …(max depth)", path.join(">"));
        return None;
    }
    let ray = match nf_ray(phi, t, FUEL) {
        Some(r) => r,
        None => {
            println!("  [{}] NO single ray (Ψ shape)", path.join(">"));
            return None;
        }
    };
    let m = focus(ray);
    if let Some(n) = dsint(m) {
        return Some(n);
    }
    match galaxy::find_blocked_pushform(ray) {
        None => {
            // Not a numeral, no Push-form redex ⇒ the genuine dead-end.
            println!(
                "  DEAD-END at [{}]: focus head={} decoded={}",
                path.join(">"),
                tag(m),
                stella_core::galaxy_decode::pretty(&stella_core::galaxy_decode::decode(m))
            );
            None
        }
        Some((op, operands, _resid)) => {
            for (i, &o) in operands.iter().enumerate() {
                path.push(op);
                let r = chase(phi, o, path, depth - 1, hits);
                path.pop();
                if r.is_none() {
                    println!(
                        "  ↑ operand[{i}] of `{op}` at [{}] did not resolve",
                        path.join(">")
                    );
                    return None;
                }
            }
            // All operands resolved ⇒ this op would compute; report success
            // implicitly (the parent recomputes via sbinarith in real run).
            Some(0)
        }
    }
}

fn main() {
    let path = "/Users/ember/dev/embershot/src/galaxy.txt";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[galaxy_chase] SKIP — {path}: {e}");
            return;
        }
    };
    let g = galaxy::parse(&src).expect("parses");
    let phi = galaxy::constellation(&g);
    let entry = galaxy::ref_atom(g.entry);
    let point = ap(
        ap(cst("cons"), stella_core::binarith::nat(0)),
        stella_core::binarith::nat(0),
    );
    let prog = ap(ap(entry, cst("nil")), point);

    println!("chasing galaxy first-interaction strict-op operand tree…");
    let mut pathv = Vec::new();
    let mut hits = 0usize;
    let r = chase(&phi, prog, &mut pathv, 60, &mut hits);
    println!("\nchase nodes visited: {hits}");
    match r {
        Some(_) => println!("→ all operands on the walked tree resolve to numerals."),
        None => println!("→ blocked: see the DEAD-END line above (the real remaining gap)."),
    }
}
