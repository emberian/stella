//! KG6b — pinpoint why galaxy's `data` payload won't force.
//!
//!   cargo run -q --release --example galaxy_data_probe
//!
//! eval_forced the entry once, readback the (flag,newState,data) triple,
//! extract `data`, take its first element term, and eval_forced THAT ONCE
//! (no recursive deep-force — that explodes). Reports exactly what data[0]
//! is before/after a single forced evaluation: the precise stall datum.

use stella_core::galaxy::{self, eval_forced, readback_ray};
use stella_core::galaxy_decode::{decode, pretty};
use stella_core::term::{self, TermData, TermId};

fn cst(n: &str) -> TermId { term::mk_app_str(n, vec![]) }
fn ap(f: TermId, x: TermId) -> TermId { term::mk_app_str("a", vec![f, x]) }
fn tag(t: TermId) -> String {
    match term::get(t) {
        TermData::Var(_) => "<var>".into(),
        TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
    }
}
/// `a(a(cons,H),T)` → (H,T).
fn as_cons(t: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(s, a) = term::get(t) else { return None };
    if s.name.as_str() != "a" || a.len() != 2 { return None; }
    let TermData::App(s2, a2) = term::get(a[0]) else { return None };
    if s2.name.as_str() != "a" || a2.len() != 2 { return None; }
    match term::get(a2[0]) {
        TermData::App(s3, a3) if a3.is_empty() && s3.name.as_str() == "cons" => Some((a2[1], a[1])),
        _ => None,
    }
}
fn tree(t: TermId, d: usize, md: usize, o: &mut String) {
    let p = "  ".repeat(d);
    if d >= md { o.push_str(&format!("{p}{} …\n", tag(t))); return; }
    match term::get(t) {
        TermData::Var(_) => o.push_str(&format!("{p}<var>\n")),
        TermData::App(s, a) => {
            o.push_str(&format!("{p}{}/{}\n", s.name.as_str(), a.len()));
            for (i, &c) in a.iter().enumerate() {
                if i >= 4 { o.push_str(&format!("{p}  …(+{})\n", a.len()-4)); break; }
                tree(c, d+1, md, o);
            }
        }
    }
}

fn main() {
    let path = "/Users/ember/dev/embershot/src/galaxy.txt";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s, Err(e) => { eprintln!("[skip] {path}: {e}"); return; }
    };
    let g = galaxy::parse(&src).expect("parse");
    let phi = galaxy::constellation(&g);
    let entry = galaxy::ref_atom(g.entry);
    let click = ap(ap(cst("cons"), stella_core::binarith::nat(0)), stella_core::binarith::nat(0));
    let prog = ap(ap(entry, cst("nil")), click);

    // Force a term once, return its readback (the canonical "force one
    // node" step decode_forced uses).
    let force1 = |t: TermId| -> (bool, usize, usize, usize, TermId) {
        let f = eval_forced(&phi, t, 2_000_000, 100_000);
        (f.fully_reduced, f.steps, f.arith_ops, f.forcings,
         readback_ray(f.final_ray.unwrap_or(f.value)))
    };
    // Force `t`, then peel ONE cons cell — forcing the cell itself first
    // (cons fields are lazy; the cell is a thunk until demanded).
    let step_cons = |label: &str, t: TermId| -> Option<(TermId, TermId)> {
        let (fr, st, ao, fo, rb) = force1(t);
        let c = as_cons(rb);
        println!("  [{label}] force: fully_reduced={fr} steps={st} arith_ops={ao} forcings={fo} \
                  head={} cons?={}", tag(rb), c.is_some());
        if c.is_none() {
            let mut s = String::new(); tree(rb, 0, 5, &mut s);
            println!("  [{label}] NOT a cons after forcing — readback:\n{s}");
        }
        c
    };

    println!("descending the (flag,newState,data) spine, forcing each field:");
    // entry → cons(flag, T1)
    let Some((flag, t1)) = step_cons("triple", prog) else { return; };
    println!("  flag = {}", pretty(&decode({ let (_,_,_,_,r)=force1(flag); r })));
    // T1 → cons(newState, T2)
    let Some((_nstate, t2)) = step_cons("after-flag", t1) else { return; };
    // T2 → cons(data, nil)
    let Some((data, _nil)) = step_cons("after-state", t2) else { return; };
    // data → cons(img0, rest)
    let Some((img0, _rest)) = step_cons("data", data) else { return; };

    println!("\n→ data[0] (an image): forcing generously, ONE level:");
    let (fr, st, ao, fo, rbd0) = force1(img0);
    println!("  fully_reduced={fr} steps={st} arith_ops={ao} forcings={fo}");
    println!("  readback_head={}  decoded={}", tag(rbd0), pretty(&decode(rbd0)));
    let mut s2 = String::new(); tree(rbd0, 0, 7, &mut s2);
    println!("  readback(data[0]) raw:\n{s2}");
    if let Some((p0, _)) = as_cons(rbd0) {
        let (fr2, st2, ao2, _, rp) = force1(p0);
        println!("  data[0][0] (first point?): fully_reduced={fr2} steps={st2} arith_ops={ao2} \
                  decoded={}", pretty(&decode(rp)));
    }
}
