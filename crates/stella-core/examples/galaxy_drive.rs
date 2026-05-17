//! KG3g — drive galaxy's first interaction to a real result.
//!
//!   cargo run -q --release --example galaxy_drive
//!
//! Calls `galaxy::eval_forced` on the canonical first interaction with
//! escalating (fuel, max_forcings) budgets and reports the measured curve:
//! arith_ops resolved, fully_reduced, and the decoded value. Honest — every
//! reduction is the stellar engine; arithmetic is the disclosed §60 forced
//! (s)binarith path (incl. div, user-authorised). Stops are measured, not
//! faked.

use std::time::Instant;
use stella_core::galaxy;
use stella_core::galaxy_decode::{decode, pretty};
use stella_core::sbinarith::dsint;
use stella_core::term::{self, TermData, TermId};

fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}
fn cst(n: &str) -> TermId {
    term::mk_app_str(n, vec![])
}

/// KAM readback: `+P(st(M, f0·f1·…·eps))` ≡ the term `M f0 f1 …`
/// (`a(a(…a(M,f0),f1)…)`). The Push rule uncurried applications onto π;
/// folding the stack back reconstructs the applicative term the decoder
/// understands. Total: a non-`st` ray, or non-`dot` π, just folds what it has.
fn readback(ray: TermId) -> TermId {
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
    loop {
        match term::get(pi) {
            TermData::App(d, da) if d.name.as_str() == "dot" && da.len() == 2 => {
                frames.push(da[0]);
                pi = da[1];
            }
            _ => break,
        }
    }
    for f in frames {
        head = ap(head, f);
    }
    head
}

/// `a(a(cons,H),T)` → `(H,T)`.
fn as_cons(t: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(s, a) = term::get(t) else { return None };
    if s.name.as_str() != "a" || a.len() != 2 {
        return None;
    }
    let TermData::App(s2, a2) = term::get(a[0]) else { return None };
    if s2.name.as_str() != "a" || a2.len() != 2 {
        return None;
    }
    match term::get(a2[0]) {
        TermData::App(s3, a3) if a3.is_empty() && s3.name.as_str() == "cons" => {
            Some((a2[1], a[1]))
        }
        _ => None,
    }
}
fn is_nil(t: TermId) -> bool {
    matches!(term::get(t), TermData::App(s,a) if a.is_empty() && s.name.as_str()=="nil")
}

/// Deep-force: galaxy's result spine is lazy — `eval_forced` yields only the
/// outer WHNF cons. To get the full `(flag,newState,data)` we recursively
/// force+readback each cons field to normal form. Bounded (depth + global
/// node budget) ⇒ a huge/looping payload is an honest measured stop.
fn deep_force(
    phi: &stella_core::constellation::Constellation,
    t: TermId,
    fuel: usize,
    maxf: usize,
    depth: usize,
    budget: &mut usize,
) -> TermId {
    if *budget == 0 || depth == 0 {
        return t;
    }
    *budget -= 1;
    let f = galaxy::eval_forced(phi, t, fuel, maxf);
    let rb = readback(f.final_ray.unwrap_or(f.value));
    if dsint(rb).is_some() || is_nil(rb) {
        return rb;
    }
    if let Some((h, tl)) = as_cons(rb) {
        let h2 = deep_force(phi, h, fuel, maxf, depth - 1, budget);
        let tl2 = deep_force(phi, tl, fuel, maxf, depth - 1, budget);
        return ap(ap(cst("cons"), h2), tl2);
    }
    rb
}

fn main() {
    let path = "/Users/ember/dev/embershot/src/galaxy.txt";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[galaxy_drive] SKIP — {path}: {e}");
            return;
        }
    };
    let g = galaxy::parse(&src).expect("galaxy.txt parses");
    let phi = galaxy::constellation(&g);
    let entry = galaxy::ref_atom(g.entry);
    let point = ap(
        ap(cst("cons"), stella_core::binarith::nat(0)),
        stella_core::binarith::nat(0),
    );
    let prog = ap(ap(entry, cst("nil")), point);

    for &(fuel, maxf) in &[
        (200_000usize, 5_000usize),
        (1_000_000, 50_000),
        (5_000_000, 500_000),
    ] {
        let t0 = Instant::now();
        let f = galaxy::eval_forced(&phi, prog, fuel, maxf);
        let dt = t0.elapsed();
        println!(
            "fuel={fuel} maxf={maxf}: steps={} arith_ops={} forcings={} fully_reduced={} elapsed={:.2}s",
            f.steps, f.arith_ops, f.forcings, f.fully_reduced, dt.as_secs_f64()
        );
        println!(
            "  value_head={:?}  decoded(value)={}",
            match term::get(f.value) {
                term::TermData::Var(_) => "<var>".to_string(),
                term::TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
            },
            pretty(&decode(f.value))
        );
        if f.fully_reduced {
            println!("  → FULLY REDUCED. Decoding the forced final ray:");
            match f.final_ray {
                Some(ray) => {
                    // KAM readback: st(M, a·b·…·eps) ≡ M applied to the stack,
                    // i.e. a(a(…a(M,a),b)…). The Push rule built π by
                    // uncurrying; fold it back so the applicative decoder sees
                    // the real cons-structure (the result is Push-form, the
                    // decoder is applicative-form — same shape mismatch the
                    // forcing fix solved, now on the output side).
                    let rb = readback(ray);
                    println!(
                        "    decode(readback)    = {}",
                        pretty(&stella_core::galaxy_decode::decode(rb))
                    );
                    // Deep-force the lazy result spine — TIGHTLY bounded
                    // (depth/node budget + small per-node fuel). Naive
                    // deep-force re-runs eval_forced per subterm ⇒ explosive;
                    // a full pixel-level force is a KS-throughput problem, not
                    // a correctness one. This shows how much structure
                    // resolves cheaply.
                    let mut budget = 1500usize;
                    let full = deep_force(&phi, prog, 60_000, 400, 16, &mut budget);
                    println!(
                        "    decode(deep_force)  = {}  (nodes used {})",
                        pretty(&decode(full)),
                        1500 - budget
                    );
                    // Drill into data[0]: full = [flag, newState, data].
                    if let Some((_flag, r1)) = as_cons(full) {
                        if let Some((_st, r2)) = as_cons(r1) {
                            if let Some((data, _)) = as_cons(r2) {
                                if let Some((d0, _)) = as_cons(data) {
                                    println!("\n  raw data[0] (an image?):");
                                    let mut s = String::new();
                                    fn tr(t: TermId, d: usize, md: usize, o: &mut String) {
                                        let p = "  ".repeat(d);
                                        if d >= md {
                                            o.push_str(&format!("{p}…\n"));
                                            return;
                                        }
                                        match term::get(t) {
                                            TermData::Var(_) => o.push_str(&format!("{p}<var>\n")),
                                            TermData::App(s, a) => {
                                                o.push_str(&format!("{p}{}/{}\n", s.name.as_str(), a.len()));
                                                for c in a.iter() {
                                                    tr(*c, d + 1, md, o);
                                                }
                                            }
                                        }
                                    }
                                    tr(d0, 0, 7, &mut s);
                                    print!("{s}");
                                    let fd0 = galaxy::eval_forced(&phi, d0, fuel, maxf);
                                    println!(
                                        "  eval_forced(data[0]): fully_reduced={} value_head={:?} readback_decoded={}",
                                        fd0.fully_reduced,
                                        match term::get(fd0.value) {
                                            TermData::Var(_) => "<var>".into(),
                                            TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
                                        },
                                        pretty(&decode(readback(fd0.final_ray.unwrap_or(fd0.value))))
                                    );
                                }
                            }
                        }
                    }
                }
                None => println!("    (no final ray — Ψ shape unexpected)"),
            }
            break;
        }
    }
}
