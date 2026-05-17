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
                        "    decode(readback) = {}",
                        pretty(&stella_core::galaxy_decode::decode(rb))
                    );
                }
                None => println!("    (no final ray — Ψ shape unexpected)"),
            }
            break;
        }
    }
}
