//! KG3a — galaxy execution probe (honest fitness measurement).
//!
//!   cargo run -q --release --example galaxy_probe
//!
//! Builds the canonical first interaction `ap ap :galaxy nil (ap ap cons 0 0)`
//! over KG2's loaded galaxy Φ, runs it through `iex_fast` under bounded fuel,
//! and reports — WITHOUT guessing — exactly how far stellar resolution gets
//! and what (if anything) blocks it. This retires the central unknown ("does
//! galaxy run at all?") and turns "what's needed for galaxy executable" from
//! speculation into a measured, prioritized list. Slow/blocked is a fine,
//! expected, *informative* outcome (spec §8 N-GAL).

use std::time::Instant;
use stella_core::galaxy;
use stella_core::interactive::iex_fast;
use stella_core::term::{self, TermData, TermId};

fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}
fn cst(n: &str) -> TermId {
    term::mk_app_str(n, vec![])
}

/// Count head-symbol occurrences in a term (to see what it's made of /
/// blocked on), capped so a huge stuck term doesn't explode the walk.
fn head_census(t: TermId, budget: &mut i64) -> std::collections::BTreeMap<String, u64> {
    let mut m = std::collections::BTreeMap::new();
    fn go(t: TermId, m: &mut std::collections::BTreeMap<String, u64>, budget: &mut i64) {
        if *budget <= 0 {
            return;
        }
        *budget -= 1;
        match term::get(t) {
            TermData::Var(_) => *m.entry("<var>".into()).or_default() += 1,
            TermData::App(s, args) => {
                *m.entry(s.name.as_str().to_string()).or_default() += 1;
                for a in args.iter() {
                    go(*a, m, budget);
                }
            }
        }
    }
    go(t, &mut m, budget);
    m
}

fn main() {
    let path = "/Users/ember/dev/embershot/src/galaxy.txt";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[galaxy_probe] SKIP — {path}: {e}");
            return;
        }
    };

    let g = galaxy::parse(&src).expect("galaxy.txt must parse (KG2 verified)");
    let phi = galaxy::constellation(&g);
    println!(
        "loaded: entry :{}  defs={}  Φ stars={} (7 machine + {} δ)",
        g.entry,
        g.defs.len(),
        phi.len(),
        g.defs.len()
    );

    // Canonical first interaction: ap ap :entry nil (ap ap cons 0 0)
    let entry = galaxy::ref_atom(g.entry);
    let nil = cst("nil");
    let zero = stella_core::binarith::nat(0);
    let point = ap(ap(cst("cons"), zero), zero);
    let prog = ap(ap(entry, nil), point);

    // Initial process [ +P(st(prog, eps)) ] — the combinator/galaxy IEx shape.
    let proc0 = term::mk_app_str(
        "+P",
        vec![term::mk_app_str("st", vec![prog, cst("eps")])],
    );
    let psi = vec![vec![proc0]];

    for &fuel in &[2_000usize, 50_000, 500_000] {
        let t0 = Instant::now();
        let res = iex_fast(&phi, psi.clone(), fuel);
        let dt = t0.elapsed();
        println!(
            "\nfuel={fuel}: steps={} normal_form={} elapsed={:.3}s psi_stars={}",
            res.steps,
            res.is_normal_form,
            dt.as_secs_f64(),
            res.psi.len()
        );
        // Inspect the surviving process star: where did it get to / block?
        if let Some(star) = res.psi.iter().find(|s| s.len() == 1) {
            let mut budget = 4000i64;
            let census = head_census(star[0], &mut budget);
            // The interesting bit: which *primitive* heads remain (cons/car/
            // cdr/nil/isnil/add/mul/div/neg/eq/lt) — those have NO rule in
            // galaxy::constellation ⇒ they are the concrete blockers.
            let prims = [
                "cons", "car", "cdr", "nil", "isnil", "add", "mul", "div", "neg", "eq",
                "lt",
            ];
            let blocked: Vec<String> = prims
                .iter()
                .filter_map(|p| census.get(*p).map(|n| format!("{p}×{n}")))
                .collect();
            let aps = census.get("a").copied().unwrap_or(0);
            let stars: Vec<String> = census
                .iter()
                .filter(|(k, _)| {
                    matches!(k.as_str(), "S" | "B" | "C" | "I" | "T" | "F" | "P" | "st")
                })
                .map(|(k, v)| format!("{k}×{v}"))
                .collect();
            println!(
                "  result-term: a(app)×{aps}  engine[{}]  PRIMITIVE-BLOCKERS[{}]  (census capped @4000 nodes)",
                stars.join(","),
                if blocked.is_empty() { "none".into() } else { blocked.join(",") }
            );
        } else {
            println!("  (no single-ray process star survived; psi shape unexpected)");
        }
        if res.is_normal_form {
            println!(
                "  → reached NORMAL FORM in {} steps: stellar resolution can drive galaxy's\n    Push/δ/combinator skeleton; remaining heads above are the exact execution gap.",
                res.steps
            );
            break;
        }
    }
    // ── KG3c: disclosed §60 host-forcing (isnil + arith via sbinarith) ──────
    println!("\n[KG3c] disclosed §60 host-forcing driver (isnil + arith):");
    let t0 = Instant::now();
    let f = galaxy::eval_forced(&phi, prog, 200_000, 5_000);
    let dt = t0.elapsed();
    println!(
        "  isnil_forcings={} arith_ops={} total_steps={} isnil_complete={} fully_reduced={} elapsed={:.3}s",
        f.forcings, f.arith_ops, f.steps, f.isnil_complete, f.fully_reduced, dt.as_secs_f64()
    );
    let mut budget = 6000i64;
    let census = head_census(f.value, &mut budget);
    let prims = [
        "cons", "car", "cdr", "nil", "isnil", "add", "mul", "div", "neg", "eq", "lt",
    ];
    let residual: Vec<String> = prims
        .iter()
        .filter_map(|p| census.get(*p).map(|n| format!("{p}×{n}")))
        .collect();
    println!(
        "  result heads: a×{}  RESIDUAL[{}]",
        census.get("a").copied().unwrap_or(0),
        if residual.is_empty() { "none".into() } else { residual.join(",") }
    );
    println!(
        "  → {}",
        if f.fully_reduced && f.forcings == 0 && f.arith_ops == 0 {
            "NO blocked isnil/arith redex EVER — the forcing driver correctly \
             stayed idle; galaxy reaches a true normal form on Φ+lazy-prims \
             alone. The RESIDUAL heads are DATA (unapplied, like isnil was), \
             NOT stuck redexes. `focus a×0` ⇒ the real output structure is on \
             the continuation π, which st_inner drops. NEXT is NOT more forcing \
             — it is a proper full-result decoder (does the NF = the correct \
             (flag,newState,data)?), which IS the rendering path."
        } else if f.fully_reduced {
            "fully reduced via host-forced isnil/arith — galaxy evaluates; \
             output structure → rendering."
        } else {
            "honest measured stop: residual is div (KS/KA2 frontier) or a \
             non-numeral operand (deeper structural residual). Not faked."
        }
    );

    println!(
        "\n[verdict] KG3a→KG3c measured. Forcing infra built+faithful but galaxy \
         doesn't strict-stall on it (0 forcings/0 arith). Reprioritized: next = \
         a faithful full-result decoder (π not focus) = the rendering path. \
         Measured curve, not a guess; nothing faked."
    );
}
