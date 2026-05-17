//! The reformulated (invariant⇒flat) Phase-4 make-or-break, skeptic-runnable.
//!
//!   cargo run -p stella-core --example reformulated_make_or_break
//!
//! Runs `perturbation::run_reformulated_make_or_break` over the locked corpus
//! (Eng-own constructions + the ω-weight §80 member + the mandatory objective
//! invariant-control), measuring closure-internal `viability_internal`
//! (re_closure·ρ, §3.1-op) under a closure-self-maintenance-disrupting
//! perturbation across strengths × caps. Prints the raw ReformReport. No
//! verdict() — read by hand against the locked spec §4 M1–M5, with the
//! perturbation-potency (inverse-confound) check done explicitly.

use stella_core::perturbation::run_reformulated_make_or_break;

fn main() {
    let strengths: Vec<u32> = vec![0, 1, 2, 3];
    let caps: Vec<usize> = vec![40, 80, 120];
    eprintln!("== reformulated make-or-break :: strengths={strengths:?} caps={caps:?} ==");
    let report = run_reformulated_make_or_break(&strengths, &caps);
    println!("{}", report.plain_text_dump);
    println!("---- locked spec §4 gate results (read by hand) ----");
    println!("M1 (smuggled individuation)        : {:?}", report.m1_result);
    println!("M2 (invariance ⇒ flat)             : {:?}", report.m2_result);
    println!("M3 (artifact, not response)        : {:?}", report.m3_result);
    println!("M4 (engineered one level up)       : {:?}", report.m4_result);
    println!("M5 (cross-level sealed)            : {:?}", report.m5_result);
    println!("(no verdict() — adjudicated by hand vs spec §4, incl. the inverse-confound/potency check)");
}
