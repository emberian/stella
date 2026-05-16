//! The Phase-4 make-or-break run, skeptic-runnable.
//!
//!   cargo run -p stella-core --example make_or_break
//!
//! Runs the N1–N4-gated harness (`experiment::run_make_or_break`) over the
//! LOCKED corpus (Eng's own subjective constructions, built for other
//! purposes; partitions solved-for, not designated). Prints the raw
//! EvidenceReport. It does NOT pronounce a verdict — that is read, by hand,
//! against the pre-registered spec §4 nulls. Honest-null is a real result.

use stella_core::experiment::run_make_or_break;

fn main() {
    let max_rounds: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(40);

    eprintln!("== Phase-4 make-or-break :: max_rounds={max_rounds} ==");
    let report = run_make_or_break(max_rounds);

    println!("{}", report.plain_text_dump);
    println!("---- pre-registered gate results (spec §4) ----");
    println!("N1 (closure only via hand-engineering)        : {:?}", report.n1_result);
    println!("N2 (closure layers causally sealed)           : {:?}", report.n2_result);
    println!("N3 (accretes only under per-task hand-tuning) : {:?}", report.n3_result);
    println!("N4 (subjective as idempotent as objective)    : {:?}", report.n4_result);
    println!("(no verdict() — the reading is done by hand, against spec §4)");
}
