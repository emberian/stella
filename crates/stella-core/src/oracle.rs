//! Unified differential-oracle harness — one call, one structured verdict.
//!
//! The codebase already has several *independent* differential oracles, each
//! cross-checking one engine component against a slower reference:
//!
//! * [`faithfulness::psi_compatible`](crate::faithfulness::psi_compatible) —
//!   the ɟ-concealed visible answer multiset of a `fast` interaction space
//!   against a `reference` one (docs/09 §A). The result-compatibility
//!   validator.
//! * The **execution α-equivalence** oracle —
//!   [`execution::aex_full`](crate::execution::aex_full) (the `Blind` /
//!   2-animist-copy reference saturator) against
//!   [`execution::aex_seminaive_full`](crate::execution::aex_seminaive_full)
//!   (the alternative semi-naive worklist engine). Documented to be
//!   α-equivalent on well-formed Φ; compared here as multisets via
//!   [`execution::stars_alpha_equiv`](crate::execution::stars_alpha_equiv).
//! * The **dep-graph index** oracle —
//!   [`DepGraph::build`](crate::dep_graph::DepGraph::build) (the O(n²) scan)
//!   against [`DepGraph::build_indexed`](crate::dep_graph::DepGraph::build_indexed)
//!   (the first-symbol index, §49.7). Documented to produce an identical edge
//!   set; this is the same canonical-edge-set compare `index.rs`'s in-module
//!   `assert_oracle_equiv` uses.
//!
//! This module does **not** reimplement any of them. [`check_all`] *calls
//! into* the existing functions and aggregates their boolean verdicts into one
//! [`OracleReport`] carrying a per-oracle pass/fail with a human reason. It is
//! the Goodhart-guard pattern of `evaluate.rs` / KG7 generalised to one entry
//! point: a single composite criterion a search cannot route around without
//! every constituent oracle agreeing.
//!
//! Honest seam (measured, not papered over): the four other in-tree
//! differential oracles — the `mll` dr_correct↔classical pair, the
//! `iex_*_result_eq_iex` family, the `unify_fast` differential fuzz, and the
//! §67.10 cut-elim calibration — are **not** composed here. They do not share
//! the `(phi, psi)` signature `check_all` takes: they are property/fuzz
//! harnesses parameterised by their own generators, not `(Φ,Ψ)`→verdict
//! deciders. Forcing them under this entry point would mean inventing inputs
//! they were not built to take, i.e. faking aggregation. They stay where they
//! are; [`OracleReport`] reports exactly the three that *do* compose on
//! `(Φ,Ψ)`, and says so.

use crate::constellation::{Constellation, Star};
use crate::dep_graph::{all_colours, DepGraph};
use crate::execution::{aex_full, aex_seminaive_full, stars_alpha_equiv};
use crate::faithfulness::psi_compatible;

/// Verdict of one constituent oracle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleVerdict {
    /// Stable oracle identifier (e.g. `"faithfulness::psi_compatible"`).
    pub name: &'static str,
    /// `true` iff this oracle's reference and fast paths agreed.
    pub passed: bool,
    /// Human-readable reason — what was compared and the outcome.
    pub reason: String,
}

/// Aggregate report from [`check_all`]: every composed oracle's verdict, plus
/// the conjunction. `all_passed` is `true` **iff every** constituent oracle
/// passed — a search that Goodharts any single component is caught here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleReport {
    pub verdicts: Vec<OracleVerdict>,
    pub all_passed: bool,
}

impl OracleReport {
    /// The first failing verdict, if any — convenient for assert messages.
    pub fn first_failure(&self) -> Option<&OracleVerdict> {
        self.verdicts.iter().find(|v| !v.passed)
    }
}

/// Canonical edge-set of a dep-graph: sorted vector of sorted endpoint pairs.
/// Identical shape to `index.rs`'s in-module `edge_set` helper (the basis of
/// its `assert_oracle_equiv`). Defined here only to *compare* the two existing
/// `DepGraph` builders' public `edges` output — no graph logic is reimplemented.
fn edge_set(dg: &DepGraph) -> Vec<[(usize, usize); 2]> {
    let mut v: Vec<[(usize, usize); 2]> = dg.edges.iter().map(|e| e.endpoints).collect();
    v.sort();
    v
}

/// Multiset-equality of two star sets under α-equivalence, using the existing
/// [`stars_alpha_equiv`](crate::execution::stars_alpha_equiv). Greedy match:
/// for each `a` star, consume one not-yet-consumed `b` star it is α-equal to.
/// Sound for the equality decision (it can only ever report a divergence that
/// is real — never mask one), which is the contract these oracles hold.
fn stars_multiset_alpha_equiv(a: &[Star], b: &[Star]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut used = vec![false; b.len()];
    for sa in a {
        let mut matched = false;
        for (j, sb) in b.iter().enumerate() {
            if !used[j] && stars_alpha_equiv(sa, sb) {
                used[j] = true;
                matched = true;
                break;
            }
        }
        if !matched {
            return false;
        }
    }
    true
}

/// Run every `(Φ,Ψ)`-composable differential oracle and aggregate.
///
/// `phi` is the program constellation; `psi` is the initial interaction space.
/// `reference` / `fast` are two final interaction spaces to be checked
/// ψ-compatible (e.g. a slow reference run and a fast-path run of the same
/// `(Φ,Ψ)`); pass the same slice twice if only the engine-internal oracles are
/// of interest.
///
/// Composes (does not reimplement):
///
/// 1. `faithfulness::psi_compatible(reference, fast)` — visible answer
///    multiset agreement.
/// 2. execution α-equivalence — `aex_full(phi)` vs `aex_seminaive_full(phi)`
///    as α-multisets.
/// 3. dep-graph index — `DepGraph::build(phi, C)` vs
///    `DepGraph::build_indexed(phi, C)` canonical edge sets.
///
/// `all_passed` is the conjunction: a single composite pass/fail-with-reasons.
pub fn check_all(
    phi: &Constellation,
    psi: &[Star],
    reference: &[Star],
    fast: &[Star],
) -> OracleReport {
    let mut verdicts = Vec::with_capacity(3);

    // 1. faithfulness::psi_compatible — the result-compatibility validator.
    let psi_ok = psi_compatible(reference, fast);
    verdicts.push(OracleVerdict {
        name: "faithfulness::psi_compatible",
        passed: psi_ok,
        reason: if psi_ok {
            "reference and fast interaction spaces are ψ-compatible \
             (equal ɟ-concealed α-canonical visible-answer multisets)"
                .to_string()
        } else {
            "reference and fast interaction spaces are NOT ψ-compatible: \
             visible answer multisets differ (missing/extra/duplicated/\
             structurally-changed answer)"
                .to_string()
        },
    });

    // 2. execution α-equivalence: Blind/2-copy reference saturator vs the
    //    alternative semi-naive worklist engine on the *same* Φ.
    let ref_aex = aex_full(phi);
    let fast_aex = aex_seminaive_full(phi);
    let aex_ok = stars_multiset_alpha_equiv(&ref_aex, &fast_aex);
    verdicts.push(OracleVerdict {
        name: "execution::aex_full~aex_seminaive_full",
        passed: aex_ok,
        reason: format!(
            "aex_full ({} stars) vs aex_seminaive_full ({} stars): {}",
            ref_aex.len(),
            fast_aex.len(),
            if aex_ok {
                "α-equivalent as multisets"
            } else {
                "NOT α-equivalent — the alternative engine diverges from the reference saturator"
            }
        ),
    });

    // 3. dep-graph index oracle: scan-built vs index-built D[Φ;C] edge sets.
    let colours = all_colours(phi);
    let scan = DepGraph::build(phi, &colours);
    let indexed = DepGraph::build_indexed(phi, &colours);
    let idx_ok = edge_set(&scan) == edge_set(&indexed);
    verdicts.push(OracleVerdict {
        name: "dep_graph::build~build_indexed",
        passed: idx_ok,
        reason: format!(
            "scan-built ({} edges) vs index-built ({} edges) dep-graph: {}",
            scan.edges.len(),
            indexed.edges.len(),
            if idx_ok {
                "identical canonical edge sets"
            } else {
                "edge sets DIFFER — the first-symbol index missed or invented a matchable pair"
            }
        ),
    });

    // psi is part of the composite contract surface (the (Φ,Ψ) the reference
    // and fast spaces were produced from); referenced here so the harness
    // signature is the documented one even though the constituent oracles
    // consume Φ and the two final spaces directly.
    let _ = psi;

    let all_passed = verdicts.iter().all(|v| v.passed);
    OracleReport {
        verdicts,
        all_passed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interactive::iex;
    use crate::term::{mk_app_str, mk_var, Term};

    fn var(x: &str) -> Term {
        mk_var(x)
    }
    fn cst(name: &str) -> Term {
        mk_app_str(name, vec![])
    }
    fn app(f: &str, args: Vec<Term>) -> Term {
        mk_app_str(f, args)
    }
    fn nat(n: usize) -> Term {
        let mut t = cst("0");
        for _ in 0..n {
            t = app("s", vec![t]);
        }
        t
    }

    /// Horn addition program, same shape as `index.rs` / `evaluate.rs` use.
    fn add_prog() -> Constellation {
        use crate::polarised::{neg_ray, pos_ray};
        vec![
            vec![pos_ray("add", vec![cst("0"), var("Y"), var("Y")])],
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray(
                    "add",
                    vec![
                        app("s", vec![var("X")]),
                        var("Y"),
                        app("s", vec![var("Z")]),
                    ],
                ),
            ],
        ]
    }

    fn add_query(a: usize, b: usize) -> Star {
        use crate::polarised::neg_ray;
        vec![neg_ray("add", vec![nat(a), nat(b), var("R")]), var("R")]
    }

    /// Positive: a real, faithful run. Every composed oracle must pass and
    /// the aggregate must be `all_passed`.
    #[test]
    fn check_all_passes_on_faithful_run() {
        let phi = add_prog();
        let psi = vec![add_query(3, 2)];
        let result = iex(&phi, psi.clone(), 5000);
        assert!(result.is_normal_form, "reference run converges");

        // reference == fast == the same faithful space: ψ-compatible trivially,
        // and the engine-internal oracles run on Φ.
        let report = check_all(&phi, &psi, &result.psi, &result.psi);
        assert!(
            report.all_passed,
            "faithful run must pass every composed oracle; first failure: {:?}",
            report.first_failure()
        );
        assert_eq!(report.verdicts.len(), 3, "three oracles compose on (Φ,Ψ)");
        assert!(report.verdicts.iter().all(|v| v.passed));
    }

    /// THE GOODHART-GUARD. Take the faithful result, forge a wrong-but-
    /// plausible "fast" space (an extra all-neutral star that SURVIVES
    /// conceal+filter as a spurious visible answer the engine never produces),
    /// and feed it as `fast`. The unified harness MUST flag it: the
    /// `faithfulness::psi_compatible` verdict fails and `all_passed` is false.
    /// This proves `check_all` actually catches an unfaithful path rather than
    /// rubber-stamping it — the point of the module.
    #[test]
    fn check_all_must_flag_unfaithful_fast_path() {
        let phi = add_prog();
        let psi = vec![add_query(3, 2)];
        let reference = iex(&phi, psi.clone(), 5000);
        assert!(reference.is_normal_form, "reference converges");

        // Forge: same shape, plus a spurious all-neutral visible answer.
        let mut forged = reference.psi.clone();
        forged.push(vec![app("BOGUS", vec![cst("0")])]);

        let report = check_all(&phi, &psi, &reference.psi, &forged);

        assert!(
            !report.all_passed,
            "unified harness MUST NOT pass an unfaithful fast path"
        );
        let failed = report
            .first_failure()
            .expect("there must be a failing verdict");
        assert_eq!(
            failed.name, "faithfulness::psi_compatible",
            "the ψ-compatibility oracle is the one that must catch the forged answer; \
             reason: {}",
            failed.reason
        );
        // The two engine-internal oracles still pass (Φ unchanged) — only the
        // result-compatibility oracle fires, exactly as the Goodhart-guard
        // pattern intends (a precise, non-blanket failure).
        let internal_pass = report
            .verdicts
            .iter()
            .filter(|v| v.name != "faithfulness::psi_compatible")
            .all(|v| v.passed);
        assert!(
            internal_pass,
            "engine-internal oracles must still pass on the unchanged Φ"
        );
    }
}
