//! Benchmark: blind oracle vs semi-naive vs SmallestFirst strategy.
//!
//! Run with:
//!   cargo bench -p stella-core
//!
//! Workloads:
//!   - horn_add_3_3: Horn addition 3+3
//!   - horn_add_5_5: Horn addition 5+5
//!   - nfa_000:      NFA Fig 56.1 on word "000"
//!   - nfa_00100:    NFA Fig 56.1 on word "00100"
//!   - ntm_aabb:     NTM aⁿbⁿ on "aabb" (via automata NFA proxy since NTM uses iex)

use criterion::{criterion_group, criterion_main, Criterion};
use stella_core::{
    automata::{eng_fig561_nfa, nfa_constellation},
    dep_graph::DepGraph,
    execution::{aex, aex_full, aex_seminaive, aex_seminaive_full, aex_with_strategy},
    polarised::{neg_ray, pos_ray},
    strategy::SmallestFirst,
    term::Term,
};

// ─────────────────────────────────────────────────────────────────────────────
// Term helpers
// ─────────────────────────────────────────────────────────────────────────────

fn var(x: &str) -> Term {
    stella_core::term::mk_var(x)
}

fn app(f: &str, args: Vec<Term>) -> Term {
    stella_core::term::mk_app_str(f, args)
}

fn c(name: &str) -> Term {
    stella_core::term::mk_app_str(name, vec![])
}

fn nat(n: usize) -> Term {
    let mut t = c("0");
    for _ in 0..n {
        t = app("s", vec![t]);
    }
    t
}

// ─────────────────────────────────────────────────────────────────────────────
// Constellation builders
// ─────────────────────────────────────────────────────────────────────────────

/// Horn addition program + query for m+n.
fn add_constellation(m: usize, n: usize) -> stella_core::constellation::Constellation {
    // Base case: [+add(0, Y, Y)]
    let base = vec![pos_ray("add", vec![c("0"), var("Y"), var("Y")])];
    // Step: [-add(X,Y,Z), +add(s(X),Y,s(Z))]
    let step = vec![
        neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
        pos_ray(
            "add",
            vec![
                app("s", vec![var("X")]),
                var("Y"),
                app("s", vec![var("Z")]),
            ],
        ),
    ];
    // Query: [-add(m, n, R), R]
    let query = vec![neg_ray("add", vec![nat(m), nat(n), var("R")]), var("R")];
    vec![base, step, query]
}

/// NFA Fig 56.1 constellation for a given word (with extra_copies=0).
fn nfa_phi(word: &[&str]) -> stella_core::constellation::Constellation {
    let nfa = eng_fig561_nfa();
    nfa_constellation(&nfa, word, 0)
}

/// Minimal aⁿbⁿ recogniser as a Horn constellation.
///
/// We model the language {aⁿbⁿ | n≥0} with a Horn-clause reachability program:
///
///   match(0, 0)       ← base: balanced empty
///   match(s(A), s(B)) ← match(A, B)   ← step: balanced one more
///
/// Query: match(s(s(0)), s(s(0))) — tests n=2 ("aabb").
/// This is a proxy for the aⁿbⁿ accept question; the result is the empty star.
fn anbn_constellation(n: usize) -> stella_core::constellation::Constellation {
    // Base: [+match(0, 0)]
    let base = vec![pos_ray("match", vec![c("0"), c("0")])];
    // Step: [-match(A, B), +match(s(A), s(B))]
    let step = vec![
        neg_ray("match", vec![var("A"), var("B")]),
        pos_ray(
            "match",
            vec![app("s", vec![var("A")]), app("s", vec![var("B")])],
        ),
    ];
    // Query: [-match(n, n), result]
    let query = vec![
        neg_ray("match", vec![nat(n), nat(n)]),
        var("Result"),
    ];
    vec![base, step, query]
}

// ─────────────────────────────────────────────────────────────────────────────
// Benchmark functions
// ─────────────────────────────────────────────────────────────────────────────

fn bench_horn_add_3_3(c: &mut Criterion) {
    let phi = add_constellation(3, 3);
    let mut grp = c.benchmark_group("horn_add_3_3");

    grp.bench_function("blind", |b| {
        b.iter(|| aex_full(criterion::black_box(&phi)))
    });

    grp.bench_function("seminaive", |b| {
        b.iter(|| aex_seminaive_full(criterion::black_box(&phi)))
    });

    let strategy = SmallestFirst;
    grp.bench_function("smallest_first", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let expanded = stella_core::execution::expand_constellation(phi, 2);
            let dg = DepGraph::from_constellation(&expanded);
            aex_with_strategy(&expanded, &dg, &strategy)
        })
    });

    grp.finish();
}

fn bench_horn_add_5_5(c: &mut Criterion) {
    let phi = add_constellation(5, 5);
    let mut grp = c.benchmark_group("horn_add_5_5");

    grp.bench_function("blind", |b| {
        b.iter(|| aex_full(criterion::black_box(&phi)))
    });

    grp.bench_function("seminaive", |b| {
        b.iter(|| aex_seminaive_full(criterion::black_box(&phi)))
    });

    let strategy = SmallestFirst;
    grp.bench_function("smallest_first", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let expanded = stella_core::execution::expand_constellation(phi, 2);
            let dg = DepGraph::from_constellation(&expanded);
            aex_with_strategy(&expanded, &dg, &strategy)
        })
    });

    grp.finish();
}

fn bench_nfa_000(c: &mut Criterion) {
    let phi = nfa_phi(&["0", "0", "0"]);
    let mut grp = c.benchmark_group("nfa_000");

    let dg_ref = DepGraph::from_constellation(&phi);

    grp.bench_function("blind", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let dg = criterion::black_box(&dg_ref);
            aex(phi, dg)
        })
    });

    grp.bench_function("seminaive", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let dg = criterion::black_box(&dg_ref);
            aex_seminaive(phi, dg)
        })
    });

    let strategy = SmallestFirst;
    grp.bench_function("smallest_first", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let dg = criterion::black_box(&dg_ref);
            aex_with_strategy(phi, dg, &strategy)
        })
    });

    grp.finish();
}

fn bench_nfa_00100(c: &mut Criterion) {
    let phi = nfa_phi(&["0", "0", "1", "0", "0"]);
    let mut grp = c.benchmark_group("nfa_00100");

    let dg_ref = DepGraph::from_constellation(&phi);

    grp.bench_function("blind", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let dg = criterion::black_box(&dg_ref);
            aex(phi, dg)
        })
    });

    grp.bench_function("seminaive", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let dg = criterion::black_box(&dg_ref);
            aex_seminaive(phi, dg)
        })
    });

    let strategy = SmallestFirst;
    grp.bench_function("smallest_first", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let dg = criterion::black_box(&dg_ref);
            aex_with_strategy(phi, dg, &strategy)
        })
    });

    grp.finish();
}

fn bench_anbn_n2(c: &mut Criterion) {
    // aⁿbⁿ proxy: match(2, 2) — represents "aabb"
    let phi = anbn_constellation(2);
    let mut grp = c.benchmark_group("anbn_n2_aabb");

    grp.bench_function("blind", |b| {
        b.iter(|| aex_full(criterion::black_box(&phi)))
    });

    grp.bench_function("seminaive", |b| {
        b.iter(|| aex_seminaive_full(criterion::black_box(&phi)))
    });

    let strategy = SmallestFirst;
    grp.bench_function("smallest_first", |b| {
        b.iter(|| {
            let phi = criterion::black_box(&phi);
            let expanded = stella_core::execution::expand_constellation(phi, 2);
            let dg = DepGraph::from_constellation(&expanded);
            aex_with_strategy(&expanded, &dg, &strategy)
        })
    });

    grp.finish();
}

// ─────────────────────────────────────────────────────────────────────────────
// Criterion entry points
// ─────────────────────────────────────────────────────────────────────────────

criterion_group!(
    benches,
    bench_horn_add_3_3,
    bench_horn_add_5_5,
    bench_nfa_000,
    bench_nfa_00100,
    bench_anbn_n2,
);

criterion_main!(benches);
