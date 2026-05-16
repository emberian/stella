//! Lazy unbounded non-linear supply streaming executor (Eng §51.13).
//!
//! # L1a: `subjective_stream`
//!
//! This module implements **Layer 1a** of the Phase-4 subjective engine plan
//! (`docs/01-subjective-engine-and-valence.md §5`): a lazy, coinductive streaming
//! interface over the IEx stellar interaction steps, with **unbounded on-demand
//! fresh supply** replacing the `expand_constellation(copies=2)` finite cap.
//!
//! ## Design: §51.13 non-linear supply
//!
//! Eng §51.13 states that the reference constellation Φ provides an *infinite*
//! supply: each interaction step fetches a **fresh α-renamed copy** of the
//! selected Φ star on demand, consuming none of the original. Our
//! `expand_constellation` approximation is replaced here by true lazy supply:
//! the iterator holds Φ by reference and freshens each star at the point of use.
//!
//! ## What L1a does NOT implement
//!
//! - **§49.50 subjective-ray reduction** (new-ray creation + semaphore sync):
//!   deliberately deferred to L1b. This step drives the *objective/animist*
//!   constellations via the existing §51.9 interaction semantics only.
//! - **D[Ψ_k;C] agent/environment cut marking**: deferred to L1c.
//! - **Proper-time extraction**: deferred to L2b.
//!
//! ## Faithfulness gate (the whole point of L1a)
//!
//! On objective/terminating constellations, `subjective_stream` driven to its
//! normal form must produce a result α-equivalent to `iex_concealed`. The tests
//! below assert this property on the existing worked examples (Horn add, tiny NFA,
//! objective pair).

use std::collections::HashSet;

use crate::ch9::{saturation_profile, ConstellationClass};
use crate::constellation::{Constellation, Star};
use crate::dep_graph::{all_colours, DepGraph};
use crate::polarised::{ray_polarity, Polarity};
use crate::subst::Substitution;
use crate::term::{mk_var_interned, Var, Term};
use crate::unify::{unify, Equation};

// ─────────────────────────────────────────────────────────────────────────────
// Re-use interaction internals
//
// We cannot call the private helpers in interactive.rs directly, so we
// reproduce the minimal subset we need here.  This duplication is bounded: L1b
// will consolidate once the module boundary is clearer.
// ─────────────────────────────────────────────────────────────────────────────

/// Collect all colours present in `psi` (the current interaction space).
fn psi_colours(psi: &[Star]) -> HashSet<String> {
    all_colours(&psi.to_vec())
}

/// α-rename an entire star, returning the renamed star and the substitution.
fn alpha_rename_star(star: &Star, prefix: &str, counter: &mut u64) -> Star {
    use rustc_hash::FxHashSet;
    let all_vars: Vec<Var> = star
        .iter()
        .flat_map(|&r| r.vars())
        .collect::<FxHashSet<_>>()
        .into_iter()
        .collect();

    let pairs: Vec<(Var, Term)> = all_vars
        .into_iter()
        .map(|v| {
            let fresh_name = format!("{prefix}_{}{counter}", v.as_str());
            *counter += 1;
            let fresh_var = Var::intern(&fresh_name);
            (v, mk_var_interned(fresh_var))
        })
        .collect();
    let subst = Substitution::from_var_pairs(pairs);
    star.iter().map(|&r| subst.apply(r)).collect()
}

/// Fusion `φ₁ ^{j, j'}∇_α φ₂` (§49.30). Returns `None` on unification failure.
fn fuse_stars(phi1: &Star, j: usize, phi2_renamed: &Star, j_prime: usize) -> Option<Star> {
    use crate::polarised::underlying_term;
    let r1 = underlying_term(phi1[j]);
    let r2 = underlying_term(phi2_renamed[j_prime]);
    let theta = unify(vec![Equation::new(r1, r2)])?;

    let mut result: Star = phi1
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j)
        .map(|(_, &r)| theta.apply(r))
        .collect();

    let rest2: Star = phi2_renamed
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j_prime)
        .map(|(_, &r)| theta.apply(r))
        .collect();

    result.extend(rest2);
    Some(result)
}

/// Self-interaction `^{j,j'}▷ star` (§51.7). Returns `None` on failure.
fn self_interact_star(star: &Star, j: usize, j_prime: usize) -> Option<Star> {
    use crate::polarised::underlying_term;
    let r1 = underlying_term(star[j]);
    let r2 = underlying_term(star[j_prime]);
    let theta = unify(vec![Equation::new(r1, r2)])?;
    let result: Star = star
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j && idx != j_prime)
        .map(|(_, &r)| theta.apply(r))
        .collect();
    Some(result)
}

/// `mat_self(star, j)`: indices `j'` in the same star matchable with `star[j]`.
fn mat_self_local(star: &Star, j: usize) -> Vec<usize> {
    use crate::polarised::matchable;
    let r = star[j];
    star.iter()
        .enumerate()
        .filter(|&(jk, _)| jk != j)
        .filter(|&(_, &ray)| matchable(r, ray))
        .map(|(jk, _)| jk)
        .collect()
}

/// mat_Φ^C(r) restricted to the colour set C = colours(Φ) ∪ colours(Ψ).
fn mat_phi_full(
    phi: &Constellation,
    r: Term,
    extra_c: &HashSet<String>,
) -> Vec<(usize, usize)> {
    use crate::dep_graph::ray_colours;
    use crate::polarised::matchable;

    let mut c_set = all_colours(phi);
    c_set.extend(extra_c.iter().cloned());
    let cr = ray_colours(r);

    let mut result = Vec::new();
    for (i, star) in phi.iter().enumerate() {
        for (j, &ray) in star.iter().enumerate() {
            if ray_polarity(ray) == Polarity::Neutral {
                continue;
            }
            let crj = ray_colours(ray);
            if !cr.is_subset(&c_set) || !crj.is_subset(&c_set) {
                continue;
            }
            if matchable(r, ray) {
                result.push((i, j));
            }
        }
    }
    result
}

/// Check normal form: no coloured ray in Ψ has a match in Φ or itself.
fn is_nf(phi: &Constellation, psi: &[Star]) -> bool {
    let c_extra = psi_colours(psi);
    for (_, star) in psi.iter().enumerate() {
        for (j, &r) in star.iter().enumerate() {
            if ray_polarity(r) == Polarity::Neutral {
                continue;
            }
            if !mat_phi_full(phi, r, &c_extra).is_empty() {
                return false;
            }
            if !mat_self_local(star, j).is_empty() {
                return false;
            }
        }
    }
    true
}

/// One §51.9 interaction step: select the first actionable (star, ray), apply it,
/// return the new Ψ. Returns `None` when already in normal form.
fn one_step(phi: &Constellation, psi: Vec<Star>, counter: &mut u64) -> Option<Vec<Star>> {
    let c_extra = psi_colours(&psi);

    // Find first actionable coloured ray in Ψ.
    let mut found = None;
    'outer: for (i, star) in psi.iter().enumerate() {
        for (j, &r) in star.iter().enumerate() {
            if ray_polarity(r) == Polarity::Neutral {
                continue;
            }
            let has_ext = !mat_phi_full(phi, r, &c_extra).is_empty();
            let has_self = !mat_self_local(star, j).is_empty();
            if has_ext || has_self {
                found = Some((i, j));
                break 'outer;
            }
        }
    }

    let (i, j) = found?; // None ⇒ normal form

    let selected = psi[i].clone();
    let r = selected[j];

    // Ψ' = Ψ − {selected}
    let mut psi_prime: Vec<Star> = psi
        .into_iter()
        .enumerate()
        .filter(|&(idx, _)| idx != i)
        .map(|(_, s)| s)
        .collect();

    // External fusions with fresh copies from Φ (§51.13 on-demand supply).
    let ext_matches = mat_phi_full(phi, r, &c_extra);
    for (ik, jk) in ext_matches {
        let prefix = format!("ext{ik}_{counter}");
        *counter += 1;
        let phi_renamed = alpha_rename_star(&phi[ik], &prefix, counter);
        if let Some(fused) = fuse_stars(&selected, j, &phi_renamed, jk) {
            psi_prime.push(fused);
        }
    }

    // Self-interactions within the selected star.
    let self_matches = mat_self_local(&selected, j);
    for jk in self_matches {
        if let Some(si) = self_interact_star(&selected, j, jk) {
            psi_prime.push(si);
        }
    }

    Some(psi_prime)
}

// ─────────────────────────────────────────────────────────────────────────────
// Step (the yielded item)
// ─────────────────────────────────────────────────────────────────────────────

/// A single step in the `subjective_stream` trajectory.
///
/// Exposed to the caller after each §51.9 interaction. Carries:
/// - the **current interaction space** `Ψ_k` (linear, consumed from Ψ₀);
/// - a **dep-graph snapshot** `D[Ψ_k; C]` for reachability analysis;
/// - **cheap structural metrics** (no AEx run): Ψ size, matchable-frontier
///   size, Ch9 §62 structural class.
///
/// Step index ≠ proper time. This is the substrate/witness clock. The agent's
/// proper time is its own reafferent-cycle count, read off the trajectory by
/// Layer 2 — never this counter (§01-spec §2.6, substrate-time-death exclusion).
#[derive(Debug, Clone)]
pub struct Step {
    /// Substrate step index (k in Ψ_k).
    pub index: usize,

    /// Current interaction space Ψ_k: the live stars at this step.
    pub psi: Vec<Star>,

    /// Dependency graph snapshot `D[Ψ_k; C]`.
    /// Callers can inspect reachability, adjacency, and edge structure.
    pub dep_graph: DepGraph,

    /// Number of stars in Ψ_k (interaction-space size metric).
    pub psi_size: usize,

    /// Number of coloured rays in Ψ_k that have at least one match in Ψ_k or Φ
    /// (the "matchable frontier" — how much live interaction potential remains).
    pub frontier_size: usize,

    /// Ch9 §62 structural class of Ψ_k.
    ///
    /// - `Terminating`: Ψ_k is structurally tame (no branching, no cycles,
    ///   no subjective/animist stars).  On objective/dead constellations this
    ///   holds at normal form.
    /// - `NonTerminatingCandidate`: at least one structural risk factor present
    ///   (branching ray, subjective/animist star, or cycle in D[Ψ_k;C]).
    ///   This is the expected regime for the subjective/animist fragment.
    pub ch9_class: ConstellationClass,

    /// Whether this step's Ψ_k is in normal form w.r.t. Φ.
    /// When `true`, the stream will yield no further steps after this one.
    pub is_normal_form: bool,
}

// ─────────────────────────────────────────────────────────────────────────────
// Streaming executor
// ─────────────────────────────────────────────────────────────────────────────

/// Iterator state for `subjective_stream`.
pub struct SubjectiveStream<'a> {
    phi: &'a Constellation,
    psi: Vec<Star>,
    counter: u64,
    index: usize,
    exhausted: bool,
}

impl<'a> Iterator for SubjectiveStream<'a> {
    type Item = Step;

    fn next(&mut self) -> Option<Step> {
        if self.exhausted {
            return None;
        }

        // Compute the step's metrics for the CURRENT Ψ (before the step).
        let dep_graph = DepGraph::from_constellation(&self.psi);
        let psi_size = self.psi.len();
        let frontier_size = compute_frontier(self.phi, &self.psi);
        let prof = saturation_profile(&self.psi);
        let ch9_class = prof.class;
        let is_nf_now = is_nf(self.phi, &self.psi);

        // Snapshot for the step.
        let step = Step {
            index: self.index,
            psi: self.psi.clone(),
            dep_graph,
            psi_size,
            frontier_size,
            ch9_class,
            is_normal_form: is_nf_now,
        };

        // If already normal form, this is the terminal step; exhaust after.
        if is_nf_now {
            self.exhausted = true;
            return Some(step);
        }

        // Advance: apply one §51.9 step to Ψ.
        match one_step(self.phi, self.psi.clone(), &mut self.counter) {
            None => {
                // one_step returns None only when normal form was not detected above,
                // which should not happen — guard anyway.
                self.exhausted = true;
                Some(step)
            }
            Some(new_psi) => {
                self.psi = new_psi;
                self.index += 1;
                Some(step)
            }
        }
    }
}

/// Count the number of coloured rays in Ψ that have at least one match in Φ or
/// in their own star (the "matchable frontier").
fn compute_frontier(phi: &Constellation, psi: &[Star]) -> usize {
    let c_extra = psi_colours(psi);
    let mut count = 0;
    for star in psi.iter() {
        for (j, &r) in star.iter().enumerate() {
            if ray_polarity(r) == Polarity::Neutral {
                continue;
            }
            let has_ext = !mat_phi_full(phi, r, &c_extra).is_empty();
            let has_self = !mat_self_local(star, j).is_empty();
            if has_ext || has_self {
                count += 1;
            }
        }
    }
    count
}

// ─────────────────────────────────────────────────────────────────────────────
// Public API
// ─────────────────────────────────────────────────────────────────────────────

/// `subjective_stream(Φ, Ψ₀) -> impl Iterator<Item=Step>`
///
/// Lazy, unbounded, non-linear supply streaming executor (Eng §51.9–§51.13).
///
/// # Semantics
///
/// At each `.next()` call:
/// 1. **Yield** a `Step` containing the current Ψ_k, its dep-graph snapshot,
///    and cheap cost/reachability metrics (Ψ size, frontier size, Ch9 class).
/// 2. **Advance** by applying one §51.9 stellar interaction step to Ψ_k:
///    - Select the first coloured ray `(i, j)` in Ψ_k with any external or
///      self-interaction.
///    - Produce external fusions with **fresh α-renamed copies** of Φ stars,
///      fetched on demand (§51.13 non-linear supply — no copy cap).
///    - Produce self-interactions within the selected star.
///    - Consume the selected star (linear use).
/// 3. When Ψ_k is in normal form w.r.t. Φ, yield a final `Step` with
///    `is_normal_form: true` and then terminate the iterator.
///
/// # Bounding
///
/// The stream is potentially unbounded. Callers bound it:
/// - `.take(n)` for a finite prefix.
/// - Take until `step.is_normal_form` for objective/terminating cases.
/// - Leave unbounded for subjective/animist exploration.
///
/// # Faithfulness gate (L1a requirement)
///
/// On objective/terminating constellations the stream-to-normal-form result is
/// α-equivalent to `iex_concealed` (the existing oracle). This is asserted by
/// the tests in this module. A failure here is a bug — never weaken the test.
///
/// # Step index vs. proper time
///
/// `Step::index` is the substrate/witness clock. The agent's proper time is its
/// reafferent-cycle count, read off the trajectory by Layer 2 (§01-spec §2.6).
pub fn subjective_stream(phi: &Constellation, psi0: Vec<Star>) -> impl Iterator<Item = Step> + '_ {
    SubjectiveStream {
        phi,
        psi: psi0,
        counter: 0,
        index: 0,
        exhausted: false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Convenience: drive to normal form (for tests and callers that want the result)
// ─────────────────────────────────────────────────────────────────────────────

/// Drive `subjective_stream(Φ, Ψ₀)` to normal form (or `max_steps` steps),
/// returning the final `Step`.
///
/// Returns `None` only if the stream is empty (Ψ₀ itself is already in normal
/// form and the stream yields one step — so `None` is never returned in practice).
pub fn stream_to_normal_form(
    phi: &Constellation,
    psi0: Vec<Star>,
    max_steps: usize,
) -> Option<Step> {
    subjective_stream(phi, psi0)
        .take(max_steps + 1) // +1: normal-form step is the terminal yield
        .find(|s| s.is_normal_form)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::execution::stars_alpha_equiv;
    use crate::interactive::iex_concealed;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::Term;

    fn var(x: &str) -> Term { crate::term::mk_var(x) }
    fn app(f: &str, args: Vec<Term>) -> Term { crate::term::mk_app_str(f, args) }
    fn c(name: &str) -> Term { crate::term::mk_app_str(name, vec![]) }

    fn nat(n: usize) -> Term {
        let mut t = c("0");
        for _ in 0..n { t = app("s", vec![t]); }
        t
    }

    fn add_prog() -> Constellation {
        vec![
            vec![pos_ray("add", vec![c("0"), var("Y"), var("Y")])],
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray("add", vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])]),
            ],
        ]
    }

    fn query_star(m: usize, n: usize) -> Star {
        vec![
            neg_ray("add", vec![nat(m), nat(n), var("R")]),
            var("R"),
        ]
    }

    /// α-equivalence check for result-star multisets (unordered).
    fn result_sets_alpha_equiv(a: &[Star], b: &[Star]) -> bool {
        if a.len() != b.len() { return false; }
        let mut used = vec![false; b.len()];
        'outer: for sa in a {
            for (i, sb) in b.iter().enumerate() {
                if !used[i] && stars_alpha_equiv(sa, sb) {
                    used[i] = true;
                    continue 'outer;
                }
            }
            return false;
        }
        true
    }

    /// Apply `↨♭` (conceal + noise filter) to a Ψ, as the oracle does.
    fn conceal_and_filter(psi: &[Star]) -> Vec<Star> {
        crate::interactive::conceal_and_filter(psi)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Faithfulness gate: objective/terminating cases
    //
    // MANDATORY: stream-to-normal-form must equal iex_concealed (the oracle).
    // Any failure here is a correctness bug; never weaken these tests.
    // ─────────────────────────────────────────────────────────────────────────

    /// Horn add 1+1: stream reaches [2̄] ≈α oracle.
    #[test]
    fn faithfulness_horn_add_1_plus_1() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        // Oracle.
        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 500);
        assert!(oracle_nf, "oracle must reach normal form for add 1+1");

        // Stream.
        let term_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("stream must reach normal form for add 1+1");
        assert!(term_step.is_normal_form, "terminal step must be normal form");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "FAITHFULNESS GATE: stream 1+1 ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );

        // Check the expected value is present.
        let expected = vec![nat(2)];
        assert!(
            stream_visible.iter().any(|s| stars_alpha_equiv(s, &expected)),
            "stream 1+1 must contain [2̄]; got {:?}", stream_visible
        );
    }

    /// Horn add 2+2: stream reaches [4̄] ≈α oracle.
    #[test]
    fn faithfulness_horn_add_2_plus_2() {
        let phi = add_prog();
        let psi0 = vec![query_star(2, 2)];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 500);
        assert!(oracle_nf, "oracle must reach normal form for add 2+2");

        let term_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("stream must reach normal form for add 2+2");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "FAITHFULNESS GATE: stream 2+2 ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );

        let expected = vec![nat(4)];
        assert!(
            stream_visible.iter().any(|s| stars_alpha_equiv(s, &expected)),
            "stream 2+2 must contain [4̄]; got {:?}", stream_visible
        );
    }

    /// Tiny NFA ("00" accepts): stream ≈α oracle, and both contain [accept].
    ///
    /// Configuration: Φ = {init, final, t1, t2} (the NFA automaton stars);
    /// Ψ₀ = {word_star} (the input word "[+i(0·0·eps)]").
    /// This mirrors the §56.5 encoding used by `iex_concealed` in interactive.rs.
    #[test]
    fn faithfulness_nfa_tiny_objective() {
        use crate::term::mk_app_str;

        let eps  = mk_app_str("eps",  vec![]);
        let ch0  = mk_app_str("0",    vec![]);
        let cons = |ch: Term, rest: Term| mk_app_str("cons", vec![ch, rest]);
        let w00  = cons(ch0.clone(), cons(ch0.clone(), eps.clone()));

        // Word star: [+i(0·0·eps)] — this is Ψ₀.
        let word_star: Star = vec![pos_ray("i", vec![w00])];

        // NFA automaton stars — these are Φ (infinite supply).
        // Init: [-i(W), +a(W, q0)]
        let init: Star = vec![
            neg_ray("i",  vec![var("W")]),
            pos_ray("a",  vec![var("W"), mk_app_str("q0", vec![])]),
        ];
        // Final: [-a(eps, q2), accept]
        let fin_: Star = vec![
            neg_ray("a",  vec![eps.clone(), mk_app_str("q2", vec![])]),
            mk_app_str("accept", vec![]),
        ];
        // Transition q0 --0--> q1
        let t1: Star = vec![
            neg_ray("a", vec![
                mk_app_str("cons", vec![mk_app_str("0", vec![]), var("W")]),
                mk_app_str("q0", vec![]),
            ]),
            pos_ray("a", vec![var("W"), mk_app_str("q1", vec![])]),
        ];
        // Transition q1 --0--> q2
        let t2: Star = vec![
            neg_ray("a", vec![
                mk_app_str("cons", vec![mk_app_str("0", vec![]), var("W")]),
                mk_app_str("q1", vec![]),
            ]),
            pos_ray("a", vec![var("W"), mk_app_str("q2", vec![])]),
        ];

        // Φ = automaton stars (non-linear supply); Ψ₀ = word star (linear input).
        let phi: Constellation = vec![init, fin_, t1, t2];
        let psi0: Vec<Star>    = vec![word_star];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 500);
        assert!(oracle_nf, "oracle must reach normal form for NFA tiny");

        // Verify the oracle itself finds [accept] (sanity check on our Φ/Ψ split).
        let accept_star: Star = vec![mk_app_str("accept", vec![])];
        assert!(
            oracle_visible.iter().any(|s| s == &accept_star),
            "oracle NFA tiny must contain [accept]; got {:?}", oracle_visible
        );

        let term_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("stream must reach normal form for NFA tiny");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "FAITHFULNESS GATE: stream NFA tiny ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );

        assert!(
            stream_visible.iter().any(|s| s == &accept_star),
            "stream NFA tiny must contain [accept]; got {:?}", stream_visible
        );
    }

    /// Pure objective constellation [+a] + [+b]: empty Ψ₀ → immediate normal form
    /// (no coloured rays in query to interact), stream yields step 0 as normal form.
    #[test]
    fn faithfulness_objective_pair_inert() {
        // Two objective stars with no matchable pairs. Ψ₀ = φ itself but all
        // rays are positive — there is nothing to interact with.
        let phi: Constellation = vec![
            vec![pos_ray("a", vec![])],
            vec![pos_ray("b", vec![])],
        ];
        // Ψ₀ = just the "result slot" — an empty query. The stream starts already
        // in normal form (frontier = 0).
        let psi0: Vec<Star> = vec![];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 10);
        assert!(oracle_nf, "oracle: empty psi0 is already normal form");

        let term_step = stream_to_normal_form(&phi, psi0, 10)
            .expect("stream must yield at least one step");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "FAITHFULNESS GATE: stream objective pair ≠ oracle"
        );
        assert_eq!(term_step.index, 0, "normal form at step 0 (no interaction needed)");
    }

    /// Objective deterministic pair [+a] + [-a]: stream resolves to [] ≈α oracle.
    #[test]
    fn faithfulness_objective_deterministic_pair() {
        let phi: Constellation = vec![
            vec![pos_ray("a", vec![])],
        ];
        // Ψ₀ = the negative ray star (the query-side).
        let psi0: Vec<Star> = vec![vec![neg_ray("a", vec![])]];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 20);
        assert!(oracle_nf, "oracle must reach normal form for +a/-a pair");

        let term_step = stream_to_normal_form(&phi, psi0, 20)
            .expect("stream must yield a normal-form step for +a/-a");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "FAITHFULNESS GATE: stream +a/-a ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Step structure / metrics tests
    // ─────────────────────────────────────────────────────────────────────────

    /// Step exposes correct index sequence for Horn add 1+1.
    #[test]
    fn step_index_monotone_add_1_plus_1() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(200)
            .collect();

        assert!(!steps.is_empty(), "must yield at least one step");

        // Indices must be 0, 1, 2, …
        for (expected_idx, step) in steps.iter().enumerate() {
            assert_eq!(step.index, expected_idx,
                "step index must be monotone; at pos {expected_idx} got index {}", step.index);
        }

        // Final step must be normal form.
        let last = steps.last().unwrap();
        assert!(last.is_normal_form, "last step must be normal form");
    }

    /// frontier_size decreases to 0 at normal form.
    #[test]
    fn frontier_zero_at_normal_form_horn() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        let final_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("must reach normal form");

        assert_eq!(final_step.frontier_size, 0,
            "frontier must be 0 at normal form; got {}", final_step.frontier_size);
    }

    /// dep_graph snapshot in each step is non-panicking and consistent.
    #[test]
    fn dep_graph_snapshot_no_panic_horn() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        for step in subjective_stream(&phi, psi0).take(50) {
            // DepGraph must be consistent with psi.
            assert_eq!(step.dep_graph.n_stars, step.psi.len(),
                "dep_graph.n_stars must match psi size at step {}", step.index);
            if step.is_normal_form { break; }
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Subjective/animist progress tests
    //
    // For the animist fragment (e.g. the full Horn program including the recursive
    // clause as part of Φ interacting with itself), we do NOT claim correctness yet
    // (that is L1b). We assert only that:
    //   (a) the stream yields Steps,
    //   (b) the index advances,
    //   (c) psi_size and frontier_size are non-negative usize values,
    //   (d) ch9_class is a valid ConstellationClass.
    //
    // Bounded by .take(small_n) as required.
    // ─────────────────────────────────────────────────────────────────────────

    /// Animist constellation (full add program with recursive star): stream
    /// progresses and exposes Steps. No correctness claim — progress only.
    #[test]
    fn progress_animist_add_self_interaction() {
        let phi = add_prog(); // both stars are in Φ
        // Ψ₀ = just the recursive step star (animist: has both +add and -add rays)
        let psi0: Vec<Star> = vec![
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray("add", vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])]),
            ],
        ];

        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(8)
            .collect();

        assert!(!steps.is_empty(), "animist stream must yield at least one step");

        // All steps must have valid (non-overflowing) metrics.
        for step in &steps {
            // psi_size is usize — always >= 0; just check it's set.
            let _ = step.psi_size;
            let _ = step.frontier_size;
            // ch9_class must be a valid variant (exhaustive match, no panic).
            let _ = match step.ch9_class {
                ConstellationClass::Terminating => 0,
                ConstellationClass::NonTerminatingCandidate => 1,
            };
        }

        // The stream must advance: at least some step has index > 0, or we got
        // exactly one (already-normal-form) step.
        let max_idx = steps.iter().map(|s| s.index).max().unwrap_or(0);
        // Either we got multiple steps (progress), or we got one at index 0.
        assert!(
            steps.len() == 1 || max_idx > 0,
            "stream must either terminate in 1 step or advance beyond index 0"
        );
    }

    /// Subjective constellation (single negative ray): stream exposes Steps.
    #[test]
    fn progress_subjective_single_neg() {
        // Φ = [+c(X)], Ψ₀ = [-c(Y)] — subjective query star.
        let phi: Constellation = vec![
            vec![pos_ray("c", vec![var("X")])],
        ];
        let psi0: Vec<Star> = vec![
            vec![neg_ray("c", vec![var("Y")])],
        ];

        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(6)
            .collect();

        assert!(!steps.is_empty(), "subjective stream must yield at least one step");

        // Confirm Step fields are accessible without panic.
        let first = &steps[0];
        let _ = first.psi_size;
        let _ = first.frontier_size;
        let _ = &first.dep_graph;
        let _ = first.ch9_class;
    }
}
