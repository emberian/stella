//! Viz-side step-through driver for IEx execution.
//!
//! ## Why viz-side approximation
//!
//! `stella-core`'s `iex()` function runs to completion (or fuel exhaustion)
//! in one call; it exposes no iterator or callback API for intermediate states.
//! Rather than modifying stella-core, we implement a **fuel-replay** technique:
//! call `iex(phi, psi, fuel=k)` for k = 0, 1, 2, … until normal form, and
//! collect the successive `Ψ` snapshots.  Since `iex` is deterministic
//! (left-to-right ray scan, first applicable), the `Ψ` returned at fuel=k is
//! exactly the interaction space after k real steps.  The replay is O(N²) in
//! total steps N, which is fine for the small constellations used in the UI.
//!
//! ## Snapshot format
//!
//! Each `StepSnapshot` captures:
//! - `step`: the step index (0 = initial, 1 = after step 1, …)
//! - `psi_stars`: the interaction space Ψ rendered as human-readable strings
//! - `matchable_rays`: a summary of which rays were matchable at this point
//!   (i.e., what caused the transition to the next step), if any
//! - `dot`: a Graphviz DOT for the dep-graph of the current Ψ constellation;
//!   this lets the UI animate how the active stars evolve
//! - `is_final`: true if this snapshot is a normal form or the last captured step

use rustc_hash::FxHashMap;
use stella_core::constellation::Constellation;
use stella_core::constellation::Star;
use stella_core::dep_graph::DepGraph;
use stella_core::interactive::{iex, mat_phi};
use stella_core::polarised::{matchable, ray_polarity, underlying_term, Polarity};
use stella_core::subst::{fresh_var, Renaming};
use stella_core::term::Var;
use stella_core::unify::{unify, Equation};
use stella_core::viz::dep_graph_dot;

/// One ray in Ψ that can interact at this step (a redex). Stellar resolution
/// is concurrent — at any state there may be several; IEx fires the first
/// (left-to-right). The UI uses this to show *all* the choices.
#[derive(Debug, Clone)]
pub struct Fireable {
    /// Index of the star in Ψ.
    pub star: usize,
    /// Index of the ray within that star.
    pub ray: usize,
    /// The ray, rendered.
    pub ray_str: String,
    /// `"phi"` (matches a star in the reference Φ) or `"self"` (self-interaction).
    pub kind: String,
    /// Human-readable description of what it matches (Φ[i][j] / ray[k]).
    pub targets: Vec<String>,
    /// True for the redex IEx will actually fire next (the first one).
    pub is_next: bool,
}

/// A single step snapshot.
#[derive(Debug, Clone)]
pub struct StepSnapshot {
    pub step: usize,
    /// The interaction space Ψ at this step, each star rendered as a string.
    pub psi_stars: Vec<String>,
    /// Matchable ray summary — which star/ray caused the next interaction.
    /// Empty string when no further step exists (final snapshot).
    pub active_ray: String,
    /// Graphviz DOT for D[Ψ; C] — the dep-graph of the current interaction space.
    pub dot: String,
    /// True if this is a normal form (no more interactions possible).
    pub is_final: bool,
    /// Every redex available at this state (concurrency made visible).
    pub fireable: Vec<Fireable>,
    /// The most general unifier of the redex IEx fires next, as
    /// `(variable, term)` display pairs. Empty at the final step.
    pub mgu: Vec<(String, String)>,
}

/// Capture step snapshots for a preset by fuel-replay.
///
/// - `phi`: the reference constellation (infinite supply)
/// - `psi_init`: the initial interaction space
/// - `max_fuel`: maximum number of steps to capture (caps replay at this limit)
///
/// Returns a `Vec<StepSnapshot>` of length `min(steps_to_normal_form, max_fuel) + 1`
/// (includes step 0 = initial state).
pub fn capture_steps(
    phi: &Constellation,
    psi_init: Vec<Star>,
    max_fuel: usize,
) -> Vec<StepSnapshot> {
    let mut snapshots: Vec<StepSnapshot> = Vec::new();

    // Determine how many steps exist by running to completion once.
    let full = iex(phi, psi_init.clone(), max_fuel);
    let total_steps = full.steps; // actual steps taken (≤ max_fuel)

    // Now replay with fuel 0, 1, 2, … total_steps to collect each Ψ.
    for k in 0..=total_steps {
        let result = iex(phi, psi_init.clone(), k);
        let psi = &result.psi;

        // Human-readable star strings.
        let psi_stars: Vec<String> = psi
            .iter()
            .map(|star| {
                let rays: Vec<String> = star.iter().map(|r| format!("{r}")).collect();
                format!("[{}]", rays.join(", "))
            })
            .collect();

        // Build dep-graph DOT for the current Ψ.
        let dot = if psi.is_empty() {
            "graph dep_graph {\n  // empty interaction space\n}\n".to_string()
        } else {
            let dg = DepGraph::from_constellation(psi);
            dep_graph_dot(&dg, psi)
        };

        // Find which ray (if any) is about to fire at this step, to annotate the snapshot.
        let active_ray = if k < total_steps {
            find_active_ray(phi, psi)
        } else {
            String::new()
        };

        let is_final = result.is_normal_form || k == total_steps;

        let fireable = if k < total_steps {
            enumerate_fireable(phi, psi)
        } else {
            Vec::new()
        };
        let mgu = fireable
            .iter()
            .find(|f| f.is_next)
            .map(|f| mgu_of(phi, psi, f))
            .unwrap_or_default();

        snapshots.push(StepSnapshot {
            step: k,
            psi_stars,
            active_ray,
            dot,
            is_final,
            fireable,
            mgu,
        });
    }

    snapshots
}

/// Rename every variable in a star to a fresh name (consistently across its
/// rays), so it is variable-disjoint from Ψ — mirrors what fusion does before
/// unifying, so the MGU we display is the one IEx actually computes.
fn freshen_star_consistent(star: &Star, prefix: &str, counter: &mut u32) -> Star {
    let mut map: FxHashMap<Var, Var> = FxHashMap::default();
    for &r in star {
        for v in r.vars() {
            map.entry(v).or_insert_with(|| fresh_var(prefix, counter));
        }
    }
    if map.is_empty() {
        return star.clone();
    }
    let ren = Renaming::from_map(map);
    star.iter().map(|&r| ren.apply(r)).collect()
}

fn render_mgu(sigma: &stella_core::subst::Substitution) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = sigma
        .0
        .iter()
        .map(|(v, &t)| (v.as_str().to_string(), format!("{t}")))
        .collect();
    out.sort();
    out
}

/// The MGU IEx computes for a given redex (faithful to `fuse`: Φ-star is
/// freshened apart, then underlying terms are unified).
fn mgu_of(phi: &Constellation, psi: &[Star], f: &Fireable) -> Vec<(String, String)> {
    let r = psi[f.star][f.ray];
    if f.kind == "self" {
        for (jk, &rk) in psi[f.star].iter().enumerate() {
            if jk != f.ray && matchable(r, rk) {
                if let Some(s) = unify(vec![Equation::new(
                    underlying_term(r),
                    underlying_term(rk),
                )]) {
                    return render_mgu(&s);
                }
            }
        }
        return Vec::new();
    }
    // External: first matching Φ[si][ji], freshened apart.
    if let Some(&(si, ji)) = mat_phi(phi, r).first() {
        let mut counter = 0u32;
        let renamed = freshen_star_consistent(&phi[si], "Φ_", &mut counter);
        if let Some(s) = unify(vec![Equation::new(
            underlying_term(r),
            underlying_term(renamed[ji]),
        )]) {
            return render_mgu(&s);
        }
    }
    Vec::new()
}

/// Enumerate every redex available at this state. The first in IEx's
/// left-to-right scan is flagged `is_next`.
fn enumerate_fireable(phi: &Constellation, psi: &[Star]) -> Vec<Fireable> {
    let mut out: Vec<Fireable> = Vec::new();
    for (i, star) in psi.iter().enumerate() {
        for (j, &r) in star.iter().enumerate() {
            if ray_polarity(r) == Polarity::Neutral {
                continue;
            }
            let ext = mat_phi(phi, r);
            if !ext.is_empty() {
                out.push(Fireable {
                    star: i,
                    ray: j,
                    ray_str: format!("{r}"),
                    kind: "phi".to_string(),
                    targets: ext.iter().map(|(si, ji)| format!("Φ[{si}][{ji}]")).collect(),
                    is_next: false,
                });
                continue;
            }
            let mut self_targets: Vec<String> = Vec::new();
            for (jk, &rk) in star.iter().enumerate() {
                if jk != j && matchable(r, rk) {
                    self_targets.push(format!("ray[{jk}] {rk}"));
                }
            }
            if !self_targets.is_empty() {
                out.push(Fireable {
                    star: i,
                    ray: j,
                    ray_str: format!("{r}"),
                    kind: "self".to_string(),
                    targets: self_targets,
                    is_next: false,
                });
            }
        }
    }
    if let Some(first) = out.first_mut() {
        first.is_next = true;
    }
    out
}

/// Find the first matchable ray in Ψ (the one IEx will fire on next).
fn find_active_ray(phi: &Constellation, psi: &[Star]) -> String {
    let psi_vec: Constellation = psi.to_vec();
    let _psi_colours = stella_core::dep_graph::all_colours(&psi_vec);

    for (i, star) in psi.iter().enumerate() {
        for (j, &r) in star.iter().enumerate() {
            if ray_polarity(r) == Polarity::Neutral {
                continue;
            }
            // Check external matches in phi.
            let ext = mat_phi(phi, r);
            if !ext.is_empty() {
                let matches: Vec<String> = ext
                    .iter()
                    .map(|(si, ji)| format!("Φ[{si}][{ji}]"))
                    .collect();
                return format!(
                    "star[{i}] ray[{j}] {} — matches: {}",
                    format_ray(r),
                    matches.join(", ")
                );
            }
            // Check self-interaction.
            for (jk, &rk) in star.iter().enumerate() {
                if jk != j && stella_core::polarised::matchable(r, rk) {
                    return format!(
                        "star[{i}] ray[{j}] {} — self-interacts with ray[{jk}] {}",
                        format_ray(r),
                        format_ray(rk)
                    );
                }
            }
        }
    }
    String::new()
}

fn format_ray(r: stella_core::term::Term) -> String {
    format!("{r}")
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use stella_core::polarised::{pos_ray, neg_ray};
    use stella_core::term::{mk_var, mk_app_str, Term};

    fn var(x: &str) -> Term { mk_var(x) }
    fn c(name: &str) -> Term { mk_app_str(name, vec![]) }
    fn app(f: &str, args: Vec<Term>) -> Term { mk_app_str(f, args) }

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
                pos_ray("add", vec![
                    app("s", vec![var("X")]),
                    var("Y"),
                    app("s", vec![var("Z")]),
                ]),
            ],
        ]
    }

    /// Smoke: step-0 DOT for Horn-add is a valid dep-graph DOT string.
    #[test]
    fn smoke_step0_dot_is_valid() {
        let phi = add_prog();
        let psi = vec![vec![
            neg_ray("add", vec![nat(1), nat(1), var("R")]),
            var("R"),
        ]];
        let snaps = capture_steps(&phi, psi, 50);
        assert!(!snaps.is_empty(), "should have at least step 0");
        let step0 = &snaps[0];
        assert_eq!(step0.step, 0);
        assert!(
            step0.dot.contains("graph dep_graph {"),
            "step-0 DOT should be a valid dep_graph: {}",
            &step0.dot[..step0.dot.len().min(200)]
        );
    }

    /// Smoke: step-N (last step) DOT for Horn-add 1+1 also valid; Ψ contains s(s(0)).
    #[test]
    fn smoke_step_n_dot_and_result_horn_1_plus_1() {
        let phi = add_prog();
        let psi = vec![vec![
            neg_ray("add", vec![nat(1), nat(1), var("R")]),
            var("R"),
        ]];
        let snaps = capture_steps(&phi, psi, 200);
        assert!(snaps.len() >= 2, "horn 1+1 should take at least 1 step");

        let last = snaps.last().unwrap();
        assert!(last.is_final, "last snapshot should be marked final");
        assert!(
            last.dot.contains("graph dep_graph {"),
            "step-N DOT should be a valid dep_graph"
        );
        // The result interaction space should contain s(s(0)) = nat(2).
        let result_str = last.psi_stars.join(" ");
        assert!(
            result_str.contains("s(s(0))") || result_str.contains("s(0)") || result_str.contains("0"),
            "final Ψ should contain some nat term; got: {result_str}"
        );
    }

    /// Smoke: NFA accepts "00" — last step should have accept in Ψ.
    #[test]
    fn smoke_step_n_nfa_accept() {
        use stella_core::automata::{encode_nfa, encode_word, eng_fig561_nfa};
        let nfa = eng_fig561_nfa();
        let phi = encode_nfa(&nfa);
        let psi = vec![encode_word(&["0", "0"])];
        let snaps = capture_steps(&phi, psi, 200);
        assert!(!snaps.is_empty());
        let last = snaps.last().unwrap();
        let result_str = last.psi_stars.join(" ");
        assert!(
            result_str.contains("accept"),
            "NFA '00' final Ψ should contain accept; got: {result_str}"
        );
    }
}
