//! Preset constellations for the visualizer.
//!
//! Each preset builds a `Constellation` and (optionally) runs execution,
//! returning a `PresetResult` with DOT strings for the dependency graph and
//! a human-readable execution summary.
//!
//! Also provides `PresetStepData` which captures a full step-by-step IEx trace
//! via the viz-side fuel-replay technique (see `stepper.rs`).

use stella_core::automata::{eng_fig561_nfa, nfa_constellation, encode_nfa, encode_word};
use stella_core::constellation::Constellation;
use stella_core::dep_graph::DepGraph;
use stella_core::interactive::{iex_concealed};
use stella_core::polarised::{pos_ray, neg_ray};
use stella_core::term::{mk_var, mk_app_str, Term};
use stella_core::tm::{trivial_accept_empty_tm, encode_ntm, encode_word_ntm};
use stella_core::viz::dep_graph_dot;

use crate::stepper::{capture_steps, StepSnapshot};

/// The result of loading and running a preset.
pub struct PresetResult {
    /// Name of the preset.
    pub name: String,
    /// Short description.
    pub description: String,
    /// Graphviz DOT for `D[Φ; C]`.
    pub dep_graph_dot: String,
    /// Human-readable execution summary.
    pub execution_summary: String,
}

/// Step-by-step execution data for a preset (for the interactive stepper UI).
///
/// Each step captures the interaction space Ψ as rendered stars, the dep-graph
/// DOT for the current Ψ, and which ray is about to fire.
pub struct PresetStepData {
    pub name: String,
    #[allow(dead_code)]
    pub description: String,
    /// All step snapshots (index 0 = initial state, last = normal form or fuel-limit).
    pub steps: Vec<StepSnapshot>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Horn addition program (preset 0)
// ─────────────────────────────────────────────────────────────────────────────

fn nat(n: usize) -> Term {
    let mut t = mk_app_str("0", vec![]);
    for _ in 0..n {
        t = mk_app_str("s", vec![t]);
    }
    t
}

fn horn_add_constellation() -> Constellation {
    vec![
        // [+add(0, Y, Y)]  — base case
        vec![pos_ray("add", vec![mk_app_str("0", vec![]), mk_var("Y"), mk_var("Y")])],
        // [-add(X,Y,Z), +add(s(X),Y,s(Z))]  — step case
        vec![
            neg_ray("add", vec![mk_var("X"), mk_var("Y"), mk_var("Z")]),
            pos_ray("add", vec![
                mk_app_str("s", vec![mk_var("X")]),
                mk_var("Y"),
                mk_app_str("s", vec![mk_var("Z")]),
            ]),
        ],
    ]
}

fn horn_add_query(m: usize, n: usize) -> Constellation {
    let mut phi = horn_add_constellation();
    // Add query star [-add(m, n, R), R]
    phi.push(vec![
        neg_ray("add", vec![nat(m), nat(n), mk_var("R")]),
        mk_var("R"),
    ]);
    phi
}

pub fn preset_horn_add() -> PresetResult {
    let m = 2;
    let n = 2;

    // Build program + query constellation for the dep graph
    let phi = horn_add_query(m, n);
    let dg = DepGraph::from_constellation(&phi);
    let dot = dep_graph_dot(&dg, &phi);

    // Run IEx for execution result
    let phi_prog = horn_add_constellation();
    let psi = vec![vec![
        neg_ray("add", vec![nat(m), nat(n), mk_var("R")]),
        mk_var("R"),
    ]];
    let (visible, normal) = iex_concealed(&phi_prog, psi, 500);

    let exec_summary = if normal {
        format!(
            "↨♭ IEx(Φ⁺_N, [-add({m},{n},R), R]) → {} star(s): {}",
            visible.len(),
            visible.iter()
                .map(|s| {
                    s.iter()
                        .map(|r| format!("{r}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .map(|s| format!("[{s}]"))
                .collect::<Vec<_>>()
                .join("; ")
        )
    } else {
        "Fuel exhausted before normal form.".to_string()
    };

    PresetResult {
        name: "Horn addition: add(2,2,R)".to_string(),
        description: format!(
            "Horn logic program Φ⁺_N for Peano addition, with query [-add({m},{n},R), R].\n\
             Stars: [+add(0,Y,Y)] (base) and [-add(X,Y,Z), +add(s(X),Y,s(Z))] (step).\n\
             Dep-graph D[Φ;C] + IEx result shown."
        ),
        dep_graph_dot: dot,
        execution_summary: exec_summary,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NFA (Eng Fig 56.1) preset
// ─────────────────────────────────────────────────────────────────────────────

pub fn preset_nfa() -> PresetResult {
    let nfa = eng_fig561_nfa();
    let word = ["0", "0", "0"];

    let phi = nfa_constellation(&nfa, &word, 0);
    let dg = DepGraph::from_constellation(&phi);
    let dot = dep_graph_dot(&dg, &phi);

    // IEx mode: reference = A⋆, psi = w⋆
    let phi_ref = encode_nfa(&nfa);
    let psi = vec![encode_word(&word)];
    let (visible, normal) = iex_concealed(&phi_ref, psi, 500);

    let accepts = visible.iter().any(|s| {
        s.len() == 1 && format!("{}", s[0]) == "accept"
    });

    let exec_summary = if normal {
        format!(
            "Word \"000\": {}. ↨♭ IEx result: {} star(s): {}",
            if accepts { "ACCEPTED" } else { "REJECTED" },
            visible.len(),
            visible.iter()
                .map(|s| {
                    format!("[{}]", s.iter().map(|r| format!("{r}")).collect::<Vec<_>>().join(", "))
                })
                .collect::<Vec<_>>()
                .join("; ")
        )
    } else {
        "Fuel exhausted before normal form.".to_string()
    };

    PresetResult {
        name: "NFA: Eng Fig 56.1 — accepts words ending in \"00\"".to_string(),
        description: "NFA over {0,1} accepting L = {w | w ends in 00} (Eng §56).\n\
            States q0 (initial), q1, q2 (final).\n\
            Word tested: \"000\" (should accept).\n\
            Dep-graph D[w⋆ + A⋆; C] with 1 extra copy per transition for saturation.".to_string(),
        dep_graph_dot: dot,
        execution_summary: exec_summary,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NTM (trivial accept-empty TM) preset
// ─────────────────────────────────────────────────────────────────────────────

pub fn preset_ntm() -> PresetResult {
    let ntm = trivial_accept_empty_tm();

    // Constellation = M⋆ + w⋆ (empty word)
    let phi_ref = encode_ntm(&ntm);
    let word: Vec<String> = vec![];
    let psi_star = encode_word_ntm(&word);

    // Build full constellation for dep-graph visualization
    let mut phi_full = phi_ref.clone();
    phi_full.push(psi_star.clone());
    let dg = DepGraph::from_constellation(&phi_full);
    let dot = dep_graph_dot(&dg, &phi_full);

    // Run IEx: reference = M⋆, psi = w⋆
    let (visible, normal) = iex_concealed(&phi_ref, vec![psi_star], 200);
    let accepts = visible.iter().any(|s| {
        s.len() == 1 && format!("{}", s[0]) == "accept"
    });
    let rejects = visible.iter().any(|s| {
        s.len() == 1 && format!("{}", s[0]) == "reject"
    });

    let exec_summary = if normal {
        let verdict = if accepts {
            "ACCEPTED"
        } else if rejects {
            "REJECTED"
        } else {
            "DIVERGED (neither accept nor reject)"
        };
        format!(
            "Empty word ε on trivial TM: {}. ↨♭ IEx result: {} star(s): {}",
            verdict,
            visible.len(),
            visible.iter()
                .map(|s| format!("[{}]", s.iter().map(|r| format!("{r}")).collect::<Vec<_>>().join(", ")))
                .collect::<Vec<_>>()
                .join("; ")
        )
    } else {
        "Fuel exhausted before normal form.".to_string()
    };

    PresetResult {
        name: "NTM: trivial TM — accepts ε only".to_string(),
        description: "Simple deterministic TM over {a, b}: accepts ε, rejects all non-empty words.\n\
            States: q0 (initial), qa (accept), qr (reject).\n\
            Word tested: ε (should accept).\n\
            Dep-graph D[M⋆ ⊢ ε⋆; C] shown.".to_string(),
        dep_graph_dot: dot,
        execution_summary: exec_summary,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Step-data builders (fuel-replay via stepper::capture_steps)
// ─────────────────────────────────────────────────────────────────────────────

/// Build step-by-step execution data for the Horn-add preset.
pub fn step_data_horn_add() -> PresetStepData {
    let m = 2;
    let n = 2;
    let phi = horn_add_constellation();
    let psi = vec![vec![
        neg_ray("add", vec![nat(m), nat(n), mk_var("R")]),
        mk_var("R"),
    ]];
    let steps = capture_steps(&phi, psi, 200);
    PresetStepData {
        name: format!("Horn addition: add({m},{n},R) — step-by-step"),
        description: format!(
            "IEx step-by-step trace for add({m},{n},R).\n\
             Reference Φ = Horn addition program.\n\
             Initial Ψ = query star [-add({m},{n},R), R].\n\
             Note: stepping uses fuel-replay (viz-side approximation); \
             stella-core exposes no iterator API."
        ),
        steps,
    }
}

/// Build step-by-step execution data for the NFA preset.
pub fn step_data_nfa() -> PresetStepData {
    let nfa = eng_fig561_nfa();
    let phi = encode_nfa(&nfa);
    let psi = vec![encode_word(&["0", "0", "0"])];
    let steps = capture_steps(&phi, psi, 200);
    PresetStepData {
        name: "NFA Fig 56.1 — step-by-step IEx".to_string(),
        description: "IEx step-by-step trace for NFA word '000'.\n\
            Reference Φ = NFA automaton A⋆. Initial Ψ = word star [+i(0·0·0·ε)].\n\
            Note: stepping uses fuel-replay (viz-side approximation).".to_string(),
        steps,
    }
}

/// Build step-by-step execution data for the NTM preset.
pub fn step_data_ntm() -> PresetStepData {
    let ntm = trivial_accept_empty_tm();
    let phi_ref = encode_ntm(&ntm);
    let word: Vec<String> = vec![];
    let psi_star = encode_word_ntm(&word);
    let steps = capture_steps(&phi_ref, vec![psi_star], 100);
    PresetStepData {
        name: "NTM trivial TM ε — step-by-step IEx".to_string(),
        description: "IEx step-by-step trace for TM on empty word ε.\n\
            Reference Φ = TM M⋆. Initial Ψ = word star w⋆.\n\
            Note: stepping uses fuel-replay (viz-side approximation).".to_string(),
        steps,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// All presets
// ─────────────────────────────────────────────────────────────────────────────

/// Return all available presets (static/summary view).
pub fn all_presets() -> Vec<PresetResult> {
    vec![
        preset_horn_add(),
        preset_nfa(),
        preset_ntm(),
    ]
}

/// Return step-by-step data for all presets (for the interactive stepper UI).
pub fn all_step_data() -> Vec<PresetStepData> {
    vec![
        step_data_horn_add(),
        step_data_nfa(),
        step_data_ntm(),
    ]
}
