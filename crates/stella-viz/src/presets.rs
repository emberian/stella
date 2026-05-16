//! Preset constellations for the visualizer.
//!
//! Each preset builds a `Constellation` and (optionally) runs execution,
//! returning a `PresetResult` with DOT strings for the dependency graph and
//! a human-readable execution summary.
//!
//! Also provides `PresetStepData` which captures a full step-by-step IEx trace
//! via the viz-side fuel-replay technique (see `stepper.rs`).
//!
//! ## Curated presets
//!
//! Rather than a free-form parser (which would be non-trivial to make robust
//! for both native and wasm32 targets and is out of scope for this sprint),
//! the UI exposes a curated dropdown of interesting constellations beyond the
//! three originals.  The curated set is:
//!
//! - **Horn addition** (original preset 0): add(2,2,R).
//! - **Horn multiplication**: mult(2,3,R) — recursive Peano multiplication
//!   via add, shows nested interaction.
//! - **NFA Fig 56.1** (original preset 1): word "000" (accepts).
//! - **NTM trivial** (original preset 2): TM accepts ε.
//! - **NPDA Fig 56.2** (new): {0ⁿ1ⁿ} for word "01" — pushdown stack in action.
//! - **NFTA bool formula** (new): boolean formula tree evaluation (or(not(1),1) → TRUE).
//!
//! Parser rationale: `stella-core` has no string→Constellation parser; adding
//! one robustly would require a non-trivial recursive-descent front-end plus
//! α-renaming support — significant new code that risks the wasm build.  The
//! curated set covers all three automata classes (NFA, NPDA, NFTA) plus two
//! Horn logic examples, giving a representative cross-section of IEx in action.

use stella_core::automata::{eng_fig561_nfa, nfa_constellation, encode_nfa, encode_word};
use stella_core::constellation::Constellation;
use stella_core::dep_graph::DepGraph;
use stella_core::interactive::{iex_concealed};
use stella_core::nfta::{Nfta, NftaRule, Tree};
use stella_core::pda::eng_fig562_npda_constellation;
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
// Horn multiplication program (preset 3 — curated)
// ─────────────────────────────────────────────────────────────────────────────

fn horn_mult_constellation() -> Constellation {
    // mult(0, Y, 0)                   — base case
    // mult(s(X), Y, Z) :- mult(X, Y, W), add(W, Y, Z)   — step case
    // add(0, Y, Y)
    // add(s(X), Y, s(Z)) :- add(X, Y, Z)
    vec![
        // [+mult(0, Y, 0)]
        vec![pos_ray("mult", vec![mk_app_str("0", vec![]), mk_var("Y"), mk_app_str("0", vec![])])],
        // [-mult(X,Y,Z), -add(W,Y,Z), +mult(s(X),Y,Z_out)]
        // Peano mult step: mult(s(X),Y,S) :- mult(X,Y,W), add(W,Y,S)
        // Encoded as two stars (nested program):
        //   [-mult(X,Y,W), -add(W,Y,Z), +mult(s(X),Y,Z)]
        vec![
            neg_ray("mult", vec![mk_var("X"), mk_var("Y"), mk_var("W")]),
            neg_ray("add",  vec![mk_var("W"), mk_var("Y"), mk_var("Z")]),
            pos_ray("mult", vec![
                mk_app_str("s", vec![mk_var("X")]),
                mk_var("Y"),
                mk_var("Z"),
            ]),
        ],
        // [+add(0, Y, Y)]
        vec![pos_ray("add", vec![mk_app_str("0", vec![]), mk_var("Y"), mk_var("Y")])],
        // [-add(X,Y,Z), +add(s(X),Y,s(Z))]
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

pub fn preset_horn_mult() -> PresetResult {
    let m = 2usize;
    let n = 3usize;

    let phi = horn_mult_constellation();
    let psi = vec![vec![
        neg_ray("mult", vec![nat(m), nat(n), mk_var("R")]),
        mk_var("R"),
    ]];

    // Dep-graph of full constellation + query
    let mut phi_full = phi.clone();
    phi_full.extend(psi.clone());
    let dg = DepGraph::from_constellation(&phi_full);
    let dot = dep_graph_dot(&dg, &phi_full);

    let (visible, normal) = iex_concealed(&phi, psi, 1000);

    let exec_summary = if normal {
        format!(
            "↨♭ IEx(Φ_mult, [-mult({m},{n},R), R]) → {} star(s): {}",
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
        name: format!("Horn multiplication: mult({m},{n},R)"),
        description: format!(
            "Horn logic program Φ_mult for Peano multiplication, query [-mult({m},{n},R), R].\n\
             Stars: [+mult(0,Y,0)] (base), [-mult(X,Y,W),-add(W,Y,Z),+mult(s(X),Y,Z)] (step),\n\
             plus standard add/2 clauses.\n\
             Shows nested Horn interaction: mult reduces to repeated add calls."
        ),
        dep_graph_dot: dot,
        execution_summary: exec_summary,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NPDA Fig 56.2 — {0ⁿ1ⁿ | n≥0} preset (curated)
// ─────────────────────────────────────────────────────────────────────────────

pub fn preset_npda() -> PresetResult {
    // Word "01" ∈ {0ⁿ1ⁿ}: n=1, should be accepted.
    let word = ["0", "1"];
    let n_copies = word.len() + 2;

    // Full constellation P★ + w★ for dep-graph
    let word_star = encode_word(&word);
    let phi_ref = eng_fig562_npda_constellation(n_copies);
    let mut phi_full = phi_ref.clone();
    phi_full.push(word_star.clone());
    let dg = DepGraph::from_constellation(&phi_full);
    let dot = dep_graph_dot(&dg, &phi_full);

    let (visible, normal) = iex_concealed(&phi_ref, vec![word_star], 4000);
    let accepts = visible.iter().any(|s| {
        s.len() == 1 && format!("{}", s[0]) == "accept"
    });

    let exec_summary = if normal {
        format!(
            "Word \"01\": {}. ↨♭ IEx result: {} star(s): {}",
            if accepts { "ACCEPTED" } else { "REJECTED" },
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
        name: "NPDA Fig 56.2 — {0ⁿ1ⁿ | n≥0}, word \"01\"".to_string(),
        description: "Eng Fig 56.2 NPDA for context-free language {0ⁿ1ⁿ | n≥0}.\n\
            States: q₀ (push 0s), q₁ (pop 0s on 1s), q₂ (final).\n\
            Word tested: \"01\" (n=1, should accept).\n\
            Shows pushdown stack machinery in IEx: +p rays carry (word, state, stack).".to_string(),
        dep_graph_dot: dot,
        execution_summary: exec_summary,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NFTA boolean formula preset (curated)
// ─────────────────────────────────────────────────────────────────────────────

fn bool_formula_nfta() -> Nfta {
    Nfta {
        states: vec!["qt".into(), "qf".into()],
        initial: vec!["qt".into()],
        rules: vec![
            // qt(or(x₁,x₂)) → or(qt(x₁), qf(x₂))
            NftaRule { state: "qt".into(), symbol: "or".into(), successors: vec!["qt".into(), "qf".into()] },
            // qt(or(x₁,x₂)) → or(qf(x₁), qt(x₂))
            NftaRule { state: "qt".into(), symbol: "or".into(), successors: vec!["qf".into(), "qt".into()] },
            // qt(not(x)) → not(qf(x))
            NftaRule { state: "qt".into(), symbol: "not".into(), successors: vec!["qf".into()] },
            // qf(not(x)) → not(qt(x))
            NftaRule { state: "qf".into(), symbol: "not".into(), successors: vec!["qt".into()] },
            // qf(or(x₁,x₂)) → or(qf(x₁), qf(x₂))
            NftaRule { state: "qf".into(), symbol: "or".into(), successors: vec!["qf".into(), "qf".into()] },
        ],
        leaf_states: vec![],
        terminal_pairs: vec![
            ("qt".into(), "1".into()),
            ("qf".into(), "0".into()),
        ],
    }
}

pub fn preset_nfta() -> PresetResult {
    // Tree: or(not(1), 1)  →  or(0, 1) = TRUE
    let tree = Tree::Node(
        "or".into(),
        vec![
            Tree::Node("not".into(), vec![Tree::Node("1".into(), vec![])]),
            Tree::Node("1".into(), vec![]),
        ],
    );

    let nfta = bool_formula_nfta();
    let phi_ref = nfta.machine_constellation();
    let tree_star = tree.tree_star();

    // Full constellation T★ + t★ for dep-graph
    let mut phi_full = phi_ref.clone();
    phi_full.push(tree_star.clone());
    let dg = DepGraph::from_constellation(&phi_full);
    let dot = dep_graph_dot(&dg, &phi_full);

    let (visible, normal) = iex_concealed(&phi_ref, vec![tree_star], 500);
    let accepts = !visible.is_empty();

    let exec_summary = if normal {
        format!(
            "Tree or(not(1),1): {}. ↨♭ IEx result: {} star(s): {}",
            if accepts { "ACCEPTED (evaluates to TRUE)" } else { "REJECTED (evaluates to FALSE)" },
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
        name: "NFTA boolean formula: or(not(1), 1) → TRUE".to_string(),
        description: "Non-deterministic Finite Tree Automaton (Eng §57.7) evaluating boolean\n\
            formula trees.  States: qt (expecting TRUE), qf (expecting FALSE).\n\
            Tree tested: or(not(1), 1) — not(1)=0, or(0,1)=1 → TRUE (accepted).\n\
            Shows conjunctive NFTA encoding: each rule star bundles all child ta-rays.".to_string(),
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

/// Build step-by-step execution data for Horn multiplication.
pub fn step_data_horn_mult() -> PresetStepData {
    let m = 2usize;
    let n = 3usize;
    let phi = horn_mult_constellation();
    let psi = vec![vec![
        neg_ray("mult", vec![nat(m), nat(n), mk_var("R")]),
        mk_var("R"),
    ]];
    let steps = capture_steps(&phi, psi, 500);
    PresetStepData {
        name: format!("Horn mult({m},{n},R) — step-by-step IEx"),
        description: format!(
            "IEx step-by-step trace for mult({m},{n},R).\n\
             Reference Φ = Horn multiplication program (with add sub-program).\n\
             Initial Ψ = query star [-mult({m},{n},R), R].\n\
             Note: stepping uses fuel-replay (viz-side approximation)."
        ),
        steps,
    }
}

/// Build step-by-step execution data for the NPDA preset.
pub fn step_data_npda() -> PresetStepData {
    let word = ["0", "1"];
    let n_copies = word.len() + 2;
    let word_star = encode_word(&word);
    let phi_ref = eng_fig562_npda_constellation(n_copies);
    let steps = capture_steps(&phi_ref, vec![word_star], 500);
    PresetStepData {
        name: "NPDA Fig 56.2 {0ⁿ1ⁿ} word \"01\" — step-by-step IEx".to_string(),
        description: "IEx step-by-step trace for NPDA on word \"01\".\n\
            Reference Φ = P★ (pushdown machine constellation).\n\
            Initial Ψ = word star [+i(0·1·ε)].\n\
            Note: stepping uses fuel-replay (viz-side approximation).".to_string(),
        steps,
    }
}

/// Build step-by-step execution data for the NFTA boolean formula preset.
pub fn step_data_nfta() -> PresetStepData {
    let tree = Tree::Node(
        "or".into(),
        vec![
            Tree::Node("not".into(), vec![Tree::Node("1".into(), vec![])]),
            Tree::Node("1".into(), vec![]),
        ],
    );
    let nfta = bool_formula_nfta();
    let phi_ref = nfta.machine_constellation();
    let tree_star = tree.tree_star();
    let steps = capture_steps(&phi_ref, vec![tree_star], 300);
    PresetStepData {
        name: "NFTA bool formula or(not(1),1) — step-by-step IEx".to_string(),
        description: "IEx step-by-step trace for NFTA evaluating or(not(1),1).\n\
            Reference Φ = T★ (boolean formula NFTA machine constellation).\n\
            Initial Ψ = tree star [+i(or(not(1()),1()))].\n\
            Note: stepping uses fuel-replay (viz-side approximation).".to_string(),
        steps,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// All presets
// ─────────────────────────────────────────────────────────────────────────────

/// Return all available presets (static/summary view).
///
/// Order is stable: first three are the original presets (0–2), then the three
/// curated additions (3–5).  The UI preserves this ordering in the sidebar.
pub fn all_presets() -> Vec<PresetResult> {
    vec![
        preset_horn_add(),        // 0 — Horn add(2,2,R)
        preset_nfa(),             // 1 — NFA "000"
        preset_ntm(),             // 2 — NTM ε
        preset_horn_mult(),       // 3 (curated) — Horn mult(2,3,R)
        preset_npda(),            // 4 (curated) — NPDA "01"
        preset_nfta(),            // 5 (curated) — NFTA bool formula
    ]
}

/// Return step-by-step data for all presets (for the interactive stepper UI).
pub fn all_step_data() -> Vec<PresetStepData> {
    vec![
        step_data_horn_add(),     // 0
        step_data_nfa(),          // 1
        step_data_ntm(),          // 2
        step_data_horn_mult(),    // 3 (curated)
        step_data_npda(),         // 4 (curated)
        step_data_nfta(),         // 5 (curated)
    ]
}
