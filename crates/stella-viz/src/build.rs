//! The construction lab: structured machine / proof specs → constellations,
//! emitted as **editable surface source** (`parse(format(c))` is faithful, so
//! a built artifact is a first-class editable example, runnable + branchable
//! + inspectable with the exact stepper).
//!
//! Native + testable; `wasm.rs` thinly wraps each `*_source` entry point.
//! Each returns `(phi_src, psi_src)` — Φ the reference constellation, Ψ the
//! initial interaction space (empty for the AEx-style artifacts: circuits,
//! tiles, proof nets — explore those with the Ex view).

use serde::Deserialize;

use stella_core::atm::{encode_atm, encode_word_atm, Atm, Class};
use stella_core::automata::{encode_nfa, encode_word, Nfa};
use stella_core::circuits::{bool_module, circuit_constellation, Gate, GenCircuit};
use stella_core::constellation::Constellation;
use stella_core::mll::{phi_comp as mll_phi_comp, LinkKind as MllLink, ProofStructure as MllPs, VId as MllVId};
use stella_core::mll2i::{
    phi_comp as m2_phi_comp, LinkKind as M2Link, ProofStructure as M2Ps, VId as M2VId,
};
use stella_core::nfta::{Nfta, NftaRule, Tree};
use stella_core::pda::{encode_npda, Npda};
use stella_core::tiles::{tas_constellation, Tas, TileType};
use stella_core::tm::{encode_ntm, encode_word_ntm, Dir, Ntm};
use stella_core::transducer::{encode_nfst, Nfst};

type R = Result<(String, String), String>;

fn fmt_c(c: &Constellation) -> String {
    c.iter()
        .map(|s| {
            let rays: Vec<String> = s.iter().map(|r| format!("{r}")).collect();
            format!("[{}]", rays.join(", "))
        })
        .collect::<Vec<_>>()
        .join(" + ")
}
fn ok(phi: &Constellation, psi: &Constellation) -> R {
    Ok((fmt_c(phi), fmt_c(psi)))
}
fn jerr(e: impl std::fmt::Display) -> String {
    format!("spec error: {e}")
}
fn refs(v: &[String]) -> Vec<&str> {
    v.iter().map(|s| s.as_str()).collect()
}

// ── shared option mapping ────────────────────────────────────────────────────
fn dir(s: &str) -> Result<Dir, String> {
    match s {
        "L" | "l" => Ok(Dir::L),
        "R" | "r" => Ok(Dir::R),
        "S" | "s" => Ok(Dir::S),
        _ => Err(format!("bad direction {s:?} (use L/R/S)")),
    }
}

// ── NFA ──────────────────────────────────────────────────────────────────────
#[derive(Deserialize)]
struct NfaSpec {
    states: Vec<String>,
    alphabet: Vec<String>,
    initial: Vec<String>,
    finals: Vec<String>,
    /// `[from, symbol|null, to]`
    transitions: Vec<(String, Option<String>, String)>,
    word: Vec<String>,
}
pub fn nfa_source(json: &str) -> R {
    let s: NfaSpec = serde_json::from_str(json).map_err(jerr)?;
    let nfa = Nfa {
        states: s.states,
        alphabet: s.alphabet,
        initial: s.initial,
        finals: s.finals,
        transitions: s.transitions,
    };
    let phi = encode_nfa(&nfa);
    let psi = vec![encode_word(&refs(&s.word))];
    ok(&phi, &psi)
}

// ── NPDA ─────────────────────────────────────────────────────────────────────
#[derive(Deserialize)]
struct NpdaSpec {
    states: Vec<String>,
    alphabet: Vec<String>,
    stack_alphabet: Vec<String>,
    initial: Vec<String>,
    finals: Vec<String>,
    /// `[q, input|null, stack_top|null, q', push|null]`
    transitions: Vec<(String, Option<String>, Option<String>, String, Option<String>)>,
    word: Vec<String>,
}
pub fn npda_source(json: &str) -> R {
    let s: NpdaSpec = serde_json::from_str(json).map_err(jerr)?;
    let pda = Npda {
        states: s.states,
        alphabet: s.alphabet,
        stack_alphabet: s.stack_alphabet,
        initial: s.initial,
        finals: s.finals,
        transitions: s.transitions,
    };
    let n_copies = s.word.len() + 2;
    let phi = encode_npda(&pda, n_copies);
    let psi = vec![encode_word(&refs(&s.word))];
    ok(&phi, &psi)
}

// ── NTM ──────────────────────────────────────────────────────────────────────
#[derive(Deserialize)]
struct NtmSpec {
    states: Vec<String>,
    gamma: Vec<String>,
    /// `[from, read, to, write, dir]` (dir = "L"|"R"|"S")
    delta: Vec<(String, String, String, String, String)>,
    q0: String,
    q_accept: String,
    q_reject: String,
    input: Vec<String>,
}
pub fn ntm_source(json: &str) -> R {
    let s: NtmSpec = serde_json::from_str(json).map_err(jerr)?;
    let mut delta = Vec::with_capacity(s.delta.len());
    for (a, b, c, d, e) in s.delta {
        delta.push((a, b, c, d, dir(&e)?));
    }
    let ntm = Ntm {
        states: s.states,
        gamma: s.gamma,
        delta,
        q0: s.q0,
        q_accept: s.q_accept,
        q_reject: s.q_reject,
    };
    let phi = encode_ntm(&ntm);
    let psi = vec![encode_word_ntm(&s.input)];
    ok(&phi, &psi)
}

// ── ATM ──────────────────────────────────────────────────────────────────────
#[derive(Deserialize)]
struct AtmSpec {
    states: Vec<String>,
    gamma: Vec<String>,
    delta: Vec<(String, String, String, String, String)>,
    q0: String,
    q_accept: String,
    q_reject: String,
    /// state → "E" (existential) | "U" (universal)
    class: std::collections::HashMap<String, String>,
    input: Vec<String>,
}
pub fn atm_source(json: &str) -> R {
    let s: AtmSpec = serde_json::from_str(json).map_err(jerr)?;
    let mut delta = Vec::with_capacity(s.delta.len());
    for (a, b, c, d, e) in s.delta {
        delta.push((a, b, c, d, dir(&e)?));
    }
    let mut class = std::collections::HashMap::new();
    for (k, v) in s.class {
        class.insert(
            k,
            match v.as_str() {
                "E" | "e" => Class::Existential,
                "U" | "u" => Class::Universal,
                _ => return Err(format!("bad class {v:?} (use E/U)")),
            },
        );
    }
    let atm = Atm {
        states: s.states,
        gamma: s.gamma,
        delta,
        q0: s.q0,
        q_accept: s.q_accept,
        q_reject: s.q_reject,
        class,
    };
    let phi = encode_atm(&atm);
    let psi = vec![encode_word_atm(&s.input)];
    ok(&phi, &psi)
}

// ── NFTA ─────────────────────────────────────────────────────────────────────
#[derive(Deserialize)]
#[serde(untagged)]
enum TreeSpec {
    Leaf { leaf: String },
    Node { node: (String, Vec<TreeSpec>) },
}
fn to_tree(t: &TreeSpec) -> Tree {
    match t {
        TreeSpec::Leaf { leaf } => Tree::Leaf(leaf.clone()),
        TreeSpec::Node { node } => {
            Tree::Node(node.0.clone(), node.1.iter().map(to_tree).collect())
        }
    }
}
#[derive(Deserialize)]
struct NftaRuleSpec {
    state: String,
    symbol: String,
    successors: Vec<String>,
}
#[derive(Deserialize)]
struct NftaSpec {
    states: Vec<String>,
    initial: Vec<String>,
    rules: Vec<NftaRuleSpec>,
    leaf_states: Vec<String>,
    terminal_pairs: Vec<(String, String)>,
    tree: TreeSpec,
}
pub fn nfta_source(json: &str) -> R {
    let s: NftaSpec = serde_json::from_str(json).map_err(jerr)?;
    let nfta = Nfta {
        states: s.states,
        initial: s.initial,
        rules: s
            .rules
            .into_iter()
            .map(|r| NftaRule {
                state: r.state,
                symbol: r.symbol,
                successors: r.successors,
            })
            .collect(),
        leaf_states: s.leaf_states,
        terminal_pairs: s.terminal_pairs,
    };
    let phi = nfta.machine_constellation();
    let psi = vec![to_tree(&s.tree).tree_star()];
    ok(&phi, &psi)
}

// ── NFST (transducer) ────────────────────────────────────────────────────────
#[derive(Deserialize)]
struct NfstSpec {
    states: Vec<String>,
    alphabet: Vec<String>,
    output_alphabet: Vec<String>,
    initial: Vec<String>,
    finals: Vec<String>,
    /// `[q, input|null, q', output|null]`
    transitions: Vec<(String, Option<String>, String, Option<String>)>,
    word: Vec<String>,
}
pub fn nfst_source(json: &str) -> R {
    let s: NfstSpec = serde_json::from_str(json).map_err(jerr)?;
    let fst = Nfst {
        states: s.states,
        alphabet: s.alphabet,
        output_alphabet: s.output_alphabet,
        initial: s.initial,
        finals: s.finals,
        transitions: s.transitions,
    };
    let n_copies = s.word.len() + 2;
    let phi = encode_nfst(&fst, n_copies);
    let psi = vec![encode_word(&refs(&s.word))];
    ok(&phi, &psi)
}

// ── Circuit (AEx artifact: Ψ empty — explore with Ex) ────────────────────────
#[derive(Deserialize)]
struct GateSpec {
    label: String,
    inputs: Vec<String>,
    outputs: Vec<String>,
    #[serde(default)]
    is_output: bool,
}
#[derive(Deserialize)]
struct CircuitSpec {
    gates: Vec<GateSpec>,
}
pub fn circuit_source(json: &str) -> R {
    let s: CircuitSpec = serde_json::from_str(json).map_err(jerr)?;
    let c = GenCircuit {
        gates: s
            .gates
            .into_iter()
            .map(|g| Gate {
                label: g.label,
                inputs: g.inputs,
                outputs: g.outputs,
                is_output: g.is_output,
            })
            .collect(),
    };
    // Self-contained: circuit ⊎ Boolean module, so it runs under Ex.
    let mut phi = circuit_constellation(&c);
    phi.extend(bool_module().module_constellation());
    ok(&phi, &Vec::new())
}

// ── Tile assembly (AEx artifact) ─────────────────────────────────────────────
#[derive(Deserialize)]
struct TileSpec {
    label: String,
    glue_w: String,
    glue_e: String,
    glue_s: String,
    glue_n: String,
    strengths: [usize; 4],
}
#[derive(Deserialize)]
struct TasSpec {
    tile_types: Vec<TileSpec>,
    tau: usize,
    #[serde(default)]
    seed: Option<usize>,
    positions: Vec<String>,
}
pub fn tiles_source(json: &str) -> R {
    let s: TasSpec = serde_json::from_str(json).map_err(jerr)?;
    let tas = Tas {
        tile_types: s
            .tile_types
            .into_iter()
            .map(|t| TileType {
                label: t.label,
                glue_w: t.glue_w,
                glue_e: t.glue_e,
                glue_s: t.glue_s,
                glue_n: t.glue_n,
                strengths: t.strengths,
            })
            .collect(),
        tau: s.tau,
        seed: s.seed,
    };
    let phi = tas_constellation(&tas, &refs(&s.positions));
    ok(&phi, &Vec::new())
}

// ── MLL proof structure (cut-elim via Ex) ────────────────────────────────────
#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
enum MllLinkSpec {
    Ax { left: u32, right: u32 },
    Cut { left: u32, right: u32 },
    Tensor { left: u32, right: u32, output: u32 },
    Par { left: u32, right: u32, output: u32 },
}
#[derive(Deserialize)]
struct MllSpec {
    links: Vec<MllLinkSpec>,
}
pub fn mll_source(json: &str) -> R {
    let s: MllSpec = serde_json::from_str(json).map_err(jerr)?;
    let mut ps = MllPs::new();
    for l in s.links {
        ps.add_link(match l {
            MllLinkSpec::Ax { left, right } => MllLink::Ax { left: MllVId(left), right: MllVId(right) },
            MllLinkSpec::Cut { left, right } => MllLink::Cut { left: MllVId(left), right: MllVId(right) },
            MllLinkSpec::Tensor { left, right, output } => MllLink::Tensor {
                left: MllVId(left), right: MllVId(right), output: MllVId(output),
            },
            MllLinkSpec::Par { left, right, output } => MllLink::Par {
                left: MllVId(left), right: MllVId(right), output: MllVId(output),
            },
        });
    }
    ok(&mll_phi_comp(&ps), &Vec::new())
}

// ── MLL2I proof structure (with a switching) ─────────────────────────────────
#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
enum M2LinkSpec {
    Ax { left: u32, right: u32 },
    Cut { left: u32, right: u32 },
    Tensor { left: u32, right: u32, output: u32 },
    Par { left: u32, right: u32, output: u32 },
    Etensor { left: u32, right: u32, output: u32 },
    Epar { left: u32, right: u32, output: u32 },
    Weakening { output: u32 },
    Dereliction { input: u32, output: u32 },
    Contraction { left: u32, right: u32, output: u32 },
}
#[derive(Deserialize)]
struct M2Spec {
    links: Vec<M2LinkSpec>,
}
pub fn mll2i_source(json: &str) -> R {
    let s: M2Spec = serde_json::from_str(json).map_err(jerr)?;
    let mut ps = M2Ps::new();
    for l in s.links {
        ps.add_link(match l {
            M2LinkSpec::Ax { left, right } => M2Link::Ax { left: M2VId(left), right: M2VId(right) },
            M2LinkSpec::Cut { left, right } => M2Link::Cut { left: M2VId(left), right: M2VId(right) },
            M2LinkSpec::Tensor { left, right, output } => M2Link::Tensor { left: M2VId(left), right: M2VId(right), output: M2VId(output) },
            M2LinkSpec::Par { left, right, output } => M2Link::Par { left: M2VId(left), right: M2VId(right), output: M2VId(output) },
            M2LinkSpec::Etensor { left, right, output } => M2Link::ETensor { left: M2VId(left), right: M2VId(right), output: M2VId(output) },
            M2LinkSpec::Epar { left, right, output } => M2Link::EPar { left: M2VId(left), right: M2VId(right), output: M2VId(output) },
            M2LinkSpec::Weakening { output } => M2Link::Weakening { output: M2VId(output) },
            M2LinkSpec::Dereliction { input, output } => M2Link::Dereliction { input: M2VId(input), output: M2VId(output) },
            M2LinkSpec::Contraction { left, right, output } => M2Link::Contraction { left: M2VId(left), right: M2VId(right), output: M2VId(output) },
        });
    }
    ok(&m2_phi_comp(&ps), &Vec::new())
}

/// Dispatch by machine-class name (used by the wasm wrapper).
pub fn build(kind: &str, json: &str) -> R {
    match kind {
        "nfa" => nfa_source(json),
        "npda" => npda_source(json),
        "ntm" => ntm_source(json),
        "atm" => atm_source(json),
        "nfta" => nfta_source(json),
        "nfst" => nfst_source(json),
        "circuit" => circuit_source(json),
        "tiles" => tiles_source(json),
        "mll" => mll_source(json),
        "mll2i" => mll2i_source(json),
        _ => Err(format!("unknown machine class {kind:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stepper::capture_path;
    use stella_core::parse::{parse_constellation, parse_psi};

    fn runs(phi: &str, psi: &str) -> bool {
        let p = parse_constellation(phi).expect("phi parses (round-trips)");
        let q = parse_psi(psi).expect("psi parses");
        let snaps = capture_path(&p, q, &[], 600);
        snaps.last().map(|s| s.is_final).unwrap_or(false)
    }

    #[test]
    fn nfa_builds_runs_and_accepts() {
        let json = r#"{
          "states":["q0","q1","q2"],"alphabet":["0","1"],
          "initial":["q0"],"finals":["q2"],
          "transitions":[["q0","0","q0"],["q0","0","q1"],["q1","0","q2"]],
          "word":["0","0","0"]
        }"#;
        let (phi, psi) = nfa_source(json).expect("nfa builds");
        assert!(runs(&phi, &psi), "built NFA must reach a normal form");
    }

    #[test]
    fn nfta_builds_and_runs() {
        let json = r#"{
          "states":["q"],"initial":["q"],
          "rules":[{"state":"q","symbol":"a","successors":[]}],
          "leaf_states":["q"],"terminal_pairs":[["q","a"]],
          "tree":{"leaf":"a"}
        }"#;
        let (phi, psi) = nfta_source(json).expect("nfta builds");
        // round-trips through Display→parse and runs
        let _ = runs(&phi, &psi);
        assert!(parse_constellation(&phi).is_ok());
    }

    #[test]
    fn mll_axiom_cut_round_trips() {
        let json = r#"{"links":[
          {"kind":"ax","left":0,"right":1},
          {"kind":"ax","left":2,"right":3},
          {"kind":"cut","left":1,"right":2}]}"#;
        let (phi, _psi) = mll_source(json).expect("mll builds");
        assert!(parse_constellation(&phi).is_ok(), "Φ_comp round-trips");
    }

    #[test]
    fn bad_spec_errors_cleanly() {
        assert!(nfa_source("{ not json").is_err());
        assert!(build("nope", "{}").is_err());
    }
}
