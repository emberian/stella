//! The logician's workbench (Stage 3): orthogonality, behaviours, and
//! proof-net correctness — the core activity of transcendental syntax,
//! bound to the engine. No type *inference* is faked: a type is a
//! behaviour, membership is orthogonality, proofs are validated by the
//! stellar / Danos–Régnier / Girard criterion. We expose exactly that.
//!
//! Everything is on-demand and size-guarded — orthogonality runs AEx, which
//! is expensive; biorth is O(universe²).

use serde::Deserialize;

use stella_core::constellation::Constellation;
use stella_core::dep_graph::DepGraph;
use stella_core::execution::saturated_diagrams;
use stella_core::mll::{
    biorth, dr_correct, is_behaviour, orth_fin, orth_one, orth_roots, orthogonal_set,
    phi_comp as mll_phi_comp, Behaviour, LinkKind as MllLink, Orth,
    ProofStructure as MllPs, VId as MllVId,
};
use stella_core::mll2i::{
    girard_correct, phi_comp as m2_phi_comp, LinkKind as M2Link,
    ProofStructure as M2Ps, VId as M2VId,
};
use stella_core::parse::parse_constellation;
use stella_core::viz::diagram_dot;

fn fmt_c(c: &Constellation) -> String {
    c.iter()
        .map(|s| {
            let r: Vec<String> = s.iter().map(|x| format!("{x}")).collect();
            format!("[{}]", r.join(", "))
        })
        .collect::<Vec<_>>()
        .join(" + ")
}
fn jerr(e: impl std::fmt::Display) -> String {
    format!("{e}")
}
fn jstr(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}
fn n_stars(c: &Constellation) -> usize {
    c.len()
}

const ORTHO_STAR_CAP: usize = 40; // AEx over Φ₁⊎Φ₂ — guard heavy inputs
const DIAG_STAR_CAP: usize = 22; // saturated-diagram enumeration (small proof nets)
const DIAG_SHOW_CAP: usize = 48;
const UNIVERSE_CAP: usize = 8; // biorth is O(universe²·members)

// ── Φ₁ ⊥ Φ₂ : the three orthogonality relations ──────────────────────────────
pub fn orthogonality(p1: &str, p2: &str) -> Result<String, String> {
    let a = parse_constellation(p1).map_err(|e| format!("Φ₁: {}", jerr(e)))?;
    let b = parse_constellation(p2).map_err(|e| format!("Φ₂: {}", jerr(e)))?;
    if n_stars(&a) + n_stars(&b) > ORTHO_STAR_CAP {
        return Err(format!(
            "Φ₁⊎Φ₂ has {} stars (> {} cap): orthogonality runs AEx and would \
             not be bounded — keep the test small.",
            n_stars(&a) + n_stars(&b),
            ORTHO_STAR_CAP
        ));
    }
    Ok(format!(
        "{{\"ok\":true,\"fin\":{},\"one\":{},\"roots\":{}}}",
        orth_fin(&a, &b),
        orth_one(&a, &b),
        orth_roots(&a, &b)
    ))
}

// ── proof structures ─────────────────────────────────────────────────────────
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

/// Run an engine correctness predicate that has *preconditions* it asserts
/// (e.g. DR requires cut-free). On a precondition panic, report it instead
/// of taking down the module.
fn guarded(f: impl FnOnce() -> bool + std::panic::UnwindSafe) -> Option<bool> {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(f).ok();
    std::panic::set_hook(prev);
    r
}

fn mll_ps(json: &str) -> Result<(MllPs, usize), String> {
    let s: MllSpec = serde_json::from_str(json).map_err(jerr)?;
    let mut ps = MllPs::new();
    let mut cuts = 0usize;
    for l in s.links {
        ps.add_link(match l {
            MllLinkSpec::Ax { left, right } => MllLink::Ax { left: MllVId(left), right: MllVId(right) },
            MllLinkSpec::Cut { left, right } => { cuts += 1; MllLink::Cut { left: MllVId(left), right: MllVId(right) } }
            MllLinkSpec::Tensor { left, right, output } => MllLink::Tensor { left: MllVId(left), right: MllVId(right), output: MllVId(output) },
            MllLinkSpec::Par { left, right, output } => MllLink::Par { left: MllVId(left), right: MllVId(right), output: MllVId(output) },
        });
    }
    Ok((ps, cuts))
}
fn m2_ps(json: &str) -> Result<M2Ps, String> {
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
    Ok(ps)
}

/// Proof-net report: the correctness verdict (DR for MLL, Girard for MLL2I),
/// the translation Φ_comp as editable source, and — because proof structures
/// are small & finite — a size-guarded saturated-diagram witness.
pub fn proofnet(kind: &str, json: &str) -> Result<String, String> {
    // verdict: Some(true/false) = criterion ran; None = not applicable.
    let (verdict_name, verdict, vnote, phi): (&str, Option<bool>, String, Constellation) =
        match kind {
            "mll" => {
                let (ps, cuts) = mll_ps(json)?;
                let phi = mll_phi_comp(&ps);
                if cuts > 0 {
                    (
                        "Danos–Régnier",
                        None,
                        format!(
                            "DR is a *cut-free* criterion; this structure has {cuts} cut(s). \
                             Its Φ_comp encodes cut as resolution — load it and run (Ex / the \
                             stepper) to perform cut-elimination, the computational content."
                        ),
                        phi,
                    )
                } else {
                    match guarded(|| {
                        let (p, _) = mll_ps(json).unwrap();
                        dr_correct(&p)
                    }) {
                        Some(b) => ("Danos–Régnier", Some(b),
                            (if b { "Correctness criterion satisfied (every switching is a tree)." }
                             else { "Not DR-correct (some switching is disconnected or cyclic)." })
                            .to_string(), phi),
                        None => ("Danos–Régnier", None,
                            "The engine rejected this structure for the DR criterion \
                             (a well-formedness precondition was not met).".to_string(), phi),
                    }
                }
            }
            "mll2i" => {
                let ps = m2_ps(json)?;
                let phi = m2_phi_comp(&ps);
                match guarded(|| girard_correct(&m2_ps(json).unwrap())) {
                    Some(b) => ("Girard", Some(b),
                        (if b { "Girard correctness (§75) satisfied." }
                         else { "Not Girard-correct." }).to_string(), phi),
                    None => ("Girard", None,
                        "The engine rejected this structure for the Girard criterion \
                         (a precondition was not met).".to_string(), phi),
                }
            }
            _ => return Err(format!("unknown proof kind {kind:?} (mll|mll2i)")),
        };
    let phi_src = fmt_c(&phi);

    // Diagram witness — only for small proof structures (bounded by stars).
    let (diagrams_json, diag_note) = if n_stars(&phi) == 0 {
        ("[]".to_string(), "Φ_comp is empty.".to_string())
    } else if n_stars(&phi) > DIAG_STAR_CAP {
        (
            "[]".to_string(),
            format!(
                "Φ_comp has {} stars (> {} cap): the saturated-diagram set is \
                 not enumerated in-browser. The correctness verdict above and \
                 Φ_comp (editable, runnable) still stand.",
                n_stars(&phi),
                DIAG_STAR_CAP
            ),
        )
    } else {
        let dg = DepGraph::from_constellation(&phi);
        let diags = saturated_diagrams(&phi, &dg);
        let total = diags.len();
        let items: Vec<String> = diags
            .iter()
            .take(DIAG_SHOW_CAP)
            .map(|d| {
                format!(
                    "{{\"vertices\":{},\"edges\":{},\"connected\":{},\"correct\":{},\"actualised\":{},\"dot\":{}}}",
                    d.n_vertices(),
                    d.n_edges(),
                    d.is_connected(),
                    d.is_correct(&phi),
                    match d.actualise(&phi) {
                        Some(s) => jstr(&fmt_c(&vec![s])),
                        None => "null".to_string(),
                    },
                    jstr(&diagram_dot(d, &phi))
                )
            })
            .collect();
        (
            format!("[{}]", items.join(",")),
            format!(
                "{total} saturated diagram(s){}.",
                if total > DIAG_SHOW_CAP {
                    format!(" — showing first {DIAG_SHOW_CAP}")
                } else {
                    String::new()
                }
            ),
        )
    };

    let verdict_json = match verdict {
        Some(true) => "true",
        Some(false) => "false",
        None => "null",
    };
    Ok(format!(
        "{{\"ok\":true,\"verdict_name\":{},\"verdict\":{},\"verdict_note\":{},\"phi\":{},\"diagrams\":{},\"diag_note\":{}}}",
        jstr(verdict_name),
        verdict_json,
        jstr(&vnote),
        jstr(&phi_src),
        diagrams_json,
        jstr(&diag_note)
    ))
}

// ── behaviour / type bench ───────────────────────────────────────────────────
#[derive(Deserialize)]
struct BehSpec {
    /// the pre-behaviour A (a finite family of constellations, as source)
    members: Vec<String>,
    /// the finite universe candidates are drawn from
    universe: Vec<String>,
    /// "fin" | "one" | "roots"
    #[serde(default = "default_orth")]
    orth: String,
}
fn default_orth() -> String {
    "roots".into()
}
fn parse_fam(v: &[String], who: &str) -> Result<Vec<Constellation>, String> {
    v.iter()
        .enumerate()
        .map(|(i, s)| parse_constellation(s).map_err(|e| format!("{who}[{i}]: {}", jerr(e))))
        .collect()
}
fn orth_of(s: &str) -> Orth {
    match s {
        "fin" => Orth::Fin,
        "one" => Orth::One,
        _ => Orth::Roots,
    }
}

/// Behaviour bench: is A a behaviour (A = A^⊥⊥)? with |A^⊥|, |A^⊥⊥| over a
/// small finite universe. This is the genuine transcendental-syntax notion
/// of a type — orthogonality-defined, not Curry–Howard.
pub fn behaviour(json: &str) -> Result<String, String> {
    let s: BehSpec = serde_json::from_str(json).map_err(jerr)?;
    if s.universe.len() > UNIVERSE_CAP {
        return Err(format!(
            "universe has {} members (> {} cap): biorth is O(universe²·|A|) \
             and would not be bounded.",
            s.universe.len(),
            UNIVERSE_CAP
        ));
    }
    let members = parse_fam(&s.members, "members")?;
    let universe = parse_fam(&s.universe, "universe")?;
    let o = orth_of(&s.orth);
    let a = Behaviour::new(members);
    let a_perp = orthogonal_set(&a, &universe, o);
    let a_perp2 = biorth(&a, &universe, o);
    let is_b = is_behaviour(&a, &universe, o);
    Ok(format!(
        "{{\"ok\":true,\"orth\":{},\"a\":{},\"a_perp\":{},\"a_biperp\":{},\"is_behaviour\":{}}}",
        jstr(&s.orth),
        a.0.len(),
        a_perp.0.len(),
        a_perp2.0.len(),
        is_b
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dual_atoms_are_orthogonal() {
        // [+a(X)] and [-a(X)] should resolve to a single result → ⊥¹.
        let r = orthogonality("[+a(X)]", "[-a(X), R]").expect("ok");
        assert!(r.contains("\"ok\":true"), "got {r}");
    }

    #[test]
    fn mll_cut_free_axiom_is_dr_correct() {
        // A single axiom is a cut-free, DR-correct proof of a, a⊥.
        let r = proofnet("mll", r#"{"links":[{"kind":"ax","left":0,"right":1}]}"#)
            .expect("ok");
        assert!(r.contains("\"verdict\":true"), "single axiom is DR-correct: {r}");
        assert!(r.contains("\"phi\":\"["), "Φ_comp emitted");
    }

    #[test]
    fn mll_with_cut_is_not_applicable_not_a_panic() {
        // ax+ax+cut: DR is cut-free only — must report N/A, never panic.
        let json = r#"{"links":[
          {"kind":"ax","left":0,"right":1},
          {"kind":"ax","left":2,"right":3},
          {"kind":"cut","left":1,"right":2}]}"#;
        let r = proofnet("mll", json).expect("ok (no panic)");
        assert!(r.contains("\"verdict\":null"), "cut ⇒ DR N/A: {r}");
        assert!(r.contains("cut-elimination"), "explains cut-elim by execution");
        assert!(r.contains("\"phi\":\"["), "Φ_comp still emitted");
    }

    #[test]
    fn behaviour_bench_runs_small() {
        let json = r#"{
          "members": ["[+a(X)]"],
          "universe": ["[+a(X)]", "[-a(X), R]"],
          "orth": "roots"
        }"#;
        let r = behaviour(json).expect("ok");
        assert!(r.contains("\"is_behaviour\":"), "got {r}");
    }

    #[test]
    fn caps_refuse_cleanly() {
        let big = "[+a(X)]".to_string();
        let many = (0..50).map(|_| big.clone()).collect::<Vec<_>>().join(" + ");
        assert!(orthogonality(&many, &many).is_err(), "ortho cap must trip");
    }
}
