//! Graphviz DOT visualizer for constellations and dependency graphs.
//!
//! Provides `dep_graph_dot` which emits DOT for the dependency graph
//! `D[Φ; C]` of a constellation, and `diagram_dot` for a `Diagram`.
//!
//! ## Design decision: hand-rolled DOT
//!
//! We emit DOT directly as a `String`.  We do NOT use `open-hypergraphs-dot`
//! because that crate visualizes open hypergraphs' own internal data model,
//! which does not correspond to our Eng-faithful `Constellation` /
//! `DepGraph` representation.  The DOT format is simple enough (~40 lines)
//! to hand-write faithfully.

use crate::constellation::Constellation;
use crate::dep_graph::DepGraph;
use crate::diagram::Diagram;

// ─────────────────────────────────────────────────────────────────────────────
// Dependency-graph DOT
// ─────────────────────────────────────────────────────────────────────────────

/// Emit Graphviz DOT for the dependency graph `D[Φ; C]`.
///
/// Layout:
/// * Each **star** is a node labelled with the star index and its rays.
///   E.g. node 0 carries label `"star_0\n[+i(cons(0,...)), ...]"`.
/// * Each **dependency edge** `{(i,j),(i',j')}` is an undirected edge
///   between the two star nodes, labelled with the two ray terms that
///   make the edge (one positive, one negative).
///
/// The DOT is `undirected` (`graph`), consistent with Eng §49.10's use
/// of unordered ray-id pairs.
pub fn dep_graph_dot(dg: &DepGraph, phi: &Constellation) -> String {
    let mut out = String::new();

    out.push_str("graph dep_graph {\n");
    out.push_str("  rankdir=LR;\n");
    out.push_str("  node [shape=box, fontname=\"monospace\"];\n");
    out.push_str("  edge [fontname=\"monospace\", fontsize=9];\n");

    // Nodes — one per star.
    for (i, star) in phi.iter().enumerate() {
        let rays_label = star
            .iter()
            .map(|r| format!("{r}"))
            .collect::<Vec<_>>()
            .join(", ");
        // Escape double-quotes and backslashes for DOT labels.
        let safe_label = rays_label.replace('\\', "\\\\").replace('"', "\\\"");
        out.push_str(&format!(
            "  star_{i} [label=\"star_{i}\\n[{safe_label}]\"];\n"
        ));
    }

    // Edges — one per DepEdge.
    for (e_idx, edge) in dg.edges.iter().enumerate() {
        let (rid_a, rid_b) = edge.ends();
        let (si_a, rj_a) = rid_a;
        let (si_b, rj_b) = rid_b;

        // Only draw edge if both star indices are in bounds.
        if si_a >= phi.len() || si_b >= phi.len() {
            continue;
        }

        let ray_a = &phi[si_a][rj_a];
        let ray_b = &phi[si_b][rj_b];
        let label_a = format!("{ray_a}").replace('"', "\\\"");
        let label_b = format!("{ray_b}").replace('"', "\\\"");
        let edge_label = format!("{label_a} ⋈ {label_b}").replace('"', "\\\"");

        out.push_str(&format!(
            "  star_{si_a} -- star_{si_b} [label=\"{edge_label}\", tooltip=\"edge_{e_idx}\"];\n"
        ));
    }

    out.push_str("}\n");
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Diagram DOT (optional)
// ─────────────────────────────────────────────────────────────────────────────

/// Emit Graphviz DOT for a `Diagram` over a `Constellation`.
///
/// Layout:
/// * Each **diagram vertex** `v` is a node labelled with vertex index and
///   the star it maps to (including the star's rays).
/// * Each **diagram edge** is an undirected edge between the two vertex
///   nodes, labelled with the two rays that gave rise to the dep-edge.
pub fn diagram_dot(diagram: &Diagram, phi: &Constellation) -> String {
    let mut out = String::new();
    out.push_str("graph diagram {\n");
    out.push_str("  rankdir=TB;\n");
    out.push_str("  node [shape=ellipse, fontname=\"monospace\"];\n");
    out.push_str("  edge [fontname=\"monospace\", fontsize=9];\n");

    // Nodes.
    for (v, &si) in diagram.vertex_star.iter().enumerate() {
        let rays_label = if si < phi.len() {
            phi[si]
                .iter()
                .map(|r| format!("{r}"))
                .collect::<Vec<_>>()
                .join(", ")
        } else {
            format!("star_{si}")
        };
        let safe = rays_label.replace('\\', "\\\\").replace('"', "\\\"");
        out.push_str(&format!(
            "  v{v} [label=\"v{v}: star_{si}\\n[{safe}]\"];\n"
        ));
    }

    // Edges.
    for (e_idx, de) in diagram.edges.iter().enumerate() {
        let (u, v) = de.vertices;
        let (rid_a, rid_b) = de.dep_edge.ends();
        let (si_a, rj_a) = rid_a;
        let (si_b, rj_b) = rid_b;
        let ray_a = if si_a < phi.len() && rj_a < phi[si_a].len() {
            format!("{}", phi[si_a][rj_a])
        } else {
            format!("({si_a},{rj_a})")
        };
        let ray_b = if si_b < phi.len() && rj_b < phi[si_b].len() {
            format!("{}", phi[si_b][rj_b])
        } else {
            format!("({si_b},{rj_b})")
        };
        let label = format!("{ray_a} ⋈ {ray_b}")
            .replace('"', "\\\"");
        out.push_str(&format!(
            "  v{u} -- v{v} [label=\"{label}\", tooltip=\"edge_{e_idx}\"];\n"
        ));
    }

    out.push_str("}\n");
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::{Nfa, nfa_constellation};
    use crate::dep_graph::DepGraph;

    /// Build the Eng Fig 56.1 NFA inline (same as in automata tests).
    fn eng_fig561_nfa() -> Nfa {
        Nfa {
            states: vec!["q0".into(), "q1".into(), "q2".into()],
            alphabet: vec!["0".into(), "1".into()],
            initial: vec!["q0".into()],
            finals: vec!["q2".into()],
            transitions: vec![
                ("q0".into(), Some("0".into()), "q0".into()),
                ("q0".into(), Some("1".into()), "q0".into()),
                ("q0".into(), Some("0".into()), "q1".into()),
                ("q1".into(), Some("0".into()), "q2".into()),
            ],
        }
    }

    /// Build the NFA constellation for the Eng Figure 56.1 example ("000"),
    /// compute the dependency graph, and check that the DOT output is well-formed.
    #[test]
    fn dep_graph_dot_nfa_example() {
        let nfa = eng_fig561_nfa();
        let word = ["0", "0", "0"];
        let phi = nfa_constellation(&nfa, &word, 0);
        let dg = DepGraph::from_constellation(&phi);

        let dot = dep_graph_dot(&dg, &phi);

        // Must start and end with graph delimiters.
        assert!(dot.starts_with("graph dep_graph {"), "DOT must open with graph declaration");
        assert!(dot.trim_end().ends_with('}'), "DOT must close with }}");

        // Every star must appear as a node.
        for i in 0..phi.len() {
            assert!(
                dot.contains(&format!("star_{i} [")),
                "DOT must contain node star_{i}"
            );
        }

        // Edge count: DOT lines containing " -- " should match dg.edges.len().
        let edge_lines: Vec<&str> = dot.lines().filter(|l| l.contains(" -- ")).collect();
        assert_eq!(
            edge_lines.len(),
            dg.edges.len(),
            "DOT edge count ({}) should equal DepGraph edge count ({})",
            edge_lines.len(),
            dg.edges.len()
        );
    }

    /// Optionally write the NFA example DOT to target/nfa_example.dot.
    ///
    /// This test always passes; it only writes if the target dir is accessible.
    /// File is placed inside the crate's own target dir to avoid repo pollution.
    #[test]
    fn write_nfa_example_dot() {
        let nfa = eng_fig561_nfa();
        let word = ["0", "0", "0"];
        let phi = nfa_constellation(&nfa, &word, 0);
        let dg = DepGraph::from_constellation(&phi);
        let dot = dep_graph_dot(&dg, &phi);

        // Write to the workspace target dir (which may differ from crate's dir
        // in a Cargo workspace).  CARGO_MANIFEST_DIR points to the crate root;
        // we try crate/target first, then the parent workspace target.
        let manifest = env!("CARGO_MANIFEST_DIR");
        let crate_target = std::path::PathBuf::from(manifest).join("target");
        let ws_target = std::path::PathBuf::from(manifest)
            .parent()
            .and_then(|p| p.parent())
            .map(|p| p.join("target"));

        let target_dir = if crate_target.exists() {
            Some(crate_target)
        } else {
            ws_target.filter(|p| p.exists())
        };

        if let Some(target) = target_dir {
            let path = target.join("nfa_example.dot");
            let _ = std::fs::write(&path, &dot);
            // No assertion: writing is best-effort.
        }
    }
}
