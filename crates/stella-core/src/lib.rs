#[cfg(test)]
mod tests {
    use open_hypergraphs::lax::{Hyperedge, OpenHypergraph};

    /// Smoke test: construct a minimal open hypergraph using the lax imperative builder.
    ///
    /// Models: `f : A → A` as a single-operation graph with one node in, one node out.
    #[test]
    fn smoke_open_hypergraph() {
        #[derive(PartialEq, Clone)]
        enum Obj { A }

        #[derive(PartialEq, Clone)]
        enum Op { F }

        let mut g = OpenHypergraph::<Obj, Op>::empty();

        // Create two nodes: one source-side, one target-side
        let src = g.new_node(Obj::A);
        let tgt = g.new_node(Obj::A);

        // Add a hyperedge Op::F with src as its source and tgt as its target
        g.new_edge(Op::F, Hyperedge { sources: vec![src], targets: vec![tgt] });

        // Wire the open hypergraph interfaces
        g.sources = vec![src];
        g.targets = vec![tgt];

        assert_eq!(g.sources.len(), 1);
        assert_eq!(g.targets.len(), 1);
        assert_eq!(g.hypergraph.nodes.len(), 2);
        assert_eq!(g.hypergraph.edges.len(), 1);
    }
}
