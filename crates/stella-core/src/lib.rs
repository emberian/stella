pub mod alpha;
pub mod arith;
pub mod atm;
pub mod automata;
pub mod ch9;
pub mod circuits;
pub mod combinator;
pub mod concrete;
pub mod nfta;
pub mod constellation;
pub mod dep_graph;
pub mod diagram;
pub mod index;
pub mod execution;
pub mod mll;
pub mod mll2i;
pub mod strategy;
pub mod interactive;
pub mod parse;
pub mod pda;
pub mod polarised;
pub mod subst;
pub mod subjective;
pub mod reafference;
pub mod valence;
pub mod experiment;
pub mod perturbation;
pub mod term;
pub mod tiles;
pub mod tm;
pub mod transducer;
pub mod unify;
pub mod viz;
pub mod omega_weight;

#[cfg(test)]
mod engine_tests;

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

// ─────────────────────────────────────────────────────────────────────────────
// Unit tests for unification and matchability
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod unification_tests {
    use crate::term::Term;
    use crate::subst::Substitution;
    use crate::unify::{unify, Equation};
    use crate::alpha::alpha_unify;
    use crate::polarised::{matchable, neg_ray, pos_ray};

    // ── Helpers ──────────────────────────────────────────────────────────────

    fn var(x: &str) -> Term { Term::var(x) }
    fn app(f: &str, args: Vec<Term>) -> Term { crate::term::mk_app_str(f, args) }
    fn c(name: &str) -> Term { Term::constant(name) }

    fn eq(l: Term, r: Term) -> Equation { Equation::new(l, r) }

    // Check that applying the substitution to lhs and rhs makes them equal.
    fn check_unifier(sigma: &Substitution, lhs: &Term, rhs: &Term) -> bool {
        sigma.apply(*lhs) == sigma.apply(*rhs)
    }

    // ── A. Terms ─────────────────────────────────────────────────────────────

    #[test]
    fn term_vars() {
        // vars(f(X, g(Y, X))) = {X, Y}
        let t = app("f", vec![var("X"), app("g", vec![var("Y"), var("X")])]);
        let vs = t.vars();
        assert!(vs.contains(&crate::term::Var::intern("X")));
        assert!(vs.contains(&crate::term::Var::intern("Y")));
        assert_eq!(vs.len(), 2);
    }

    // ── B. Substitution & Composition ────────────────────────────────────────

    #[test]
    fn substitution_apply() {
        // θ = {X ↦ c, Y ↦ c}   (§B.1.8 example style)
        let theta = Substitution::from_pairs([
            ("X".into(), c("c")),
            ("Y".into(), c("c")),
        ]);
        let t = app("f", vec![var("X"), var("Y")]);
        assert_eq!(theta.apply(t), app("f", vec![c("c"), c("c")]));
    }

    #[test]
    fn substitution_composition() {
        // §B.1.7: (θ₁ ∘ θ₂)(t) = θ₁(θ₂(t))
        // θ₂ = {X ↦ f(Y)},  θ₁ = {Y ↦ c}
        // Expect: (θ₁ ∘ θ₂)(X) = θ₁(f(Y)) = f(c)
        let theta2 = Substitution::from_pairs([("X".into(), app("f", vec![var("Y")]))]);
        let theta1 = Substitution::from_pairs([("Y".into(), c("c"))]);
        let composed = Substitution::compose(&theta1, &theta2);
        assert_eq!(composed.apply(var("X")), app("f", vec![c("c")]));
    }

    // ── C. Martelli-Montanari rules ───────────────────────────────────────────

    /// Clear rule: `{t =? t} → {}`.
    #[test]
    fn unify_clear_trivial() {
        let result = unify(vec![eq(var("X"), var("X"))]);
        assert!(result.is_some());
        let s = result.unwrap();
        // X maps to itself (or is absent from the substitution).
        assert_eq!(s.apply(var("X")), var("X"));
    }

    /// Open rule: `{f(t₁,t₂) =? f(u₁,u₂)} → {t₁=?u₁, t₂=?u₂}`.
    #[test]
    fn unify_open_decomposition() {
        // {f(X, c) =? f(g(Y), c)} should give X ↦ g(Y).
        let lhs = app("f", vec![var("X"), c("c")]);
        let rhs = app("f", vec![app("g", vec![var("Y")]), c("c")]);
        let result = unify(vec![eq(lhs, rhs)]);
        assert!(result.is_some());
        let s = result.unwrap();
        // X must be mapped to g(Y).
        assert_eq!(s.apply(var("X")), app("g", vec![var("Y")]));
    }

    /// Orient rule makes `{f(X) =? Y}` become `{Y =? f(X)}`, then Replace.
    #[test]
    fn unify_orient_then_replace() {
        // {f(c) =? Y}  →orient→  {Y =? f(c)}  →replace→  done; Y ↦ f(c)
        let result = unify(vec![eq(app("f", vec![c("c")]), var("Y"))]);
        assert!(result.is_some());
        let s = result.unwrap();
        assert_eq!(s.apply(var("Y")), app("f", vec![c("c")]));
    }

    /// Replace rule propagates a binding.
    #[test]
    fn unify_replace() {
        // {X =? c, f(X) =? f(c)} should succeed with X ↦ c.
        let result = unify(vec![
            eq(var("X"), c("c")),
            eq(app("f", vec![var("X")]), app("f", vec![c("c")])),
        ]);
        assert!(result.is_some());
        let s = result.unwrap();
        assert_eq!(s.apply(var("X")), c("c"));
    }

    /// Multi-equation successful unification.
    #[test]
    fn unify_multi_equation() {
        // From §B.1.10: {f(X, f(Y)) =? f(g(c,c), Z)}
        // should give X ↦ g(c,c), Z ↦ f(Y) (or similar mgu).
        let lhs = app("f", vec![var("X"), app("f", vec![var("Y")])]);
        let rhs = app("f", vec![app("g", vec![c("c"), c("c")]), var("Z")]);
        let result = unify(vec![eq(lhs.clone(), rhs.clone())]);
        assert!(result.is_some());
        let s = result.unwrap();
        // The unifier must equate both sides.
        assert!(check_unifier(&s, &lhs, &rhs));
    }

    /// Occur-check failure: `{X =? f(X)}` is unsolvable (§B.1.10 example).
    #[test]
    fn unify_occur_check_failure() {
        // The side-condition X ∉ vars(t) in Replace is the occur check.
        let result = unify(vec![eq(var("X"), app("f", vec![var("X")]))]);
        assert!(result.is_none(), "occur check must reject X =? f(X)");
    }

    /// Clash: `{f(X) =? g(c)}` is unsolvable because f ≠ g (§B.2.1 Open fails).
    #[test]
    fn unify_clash_failure() {
        let result = unify(vec![eq(app("f", vec![var("X")]), app("g", vec![c("c")]))]);
        assert!(result.is_none(), "f ≠ g is a clash");
    }

    /// Arity mismatch is also a clash.
    #[test]
    fn unify_arity_mismatch() {
        let result = unify(vec![eq(
            app("f", vec![var("X"), var("Y")]),
            app("f", vec![var("X")]),
        )]);
        assert!(result.is_none());
    }

    // ── D. α-unification ─────────────────────────────────────────────────────

    /// §B.1.13 example: `{X =? f(X)}` has no unifier but has an α-unifier.
    /// Here we test a simpler version: `X` and `f(Y)` are α-unifiable
    /// (rename X → X', then unify X' with f(Y): trivially solved as X' ↦ f(Y)).
    #[test]
    fn alpha_unify_simple() {
        // t1 = X,  t2 = f(Y);  they share no structure, but after renaming
        // t1 = a0 and t2 = f(b0), unification gives a0 ↦ f(b0). Should succeed.
        let t1 = var("X");
        let t2 = app("f", vec![var("Y")]);
        assert!(alpha_unify(t1, t2).is_some());
    }

    /// Two terms sharing a variable name: α-unification renames them apart first.
    #[test]
    fn alpha_unify_shared_variable() {
        // t1 = f(X),  t2 = g(X).
        // After renaming: t1 = f(a0),  t2 = g(b0).
        // These are plainly unifiable only if f = g.  Here f ≠ g: should fail.
        let t1 = app("f", vec![var("X")]);
        let t2 = app("g", vec![var("X")]);
        assert!(alpha_unify(t1, t2).is_none());
    }

    /// α-unifiable when terms share a variable name but ARE structurally compatible.
    #[test]
    fn alpha_unify_shared_var_compatible() {
        // t1 = f(X),  t2 = f(X).
        // After renaming to disjoint vars: f(a0) =? f(b0).
        // Succeeds with a0 ↦ b0 (or b0 ↦ a0).
        let t1 = app("f", vec![var("X")]);
        let t2 = app("f", vec![var("X")]);
        assert!(alpha_unify(t1, t2).is_some());
    }

    // ── E. Polarised signature & matchability (§49.9 examples) ───────────────

    /// §49.9: `+c(X) ⋈ −c(0)` holds.
    #[test]
    fn matchable_pos_c_neg_c() {
        // +c(X) is a positive ray; -c(0) is a negative ray; same neutral symbol c.
        let r  = pos_ray("c", vec![var("X")]);
        let rp = neg_ray("c", vec![c("0")]);
        assert!(matchable(r, rp), "+c(X) ⋈ -c(0) should hold");
    }

    /// §49.9: `−d(X) ⋈ +d(f(X))` holds.
    #[test]
    fn matchable_neg_d_pos_d() {
        // -d(X) is negative; +d(f(X)) is positive; same underlying symbol d.
        // After renaming, -d(a0) =? +d(f(b0)): compatible (d,d, opp polarity)
        // decompose → a0 =? f(b0): solved.
        let r  = neg_ray("d", vec![var("X")]);
        let rp = pos_ray("d", vec![app("f", vec![var("X")])]);
        assert!(matchable(r, rp), "-d(X) ⋈ +d(f(X)) should hold");
    }

    /// §49.9: NOT `+c(X) ⋈ f(Y)` — `f(Y)` is an unpolarised (neutral) ray,
    /// but `+c` has a neutral underlying `c` and `f` is neutral name `f`;
    /// they are different underlying symbols.
    #[test]
    fn not_matchable_pos_c_unpolarised_f() {
        // +c(X) has neutral name "c", f(Y) has neutral name "f".  |c| ≠ |f|.
        let r  = pos_ray("c", vec![var("X")]);
        let rp = crate::term::mk_app_str("f", vec![var("Y")]);
        assert!(!matchable(r, rp), "+c(X) should not match f(Y)");
    }

    /// §49.9: NOT `+c(X) ⋈ −d(X)` — different underlying symbols.
    #[test]
    fn not_matchable_different_underlying() {
        let r  = pos_ray("c", vec![var("X")]);
        let rp = neg_ray("d", vec![var("X")]);
        assert!(!matchable(r, rp), "+c(X) should not match -d(X)");
    }

    /// §49.9: NOT `+c(X) ⋈ +c(f(Y))` — same polarity, not opposite.
    #[test]
    fn not_matchable_same_polarity() {
        let r  = pos_ray("c", vec![var("X")]);
        let rp = pos_ray("c", vec![app("f", vec![var("Y")])]);
        assert!(!matchable(r, rp), "+c(X) should not match +c(f(Y)) (same polarity)");
    }

    /// §49.9: NOT `+c(f(X)) ⋈ −c(g(Y))` — terms not α-unifiable (f ≠ g clash).
    #[test]
    fn not_matchable_terms_not_alpha_unifiable() {
        let r  = pos_ray("c", vec![app("f", vec![var("X")])]);
        let rp = neg_ray("c", vec![app("g", vec![var("Y")])]);
        assert!(!matchable(r, rp), "+c(f(X)) should not match -c(g(Y))");
    }

    // ── §49.8: anti-reflexivity and anti-transitivity of ⋈ ──────────────────

    /// §49.8: anti-reflexive — `r ⋈ r` never holds.
    ///
    /// Proof sketch (Eng §49.8): `r` and `r` have the same polarity, and
    /// two symbols of the same polarity cannot be compatible by `⊂`.
    #[test]
    fn matchable_anti_reflexive_positive() {
        let r = pos_ray("c", vec![var("X")]);
        assert!(!matchable(r, r), "⋈ is anti-reflexive");
    }

    #[test]
    fn matchable_anti_reflexive_negative() {
        let r = neg_ray("d", vec![var("Y")]);
        assert!(!matchable(r, r), "⋈ is anti-reflexive");
    }

    /// §49.8: anti-transitive — `r₁ ⋈ r₂` and `r₂ ⋈ r₃` do not imply `r₁ ⋈ r₃`.
    ///
    /// Proof sketch: `r₁ ⋈ r₂` means opposite polarities, `r₂ ⋈ r₃` means
    /// r₂ and r₃ have opposite polarities too, so r₃ has the same polarity
    /// as r₁; hence `r₁ ⋈ r₃` fails by `⊂`.
    #[test]
    fn matchable_anti_transitive() {
        // r₁ = +c(X), r₂ = -c(Y), r₃ = +c(Z)
        // r₁ ⋈ r₂ holds (opposite polarities, same neutral c)
        // r₂ ⋈ r₃ holds
        // r₁ ⋈ r₃ must NOT hold (both positive)
        let r1 = pos_ray("c", vec![var("X")]);
        let r2 = neg_ray("c", vec![var("Y")]);
        let r3 = pos_ray("c", vec![var("Z")]);
        assert!(matchable(r1, r2), "r1 ⋈ r2 should hold");
        assert!(matchable(r2, r3), "r2 ⋈ r3 should hold");
        assert!(!matchable(r1, r3), "⋈ is anti-transitive: r1 ⋈ r3 must fail");
    }

    /// §49.8: symmetry — `r ⋈ r′` iff `r′ ⋈ r`.
    #[test]
    fn matchable_symmetric() {
        let r  = pos_ray("c", vec![var("X")]);
        let rp = neg_ray("c", vec![var("Y")]);
        assert_eq!(matchable(r, rp), matchable(rp, r), "⋈ is symmetric");
    }
}
