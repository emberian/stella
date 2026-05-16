//! Non-deterministic Finite Tree Automata (NFTA) encoding (Eng §57.7–57.12).
//!
//! ## Overview (§57.7)
//!
//! A **top-down NFTA** `T = (Q, F, ar, Q₀, Δ)` consists of:
//! - `Q`: finite set of states.
//! - `F`: ranked alphabet (function symbols with arities).
//! - `ar : F → ℕ`: arity function.
//! - `Q₀ ⊆ Q`: set of initial states.
//! - `Δ`: set of transition rules `q(f(x₁…xₙ)) → f(q₁(x₁)…qₙ(xₙ))` for
//!   `q, q₁, …, qₙ ∈ Q`, `f ∈ F`, `ar(f) = n`.
//!
//! ## Tree encoding (§57.8) — `t★`
//!
//! Trees over `F` are encoded as terms:
//!
//! ```text
//! leaf x   →  variable X          (i.e. a fresh variable — Tree::Leaf)
//! f(t₁…tₙ) →  f(t₁★ … tₙ★)      (function symbol applied to encoded subtrees — Tree::Node)
//! ```
//!
//! In our API: `Tree::Leaf` becomes a `Term::var`, `Tree::Node` becomes `mk_app_str`.
//!
//! ## Automaton constellation `T★` (§57.9–57.10)
//!
//! The NFTA machine constellation `T★` consists of three kinds of stars:
//!
//! 1. **Initial stars** — one per initial state `q₀ ∈ Q₀`:
//!    ```text
//!    [−i(T), +ta(q₀, T)]
//!    ```
//!
//! 2. **Rule stars** — one per `(q, f)` transition and per child position `i`:
//!    ```text
//!    [−ta(q, f(X₁, …, Xₙ)), +ta(qᵢ, Xᵢ)]
//!    ```
//!    (n stars per rule with n children)
//!
//! 3. **Terminal stars** — two kinds:
//!
//!    a. **Variable-leaf stars** (§57.10 verbatim): one per leaf-accepting state `q`:
//!       ```text
//!       [−ta(q, X), accept]
//!       ```
//!       These fire when the automaton reaches a `Tree::Leaf` (variable in the encoding).
//!
//!    b. **Ground-constant stars**: one per `(state, arity-0-symbol)` pair:
//!       ```text
//!       [−ta(q, c()), accept]
//!       ```
//!       These fire when the automaton reaches a `Tree::Node("c", [])` constant (arity 0).
//!       Required for closed trees (no free variables) like boolean formula evaluation.
//!
//! ## Acceptance criterion (Thm §57.11)
//!
//! ```text
//! T(t) = 1   ⟺   ɟEx(T★ + t★) ≠ ∅
//! ```
//!
//! where `ɟ = ↨♭` (conceal + noise-filter), and `Ex` is **abstract execution**
//! (AEx), NOT IEx.
//!
//! ## Fast execution
//!
//! We use **IEx** (interactive execution) with:
//! - Reference Φ = T★ (infinite supply of machine stars)
//! - Initial Ψ = {t★} (tree star, consumed once)
//!
//! This is equivalent to AEx for deterministic top-down traversal (one acceptance
//! path per tree) and runs in O(|tree| × |rules|) steps rather than the
//! exponential AEx diagram enumeration.
//!
//! The criterion becomes: `T` accepts `t` iff `[accept] ∈ ↨♭ IEx(T★, {t★})`.
//!
//! ## Notation
//!
//! ```text
//! T★ = initial stars + rule stars + terminal stars
//! t★ = [+i(encode(t))]
//! IEx(T★, {t★}) — drive Φ ⊢ {t★} ↝* normal form
//! accept ∈ ↨♭(result) ⟺ T(t) = 1
//! ```

use crate::constellation::{Constellation, Star};
use crate::execution::stars_alpha_equiv;
use crate::interactive::{conceal_and_filter, iex};
use crate::term::Term;

// ─────────────────────────────────────────────────────────────────────────────
// Helper constructors
// ─────────────────────────────────────────────────────────────────────────────

fn var(name: &str) -> Term {
    crate::term::mk_var(name)
}

fn cst(name: &str) -> Term {
    crate::term::mk_app_str(name, vec![])
}

fn app(f: &str, args: Vec<Term>) -> Term {
    crate::term::mk_app_str(f, args)
}

fn pos_ray(neutral: &str, args: Vec<Term>) -> Term {
    app(&format!("+{neutral}"), args)
}

fn neg_ray(neutral: &str, args: Vec<Term>) -> Term {
    app(&format!("-{neutral}"), args)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tree representation
// ─────────────────────────────────────────────────────────────────────────────

/// A **finite tree** over a ranked alphabet.
///
/// - `Leaf(name)`: a leaf node (becomes a variable in the tree encoding `t★`).
///   Represents a free variable position — e.g. `x` in `f(x)`.
/// - `Node(f, children)`: an internal node `f(t₁, …, tₙ)` where `f` has arity `n`.
///   For arity-0 constants (like `1`, `0` in boolean formulas), use `Node("c", [])`.
#[derive(Debug, Clone)]
pub enum Tree {
    /// A leaf variable (encodes to a `Term::var`).
    Leaf(String),
    /// An internal (or constant) node `f(t₁, …, tₙ)`.
    Node(String, Vec<Tree>),
}

impl Tree {
    /// Encode the tree as a term `t★` (§57.8).
    ///
    /// ```text
    /// leaf x       →  Var(x)
    /// f(t₁ … tₙ)  →  f(t₁★ … tₙ★)
    /// ```
    pub fn encode(&self) -> Term {
        match self {
            Tree::Leaf(name) => var(name),
            Tree::Node(f, children) => {
                let encoded_children: Vec<Term> = children.iter().map(|c| c.encode()).collect();
                app(f, encoded_children)
            }
        }
    }

    /// Build the tree input star `t★ = [+i(encode(t))]`.
    pub fn tree_star(&self) -> Star {
        vec![pos_ray("i", vec![self.encode()])]
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NFTA transition rule
// ─────────────────────────────────────────────────────────────────────────────

/// A **transition rule** in a top-down NFTA (§57.7).
///
/// Encodes: `q(f(x₁…xₙ)) → f(q₁(x₁) … qₙ(xₙ))`.
///
/// When the automaton is in state `q` and sees tree node `f` with `n` children,
/// it sends child `i` to state `q_successors[i]`.
#[derive(Debug, Clone)]
pub struct NftaRule {
    /// State at this node: `q`.
    pub state: String,
    /// Function symbol at this node: `f`, with arity = `successors.len()`.
    pub symbol: String,
    /// States for each child position: `[q₁, …, qₙ]`.
    pub successors: Vec<String>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Top-down NFTA
// ─────────────────────────────────────────────────────────────────────────────

/// A **top-down non-deterministic finite tree automaton** (§57.7).
///
/// The automaton accepts a tree `t` if there exists a run that starts in an
/// initial state at the root and reaches acceptance at every leaf.
///
/// ## Two kinds of leaf acceptance
///
/// - **`leaf_states`** (§57.10 canonical): for trees with variable leaves. A
///   star `[−ta(q, X), accept]` is generated for each `q ∈ leaf_states`.
///   Matches any leaf variable in the tree encoding.
///
/// - **`terminal_pairs`**: for closed trees with arity-0 constant leaves
///   (like `1` and `0` in boolean formula trees). A star
///   `[−ta(q, c()), accept]` is generated for each `(q, c)` pair. Matches
///   only the specific constant `c`.
///
/// Most automata need only one of these; the boolean formula NFTA needs
/// `terminal_pairs` since all leaves are ground constants `1()` or `0()`.
#[derive(Debug, Clone)]
pub struct Nfta {
    /// All states `Q`.
    pub states: Vec<String>,
    /// Initial states `Q₀ ⊆ Q`.
    pub initial: Vec<String>,
    /// Transition rules `Δ` for symbols with arity ≥ 1.
    pub rules: Vec<NftaRule>,
    /// Leaf-accepting states (§57.10): generate `[−ta(q, X), accept]` for
    /// each `q`. Used for trees with variable leaves (`Tree::Leaf`).
    pub leaf_states: Vec<String>,
    /// Ground-constant acceptance pairs: generate `[−ta(q, c()), accept]`
    /// for each `(q, c)`. Used for closed trees with arity-0 constant leaves.
    pub terminal_pairs: Vec<(String, String)>,
}

impl Nfta {
    /// Build the machine constellation `T★` (§57.9–57.10).
    ///
    /// Produces three kinds of stars:
    ///
    /// 1. **Initial stars**: for each `q₀ ∈ Q₀`:
    ///    `[−i(T), +ta(q₀, T)]`
    ///
    /// 2. **Rule stars**: for each rule `q/f(X₁…Xₙ)→[q₁,…,qₙ]` and each child `i`:
    ///    `[−ta(q, f(X₁, …, Xₙ)), +ta(qᵢ, Xᵢ)]`
    ///
    /// 3. **Terminal stars** (two kinds):
    ///    - Variable-leaf: `[−ta(q, X), accept]` for each `q ∈ leaf_states`
    ///    - Ground-constant: `[−ta(q, c()), accept]` for each `(q,c) ∈ terminal_pairs`
    pub fn machine_constellation(&self) -> Constellation {
        let mut stars: Constellation = Vec::new();

        // 1. Initial stars.
        for q0 in &self.initial {
            stars.push(vec![
                neg_ray("i", vec![var("T")]),
                pos_ray("ta", vec![cst(q0), var("T")]),
            ]);
        }

        // 2. Rule stars (one per child per rule).
        for (rule_idx, rule) in self.rules.iter().enumerate() {
            let n = rule.successors.len();
            let child_vars: Vec<Term> = (0..n)
                .map(|i| var(&format!("X_r{rule_idx}_c{i}")))
                .collect();
            let pattern = app(&rule.symbol, child_vars.clone());

            for (i, qi) in rule.successors.iter().enumerate() {
                stars.push(vec![
                    neg_ray("ta", vec![cst(&rule.state), pattern.clone()]),
                    pos_ray("ta", vec![cst(qi), child_vars[i].clone()]),
                ]);
            }
        }

        // 3a. Variable-leaf stars: [−ta(q, X), accept] for each q ∈ leaf_states.
        for q in &self.leaf_states {
            stars.push(vec![
                neg_ray("ta", vec![cst(q), var("X_leaf")]),
                cst("accept"),
            ]);
        }

        // 3b. Ground-constant terminal stars: [−ta(q, c()), accept]
        // for each (q, c) ∈ terminal_pairs.
        for (q, c) in &self.terminal_pairs {
            stars.push(vec![
                neg_ray("ta", vec![cst(q), cst(c)]),
                cst("accept"),
            ]);
        }

        stars
    }

    /// Check whether the NFTA accepts tree `t` (§57.11 criterion).
    ///
    /// Uses **IEx** with:
    /// - Φ = T★ (machine constellation, infinite supply)
    /// - Ψ = {t★} (tree input star, consumed once)
    ///
    /// Accepts iff `[accept] ∈ ↨♭ IEx(T★, {t★})`.
    ///
    /// Fuel is bounded by `(rules+terminals) × (tree_depth+1) × 4` — sufficient
    /// for top-down deterministic traversal with branching rules.
    pub fn accepts(&self, tree: &Tree) -> bool {
        let phi: Constellation = self.machine_constellation();
        let psi: Vec<Star> = vec![tree.tree_star()];

        // Fuel: each tree node fires one initial/rule star, plus terminal matching.
        let n_stars = phi.len();
        let fuel = (n_stars + 1) * (n_stars + 1) * 4;

        let result = iex(&phi, psi, fuel);
        let visible = conceal_and_filter(&result.psi);

        let accept_star: Star = vec![cst("accept")];
        visible.iter().any(|s| stars_alpha_equiv(s, &accept_star))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── Boolean formula NFTA (Fig 57.1 example) ───────────────────────────────
    //
    // Language: closed boolean formula trees that evaluate to TRUE.
    //
    // Ranked alphabet:
    //   or/2: disjunction
    //   not/1: negation
    //   1/0: true constant
    //   0/0: false constant
    //
    // States: qt (expecting TRUE), qf (expecting FALSE).
    // Initial: {qt} — root must evaluate to TRUE.
    //
    // Transitions:
    //   qt(or(x₁,x₂)) → or(qt(x₁), qf(x₂))  -- left true, right false → OR true
    //   qt(or(x₁,x₂)) → or(qf(x₁), qt(x₂))  -- left false, right true → OR true
    //   qt(not(x))    → not(qf(x))             -- not(false) = true
    //   qf(not(x))    → not(qt(x))             -- not(true) = false
    //   qf(or(x₁,x₂)) → or(qf(x₁), qf(x₂))  -- both false → OR false
    //
    // Acceptance of arity-0 constants:
    //   qt accepts 1  (true constant in "true" context)
    //   qf accepts 0  (false constant in "false" context)
    //
    // ```text
    // Tree encodings:
    //   t★  leaf x →  Var(x)
    //   t★  1      →  1()     (arity-0 application)
    //   t★  0      →  0()
    //   t★  not(t) →  not(t★)
    //   t★  or(t,u)→  or(t★,u★)
    //
    // Machine stars T★:
    //   [−i(T), +ta(qt,T)]                          -- initial
    //   [−ta(qt,or(X1,X2)), +ta(qt,X1)]  (rule 0a) -- qt/or left child qt
    //   [−ta(qt,or(X1,X2)), +ta(qf,X2)]  (rule 0b) -- qt/or right child qf
    //   [−ta(qt,or(X1,X2)), +ta(qf,X1)]  (rule 1a) -- qt/or left child qf
    //   [−ta(qt,or(X1,X2)), +ta(qt,X2)]  (rule 1b) -- qt/or right child qt
    //   [−ta(qt,not(X1)),   +ta(qf,X1)]  (rule 2)  -- qt/not
    //   [−ta(qf,not(X1)),   +ta(qt,X1)]  (rule 3)  -- qf/not
    //   [−ta(qf,or(X1,X2)), +ta(qf,X1)]  (rule 4a) -- qf/or left
    //   [−ta(qf,or(X1,X2)), +ta(qf,X2)]  (rule 4b) -- qf/or right
    //   [−ta(qt,1()),  accept]                       -- terminal qt/1
    //   [−ta(qf,0()),  accept]                       -- terminal qf/0
    // ```

    fn bool_formula_nfta() -> Nfta {
        Nfta {
            states: vec!["qt".into(), "qf".into()],
            initial: vec!["qt".into()],
            rules: vec![
                // qt(or(x₁,x₂)) → or(qt(x₁), qf(x₂))
                NftaRule {
                    state: "qt".into(),
                    symbol: "or".into(),
                    successors: vec!["qt".into(), "qf".into()],
                },
                // qt(or(x₁,x₂)) → or(qf(x₁), qt(x₂))
                NftaRule {
                    state: "qt".into(),
                    symbol: "or".into(),
                    successors: vec!["qf".into(), "qt".into()],
                },
                // qt(not(x)) → not(qf(x))
                NftaRule {
                    state: "qt".into(),
                    symbol: "not".into(),
                    successors: vec!["qf".into()],
                },
                // qf(not(x)) → not(qt(x))
                NftaRule {
                    state: "qf".into(),
                    symbol: "not".into(),
                    successors: vec!["qt".into()],
                },
                // qf(or(x₁,x₂)) → or(qf(x₁), qf(x₂))
                NftaRule {
                    state: "qf".into(),
                    symbol: "or".into(),
                    successors: vec!["qf".into(), "qf".into()],
                },
            ],
            // No variable-leaf states (all leaves are ground constants).
            leaf_states: vec![],
            // Ground-constant acceptance:
            //   qt accepts constant 1 (true value in true context)
            //   qf accepts constant 0 (false value in false context)
            terminal_pairs: vec![
                ("qt".into(), "1".into()),
                ("qf".into(), "0".into()),
            ],
        }
    }

    /// Build `or(not(1), 1)`:
    ///
    /// ```text
    ///      or
    ///     /  \
    ///   not   1
    ///    |
    ///    1
    /// ```
    ///
    /// Evaluation: `not(1) = 0`, `or(0, 1) = 1` → TRUE.
    fn tree_or_not1_1() -> Tree {
        Tree::Node(
            "or".into(),
            vec![
                Tree::Node("not".into(), vec![Tree::Node("1".into(), vec![])]),
                Tree::Node("1".into(), vec![]),
            ],
        )
    }

    /// Build `or(not(1), 0)`:
    ///
    /// ```text
    ///      or
    ///     /  \
    ///   not   0
    ///    |
    ///    1
    /// ```
    ///
    /// Evaluation: `not(1) = 0`, `or(0, 0) = 0` → FALSE.
    fn tree_or_not1_0() -> Tree {
        Tree::Node(
            "or".into(),
            vec![
                Tree::Node("not".into(), vec![Tree::Node("1".into(), vec![])]),
                Tree::Node("0".into(), vec![]),
            ],
        )
    }

    // ── Structural tests ─────────────────────────────────────────────────────

    /// Tree encoding: leaf becomes variable, node becomes application.
    #[test]
    fn tree_encoding_leaf() {
        let leaf = Tree::Leaf("x".into());
        let enc = leaf.encode();
        assert!(enc.is_var(), "leaf should encode to a variable");
    }

    #[test]
    fn tree_encoding_node() {
        let t = Tree::Node("f".into(), vec![Tree::Leaf("x".into()), Tree::Leaf("y".into())]);
        let enc = t.encode();
        assert_eq!(enc.head(), Some("f".to_string()), "node should encode to application f(…)");
        assert_eq!(enc.args().len(), 2);
    }

    #[test]
    fn tree_encoding_constant() {
        // Arity-0 node encodes as constant application.
        let t = Tree::Node("1".into(), vec![]);
        let enc = t.encode();
        assert_eq!(enc.head(), Some("1".to_string()));
        assert_eq!(enc.args().len(), 0);
        assert!(!enc.is_var(), "constant node should not be a variable");
    }

    /// Machine constellation structure check.
    #[test]
    fn nfta_machine_constellation_structure() {
        let nfta = bool_formula_nfta();
        let t_star = nfta.machine_constellation();
        // 1 initial + rule stars + terminal stars
        let n_initial = nfta.initial.len();   // 1
        let n_rule: usize = nfta.rules.iter().map(|r| r.successors.len()).sum();
        // rule 0: qt/or → 2 children → 2 stars
        // rule 1: qt/or → 2 children → 2 stars
        // rule 2: qt/not → 1 child → 1 star
        // rule 3: qf/not → 1 child → 1 star
        // rule 4: qf/or → 2 children → 2 stars
        // total = 8
        let n_leaf = nfta.leaf_states.len();  // 0
        let n_term = nfta.terminal_pairs.len(); // 2
        let expected = n_initial + n_rule + n_leaf + n_term;
        assert_eq!(
            t_star.len(), expected,
            "machine constellation should have {} stars; got {}",
            expected, t_star.len()
        );
    }

    // ── Acceptance tests (§57.11 criterion via IEx fast path) ────────────────

    /// `or(not(1), 1)` evaluates to TRUE → NFTA accepts.
    ///
    /// IEx fast path; should complete in well under 10s.
    #[test]
    fn nfta_accepts_true_formula() {
        let nfta = bool_formula_nfta();
        let tree = tree_or_not1_1();
        assert!(
            nfta.accepts(&tree),
            "NFTA should accept or(not(1), 1) — evaluates to true"
        );
    }

    /// `or(not(1), 0)` evaluates to FALSE → NFTA rejects.
    #[test]
    fn nfta_rejects_false_formula() {
        let nfta = bool_formula_nfta();
        let tree = tree_or_not1_0();
        assert!(
            !nfta.accepts(&tree),
            "NFTA should reject or(not(1), 0) — evaluates to false"
        );
    }

    /// Structural: a single constant `1` is accepted (qt accepts 1 directly).
    #[test]
    fn nfta_accepts_constant_true() {
        let nfta = bool_formula_nfta();
        let tree = Tree::Node("1".into(), vec![]);
        assert!(
            nfta.accepts(&tree),
            "NFTA should accept the constant tree `1`"
        );
    }

    /// Structural: a single constant `0` is rejected (initial state is qt, qt rejects 0).
    #[test]
    fn nfta_rejects_constant_false() {
        let nfta = bool_formula_nfta();
        let tree = Tree::Node("0".into(), vec![]);
        assert!(
            !nfta.accepts(&tree),
            "NFTA should reject the constant tree `0` (root must be in qt)"
        );
    }

    /// Structural: `not(0)` evaluates to TRUE → accepted.
    #[test]
    fn nfta_accepts_not_false() {
        let nfta = bool_formula_nfta();
        let tree = Tree::Node("not".into(), vec![Tree::Node("0".into(), vec![])]);
        assert!(
            nfta.accepts(&tree),
            "NFTA should accept not(0) — evaluates to true"
        );
    }
}
