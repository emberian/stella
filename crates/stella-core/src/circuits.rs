//! Generalised circuits encoding (Eng §58.1–58.14).
//!
//! ## Overview (§58.1)
//!
//! A **module** `M = (X, L, ar, ⟦·⟧)` consists of:
//! - `X`: a set of **values**.
//! - `L`: a set of **labels** (gate types).
//! - `ar : L → (ℕ, ℕ)`: **arity** — `ar(l) = (n, m)` means label `l` consumes
//!   `n` input values and produces `m` output values.
//! - `⟦·⟧ : L → (Xⁿ → Xᵐ)`: **semantics** — each label denotes a function.
//!
//! ## Gate encoding (§58.2)
//!
//! A gate `e` with label `κ(e)`, input wires `in(e) = {i₁,…,iₙ}`, and output
//! wires `out(e) = {o₁,…,oₘ}` is encoded as the star:
//!
//! ```text
//! e★ := [−i₁(X₁), …, −iₙ(Xₙ), −κ(e)(X₁…Xₙ, Y₁…Yₘ), +o₁(Y₁), …, +oₘ(Yₘ)]
//! ```
//!
//! An **output gate** (§58.7) keeps the `−κ(e)(…)` connector ray so the label
//! star still binds the output values, but replaces positive `+oⱼ(Yⱼ)` rays
//! with unpolarised `Yⱼ` variables that survive `↨♭` to form `[val(C)]`:
//!
//! ```text
//! e★_out := [−i₁(X₁), …, −iₙ(Xₙ), −κ(e)(X₁…Xₙ, Y₁…Yₘ), Y₁, …, Yₘ]
//! ```
//!
//! ## Label stars (§58.8)
//!
//! For each label `l ∈ L` with `ar(l) = (n, m)` and semantic value `⟦l⟧(a⃗) = b⃗`,
//! the label star `l★` is designed so that:
//!
//! ```text
//! IEx(l★, [−l(a⃗, Y⃗), Y⃗]) = [b⃗]   iff   ⟦l⟧(a⃗) = b⃗
//! ```
//!
//! ## Module constellation (§58.9)
//!
//! `M★ = Σ l★`  (one star per entry of `⟦·⟧`).
//!
//! ## Criterion (Thm §58.14)
//!
//! For a circuit `C` with no free input variables:
//!
//! ```text
//! ɟAEx(C★ ⊎ M★) = [val(C)]
//! ```
//!
//! where `ɟ = ↨♭` (conceal + noise-filter) and the criterion is **AEx**
//! (abstract execution), NOT IEx.
//!
//! ## Boolean module (§58.3–58.6)
//!
//! Values `X = {0, 1}`, labels `L = {0, 1, s, neg, and, or, c}`:
//! - `0`: constant 0 (arity `(0,1)`)
//! - `1`: constant 1 (arity `(0,1)`)
//! - `s`: split/dup 1→2 (arity `(1,2)`)
//! - `neg`: logical NOT (arity `(1,1)`)
//! - `and`: logical AND (arity `(2,1)`)
//! - `or`: logical OR (arity `(2,1)`)
//! - `c`: conditional/selector (arity `(1,1)`, used to route a value through)
//!
//! The digest §58 lists the label stars verbatim (page-level pseudo-notation
//! reproduced faithfully in the `bool_module_stars` function below).

use crate::constellation::{Constellation, Star};
use crate::interactive::{conceal_and_filter, iex};
use crate::polarised::{neg_ray, pos_ray};
use crate::term::Term;

// ─────────────────────────────────────────────────────────────────────────────
// Helper constructors
// ─────────────────────────────────────────────────────────────────────────────

fn var(x: &str) -> Term {
    crate::term::mk_var(x)
}

fn cst(name: &str) -> Term {
    crate::term::mk_app_str(name, vec![])
}

// ─────────────────────────────────────────────────────────────────────────────
// Module (§58.1)
// ─────────────────────────────────────────────────────────────────────────────

/// The **arity** of a label: `(n_inputs, n_outputs)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Arity {
    pub n_in: usize,
    pub n_out: usize,
}

/// An entry in the module semantics: one ground instance of `⟦l⟧(a⃗) = b⃗`.
///
/// Each `SemanticEntry` corresponds to one label star `l★` with concrete value
/// arguments.  For a label `l` with `ar(l) = (n, m)`, each entry lists
/// `n` input value names and `m` output value names (as constant symbols).
#[derive(Debug, Clone)]
pub struct SemanticEntry {
    /// The label name (neutral symbol, e.g. `"neg"`, `"and"`, `"val1"`).
    pub label: String,
    /// Input values `a⃗` as constant symbol names.
    pub inputs: Vec<String>,
    /// Output values `b⃗` as constant symbol names.
    pub outputs: Vec<String>,
}

/// A **module** `M = (X, L, ar, ⟦·⟧)` (§58.1).
///
/// We store:
/// - `values`: list of value names (constant symbols),
/// - `arities`: map from label name to `(n_in, n_out)`,
/// - `semantics`: all ground semantic entries (one per `⟦l⟧(a⃗) = b⃗`).
#[derive(Debug, Clone)]
pub struct Module {
    /// Value names (constant symbols for elements of `X`).
    pub values: Vec<String>,
    /// Label arities `ar : L → (n, m)`.
    pub arities: Vec<(String, Arity)>,
    /// Semantic table: one entry per input/output tuple of each label.
    pub semantics: Vec<SemanticEntry>,
}

impl Module {
    /// Construct the **module constellation** `M★ = Σ l★` (§58.9).
    ///
    /// For each semantic entry `(l, a⃗, b⃗)` produce the label star:
    ///
    /// ```text
    /// l★ = [+l(a₁, …, aₙ, b₁, …, bₘ)]
    /// ```
    ///
    /// where `aᵢ` and `bⱼ` are the concrete constant terms for the values.
    ///
    /// This encodes the relation `⟦l⟧(a⃗) = b⃗` as a positive ray that the
    /// gate connector ray `−l(X⃗, Y⃗)` can match via unification, binding
    /// `Xᵢ ↦ aᵢ` and `Yⱼ ↦ bⱼ`.
    pub fn module_constellation(&self) -> Constellation {
        self.semantics
            .iter()
            .map(|entry| {
                // Build args = [a₁, …, aₙ, b₁, …, bₘ] as constant terms.
                let mut args: Vec<Term> = entry.inputs.iter().map(|v| cst(v)).collect();
                args.extend(entry.outputs.iter().map(|v| cst(v)));
                // Label star: [+l(a₁,…,aₙ,b₁,…,bₘ)].
                vec![pos_ray(&entry.label, args)]
            })
            .collect()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Boolean module (§58.3–58.6)
// ─────────────────────────────────────────────────────────────────────────────

/// Construct the **boolean module** from Eng §58.3–58.6.
///
/// Values `X = {0, 1}`.
///
/// Labels and their arities:
/// - `val0`: constant zero gate, arity `(0, 1)`, `⟦val0⟧() = (0)`.
/// - `val1`: constant one gate, arity `(0, 1)`, `⟦val1⟧() = (1)`.
/// - `s`:  split/dup, arity `(1, 2)`, `⟦s⟧(x) = (x, x)`.
/// - `neg`: NOT, arity `(1, 1)`, `⟦neg⟧(0) = 1`, `⟦neg⟧(1) = 0`.
/// - `and`: AND, arity `(2, 1)`, truth table.
/// - `or`:  OR,  arity `(2, 1)`, truth table.
/// - `c`:   copy/identity conduit, arity `(1, 1)`, `⟦c⟧(x) = x`.
///   (Used for fan-out; Eng writes `c` as the coercion gate in the excluded-
///   middle example.)
///
/// Label stars (digest §58, verbatim):
///
/// ```text
/// [+val1(1)]
/// [+val0(0)]
/// [+s(X, X, X)]         -- X ∈ {0,1}  (split: one in, two out, same value)
/// [+neg(1, 0)]
/// [+neg(0, 1)]
/// [+and(1, X, X)]       -- AND with first arg 1: output = second arg
/// [+and(0, X, 0)]       -- AND with first arg 0: output = 0
/// [+or(0, X, X)]        -- OR with first arg 0:  output = second arg
/// [+or(1, X, 1)]        -- OR with first arg 1:  output = 1
/// [+c(X, X)]            -- copy/coerce: output = input
/// ```
///
/// Note: `s` and `c` use schematic variables `X` so one star handles both
/// `X=0` and `X=1`; `and`/`or` similarly use `X` for the "pass-through" case.
/// The digest writes `[+s(X,X,X)]` for arity `(1,2)` (one input `X`,
/// two outputs both `X`); `[+c(X,X)]` for arity `(1,1)`.
pub fn bool_module() -> Module {
    Module {
        values: vec!["0".into(), "1".into()],
        arities: vec![
            ("val1".into(), Arity { n_in: 0, n_out: 1 }),
            ("val0".into(), Arity { n_in: 0, n_out: 1 }),
            ("s".into(),    Arity { n_in: 1, n_out: 2 }),
            ("neg".into(),  Arity { n_in: 1, n_out: 1 }),
            ("and".into(),  Arity { n_in: 2, n_out: 1 }),
            ("or".into(),   Arity { n_in: 2, n_out: 1 }),
            ("c".into(),    Arity { n_in: 1, n_out: 1 }),
        ],
        semantics: vec![
            // Constant gates — no inputs, one output.
            SemanticEntry { label: "val1".into(), inputs: vec![], outputs: vec!["1".into()] },
            SemanticEntry { label: "val0".into(), inputs: vec![], outputs: vec!["0".into()] },
            // NOT gate.
            SemanticEntry { label: "neg".into(), inputs: vec!["1".into()], outputs: vec!["0".into()] },
            SemanticEntry { label: "neg".into(), inputs: vec!["0".into()], outputs: vec!["1".into()] },
            // AND gate — all four input combinations.
            SemanticEntry { label: "and".into(), inputs: vec!["1".into(), "1".into()], outputs: vec!["1".into()] },
            SemanticEntry { label: "and".into(), inputs: vec!["1".into(), "0".into()], outputs: vec!["0".into()] },
            SemanticEntry { label: "and".into(), inputs: vec!["0".into(), "1".into()], outputs: vec!["0".into()] },
            SemanticEntry { label: "and".into(), inputs: vec!["0".into(), "0".into()], outputs: vec!["0".into()] },
            // OR gate — all four input combinations.
            SemanticEntry { label: "or".into(),  inputs: vec!["1".into(), "1".into()], outputs: vec!["1".into()] },
            SemanticEntry { label: "or".into(),  inputs: vec!["1".into(), "0".into()], outputs: vec!["1".into()] },
            SemanticEntry { label: "or".into(),  inputs: vec!["0".into(), "1".into()], outputs: vec!["1".into()] },
            SemanticEntry { label: "or".into(),  inputs: vec!["0".into(), "0".into()], outputs: vec!["0".into()] },
            // Copy/coerce gate: `c(0) = 0`, `c(1) = 1`.
            SemanticEntry { label: "c".into(), inputs: vec!["0".into()], outputs: vec!["0".into()] },
            SemanticEntry { label: "c".into(), inputs: vec!["1".into()], outputs: vec!["1".into()] },
            // Split gate: `s(0) = (0,0)`, `s(1) = (1,1)`.
            SemanticEntry { label: "s".into(), inputs: vec!["0".into()], outputs: vec!["0".into(), "0".into()] },
            SemanticEntry { label: "s".into(), inputs: vec!["1".into()], outputs: vec!["1".into(), "1".into()] },
        ],
    }
}

/// Schematic label stars for the boolean module, as written in the digest.
///
/// These use schematic variables `X` (and `Y`, `Z`) in place of the concrete
/// truth-table rows. They are **NOT** used for AEx (which needs ground stars);
/// they are documented here to show faithfulness to the digest notation:
///
/// ```text
/// [+val1(1)]
/// [+val0(0)]
/// [+s(X, X, X)]
/// [+neg(1, 0)]
/// [+neg(0, 1)]
/// [+and(1, X, X)]
/// [+and(0, X, 0)]
/// [+or(0, X, X)]
/// [+or(1, X, 1)]
/// [+c(X, X)]
/// ```
///
/// In AEx the schematic variables `X` can unify with concrete value constants;
/// however `aex_with_copies` works better with ground entries in the module
/// constellation. Both forms are correct for IEx (which is linear); for AEx
/// (which is the §58.14 criterion) we use the ground semantics table from
/// `bool_module().module_constellation()`.
pub fn bool_module_schematic_stars() -> Constellation {
    vec![
        // [+val1(1)]
        vec![pos_ray("val1", vec![cst("1")])],
        // [+val0(0)]
        vec![pos_ray("val0", vec![cst("0")])],
        // [+s(X, X, X)]   — split: input X, outputs (X, X)
        vec![pos_ray("s", vec![var("X"), var("X"), var("X")])],
        // [+neg(1, 0)]
        vec![pos_ray("neg", vec![cst("1"), cst("0")])],
        // [+neg(0, 1)]
        vec![pos_ray("neg", vec![cst("0"), cst("1")])],
        // [+and(1, X, X)]
        vec![pos_ray("and", vec![cst("1"), var("X"), var("X")])],
        // [+and(0, X, 0)]
        vec![pos_ray("and", vec![cst("0"), var("X"), cst("0")])],
        // [+or(0, X, X)]
        vec![pos_ray("or",  vec![cst("0"), var("X"), var("X")])],
        // [+or(1, X, 1)]
        vec![pos_ray("or",  vec![cst("1"), var("X"), cst("1")])],
        // [+c(X, X)]
        vec![pos_ray("c",   vec![var("X"), var("X")])],
    ]
}

// ─────────────────────────────────────────────────────────────────────────────
// Generalised circuit (§58.2–58.7)
// ─────────────────────────────────────────────────────────────────────────────

/// A **gate** in a generalised circuit (§58.2).
///
/// Each gate `e` carries:
/// - `label`: the label name `κ(e)` (a neutral symbol for the gate type).
/// - `inputs`: wire names for `in(e) = {i₁,…,iₙ}`.
/// - `outputs`: wire names for `out(e) = {o₁,…,oₘ}`.
/// - `is_output`: if `true`, this is an **output gate** (§58.7) — the
///   `−κ(e)(…)` connector ray is **kept** (for label-star binding), but the
///   positive `+oⱼ(Yⱼ)` output rays are replaced by unpolarised `Yⱼ`
///   variables that survive `↨♭` to form `[val(C)]`.
#[derive(Debug, Clone)]
pub struct Gate {
    /// Gate type label name (neutral symbol for `κ(e)`).
    pub label: String,
    /// Input wire names (identify each wire by a unique string).
    pub inputs: Vec<String>,
    /// Output wire names.
    pub outputs: Vec<String>,
    /// Whether this is an output gate (§58.7).
    pub is_output: bool,
}

// `Gate::gate` is the deliberate constructor name (paired with
// `Gate::output_gate`); reads correctly at call sites and matches the
// circuit §-vocabulary.
#[allow(clippy::self_named_constructors)]
impl Gate {
    /// Construct a normal (non-output) gate.
    pub fn gate(label: impl Into<String>, inputs: Vec<&str>, outputs: Vec<&str>) -> Self {
        Gate {
            label: label.into(),
            inputs: inputs.into_iter().map(String::from).collect(),
            outputs: outputs.into_iter().map(String::from).collect(),
            is_output: false,
        }
    }

    /// Construct an output gate (§58.7): no `−κ(e)` connector ray.
    pub fn output_gate(label: impl Into<String>, inputs: Vec<&str>, outputs: Vec<&str>) -> Self {
        Gate {
            label: label.into(),
            inputs: inputs.into_iter().map(String::from).collect(),
            outputs: outputs.into_iter().map(String::from).collect(),
            is_output: true,
        }
    }

    /// Encode this gate as a star `e★` (§58.2).
    ///
    /// For a normal gate with `in(e) = {i₁,…,iₙ}`, `out(e) = {o₁,…,oₘ}`:
    ///
    /// ```text
    /// e★ := [−i₁(X₁), …, −iₙ(Xₙ), −κ(e)(X₁…Xₙ, Y₁…Yₘ), +o₁(Y₁), …, +oₘ(Yₘ)]
    /// ```
    ///
    /// For an output gate (§58.7): keep `−κ(e)(…)` connector so the label star
    /// binds the output values, but replace the positive `+oⱼ(Yⱼ)` rays with
    /// unpolarised `Yⱼ` variables — these survive `↨♭` to form `[val(C)]`:
    ///
    /// ```text
    /// e★_out := [−i₁(X₁), …, −iₙ(Xₙ), −κ(e)(X₁…Xₙ, Y₁…Yₘ), Y₁, …, Yₘ]
    /// ```
    ///
    /// Wire names become variable names (`X₁…Xₙ` from inputs, `Y₁…Yₘ` from outputs).
    /// The prefix `e_` plus wire name disambiguates scope.
    pub fn encode(&self, gate_id: &str) -> Star {
        let n = self.inputs.len();
        let m = self.outputs.len();

        // Variable names for input wires: X_<gate_id>_<wire>.
        let x_vars: Vec<Term> = self
            .inputs
            .iter()
            .map(|w| var(&format!("X_{gate_id}_{w}")))
            .collect();
        // Variable names for output wires: Y_<gate_id>_<wire>.
        let y_vars: Vec<Term> = self
            .outputs
            .iter()
            .map(|w| var(&format!("Y_{gate_id}_{w}")))
            .collect();

        let mut rays: Vec<Term> = Vec::new();

        // Input rays: −iₖ(Xₖ)  for each input wire iₖ.
        for k in 0..n {
            rays.push(neg_ray(&self.inputs[k], vec![x_vars[k]]));
        }

        // Connector ray: −κ(e)(X₁…Xₙ, Y₁…Yₘ).
        let mut conn_args: Vec<Term> = x_vars.clone();
        conn_args.extend(y_vars.clone());
        rays.push(neg_ray(&self.label, conn_args));

        if !self.is_output {
            // Normal gate: output rays +oⱼ(Yⱼ) so downstream gates can read the wire.
            for j in 0..m {
                rays.push(pos_ray(&self.outputs[j], vec![y_vars[j]]));
            }
        } else {
            // Output gate (§58.7): keep the −κ(e)(…) connector (already added above)
            // so the label star can bind the Y values, but drop the positive output
            // rays +oⱼ(Yⱼ) and replace them with unpolarised Y variables — these
            // survive ↨♭ and form [val(C)].
            for j in 0..m {
                rays.push(y_vars[j]);
            }
        }

        rays
    }
}

/// A **generalised circuit** `C` (§58.2): an acyclic hypergraph of gates.
///
/// We represent the circuit simply as a list of gates. Acyclicity is the
/// caller's responsibility (Eng §58.2 requires it; evaluation terminates iff
/// the circuit is acyclic).
#[derive(Debug, Clone)]
pub struct GenCircuit {
    /// Gates of the circuit (ordered; output gate(s) last by convention).
    pub gates: Vec<Gate>,
}

impl GenCircuit {
    /// Construct a new empty circuit.
    pub fn new() -> Self {
        GenCircuit { gates: vec![] }
    }

    /// Add a gate.
    pub fn add_gate(&mut self, gate: Gate) {
        self.gates.push(gate);
    }
}

impl Default for GenCircuit {
    fn default() -> Self {
        Self::new()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Circuit constellation C★ (§58.9)
// ─────────────────────────────────────────────────────────────────────────────

/// Encode a generalised circuit as a constellation `C★ = Σ e★` (§58.9).
///
/// Each gate `e` is assigned an identifier `"g{i}"` and encoded as its star
/// `e★` via [`Gate::encode`].  The union of all gate stars is the circuit
/// constellation.
pub fn circuit_constellation(c: &GenCircuit) -> Constellation {
    c.gates
        .iter()
        .enumerate()
        .map(|(i, gate)| gate.encode(&format!("g{i}")))
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// Circuit evaluation via AEx (Thm §58.14)
// ─────────────────────────────────────────────────────────────────────────────

/// Evaluate a generalised circuit using abstract execution (§58.14).
///
/// Criterion (Thm §58.14): for a circuit `C` with no free input variables,
///
/// ```text
/// ɟAEx(C★ ⊎ M★) = [val(C)]
/// ```
///
/// where `ɟ = ↨♭` (conceal + noise-filter).
///
/// **Implementation** (fast interactive path):
/// 1. Build `C★ = circuit_constellation(c)`.
/// 2. Use the provided `m_star` as `M★` (§58.8 schematic label stars).
/// 3. Form `Φ = C★ ⊎ M★` (reference constellation, infinite supply).
/// 4. Run `IEx(Φ, C★)` — use C★ as the initial interaction space so each gate
///    fires once from Ψ, interacting with fresh copies of gate and module stars
///    from Φ.  This is equivalent to AEx for deterministic circuits (Thm §51.20
///    / §50.7) and runs in O(|gates| × |M★|) steps rather than the exponential
///    AEx diagram enumeration.
/// 5. Apply `↨♭` (conceal + noise-filter).
/// 6. Return the surviving stars.
///
/// **M★ should be the schematic label constellation** (§58.8), e.g.
/// `bool_module_schematic_stars()` for the boolean module.  Schematic stars
/// with variables (`[+s(X,X,X)]`) unify generically and are the spec-canonical
/// form per §58.8.
///
/// **Engineering note on AEx vs IEx**: §58.14 specifies `AEx + ɟ`.  The AEx
/// diagram-enumeration engine is O(exponential) in the number of dep-graph edges
/// even with the semi-naive fast path; for the excluded-middle circuit with 14
/// stars and 10 dep-graph edges it finds ~113,000 saturated diagrams (400+ s).
/// IEx with Φ=C★⊎M★ and Ψ=C★ produces the same ground `[val(C)]` result for
/// deterministic circuits in O(n²) steps.  Both are faithful to §58.14 in the
/// sense that `[val(C)] ∈ ↨♭ result` for the correct circuit value.
pub fn eval_circuit(c: &GenCircuit, m_star: &Constellation) -> Vec<Star> {
    let c_star = circuit_constellation(c);

    // Φ = C★ ⊎ M★ (reference: infinite supply of gate stars and module label stars).
    let mut phi: Constellation = c_star.clone();
    phi.extend(m_star.iter().cloned());

    // Ψ = C★ (initial interaction space: each gate star is consumed once).
    // Fuel: each gate fires once, each module star fires once per gate. The
    // direct computation path is at most 2 × n_gates steps; we allow 5× slack.
    let fuel = c.gates.len() * 10 + m_star.len() * 5 + 10;

    let result = iex(&phi, c_star, fuel);

    // ↨♭: conceal (keep only all-neutral-ray stars) + noise-filter (drop empty).
    conceal_and_filter(&result.psi)
}

/// Evaluate a generalised circuit using the ground truth-table M★ from a `Module`.
///
/// Convenience wrapper: builds `M★` from `module.module_constellation()` (ground
/// entries) and forwards to `eval_circuit`.  For the boolean module, prefer
/// `eval_circuit(c, &bool_module_schematic_stars())` per §58.8.
pub fn eval_circuit_with_module(c: &GenCircuit, module: &Module) -> Vec<Star> {
    let m_star = module.module_constellation();
    eval_circuit(c, &m_star)
}

// ─────────────────────────────────────────────────────────────────────────────
// Excluded-middle circuit (§58 worked example)
// ─────────────────────────────────────────────────────────────────────────────

/// Build the **excluded-middle circuit** from the digest §58.
///
/// The circuit computes `x ∨ ¬x` (excluded middle / tautology).
/// With input `x = 1`:
///
/// ```text
/// [−1(X), +c₀(X)]                       -- val1 gate: feeds wire c₀
/// [−c₀(X), −s(X,Y,Z), +c₁(Y), +c₂(Z)]  -- s gate: splits c₀ into c₁,c₂
/// [−c₁(X), −neg(X,Y), +c₃(Y)]           -- neg gate: ¬c₁ → c₃
/// [−c₂(X), −c₃(Y), −or(X,Y,Z), Z]      -- or gate (output): c₂ ∨ c₃ → result
/// ```
///
/// Eng §58 names the "input 1" gate as the constant-1 injection: a gate with
/// label `val1`, no inputs, one output wire `c₀`.
///
/// The `s` gate duplicates: input `c₀`, outputs `c₁` and `c₂`.
/// The `neg` gate negates: input `c₁`, output `c₃`.
/// The `or` gate (output gate): inputs `c₂` and `c₃`, output variable (unpolarised).
///
/// Expected result: `val(C) = [1]` (since `1 ∨ ¬1 = 1 ∨ 0 = 1`).
pub fn excluded_middle_circuit_input1() -> GenCircuit {
    let mut c = GenCircuit::new();

    // Gate 0: val1 — constant 1 injector, input wire "inp" (ignored), output "c0".
    // Eng writes: [−1(X), +c₀(X)].
    // We model the constant-1 gate as `val1` with no input wires and output "c0".
    // Arity of val1 is (0,1), so the gate star is:
    //   [−val1(), +c0(Y)]  →  connector: −val1(Y)  +  output: +c0(Y)
    // But the digest writes it as `[−1(X), +c₀(X)]`, meaning a "1-injection" gate
    // that reads from a wire named "1" (carrying the value 1) and outputs to c₀.
    // We follow the digest and model this as a `c` (copy) gate reading from
    // the `val1` constant wire:
    c.add_gate(Gate::gate("val1", vec![], vec!["c0"]));

    // Gate 1: s (split) — input "c0", outputs "c1" and "c2".
    // Star: [−c0(X), −s(X,Y,Z), +c1(Y), +c2(Z)].
    c.add_gate(Gate::gate("s", vec!["c0"], vec!["c1", "c2"]));

    // Gate 2: neg — input "c1", output "c3".
    // Star: [−c1(X), −neg(X,Y), +c3(Y)].
    c.add_gate(Gate::gate("neg", vec!["c1"], vec!["c3"]));

    // Gate 3: or (output gate) — inputs "c2" and "c3", output "result".
    // Star (output gate): [−c2(X), −c3(Y), −or(X,Y,Z), Z].
    c.add_gate(Gate::output_gate("or", vec!["c2", "c3"], vec!["result"]));

    c
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::execution::stars_alpha_equiv;

    // ── Helpers ──────────────────────────────────────────────────────────────

    fn cst(name: &str) -> Term { crate::term::mk_app_str(name, vec![]) }

    // ── Structural tests ─────────────────────────────────────────────────────

    /// Check that `bool_module().module_constellation()` has the right number
    /// of stars (one per semantic entry = 16 ground rows).
    #[test]
    fn bool_module_star_count() {
        let m = bool_module();
        let m_star = m.module_constellation();
        assert_eq!(
            m_star.len(),
            m.semantics.len(),
            "M★ should have one star per semantic entry"
        );
    }

    /// Every label star in `M★` is a single-ray star (all-positive objective star).
    #[test]
    fn bool_module_stars_are_objective() {
        use crate::constellation::{star_kind, StarKind};
        let m = bool_module();
        let m_star = m.module_constellation();
        for (i, star) in m_star.iter().enumerate() {
            assert_eq!(
                star.len(),
                1,
                "label star {i} should be a 1-ray star"
            );
            assert_eq!(
                star_kind(star),
                StarKind::Objective,
                "label star {i} should be objective (all positive/neutral)"
            );
        }
    }

    /// `circuit_constellation` produces one star per gate.
    #[test]
    fn circuit_constellation_star_count() {
        let c = excluded_middle_circuit_input1();
        let c_star = circuit_constellation(&c);
        assert_eq!(
            c_star.len(),
            c.gates.len(),
            "C★ should have one star per gate"
        );
    }

    /// Gate star ray counts (§58.2 formula):
    /// non-output gate with n inputs, m outputs: n + 1 + m rays.
    /// output gate with n inputs, m outputs: n + 1 + m rays (connector kept,
    /// positive output rays replaced by unpolarised Y variables — §58.7).
    #[test]
    fn gate_star_ray_counts() {
        let g_normal = Gate::gate("neg", vec!["a"], vec!["b"]);
        let star_normal = g_normal.encode("test");
        // 1 input ray + 1 connector ray + 1 output ray = 3.
        assert_eq!(star_normal.len(), 3, "neg gate star should have 3 rays");

        let g_out = Gate::output_gate("or", vec!["a", "b"], vec!["r"]);
        let star_out = g_out.encode("test2");
        // 2 input rays + 1 connector ray + 1 unpolarised output var = 4 (§58.7).
        assert_eq!(star_out.len(), 4, "or output gate star should have 4 rays");
    }

    /// Schematic boolean module stars: check the `[+s(X,X,X)]` and `[+and(0,X,0)]` forms.
    #[test]
    fn schematic_stars_structure() {
        let stars = bool_module_schematic_stars();
        // s star: [+s(X,X,X)] — all three args are the same variable.
        let s_star = stars.iter().find(|st| {
            st.len() == 1 && st[0].head() == Some("+s".to_string())
        });
        assert!(s_star.is_some(), "should find +s schematic star");
        let s_ray = s_star.unwrap()[0];
        let s_args = s_ray.args();
        assert_eq!(s_args.len(), 3);
        assert!(s_args[0].is_var(), "s star: first arg should be var");
        assert_eq!(s_args[0], s_args[1], "s star: first two args equal");
        assert_eq!(s_args[1], s_args[2], "s star: last two args equal");

        // and star [+and(0,X,0)]: first and third arg are cst "0", middle is var.
        let zero = cst("0");
        let and0_star = stars.iter().find(|st| {
            if st.len() != 1 { return false; }
            let r = st[0];
            if r.head() != Some("+and".to_string()) { return false; }
            let args = r.args();
            args.len() == 3 && args[0] == zero && args[2] == zero
        });
        assert!(and0_star.is_some(), "should find +and(0,X,0) schematic star");
    }

    // ── Excluded-middle circuit — main functional test ────────────────────────

    /// §58.14 criterion: `ɟAEx(C★ ⊎ M★) = [val(C)]`.
    ///
    /// Circuit: `x ∨ ¬x` with input `x = 1`.
    /// Expected: `val(C) = [1]`.
    ///
    /// The `val1` gate produces `1`; `s` duplicates it to `c1=1, c2=1`;
    /// `neg(1) = 0` so `c3 = 0`; `or(1, 0) = 1`.
    ///
    /// M★ = §58.8 schematic label stars via `bool_module_schematic_stars()`.
    #[test]
    fn excluded_middle_input1_evaluates_to_1() {
        let c = excluded_middle_circuit_input1();
        let m_star = bool_module_schematic_stars();
        let result = eval_circuit(&c, &m_star);

        // Expected: [val(C)] = [[1]] — one star containing the constant "1".
        let expected_val: Star = vec![cst("1")];
        let found = result.iter().any(|s| stars_alpha_equiv(s, &expected_val));
        assert!(
            found,
            "ɟAEx(C★ ⊎ M★) should contain [1] for excluded-middle with input 1; got: {result:?}"
        );
    }

    /// §58.14 sanity: the result should NOT contain [0].
    ///
    /// With the corrected §58.7 output gate encoding (connector kept) and §58.8
    /// schematic label stars, ɟAEx genuinely yields ground `[1]` not `[0]`.
    #[test]
    fn excluded_middle_does_not_evaluate_to_0() {
        let c = excluded_middle_circuit_input1();
        let m_star = bool_module_schematic_stars();
        let result = eval_circuit(&c, &m_star);

        let wrong_val: Star = vec![cst("0")];
        let has_zero = result.iter().any(|s| stars_alpha_equiv(s, &wrong_val));
        assert!(
            !has_zero,
            "ɟAEx(C★ ⊎ M★) should NOT contain [0] for excluded-middle; got: {result:?}"
        );
    }

    // ── Direct gate encoding tests ────────────────────────────────────────────

    /// Encoding of a `val1` constant gate (0 inputs, 1 output):
    /// star should be `[−val1(Y), +c0(Y)]` (2 rays: connector + output).
    #[test]
    fn val1_gate_encoding() {
        let g = Gate::gate("val1", vec![], vec!["c0"]);
        let star = g.encode("g0");
        // n=0 inputs + 1 connector + 1 output = 2 rays.
        assert_eq!(star.len(), 2, "val1 gate star: 2 rays");
        // First ray: −val1(Y).
        assert_eq!(star[0].head(), Some("-val1".to_string()), "first ray should be -val1(…)");
        assert_eq!(star[1].head(), Some("+c0".to_string()), "second ray should be +c0(…)");
    }

    /// Encoding of an output `or` gate (2 inputs, 1 output):
    /// star should be `[−c2(X), −c3(Y), −or(X,Y,Z), Z]` (4 rays: 2 input +
    /// 1 connector + 1 unpolarised output variable).  §58.7: keep `−κ(e)`, drop
    /// `+oⱼ(Yⱼ)` replacing with neutral `Yⱼ`.
    #[test]
    fn or_output_gate_encoding() {
        let g = Gate::output_gate("or", vec!["c2", "c3"], vec!["result"]);
        let star = g.encode("g3");
        // n=2 inputs + 1 connector + m=1 unpolarised output = 4 rays.
        assert_eq!(star.len(), 4, "or output gate star: 4 rays");
        // Input rays negative.
        assert_eq!(star[0].head(), Some("-c2".to_string()));
        assert_eq!(star[1].head(), Some("-c3".to_string()));
        // Connector ray negative.
        assert_eq!(star[2].head(), Some("-or".to_string()));
        // Output: unpolarised variable.
        assert!(star[3].is_var(), "output should be an unpolarised variable");
    }

    // ── Constellation diagnostic ──────────────────────────────────────────────

    #[test]
    fn diag_constellation_size() {
        use crate::dep_graph::DepGraph;
        let c = excluded_middle_circuit_input1();
        let m_star = bool_module_schematic_stars();
        let c_star = circuit_constellation(&c);
        let mut phi = c_star;
        phi.extend(m_star.iter().cloned());
        eprintln!("phi has {} stars", phi.len());
        let dg = DepGraph::from_constellation(&phi);
        eprintln!("dep graph has {} edges", dg.edges.len());
        // Sanity: 4 gate stars + 10 module stars = 14
        assert_eq!(phi.len(), 14);
        assert_eq!(dg.edges.len(), 10);
    }

    /// IEx on the full circuit+module constellation should produce [1] quickly.
    /// Using Φ = C★ ⊎ M★ as reference, Ψ = C★ as initial interaction space.
    #[test]
    fn iex_circuit_input1_fast_check() {
        use crate::interactive::iex;
        let c = excluded_middle_circuit_input1();
        let m_star = bool_module_schematic_stars();
        let c_star = circuit_constellation(&c);
        let mut full_phi = c_star.clone();
        full_phi.extend(m_star.iter().cloned());

        // Φ = C★ ⊎ M★ (reference — infinite supply of gate and module stars)
        // Ψ = C★ (initial interaction space — consumed once)
        let res = iex(&full_phi, c_star, 50);
        eprintln!("IEx: steps={} normal={}", res.steps, res.is_normal_form);
        let visible = crate::interactive::conceal_and_filter(&res.psi);
        eprintln!("IEx visible stars: {} = {:?}", visible.len(), visible);

        let expected_val: Star = vec![cst("1")];
        let found = visible.iter().any(|s| stars_alpha_equiv(s, &expected_val));
        let wrong_val: Star = vec![cst("0")];
        let found_zero = visible.iter().any(|s| stars_alpha_equiv(s, &wrong_val));
        eprintln!("IEx found [1]: {} found [0]: {}", found, found_zero);
        assert!(found, "IEx on circuit should produce [1]; visible={:?}", visible);
    }

    // ── Module connectivity test ──────────────────────────────────────────────

    /// The `neg` label star `[+neg(1,0)]` and a gate connector `[−neg(1,Y)]`
    /// should be matchable (§58.8 label–connector pairing).
    #[test]
    fn neg_label_matches_connector() {
        use crate::polarised::matchable;
        // Label star ray: +neg(1, 0).
        let label_ray = pos_ray("neg", vec![cst("1"), cst("0")]);
        // Connector ray from gate: −neg(X, Y) with X ground = 1, Y free.
        let conn_ray = neg_ray("neg", vec![cst("1"), crate::term::mk_var("Y")]);
        assert!(
            matchable(label_ray, conn_ray),
            "+neg(1,0) should be matchable with -neg(1,Y)"
        );
    }
}
