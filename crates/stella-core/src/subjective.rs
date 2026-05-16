//! Lazy unbounded non-linear supply streaming executor (Eng §51.13).
//!
//! # L1b: `subjective_stream` — §49.50 new-ray dynamics + §49.52 hyper-execution
//!
//! This module implements **Layer 1b** of the Phase-4 subjective engine plan
//! (`docs/01-subjective-engine-and-valence.md §5`).
//!
//! ## L1b additions over L1a
//!
//! - **§49.50 subjective-ray reduction** (new-ray creation): fusion now uses
//!   PolarisedCompat unification on raw polarised rays (not `underlying_term`
//!   stripping), so `θ = {X' ↦ +g(X)}` rather than `{X' ↦ g(X)}`.  This is the
//!   fix that makes bare-variable rays enter the matchable frontier after
//!   substitution.  Variable rays are *retained* (never dropped); matchability
//!   is *recomputed every step* — so a variable ray bound to a coloured term by a
//!   subjective fusion's substitution enters the frontier automatically (§2.1 (1)).
//!
//! - **Semaphore = emergent** (§2.1 (2)): no locking primitive.  `+g(X)` does not
//!   exist as a surface ray until the `f`-fusion creates it; this is automatic
//!   under the PolarisedCompat unification fix.
//!
//! - **§49.52 iterated/hyper execution** (§2.1 (3)): `AEx^{n+1} = AEx(Ψ' ⊎ AEx^n)`
//!   where `Ψ'` = fresh α-renamed copies of Φ-stars that have at least one ray
//!   matchable with something in `AEx^n`.  One complete round (local normal form
//!   reached, then next round started) = one tick of the agent's **proper time**.
//!
//! - **`Step::round`**: the reafferent-round index (proper-time clock, §01-spec §2.6).
//!   `Step::index` remains the substrate/witness step counter.
//!
//! ## Faithfulness note (§2.1 inference)
//!
//! Adjudicated canonical (2026-05-16).  The one inferred decision: using
//! PolarisedCompat directly on the polarised rays (rather than `underlying_term`
//! stripping + StdCompat) is grounded in Eng §49.50's worked example:
//! `[−f(+g(X))] ⋈ [X, +f(X)]` → `θ = {X ↦ +g(X)}`.  This can only arise from
//! unifying `−f(+g(X)) =? +f(X')` under `−f ⊂ +f` (PolarisedCompat Open rule),
//! giving `+g(X) =? X'` → `X' ↦ +g(X)`.  The `underlying_term` path gives
//! `X' ↦ g(X)` (neutral) which fails the gate.
//!
//! On the *objective* fragment this change is transparent: objective rays have
//! only neutral arguments, so PolarisedCompat and StdCompat-on-underlying-terms
//! produce identical substitutions.  The faithfulness gate tests confirm this.

use std::collections::HashSet;

use crate::ch9::{saturation_profile, ConstellationClass};
use crate::constellation::{star_kind, Constellation, Star, StarKind};
use crate::dep_graph::{all_colours, DepEdge, DepGraph};
use crate::polarised::{matchable, ray_polarity, Polarity, PolarisedCompat};
use crate::subst::Substitution;
use crate::term::{mk_var_interned, Var, Term};
use crate::unify::{unify_with, Equation};

// ─────────────────────────────────────────────────────────────────────────────
// Interaction helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Collect all colours present in `psi` (the current interaction space).
fn psi_colours(psi: &[Star]) -> HashSet<String> {
    all_colours(&psi.to_vec())
}

/// α-rename an entire star, returning the renamed star.
fn alpha_rename_star(star: &Star, prefix: &str, counter: &mut u64) -> Star {
    use rustc_hash::FxHashSet;
    let all_vars: Vec<Var> = star
        .iter()
        .flat_map(|&r| r.vars())
        .collect::<FxHashSet<_>>()
        .into_iter()
        .collect();

    let pairs: Vec<(Var, Term)> = all_vars
        .into_iter()
        .map(|v| {
            let fresh_name = format!("{prefix}_{}{counter}", v.as_str());
            *counter += 1;
            let fresh_var = Var::intern(&fresh_name);
            (v, mk_var_interned(fresh_var))
        })
        .collect();
    let subst = Substitution::from_var_pairs(pairs);
    star.iter().map(|&r| subst.apply(r)).collect()
}

/// Fusion `φ₁ ^{j, j'}∇_α φ₂` (§49.30) using **PolarisedCompat** unification.
///
/// # L1b faithfulness fix
///
/// Previous L1a code stripped polarities via `underlying_term` before unifying.
/// That loses colour: `−f(+g(X)) =? +f(X')` (underlying) gives `g(X) =? X'` →
/// `θ = {X' ↦ g(X)}` (neutral).  Correct Eng §49.50 result requires unifying the
/// polarised rays directly under PolarisedCompat: Open rule fires (`−f ⊂ +f`),
/// yielding `+g(X) =? X'` → `θ = {X' ↦ +g(X)}`.  On objective rays (neutral
/// arguments only), both approaches are identical.
fn fuse_stars(phi1: &Star, j: usize, phi2_renamed: &Star, j_prime: usize) -> Option<Star> {
    let r1 = phi1[j];
    let r2 = phi2_renamed[j_prime];
    let theta = unify_with(vec![Equation::new(r1, r2)], &PolarisedCompat)?;

    let mut result: Star = phi1
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j)
        .map(|(_, &r)| theta.apply(r))
        .collect();

    let rest2: Star = phi2_renamed
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j_prime)
        .map(|(_, &r)| theta.apply(r))
        .collect();

    result.extend(rest2);
    Some(result)
}

/// Self-interaction `^{j,j'}▷ star` (§51.7) using PolarisedCompat.
fn self_interact_star(star: &Star, j: usize, j_prime: usize) -> Option<Star> {
    let r1 = star[j];
    let r2 = star[j_prime];
    let theta = unify_with(vec![Equation::new(r1, r2)], &PolarisedCompat)?;
    let result: Star = star
        .iter()
        .enumerate()
        .filter(|&(idx, _)| idx != j && idx != j_prime)
        .map(|(_, &r)| theta.apply(r))
        .collect();
    Some(result)
}

/// `mat_self(star, j)`: indices `j'` in the same star matchable with `star[j]`.
fn mat_self_local(star: &Star, j: usize) -> Vec<usize> {
    let r = star[j];
    star.iter()
        .enumerate()
        .filter(|&(jk, _)| jk != j)
        .filter(|&(_, &ray)| matchable(r, ray))
        .map(|(jk, _)| jk)
        .collect()
}

/// mat_Φ^C(r) restricted to the colour set C = colours(Φ) ∪ colours(Ψ).
fn mat_phi_full(
    phi: &Constellation,
    r: Term,
    extra_c: &HashSet<String>,
) -> Vec<(usize, usize)> {
    use crate::dep_graph::ray_colours;

    let mut c_set = all_colours(phi);
    c_set.extend(extra_c.iter().cloned());
    let cr = ray_colours(r);

    let mut result = Vec::new();
    for (i, star) in phi.iter().enumerate() {
        for (j, &ray) in star.iter().enumerate() {
            if ray_polarity(ray) == Polarity::Neutral {
                continue;
            }
            let crj = ray_colours(ray);
            if !cr.is_subset(&c_set) || !crj.is_subset(&c_set) {
                continue;
            }
            if matchable(r, ray) {
                result.push((i, j));
            }
        }
    }
    result
}

/// Check whether a ray is "active" (coloured and matchable in current config).
///
/// Variable rays (Polarity::Neutral) are not active unless they have been
/// substituted to a coloured term.  Matchability is recomputed here every step
/// (§2.1 (1): "recomputed every step").
fn ray_is_active(phi: &Constellation, star: &Star, j: usize, c_extra: &HashSet<String>) -> bool {
    let r = star[j];
    if ray_polarity(r) == Polarity::Neutral {
        return false;
    }
    let has_ext = !mat_phi_full(phi, r, c_extra).is_empty();
    let has_self = !mat_self_local(star, j).is_empty();
    has_ext || has_self
}

/// Check normal form: no coloured ray in Ψ has a match in Φ or itself.
fn is_nf(phi: &Constellation, psi: &[Star]) -> bool {
    let c_extra = psi_colours(psi);
    for star in psi.iter() {
        for j in 0..star.len() {
            if ray_is_active(phi, star, j, &c_extra) {
                return false;
            }
        }
    }
    true
}

// ─────────────────────────────────────────────────────────────────────────────
// §49.52 Hyper-execution / reafferent-round tracking
//
// Faithfulness note (adjudicated 2026-05-16):
//
// Eng §49.52 defines `AEx^{n+1} = AEx(Ψ' ⊎ AEx^n)` where
// `Ψ' = Φ-stars matchable with AEx^n`.  When AEx^n is in NF wrt Φ, no coloured
// ray in it matches any coloured ray in Φ, so Ψ' = ∅ and the iteration is at a
// global fixpoint.  For the objective fragment this always happens at round 0.
//
// For the subjective/animist fragment, the round structure is *generational*:
// each round processes the stars BORN in the previous round.  A "generation
// boundary" occurs when all stars alive at the START of the current round have
// been consumed by interactions.  The stars born from those interactions form the
// next generation (round n+1).
//
// This is the minimal faithful implementation of §49.52's AEx iteration in a
// streaming setting: one `AEx^n → AEx^{n+1}` tick = one generation where the
// current "live born" star-set is fully processed.  Grounded in §49.52's
// structure (the output of one AEx feeds the next), tracked here as the
// count of "current-generation stars still to be consumed."
//
// The `round` field of `Step` is this generational index (= the agent's proper
// time, §01-spec §2.6).  It advances when all stars from the current generation
// have been consumed.  Round 0 processes Ψ₀.
// ─────────────────────────────────────────────────────────────────────────────

/// Compute the matchable-frontier count for a Ψ.
fn compute_frontier(phi: &Constellation, psi: &[Star]) -> usize {
    let c_extra = psi_colours(psi);
    let mut count = 0;
    for star in psi.iter() {
        for j in 0..star.len() {
            if ray_is_active(phi, star, j, &c_extra) {
                count += 1;
            }
        }
    }
    count
}

/// Check whether star at index `i` in `psi` is a "current-generation star"
/// (index < gen_front) that can be consumed this round.
///
/// Stars with index ≥ gen_front were born in the current round from fusions
/// and belong to the next generation.
fn find_gen_step(
    phi: &Constellation,
    psi: &[Star],
    gen_front: usize,
    c_extra: &HashSet<String>,
) -> Option<(usize, usize)> {
    // Only consider current-generation stars (index 0..gen_front after re-ordering).
    // Since `one_step` consumes the selected star and shifts indices, we track
    // which stars are in the current generation by their POSITION in psi.
    // Stars 0..gen_front are current-gen; stars gen_front.. are next-gen.
    for i in 0..gen_front.min(psi.len()) {
        let star = &psi[i];
        for j in 0..star.len() {
            if ray_is_active(phi, star, j, c_extra) {
                return Some((i, j));
            }
        }
    }
    None
}

// ─────────────────────────────────────────────────────────────────────────────
// L1c: Agent/environment cut types
// ─────────────────────────────────────────────────────────────────────────────

/// A caller-supplied designation of which star indices (in the current `Ψ_k`)
/// belong to the candidate *agent* sub-constellation.
///
/// The cut is **structural**: a partition of star-occurrence indices in the
/// dep-graph.  No ray is ever hand-tagged motor/sensor.  Layer 2 will later
/// *solve for* the correct agent designation by detecting the reafferent-closure
/// fixed point; L1c only provides the instrument to evaluate any given
/// candidate cut.
pub type AgentSet = HashSet<usize>;

/// Classification of a single dep-graph edge under an agent/environment cut.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EdgeKind {
    /// Both endpoint stars are in the agent sub-constellation.
    AgentInternal,
    /// Both endpoint stars are in the environment partition.
    EnvInternal,
    /// One endpoint is in the agent, the other in the environment — a
    /// cross-cut edge (crosses the agent/environment boundary).
    CrossCut,
}

/// A dep-graph edge together with its cut classification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LabelledEdge {
    pub edge: DepEdge,
    pub kind: EdgeKind,
}

/// The agent/environment cut view of `D[Ψ_k; C]` for a given `AgentSet`.
///
/// Computed by `Step::cut_view(agent_stars)`.  Pure structural analysis of the
/// existing dep-graph under the caller-supplied partition — no ray hand-tagging,
/// no reafference detection (that is L2a).
///
/// # Cross-cut edges and boundary flux
///
/// A *cross-cut edge* connects one star in the agent sub-constellation to one
/// star in the environment partition.  Each such edge represents a potential
/// interaction crossing the boundary.  The *boundary flux* counts how many such
/// edges exist in this step's dep-graph snapshot — a per-step measure of how
/// much the agent and environment are currently coupled.
#[derive(Debug, Clone)]
pub struct CutView {
    /// Dep-graph edges whose both endpoints lie inside the agent sub-constellation.
    pub agent_internal_edges: Vec<LabelledEdge>,
    /// Dep-graph edges whose both endpoints lie outside the agent (i.e. inside the environment).
    pub env_internal_edges: Vec<LabelledEdge>,
    /// Dep-graph edges that cross the agent/environment boundary (one endpoint in each).
    pub cross_cut_edges: Vec<LabelledEdge>,
    /// Number of cross-cut edges (boundary flux count for this step).
    ///
    /// Zero iff the agent and environment are fully decoupled in `D[Ψ_k; C]` at
    /// this step.  Non-zero iff at least one cross-boundary interaction is
    /// structurally available.
    pub boundary_flux: usize,
}

/// Candidacy-gating data exposed by `Step::subjective_profile()`.
///
/// Used by Layer 2 to determine whether the step's `Ψ_k` is in the
/// subjective/animist fragment (where reafferent closure can self-organise)
/// vs the objective/dead fragment (no charge, flat valence).
#[derive(Debug, Clone)]
pub struct SubjectiveProfile {
    /// Number of *subjective* rays in `Ψ_k`: coloured rays with at least one
    /// coloured argument (§48.7).
    pub n_subjective_rays: usize,
    /// Number of *animist* stars in `Ψ_k` (§48.10): stars that contain both
    /// positive and negative rays.
    pub n_animist_stars: usize,
    /// Ch9 §62 structural class of `Ψ_k` (reused from the step's `ch9_class`).
    pub ch9_class: ConstellationClass,
}

// ─────────────────────────────────────────────────────────────────────────────
// Step (the yielded item)
// ─────────────────────────────────────────────────────────────────────────────

/// A single step in the `subjective_stream` trajectory.
///
/// Exposed to the caller after each §51.9 interaction.  Carries:
/// - the **current interaction space** `Ψ_k`;
/// - a **dep-graph snapshot** `D[Ψ_k; C]`;
/// - **cheap structural metrics**: Ψ size, matchable-frontier size, Ch9 §62 class;
/// - the **substrate step index** `index` (witness clock, not proper time);
/// - the **reafferent-round index** `round` (the agent's proper time, §01-spec §2.6
///   and §49.52): advances once per completed `AEx^n → AEx^{n+1}` round.
///
/// # Step index vs. proper time
///
/// `Step::index` is the substrate/witness clock (substrate steps since stream start).
/// `Step::round` is the agent's proper time (reafferent-cycle count, §49.52).
/// These are distinct: a single proper-time tick spans many substrate steps.
/// Layer 2 reads proper time off `round`; never uses `index` for agent mortality.
#[derive(Debug, Clone)]
pub struct Step {
    /// Substrate step index (k in Ψ_k).  Monotone from 0.
    pub index: usize,

    /// Reafferent-round index (proper-time clock, §49.52).
    ///
    /// Increments when one `AEx^n → AEx^{n+1}` round closes (local normal form
    /// reached) and the next round begins.  Round 0 = the initial IEx run from Ψ₀.
    pub round: usize,

    /// Current interaction space Ψ_k: the live stars at this step.
    pub psi: Vec<Star>,

    /// Dependency graph snapshot `D[Ψ_k; C]`.
    pub dep_graph: DepGraph,

    /// Number of stars in Ψ_k (interaction-space size metric).
    pub psi_size: usize,

    /// Number of coloured rays in Ψ_k that have at least one match in Ψ_k or Φ
    /// (the "matchable frontier" — how much live interaction potential remains).
    pub frontier_size: usize,

    /// Ch9 §62 structural class of Ψ_k.
    pub ch9_class: ConstellationClass,

    /// Whether this step's Ψ_k is in normal form w.r.t. Φ (within the current round).
    ///
    /// When `true`, the stream will either:
    /// (a) terminate (if no more matchable Φ-stars exist for the next round), or
    /// (b) advance to the next §49.52 round (incrementing `round`) with fresh Φ supply.
    pub is_normal_form: bool,
}

impl Step {
    // ─────────────────────────────────────────────────────────────────────────
    // L1c: cut_view — markable agent/environment cut over dep_graph
    // ─────────────────────────────────────────────────────────────────────────

    /// Classify dep-graph edges under a caller-supplied agent/environment cut.
    ///
    /// # Arguments
    ///
    /// `agent_stars` — a set of star indices (positions in `self.psi`) that
    /// the caller designates as the candidate *agent* sub-constellation.
    /// Star indices NOT in the set form the *environment* partition.
    ///
    /// # Returns
    ///
    /// A [`CutView`] partitioning `self.dep_graph.edges` into:
    /// - `agent_internal_edges`: both endpoint stars in `agent_stars`
    /// - `env_internal_edges`: both endpoint stars outside `agent_stars`
    /// - `cross_cut_edges`: one endpoint in each partition
    /// - `boundary_flux`: `cross_cut_edges.len()`
    ///
    /// # Faithfulness
    ///
    /// Pure structural analysis — no ray is hand-tagged, no substitution is
    /// applied.  The dep-graph snapshot is taken as-is from `self.dep_graph`.
    /// Calling this method does NOT alter the stream or any Step field.
    pub fn cut_view(&self, agent_stars: &AgentSet) -> CutView {
        let mut agent_internal_edges = Vec::new();
        let mut env_internal_edges = Vec::new();
        let mut cross_cut_edges = Vec::new();

        for edge in &self.dep_graph.edges {
            let (si, sj) = edge.star_indices();
            let si_agent = agent_stars.contains(&si);
            let sj_agent = agent_stars.contains(&sj);

            let kind = match (si_agent, sj_agent) {
                (true, true) => EdgeKind::AgentInternal,
                (false, false) => EdgeKind::EnvInternal,
                _ => EdgeKind::CrossCut,
            };

            let labelled = LabelledEdge { edge: edge.clone(), kind };
            match kind {
                EdgeKind::AgentInternal => agent_internal_edges.push(labelled),
                EdgeKind::EnvInternal   => env_internal_edges.push(labelled),
                EdgeKind::CrossCut      => cross_cut_edges.push(labelled),
            }
        }

        let boundary_flux = cross_cut_edges.len();
        CutView {
            agent_internal_edges,
            env_internal_edges,
            cross_cut_edges,
            boundary_flux,
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // L1c: subjective_profile — candidacy gating data (§62 + §48.7/§48.10)
    // ─────────────────────────────────────────────────────────────────────────

    /// Compute candidacy-gating data for Layer 2.
    ///
    /// Returns a [`SubjectiveProfile`] with:
    /// - `n_subjective_rays`: count of rays in `Ψ_k` that are coloured AND
    ///   have at least one coloured argument (the §48.7 definition of a
    ///   subjective ray).
    /// - `n_animist_stars`: count of stars in `Ψ_k` that are animist (§48.10):
    ///   contain both positive and negative rays.
    /// - `ch9_class`: the §62 structural class (reused from `self.ch9_class`).
    ///
    /// # Faithfulness
    ///
    /// Pure read of `self.psi` and `self.ch9_class` — no stream mutation.
    pub fn subjective_profile(&self) -> SubjectiveProfile {
        use crate::term::{get, TermData};

        let mut n_subjective_rays = 0usize;
        let mut n_animist_stars = 0usize;

        for star in &self.psi {
            // Count animist stars.
            if star_kind(star) == StarKind::Animist {
                n_animist_stars += 1;
            }

            // Count subjective rays: coloured head with ≥1 coloured argument.
            for &ray in star.iter() {
                if let TermData::App(sym, ref args) = get(ray) {
                    if sym.pol != Polarity::Neutral {
                        // Coloured head — check if any argument is coloured.
                        let has_coloured_arg = args.iter().any(|&arg| {
                            matches!(get(arg), TermData::App(s, _) if s.pol != Polarity::Neutral)
                        });
                        if has_coloured_arg {
                            n_subjective_rays += 1;
                        }
                    }
                }
            }
        }

        SubjectiveProfile {
            n_subjective_rays,
            n_animist_stars,
            ch9_class: self.ch9_class,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Streaming executor
// ─────────────────────────────────────────────────────────────────────────────

/// Iterator state for `subjective_stream`.
///
/// `gen_front`: the number of "current-generation" stars in `psi`.  Stars at
/// indices `0..gen_front` belong to the current §49.52 round; stars produced
/// by fusions during this round appear at indices `gen_front..` and belong to
/// the NEXT round.  When `gen_front` reaches 0 (all current-gen stars consumed),
/// we promote the next-gen stars to current-gen (increment `round`).
pub struct SubjectiveStream<'a> {
    phi: &'a Constellation,
    /// Current interaction space.  Stars 0..gen_front are current-gen.
    psi: Vec<Star>,
    counter: u64,
    /// Substrate step index (monotone).
    index: usize,
    /// Reafferent-round index (§49.52 proper time).
    round: usize,
    /// How many stars in `psi[0..gen_front]` remain in the current generation.
    /// When this hits 0, all current-gen stars are consumed → advance round.
    gen_front: usize,
    exhausted: bool,
}

impl<'a> Iterator for SubjectiveStream<'a> {
    type Item = Step;

    fn next(&mut self) -> Option<Step> {
        if self.exhausted {
            return None;
        }

        // ── Round-boundary check ─────────────────────────────────────────────
        // All current-generation stars consumed?  Promote next-gen to current.
        if self.gen_front == 0 || self.gen_front > self.psi.len() {
            // Remaining psi stars are next-gen; they become the new current-gen.
            if self.psi.is_empty() {
                // No stars left at all → global NF; yield final step then stop.
                let dep_graph = DepGraph::from_constellation(&self.psi);
                let step = Step {
                    index: self.index,
                    round: self.round,
                    psi: self.psi.clone(),
                    dep_graph,
                    psi_size: 0,
                    frontier_size: 0,
                    ch9_class: ConstellationClass::Terminating,
                    is_normal_form: true,
                };
                self.exhausted = true;
                return Some(step);
            }
            // New round: all remaining stars are the current generation.
            self.gen_front = self.psi.len();
            self.round += 1;
        }

        // Compute metrics for the CURRENT Ψ (before the step).
        let dep_graph = DepGraph::from_constellation(&self.psi);
        let psi_size = self.psi.len();
        let frontier_size = compute_frontier(self.phi, &self.psi);
        let prof = saturation_profile(&self.psi);
        let ch9_class = prof.class;
        let is_nf_now = is_nf(self.phi, &self.psi);

        let step = Step {
            index: self.index,
            round: self.round,
            psi: self.psi.clone(),
            dep_graph,
            psi_size,
            frontier_size,
            ch9_class,
            is_normal_form: is_nf_now,
        };

        // Find an actionable ray in the CURRENT generation (0..gen_front).
        let c_extra = psi_colours(&self.psi);
        let found = find_gen_step(self.phi, &self.psi, self.gen_front, &c_extra);

        match found {
            None => {
                // No actionable ray in current-gen → this generation is done.
                // Stars remaining past gen_front (next-gen) become the next round.
                // Slice off current-gen stars that are "inert" (no active rays at all).
                // They stay in psi (as normal-form residual) but don't count as gen.
                // Advance: mark current-gen exhausted.
                self.gen_front = 0;
                self.index += 1;
                Some(step)
            }
            Some((i, j)) => {
                // Apply one interaction step, selecting star i, ray j.
                let selected = self.psi[i].clone();
                let r = selected[j];

                // Ψ' = Ψ − {selected}.  Track how gen_front shifts:
                // removing star at index i shifts all indices > i by -1.
                let old_psi: Vec<Star> = std::mem::take(&mut self.psi);
                let mut psi_prime: Vec<Star> = old_psi
                    .into_iter()
                    .enumerate()
                    .filter(|&(idx, _)| idx != i)
                    .map(|(_, s)| s)
                    .collect();

                // gen_front decremented because we consumed one current-gen star.
                if i < self.gen_front {
                    self.gen_front = self.gen_front.saturating_sub(1);
                }

                // Count of current-gen stars in psi_prime (before new fusions).
                let next_gen_start = psi_prime.len();

                // External fusions — appended AFTER current-gen stars.
                let ext_matches = mat_phi_full(self.phi, r, &c_extra);
                for (ik, jk) in ext_matches {
                    let prefix = format!("ext{ik}_{}", self.counter);
                    self.counter += 1;
                    let phi_renamed = alpha_rename_star(&self.phi[ik], &prefix, &mut self.counter);
                    if let Some(fused) = fuse_stars(&selected, j, &phi_renamed, jk) {
                        psi_prime.push(fused);
                    }
                }

                // Self-interactions — also next-gen.
                let self_matches = mat_self_local(&selected, j);
                for jk in self_matches {
                    if let Some(si) = self_interact_star(&selected, j, jk) {
                        psi_prime.push(si);
                    }
                }

                let _ = next_gen_start; // next-gen stars are psi_prime[gen_front..]
                self.psi = psi_prime;
                self.index += 1;
                Some(step)
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public API
// ─────────────────────────────────────────────────────────────────────────────

/// `subjective_stream(Φ, Ψ₀) -> impl Iterator<Item=Step>`
///
/// Lazy, unbounded, non-linear supply streaming executor (Eng §51.9–§51.13,
/// §49.52 hyper-execution).
///
/// # Semantics
///
/// Each `.next()` call:
/// 1. **Yields** a `Step` with the current Ψ_k, dep-graph snapshot, and metrics.
/// 2. **Advances** by one §51.9 interaction step, OR:
///    - when local normal form is reached within the current §49.52 round,
///      starts the next round by injecting fresh matchable Φ-stars (§49.52).
///    - terminates when no new matchable Φ-stars exist (global fixpoint).
///
/// `Step::round` (reafferent-round index, proper time) and `Step::index`
/// (substrate step index, witness clock) are both exposed.
///
/// # Bounding
///
/// Potentially unbounded.  Callers bound with `.take(n)` or until
/// `step.is_normal_form && step.round >= desired_rounds`.
pub fn subjective_stream(phi: &Constellation, psi0: Vec<Star>) -> impl Iterator<Item = Step> + '_ {
    let gen_front = psi0.len();
    SubjectiveStream {
        phi,
        psi: psi0,
        counter: 0,
        index: 0,
        round: 0,
        gen_front,
        exhausted: false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Convenience: drive to normal form (for tests)
// ─────────────────────────────────────────────────────────────────────────────

/// Drive `subjective_stream(Φ, Ψ₀)` to the first local normal form (within round 0),
/// or `max_steps` steps, returning the final `Step`.
pub fn stream_to_normal_form(
    phi: &Constellation,
    psi0: Vec<Star>,
    max_steps: usize,
) -> Option<Step> {
    subjective_stream(phi, psi0)
        .take(max_steps + 1)
        .find(|s| s.is_normal_form)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::execution::stars_alpha_equiv;
    use crate::interactive::iex_concealed;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::Term;

    fn var(x: &str) -> Term { crate::term::mk_var(x) }
    fn app(f: &str, args: Vec<Term>) -> Term { crate::term::mk_app_str(f, args) }
    fn c(name: &str) -> Term { crate::term::mk_app_str(name, vec![]) }

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
                pos_ray("add", vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])]),
            ],
        ]
    }

    fn query_star(m: usize, n: usize) -> Star {
        vec![
            neg_ray("add", vec![nat(m), nat(n), var("R")]),
            var("R"),
        ]
    }

    /// α-equivalence check for result-star multisets (unordered).
    fn result_sets_alpha_equiv(a: &[Star], b: &[Star]) -> bool {
        if a.len() != b.len() { return false; }
        let mut used = vec![false; b.len()];
        'outer: for sa in a {
            for (i, sb) in b.iter().enumerate() {
                if !used[i] && stars_alpha_equiv(sa, sb) {
                    used[i] = true;
                    continue 'outer;
                }
            }
            return false;
        }
        true
    }

    fn conceal_and_filter(psi: &[Star]) -> Vec<Star> {
        crate::interactive::conceal_and_filter(psi)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // GATE (a): Eng §49.50 worked example — MANDATORY
    //
    // `[−f(+g(X))] ⋈ [X, +f(X)]` along `−f(+g(X))`/`+f(X)` must yield `[+g(X)]`.
    //
    // The bare `X` ray in star2 becomes the new polarised `+g(X)` via the
    // substitution θ = {X' ↦ +g(X)} produced by PolarisedCompat unification.
    // ─────────────────────────────────────────────────────────────────────────

    /// §49.50 worked example: `[−f(+g(X))]` × `[X, +f(X)]` → `[+g(X)]`.
    ///
    /// Setup:
    ///   Φ = { [X, +f(X)] }        ← star with bare variable ray X and coloured +f(X)
    ///   Ψ₀ = { [−f(+g(X_psi))] } ← query star (X_psi renamed to avoid capture)
    ///
    /// Expected: stream reaches normal form with psi containing a star α-equivalent
    /// to [+g(_)] (a positive application of g with one argument).
    #[test]
    fn gate_a_eng_4950_new_ray_creation() {
        // Φ = { [X, +f(X)] } — the "animist" supply star
        // (has bare variable ray X and coloured ray +f(X))
        let phi: Constellation = vec![
            vec![var("X"), pos_ray("f", vec![var("X")])],
        ];

        // Ψ₀ = { [−f(+g(Z))] } — query: a negative f applied to a coloured g(Z)
        // We use fresh variable Z to keep it separate from Φ's X.
        let psi0: Vec<Star> = vec![
            vec![neg_ray("f", vec![pos_ray("g", vec![var("Z")])])],
        ];

        // Drive to normal form.
        let final_step = stream_to_normal_form(&phi, psi0, 100)
            .expect("§49.50 example must reach normal form");

        assert!(final_step.is_normal_form,
            "§49.50 example: terminal step must be normal form");

        // The result must contain a star that is [+g(_)] — a positive application
        // of g with one argument.  The exact variable name doesn't matter (α-equiv).
        let psi = &final_step.psi;

        // Find a star with a single ray that is +g applied to something.
        let has_pos_g = psi.iter().any(|star| {
            star.len() == 1 && {
                let r = star[0];
                match crate::term::get(r) {
                    crate::term::TermData::App(sym, args) =>
                        sym.pol == Polarity::Pos
                        && sym.name.as_str() == "g"
                        && args.len() == 1,
                    _ => false,
                }
            }
        });

        assert!(has_pos_g,
            "GATE (a) FAIL: §49.50 example must yield star [+g(_)]; got:\n  {:?}",
            psi);

        // Stronger check: the argument of +g must NOT be a bare variable that has
        // been substituted to something — actually it should be a variable (Z from Φ),
        // since Z was the free variable in -f(+g(Z)) and it threads through.
        // The bare X variable ray in Φ becomes +g(Z) via substitution.
        // We just verify the coloured structure, not the exact variable name.
    }

    /// §49.50 gate — explicit structure check using the exact example from the doc.
    ///
    /// Verify the substitution produced is {X' ↦ +g(X)} and NOT {X' ↦ g(X)}.
    /// We do this by checking that the result ray is positive (has Pos polarity).
    #[test]
    fn gate_a_eng_4950_result_is_coloured() {
        let phi: Constellation = vec![
            vec![var("X"), pos_ray("f", vec![var("X")])],
        ];
        let psi0: Vec<Star> = vec![
            vec![neg_ray("f", vec![pos_ray("g", vec![var("Z")])])],
        ];

        let final_step = stream_to_normal_form(&phi, psi0, 100)
            .expect("§49.50 must terminate");

        // The ray must be POSITIVE (+g), not neutral (g).
        // If fuse_stars incorrectly uses underlying_term, the result is [g(Z)]
        // (neutral) which would not appear here as positive.
        let all_rays_and_pols: Vec<(String, Polarity)> = final_step.psi.iter().flat_map(|star| {
            star.iter().map(|&r| {
                match crate::term::get(r) {
                    crate::term::TermData::App(sym, _) =>
                        (sym.name.as_str().to_string(), sym.pol),
                    crate::term::TermData::Var(v) =>
                        (v.as_str().to_string(), Polarity::Neutral),
                }
            })
        }).collect();

        let has_positive_g = all_rays_and_pols.iter()
            .any(|(name, pol)| name == "g" && *pol == Polarity::Pos);

        assert!(has_positive_g,
            "GATE (a) FAIL: result must contain +g (positive), not neutral g.\n\
             Ray polarities found: {:?}\n\
             (If underlying_term stripping is used, polarity is lost and g is neutral.)",
            all_rays_and_pols);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // GATE (b): Objective-fragment regression — MANDATORY
    //
    // stream-to-normal-form must equal iex_concealed (oracle) on all objective cases.
    // Never weaken these tests.
    // ─────────────────────────────────────────────────────────────────────────

    /// Horn add 1+1: stream reaches [2̄] ≈α oracle.
    #[test]
    fn faithfulness_horn_add_1_plus_1() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 500);
        assert!(oracle_nf, "oracle must reach normal form for add 1+1");

        let term_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("stream must reach normal form for add 1+1");
        assert!(term_step.is_normal_form);

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "GATE (b) FAIL: stream 1+1 ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );

        let expected = vec![nat(2)];
        assert!(
            stream_visible.iter().any(|s| stars_alpha_equiv(s, &expected)),
            "stream 1+1 must contain [2̄]; got {:?}", stream_visible
        );
    }

    /// Horn add 2+2: stream reaches [4̄] ≈α oracle.
    #[test]
    fn faithfulness_horn_add_2_plus_2() {
        let phi = add_prog();
        let psi0 = vec![query_star(2, 2)];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 500);
        assert!(oracle_nf, "oracle must reach normal form for add 2+2");

        let term_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("stream must reach normal form for add 2+2");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "GATE (b) FAIL: stream 2+2 ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );

        let expected = vec![nat(4)];
        assert!(
            stream_visible.iter().any(|s| stars_alpha_equiv(s, &expected)),
            "stream 2+2 must contain [4̄]; got {:?}", stream_visible
        );
    }

    /// Tiny NFA ("00" accepts): stream ≈α oracle, and both contain [accept].
    #[test]
    fn faithfulness_nfa_tiny_objective() {
        use crate::term::mk_app_str;

        let eps  = mk_app_str("eps",  vec![]);
        let ch0  = mk_app_str("0",    vec![]);
        let cons = |ch: Term, rest: Term| mk_app_str("cons", vec![ch, rest]);
        let w00  = cons(ch0.clone(), cons(ch0.clone(), eps.clone()));

        let word_star: Star = vec![pos_ray("i", vec![w00])];

        let init: Star = vec![
            neg_ray("i",  vec![var("W")]),
            pos_ray("a",  vec![var("W"), mk_app_str("q0", vec![])]),
        ];
        let fin_: Star = vec![
            neg_ray("a",  vec![eps.clone(), mk_app_str("q2", vec![])]),
            mk_app_str("accept", vec![]),
        ];
        let t1: Star = vec![
            neg_ray("a", vec![
                mk_app_str("cons", vec![mk_app_str("0", vec![]), var("W")]),
                mk_app_str("q0", vec![]),
            ]),
            pos_ray("a", vec![var("W"), mk_app_str("q1", vec![])]),
        ];
        let t2: Star = vec![
            neg_ray("a", vec![
                mk_app_str("cons", vec![mk_app_str("0", vec![]), var("W")]),
                mk_app_str("q1", vec![]),
            ]),
            pos_ray("a", vec![var("W"), mk_app_str("q2", vec![])]),
        ];

        let phi: Constellation = vec![init, fin_, t1, t2];
        let psi0: Vec<Star>    = vec![word_star];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 500);
        assert!(oracle_nf, "oracle must reach normal form for NFA tiny");

        let accept_star: Star = vec![mk_app_str("accept", vec![])];
        assert!(
            oracle_visible.iter().any(|s| s == &accept_star),
            "oracle NFA tiny must contain [accept]; got {:?}", oracle_visible
        );

        let term_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("stream must reach normal form for NFA tiny");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "GATE (b) FAIL: stream NFA tiny ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );

        assert!(
            stream_visible.iter().any(|s| s == &accept_star),
            "stream NFA tiny must contain [accept]; got {:?}", stream_visible
        );
    }

    /// Pure objective constellation: empty Ψ₀ → immediate normal form.
    #[test]
    fn faithfulness_objective_pair_inert() {
        let phi: Constellation = vec![
            vec![pos_ray("a", vec![])],
            vec![pos_ray("b", vec![])],
        ];
        let psi0: Vec<Star> = vec![];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 10);
        assert!(oracle_nf, "oracle: empty psi0 is already normal form");

        let term_step = stream_to_normal_form(&phi, psi0, 10)
            .expect("stream must yield at least one step");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "GATE (b) FAIL: stream objective pair ≠ oracle"
        );
        assert_eq!(term_step.index, 0, "normal form at step 0");
    }

    /// Objective deterministic pair [+a] + [-a]: stream resolves to [] ≈α oracle.
    #[test]
    fn faithfulness_objective_deterministic_pair() {
        let phi: Constellation = vec![
            vec![pos_ray("a", vec![])],
        ];
        let psi0: Vec<Star> = vec![vec![neg_ray("a", vec![])]];

        let (oracle_visible, oracle_nf) = iex_concealed(&phi, psi0.clone(), 20);
        assert!(oracle_nf, "oracle must reach normal form for +a/-a pair");

        let term_step = stream_to_normal_form(&phi, psi0, 20)
            .expect("stream must yield a normal-form step for +a/-a");

        let stream_visible = conceal_and_filter(&term_step.psi);

        assert!(
            result_sets_alpha_equiv(&stream_visible, &oracle_visible),
            "GATE (b) FAIL: stream +a/-a ≠ oracle\n  stream={:?}\n  oracle={:?}",
            stream_visible, oracle_visible
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // GATE (c): Reafferent-round index advances ≥ 2 rounds over a bounded stream.
    //
    // Demonstrates §49.52 iteration + proper-time exposure.
    //
    // Setup: a subjective/animist constellation where:
    //   Φ = { [−tick(N), +tick(s(N))] }  ← "ticker": consuming −tick(N) produces +tick(s(N))
    //   Ψ₀ = { [+tick(0)] }              ← initial tick at 0
    //
    // Round 0: [+tick(0)] fuses with Φ-star (−tick(N) ⋈ +tick(0), N↦0) → [+tick(s(0))]
    // At NF (no match left from Φ's −tick until a fresh copy is added):
    //   Actually +tick(s(0)) matches −tick(N') in a fresh Φ-copy → starts round 1.
    // Round 1: [+tick(s(0))] + fresh [−tick(N'), +tick(s(N'))] →
    //   fuse → [+tick(s(s(0)))] → NF → round 2.
    // So round advances at least twice.
    // ─────────────────────────────────────────────────────────────────────────

    /// Reafferent-round (proper-time) index advances ≥ 2 rounds.
    #[test]
    fn gate_c_reafferent_round_advances() {
        // Φ = { [−tick(N), +tick(s(N))] }
        let phi: Constellation = vec![
            vec![
                neg_ray("tick", vec![var("N")]),
                pos_ray("tick", vec![app("s", vec![var("N")])]),
            ],
        ];

        // Ψ₀ = { [+tick(0)] }
        let psi0: Vec<Star> = vec![
            vec![pos_ray("tick", vec![c("zero")])],
        ];

        // Collect up to 30 steps; we expect round to reach at least 2.
        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(30)
            .collect();

        assert!(!steps.is_empty(), "stream must yield steps");

        let max_round = steps.iter().map(|s| s.round).max().unwrap_or(0);

        assert!(
            max_round >= 2,
            "GATE (c) FAIL: reafferent-round must reach ≥ 2; max_round = {}\n\
             Steps: round sequence = {:?}",
            max_round,
            steps.iter().map(|s| (s.index, s.round, s.is_normal_form)).collect::<Vec<_>>()
        );

        // Verify round is monotone non-decreasing.
        let rounds: Vec<usize> = steps.iter().map(|s| s.round).collect();
        for w in rounds.windows(2) {
            assert!(w[1] >= w[0],
                "round must be non-decreasing; got {:?}", rounds);
        }

        // Verify index is strictly monotone.
        let indices: Vec<usize> = steps.iter().map(|s| s.index).collect();
        for w in indices.windows(2) {
            assert!(w[1] > w[0],
                "index must be strictly increasing; got {:?}", indices);
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Step structure / metrics tests
    // ─────────────────────────────────────────────────────────────────────────

    /// Step exposes correct index sequence for Horn add 1+1.
    #[test]
    fn step_index_monotone_add_1_plus_1() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(200)
            .collect();

        assert!(!steps.is_empty(), "must yield at least one step");

        for (expected_idx, step) in steps.iter().enumerate() {
            assert_eq!(step.index, expected_idx,
                "step index must be monotone; at pos {expected_idx} got index {}", step.index);
        }

        let last = steps.last().unwrap();
        assert!(last.is_normal_form, "last step must be normal form");
    }

    /// frontier_size decreases to 0 at normal form.
    #[test]
    fn frontier_zero_at_normal_form_horn() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        let final_step = stream_to_normal_form(&phi, psi0, 500)
            .expect("must reach normal form");

        assert_eq!(final_step.frontier_size, 0,
            "frontier must be 0 at normal form; got {}", final_step.frontier_size);
    }

    /// dep_graph snapshot is consistent.
    #[test]
    fn dep_graph_snapshot_no_panic_horn() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        for step in subjective_stream(&phi, psi0).take(50) {
            assert_eq!(step.dep_graph.n_stars, step.psi.len(),
                "dep_graph.n_stars must match psi size at step {}", step.index);
            if step.is_normal_form { break; }
        }
    }

    /// round field is non-decreasing; for an objective (terminating) run,
    /// rounds advance with each generation but the stream terminates (NF reached).
    #[test]
    fn round_nondecreasing_objective_run() {
        let phi = add_prog();
        let psi0 = vec![query_star(1, 1)];

        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(200)
            .collect();

        assert!(!steps.is_empty(), "must yield steps");

        // Round must be non-decreasing.
        let rounds: Vec<usize> = steps.iter().map(|s| s.round).collect();
        for w in rounds.windows(2) {
            assert!(w[1] >= w[0],
                "round must be non-decreasing; got {:?}", rounds);
        }

        // Stream must terminate (reach is_normal_form) within budget.
        assert!(
            steps.iter().any(|s| s.is_normal_form),
            "objective run must reach normal form within budget"
        );
    }

    /// Animist progress test.
    #[test]
    fn progress_animist_add_self_interaction() {
        let phi = add_prog();
        let psi0: Vec<Star> = vec![
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray("add", vec![app("s", vec![var("X")]), var("Y"), app("s", vec![var("Z")])]),
            ],
        ];

        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(8)
            .collect();

        assert!(!steps.is_empty(), "animist stream must yield at least one step");

        for step in &steps {
            let _ = step.psi_size;
            let _ = step.frontier_size;
            let _ = step.round;
            let _ = match step.ch9_class {
                ConstellationClass::Terminating => 0,
                ConstellationClass::NonTerminatingCandidate => 1,
            };
        }

        let max_idx = steps.iter().map(|s| s.index).max().unwrap_or(0);
        assert!(
            steps.len() == 1 || max_idx > 0,
            "stream must either terminate in 1 step or advance beyond index 0"
        );
    }

    /// Subjective stream exposes Steps.
    #[test]
    fn progress_subjective_single_neg() {
        let phi: Constellation = vec![
            vec![pos_ray("c", vec![var("X")])],
        ];
        let psi0: Vec<Star> = vec![
            vec![neg_ray("c", vec![var("Y")])],
        ];

        let steps: Vec<Step> = subjective_stream(&phi, psi0)
            .take(6)
            .collect();

        assert!(!steps.is_empty(), "subjective stream must yield at least one step");

        let first = &steps[0];
        let _ = first.psi_size;
        let _ = first.frontier_size;
        let _ = &first.dep_graph;
        let _ = first.ch9_class;
        let _ = first.round;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // L1c: cut_view tests
    //
    // Tiny constellation: 3 stars, star 0 and 1 in agent; star 2 in environment.
    // dep_graph has:
    //   edge (0, 1) — agent-internal (0∈agent, 1∈agent)
    //   edge (1, 2) — cross-cut     (1∈agent, 2∉agent)
    //
    // We construct this directly using a small matchable constellation:
    //   star 0 = [+p(A)]
    //   star 1 = [-p(B), +q(B)]
    //   star 2 = [-q(C)]
    //
    // D[Ψ;C] edges: (0,1) from +p(A)⋈-p(B); (1,2) from +q(B)⋈-q(C).
    // agent_stars = {0, 1}.
    // Expected: agent_internal=[(0,1)], cross_cut=[(1,2)], env_internal=[].
    // boundary_flux = 1.
    // ─────────────────────────────────────────────────────────────────────────

    /// cut_view correctly classifies a known agent-internal edge vs cross-cut edge.
    #[test]
    fn cut_view_classifies_internal_vs_cross_cut() {
        // Ψ = [+p(A)], [-p(B), +q(B)], [-q(C)]
        // star 0 ∈ agent; star 1 ∈ agent; star 2 ∈ environment
        let psi0: Vec<Star> = vec![
            vec![pos_ray("p", vec![var("A")])],
            vec![neg_ray("p", vec![var("B")]), pos_ray("q", vec![var("B")])],
            vec![neg_ray("q", vec![var("C")])],
        ];

        // Use empty Φ (no supply); just drive one step to get a dep-graph snapshot.
        // Actually: use Ψ directly as its own psi0 with empty phi so the dep-graph
        // is built over the 3 stars as-is at step 0.
        let phi: Constellation = vec![];
        let step0 = subjective_stream(&phi, psi0)
            .next()
            .expect("must yield at least one step");

        // Verify dep_graph has the expected edge structure.
        // D[Ψ;C] should contain edges (0,1) and (1,2).
        let edges = &step0.dep_graph.edges;
        let has_01 = edges.iter().any(|e| {
            let (si, sj) = e.star_indices(); (si == 0 && sj == 1) || (si == 1 && sj == 0)
        });
        let has_12 = edges.iter().any(|e| {
            let (si, sj) = e.star_indices(); (si == 1 && sj == 2) || (si == 2 && sj == 1)
        });
        assert!(has_01, "dep_graph must contain edge (0,1); edges={:?}", edges);
        assert!(has_12, "dep_graph must contain edge (1,2); edges={:?}", edges);

        // Now apply cut: agent = {0, 1}, env = {2}.
        let agent_stars: AgentSet = [0usize, 1].iter().copied().collect();
        let cv = step0.cut_view(&agent_stars);

        assert_eq!(cv.agent_internal_edges.len(), 1,
            "must have exactly 1 agent-internal edge; got {:?}", cv.agent_internal_edges);
        assert_eq!(cv.env_internal_edges.len(), 0,
            "must have 0 env-internal edges; got {:?}", cv.env_internal_edges);
        assert_eq!(cv.cross_cut_edges.len(), 1,
            "must have exactly 1 cross-cut edge; got {:?}", cv.cross_cut_edges);
        assert_eq!(cv.boundary_flux, 1,
            "boundary_flux must be 1; got {}", cv.boundary_flux);

        // Verify the agent-internal edge is (0,1).
        let ai_edge = &cv.agent_internal_edges[0];
        assert_eq!(ai_edge.kind, EdgeKind::AgentInternal);
        let (si, sj) = ai_edge.edge.star_indices();
        assert!(
            (si == 0 && sj == 1) || (si == 1 && sj == 0),
            "agent-internal edge must be (0,1); got ({si},{sj})"
        );

        // Verify the cross-cut edge is (1,2).
        let cc_edge = &cv.cross_cut_edges[0];
        assert_eq!(cc_edge.kind, EdgeKind::CrossCut);
        let (si, sj) = cc_edge.edge.star_indices();
        assert!(
            (si == 1 && sj == 2) || (si == 2 && sj == 1),
            "cross-cut edge must be (1,2); got ({si},{sj})"
        );
    }

    /// boundary_flux is zero when agent and environment have no shared dep-graph edges.
    #[test]
    fn cut_view_boundary_flux_zero_when_no_cross_cut() {
        // Ψ = [+p(A)], [-p(B)], [+q(X)], [-q(Y)]
        // D[Ψ;C] edges: (0,1) from +p/-p; (2,3) from +q/-q.
        // agent = {0, 1}, env = {2, 3}: no cross-cut edges → boundary_flux = 0.
        let psi0: Vec<Star> = vec![
            vec![pos_ray("p", vec![var("A")])],
            vec![neg_ray("p", vec![var("B")])],
            vec![pos_ray("q", vec![var("X")])],
            vec![neg_ray("q", vec![var("Y")])],
        ];
        let phi: Constellation = vec![];
        let step0 = subjective_stream(&phi, psi0)
            .next()
            .expect("must yield step");

        let agent_stars: AgentSet = [0usize, 1].iter().copied().collect();
        let cv = step0.cut_view(&agent_stars);

        assert_eq!(cv.boundary_flux, 0,
            "no cross-cut edges ⇒ boundary_flux must be 0; got {}", cv.boundary_flux);
        assert_eq!(cv.cross_cut_edges.len(), 0);
        assert_eq!(cv.agent_internal_edges.len(), 1,
            "edge (0,1) must be agent-internal");
        assert_eq!(cv.env_internal_edges.len(), 1,
            "edge (2,3) must be env-internal");
    }

    /// boundary_flux is nonzero exactly when a cross-cut interaction exists.
    #[test]
    fn cut_view_boundary_flux_nonzero_iff_cross_cut_present() {
        // Same 3-star constellation as cut_view_classifies_internal_vs_cross_cut.
        // Varies the cut: agent = {0} only → edge (0,1) becomes cross-cut.
        let psi0: Vec<Star> = vec![
            vec![pos_ray("p", vec![var("A")])],
            vec![neg_ray("p", vec![var("B")]), pos_ray("q", vec![var("B")])],
            vec![neg_ray("q", vec![var("C")])],
        ];
        let phi: Constellation = vec![];
        let step0 = subjective_stream(&phi, psi0)
            .next()
            .expect("must yield step");

        // agent = {0}: both edges (0,1) and nothing else; (0,1) is cross-cut.
        let agent_stars: AgentSet = [0usize].iter().copied().collect();
        let cv = step0.cut_view(&agent_stars);

        assert!(cv.boundary_flux > 0,
            "with agent={{0}}, edge (0,1) must be cross-cut ⇒ boundary_flux > 0; got {}",
            cv.boundary_flux);

        // agent = {} (empty): all edges are env-internal → boundary_flux = 0.
        let empty_agent: AgentSet = HashSet::new();
        let cv2 = step0.cut_view(&empty_agent);
        assert_eq!(cv2.boundary_flux, 0,
            "empty agent ⇒ all edges env-internal ⇒ boundary_flux = 0; got {}", cv2.boundary_flux);
        assert_eq!(cv2.agent_internal_edges.len(), 0);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // L1c: subjective_profile tests
    // ─────────────────────────────────────────────────────────────────────────

    /// subjective_profile counts subjective rays and animist stars correctly.
    #[test]
    fn subjective_profile_counts_subjective_rays_and_animist_stars() {
        // Ψ = { [-f(+g(X)), +h(Y)] }   ← animist star (has + and -)
        //       ray -f(+g(X)) is subjective: negative head, coloured argument +g(X)
        //       ray +h(Y) is NOT subjective: no coloured argument (Y is a variable)
        // Expected: n_subjective_rays=1, n_animist_stars=1
        let psi0: Vec<Star> = vec![
            vec![
                neg_ray("f", vec![pos_ray("g", vec![var("X")])]),  // -f(+g(X)) — subjective
                pos_ray("h", vec![var("Y")]),                       // +h(Y) — not subjective (Y is Var)
            ],
        ];
        let phi: Constellation = vec![];
        let step0 = subjective_stream(&phi, psi0)
            .next()
            .expect("must yield step");

        let profile = step0.subjective_profile();
        assert_eq!(profile.n_subjective_rays, 1,
            "must count 1 subjective ray; got {}", profile.n_subjective_rays);
        assert_eq!(profile.n_animist_stars, 1,
            "must count 1 animist star; got {}", profile.n_animist_stars);
    }

    /// subjective_profile returns zero counts for a purely objective constellation.
    #[test]
    fn subjective_profile_zero_for_objective_constellation() {
        // Ψ = { [+a], [-b] } — two objective/subjective (but not animist) stars,
        // no subjective rays (no coloured arguments).
        let psi0: Vec<Star> = vec![
            vec![pos_ray("a", vec![])],
            vec![neg_ray("b", vec![])],
        ];
        let phi: Constellation = vec![];
        let step0 = subjective_stream(&phi, psi0)
            .next()
            .expect("must yield step");

        let profile = step0.subjective_profile();
        assert_eq!(profile.n_subjective_rays, 0,
            "no subjective rays expected; got {}", profile.n_subjective_rays);
        assert_eq!(profile.n_animist_stars, 0,
            "no animist stars expected; got {}", profile.n_animist_stars);
    }
}
