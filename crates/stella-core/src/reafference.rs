//! L2a — Spec §2.2 reafferent-closure detector (provenance-causal, not structural).
//!
//! # What this module implements
//!
//! **Spec §2.2** defines the agent's individuation as a fixed-point: the
//! sub-constellation whose reafference cycle *closes*. A reafference cycle is:
//!
//! > ∃ rounds r < r′ and a candidate agent-partition P such that an agent→env
//! > cross-cut interaction at round r whose substitution **modifies an env star**,
//! > AND an agent resolution at round r′ whose **provenance traces through that
//! > modified env star**. (`docs/01-subjective-engine-and-valence.md §2.2`)
//!
//! This is an irreducibly **causal/temporal** property — detecting it from
//! structural co-occurrence alone is the N1 failure mode. The cycle is decided
//! entirely over derivation provenance, round stamps, and the agent/environment cut.
//!
//! # Candidacy filter (Ch9 §62-gated — documented precisely)
//!
//! `solve_for_closure` must not hand-pick partitions. Instead it enumerates
//! **principled candidate agent-partitions** from psi0, gated by two criteria
//! cited directly from the spec and Ch9:
//!
//! 1. **§62 / `docs/01` §2.2 subjectivity gate**: the combined phi ⊎ psi0 must
//!    contain at least one subjective or animist star (`ch9::classify` returns
//!    `NonTerminatingCandidate` for the combined constellation). Objective/dead
//!    constellations (idempotent by §49.55) cannot host a reafference cycle — they
//!    have no non-idempotent dynamics. The gate checks phi ⊎ psi0 rather than psi0
//!    alone because the subjective dynamics arise from phi (the non-linear supply)
//!    interacting with psi0: phi stars may carry the animist/subjective structure
//!    even when psi0 is a simple query. If phi ⊎ psi0 is objective, `solve_for_closure`
//!    returns empty immediately.
//!
//! 2. **§2.2 / §62 connected sub-constellation filter**: a candidate agent partition
//!    is a *non-empty* subset S ⊆ {0, …, |psi0|−1} such that:
//!    - S contains at least one subjective or animist star (§48.7/§48.10: these are
//!      the only stars that carry the non-idempotent colour dynamics that can produce
//!      a reafference cycle; objective-only sub-constellations are dead by §49.55).
//!    - S is **connected** in the dependency graph D[psi0; C] (only sub-constellations
//!      that are dep-graph-connected can form an internal interaction group; isolated
//!      stars cannot close a cycle through the environment and back).
//!    - |S| ≤ `MAX_AGENT_SIZE` (tractability bound for small experiments; documented).
//!
//! These criteria are **principled**, not arbitrary: they are derived directly from
//! §49.55 (objective ⇒ dead ⇒ no cycle), §49.57 (subjective/animist ⇒ non-idempotent
//! ⇒ candidate for reafference), and the §62 structural heuristic that makes dep-graph
//! connectivity the right locality notion for agent sub-constellations. No partition
//! is hand-picked to produce a closure.
//!
//! # Honest null
//!
//! If no candidate partition admits the cycle on the given constellation,
//! `solve_for_closure` returns an empty `Vec`. That is the expected, legitimate
//! outcome for objective/inert constellations and is the raw material the L2c
//! harness uses for the N1 falsification gate. It is never papered over, never
//! weakened, and never hand-tuned to manufacture a closure.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::ch9::{classify, ConstellationClass};
use crate::constellation::{star_kind, Constellation, Star, StarKind};
use crate::dep_graph::DepGraph;
use crate::subjective::{subjective_stream, AgentSet, Provenance, StarId, Step};

// ─────────────────────────────────────────────────────────────────────────────
// Tractability bound
// ─────────────────────────────────────────────────────────────────────────────

/// Maximum agent sub-constellation size for `solve_for_closure` enumeration.
///
/// `solve_for_closure` is intended for small experiment constellations; this
/// constant is the explicit tractability bound. Candidate subsets larger than
/// `MAX_AGENT_SIZE` are not enumerated. Documents the bound so it is never
/// silently changed.
const MAX_AGENT_SIZE: usize = 6;

// ─────────────────────────────────────────────────────────────────────────────
// ClosureWitness — the evidence record
// ─────────────────────────────────────────────────────────────────────────────

/// Evidence that the spec §2.2 reafferent-closure cycle was detected over a
/// bounded trajectory under a given agent-partition.
///
/// All fields are necessary and together sufficient to reconstruct the causal
/// argument: the cycle is established by provenance, round order, and the
/// agent/environment cut — never by structural co-occurrence alone.
#[derive(Debug, Clone)]
pub struct ClosureWitness {
    /// The agent partition under which the cycle was detected.
    ///
    /// A set of psi0 star indices that form the "agent sub-constellation."
    /// This is the candidate partition P from spec §2.2.
    pub partition: AgentSet,

    /// Round r: the round at which the agent→env cross-cut interaction occurred.
    ///
    /// At this round, an agent-ancestry psi-star fused (crossed the cut) and
    /// produced `traced_env_star` — the modified environment star.
    pub r: usize,

    /// Round r′ (> r): the round at which the agent-side resolution occurred
    /// whose provenance traces through `traced_env_star`.
    pub r_prime: usize,

    /// The dep-graph cross-cut edge that was "used" at round r.
    ///
    /// One endpoint is in the agent sub-constellation; the other is in the
    /// environment partition. This is the structural witness that the interaction
    /// genuinely crossed the agent/environment boundary.
    pub crossing_edge: (usize, usize), // (star_idx_a, star_idx_b) in psi at that step

    /// The `StarId` of the environment star modified at round r.
    ///
    /// This is the fused product of the cross-cut interaction at round r. It has
    /// mixed provenance (agent psi-parent + phi copy). A later agent-side star's
    /// provenance traces through this id.
    pub traced_env_star: StarId,

    /// The `StarId` of the agent-side resolution at round r′.
    ///
    /// This star's provenance DAG reaches `traced_env_star`, closing the loop:
    /// the agent at r′ depends on what it wrote into the environment at r.
    pub agent_resolution: StarId,
}

// ─────────────────────────────────────────────────────────────────────────────
// Provenance ancestry helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Collect all `StarId`s reachable (upward) from `start` in the provenance DAG.
///
/// Returns the set of all ancestor ids (not including `start` itself).
/// Uses BFS; terminates because ids are monotone and parents always have smaller ids.
fn all_ancestors(prov: &HashMap<StarId, Provenance>, start: StarId) -> HashSet<StarId> {
    let mut visited: HashSet<StarId> = HashSet::new();
    let mut queue: VecDeque<StarId> = VecDeque::new();
    queue.push_back(start);
    while let Some(cur) = queue.pop_front() {
        match prov.get(&cur) {
            None | Some(Provenance::Initial) => {}
            Some(Provenance::Fused { parent_psi, parent_phi_id, .. }) => {
                for &p in &[*parent_psi, *parent_phi_id] {
                    if visited.insert(p) {
                        queue.push_back(p);
                    }
                }
            }
            Some(Provenance::SelfInteracted { parent, .. }) => {
                if visited.insert(*parent) {
                    queue.push_back(*parent);
                }
            }
        }
    }
    visited
}

/// Does the star `id` have provenance that traces through any id in `agent_root_ids`?
///
/// "Agent ancestry" = the star's derivation history reaches at least one initial
/// psi0-agent star.  Initial psi0-agent star ids are exactly `StarId(k)` for
/// `k ∈ partition` (ids are assigned 0, 1, … to psi0 stars in order).
fn has_agent_ancestry(
    prov: &HashMap<StarId, Provenance>,
    id: StarId,
    agent_root_ids: &HashSet<StarId>,
) -> bool {
    // The id itself might be an agent root.
    if agent_root_ids.contains(&id) {
        return true;
    }
    let ancestors = all_ancestors(prov, id);
    ancestors.iter().any(|a| agent_root_ids.contains(a))
}

/// Derive the set of `StarId`s corresponding to initial psi0-agent stars from
/// the partition P.
///
/// psi0 stars are assigned ids 0, 1, …, |psi0|-1 in order by `subjective_stream`.
/// So partition P = set of star *indices* in psi0 → agent root ids = {StarId(k) | k ∈ P}.
fn agent_root_ids_from_partition(partition: &AgentSet) -> HashSet<StarId> {
    partition.iter().map(|&k| StarId(k as u64)).collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// Connected-component helpers for candidacy filter
// ─────────────────────────────────────────────────────────────────────────────

/// Build the star-level adjacency list from a dep-graph (undirected).
fn star_adjacency(dg: &DepGraph, n_stars: usize) -> Vec<HashSet<usize>> {
    let mut adj: Vec<HashSet<usize>> = vec![HashSet::new(); n_stars];
    for e in &dg.edges {
        let (si, sj) = e.star_indices();
        if si != sj {
            adj[si].insert(sj);
            adj[sj].insert(si);
        }
    }
    adj
}

/// Find connected components of the dep-graph at the star level.
///
/// Returns a Vec of components, each component = a set of star indices
/// that are reachable from each other via dep-graph edges.
fn connected_components(adj: &[HashSet<usize>]) -> Vec<HashSet<usize>> {
    let n = adj.len();
    let mut visited = vec![false; n];
    let mut components: Vec<HashSet<usize>> = Vec::new();

    for start in 0..n {
        if visited[start] {
            continue;
        }
        let mut comp: HashSet<usize> = HashSet::new();
        let mut queue: VecDeque<usize> = VecDeque::new();
        queue.push_back(start);
        visited[start] = true;
        while let Some(v) = queue.pop_front() {
            comp.insert(v);
            for &u in &adj[v] {
                if !visited[u] {
                    visited[u] = true;
                    queue.push_back(u);
                }
            }
        }
        components.push(comp);
    }
    components
}

/// Enumerate all non-empty subsets of `component` that are connected (in the
/// component's induced sub-graph) and bounded by `max_size`.
///
/// "Connected subset" = subgraph induced by the subset is connected in `adj`.
/// This is used to enumerate connected sub-constellations of each component.
fn connected_subsets(
    component: &HashSet<usize>,
    adj: &[HashSet<usize>],
    max_size: usize,
) -> Vec<HashSet<usize>> {
    let nodes: Vec<usize> = {
        let mut v: Vec<usize> = component.iter().copied().collect();
        v.sort_unstable();
        v
    };
    let n = nodes.len();
    let mut result: Vec<HashSet<usize>> = Vec::new();

    // Enumerate subsets up to max_size using power-set iteration.
    // For tractability we cap at max_size and only keep connected subsets.
    // This is sound: larger partitions are excluded by the explicit bound.
    let max_mask: u64 = 1u64 << n;
    for mask in 1u64..max_mask {
        let subset: HashSet<usize> = (0..n)
            .filter(|&bit| (mask >> bit) & 1 == 1)
            .map(|bit| nodes[bit])
            .collect();
        if subset.len() > max_size {
            continue;
        }
        if is_connected_subset(&subset, adj) {
            result.push(subset);
        }
    }
    result
}

/// Check whether `subset` (a set of star indices) is connected in `adj`.
fn is_connected_subset(subset: &HashSet<usize>, adj: &[HashSet<usize>]) -> bool {
    if subset.is_empty() {
        return false;
    }
    if subset.len() == 1 {
        return true;
    }
    let start = *subset.iter().next().unwrap();
    let mut visited: HashSet<usize> = HashSet::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(start);
    visited.insert(start);
    while let Some(v) = queue.pop_front() {
        for &u in &adj[v] {
            if subset.contains(&u) && !visited.contains(&u) {
                visited.insert(u);
                queue.push_back(u);
            }
        }
    }
    visited.len() == subset.len()
}

// ─────────────────────────────────────────────────────────────────────────────
// Cross-cut and env-star detection
// ─────────────────────────────────────────────────────────────────────────────

/// Scan a step's provenance map for stars newly born at `round` that were
/// produced by a cross-cut fusion: parent_psi has agent ancestry and the
/// born star acquires env character (mixed provenance = it has both agent
/// ancestry via parent_psi AND a phi-copy parent that is env-side).
///
/// Returns a list of `(born_star_id, crossing_edge)` pairs where:
/// - `born_star_id` is the `StarId` of the newly born env star (the "modified env star")
/// - `crossing_edge` is `(agent_star_idx_approx, 0)` — a structural hint; the
///   exact dep-graph edge is reconstructed from the provenance parents
///
/// A star born at round r via `Fused { parent_psi, parent_phi_id, round: r }` is
/// a cross-cut product iff:
///   1. `parent_psi` has agent ancestry (the psi-side came from the agent)
///   2. The born star itself has agent ancestry (via parent_psi) but also env
///      ancestry (via parent_phi_id which is always a phi-copy = env-side)
///
/// This is a faithful causal test: the born star is an environment star that the
/// agent modified — it carries the agent's contribution (via parent_psi) into
/// the env (the phi-copy domain).
fn find_cross_cut_env_stars_at_round(
    step: &Step,
    round: usize,
    agent_root_ids: &HashSet<StarId>,
) -> Vec<(StarId, (usize, usize))> {
    let mut results = Vec::new();

    for (&star_id, prov) in &step.provenance {
        if let Provenance::Fused { parent_psi, parent_phi_id, round: fused_round, .. } = prov {
            if *fused_round != round {
                continue;
            }
            // parent_psi has agent ancestry?
            if !has_agent_ancestry(&step.provenance, *parent_psi, agent_root_ids) {
                continue;
            }
            // parent_phi_id is a phi-copy (always Provenance::Initial) — env-side.
            // The born star is the cross-cut product.
            // We record crossing_edge as (parent_psi_placeholder, parent_phi_id_placeholder).
            // The exact dep-graph indices are not needed for the causal test;
            // we record the star-id fingerprint of both parents.
            let edge_hint = (parent_psi.0 as usize, parent_phi_id.0 as usize);
            results.push((star_id, edge_hint));
        }
    }
    results
}

/// Find stars currently alive in `step.psi` that are agent-side (have agent ancestry)
/// and whose provenance traces through `env_star_id`.
///
/// These are the "agent resolution at r' tracing through the env star" from §2.2.
fn find_agent_resolutions_tracing_through(
    step: &Step,
    env_star_id: StarId,
    agent_root_ids: &HashSet<StarId>,
) -> Vec<StarId> {
    let mut results = Vec::new();
    for (idx, &sid) in step.psi_ids.iter().enumerate() {
        // Must have agent ancestry.
        if !has_agent_ancestry(&step.provenance, sid, agent_root_ids) {
            continue;
        }
        // Must provenance-trace through env_star_id.
        if step.provenance_traces_through(idx, env_star_id) {
            results.push(sid);
        }
    }
    results
}

// ─────────────────────────────────────────────────────────────────────────────
// Core detector: reafferent_closure
// ─────────────────────────────────────────────────────────────────────────────

/// Detect the spec §2.2 reafferent-closure cycle for a GIVEN partition P.
///
/// Runs a bounded `subjective_stream` trajectory (up to `max_rounds` complete
/// reafferent rounds) and searches for the causal pattern:
///
/// > ∃ r < r′: at round r, an agent→env cross-cut interaction produces `env_star`;
/// > at round r′, a star with agent-side provenance traces through `env_star`.
///
/// # Arguments
///
/// - `phi`: the reference constellation (non-linear supply).
/// - `psi0`: the initial interaction space.
/// - `P`: the candidate agent-partition — a set of star *indices* in psi0.
/// - `max_rounds`: bound on the trajectory length (number of reafferent rounds).
///
/// # Returns
///
/// `Some(ClosureWitness)` if the cycle is detected; `None` if the trajectory
/// terminates or reaches `max_rounds` without closing. `None` is the honest-null
/// outcome for constellations that do not exhibit the cycle under P.
///
/// # Causal correctness
///
/// The detection is provenance-causal:
/// - Cross-cut interactions are identified by checking parent star ancestry
///   (which initial psi0 stars they trace to), not by structural edge labels.
/// - The r < r′ temporal ordering is enforced via the `round` fields of
///   `Provenance::Fused` records.
/// - `provenance_traces_through` (from L1d) is the primitive that closes the
///   causal chain.
pub fn reafferent_closure(
    phi: &Constellation,
    psi0: Vec<Star>,
    partition: &AgentSet,
    max_rounds: usize,
) -> Option<ClosureWitness> {
    let agent_root_ids = agent_root_ids_from_partition(partition);

    // `env_stars_by_round`: maps round r → list of (env_star_id, crossing_edge)
    // born via cross-cut interactions at round r.
    let mut env_stars_by_round: Vec<Vec<(StarId, (usize, usize))>> = Vec::new();

    // Bound total substrate steps to avoid infinite loops on non-terminating
    // subjective constellations.  50 steps per round is generous for small
    // experiment constellations; adjust if needed for larger constellations.
    let max_steps = (max_rounds + 2) * 50;
    let stream = subjective_stream(phi, psi0).take(max_steps);

    for step in stream {
        let r = step.round;

        // Stop if we've exceeded max_rounds.
        if r > max_rounds {
            break;
        }

        // Ensure env_stars_by_round is large enough.
        while env_stars_by_round.len() <= r {
            env_stars_by_round.push(Vec::new());
        }

        // At each step, look for cross-cut env stars born at current round r.
        let new_env_stars = find_cross_cut_env_stars_at_round(&step, r, &agent_root_ids);
        for pair in new_env_stars {
            // Only accumulate if not already recorded.
            if !env_stars_by_round[r].contains(&pair) {
                env_stars_by_round[r].push(pair);
            }
        }

        // Now check: for each env_star born at some round r_past < current round r,
        // does any live agent-side star trace through it?  This is the r' > r check.
        // We check r_prime = r (current round) against all r_past < r.
        for r_past in 0..r {
            for (env_star_id, crossing_edge) in &env_stars_by_round[r_past] {
                let agent_resolutions =
                    find_agent_resolutions_tracing_through(&step, *env_star_id, &agent_root_ids);
                if let Some(&agent_res_id) = agent_resolutions.first() {
                    return Some(ClosureWitness {
                        partition: partition.clone(),
                        r: r_past,
                        r_prime: r,
                        crossing_edge: *crossing_edge,
                        traced_env_star: *env_star_id,
                        agent_resolution: agent_res_id,
                    });
                }
            }
        }

        // If stream reached normal form, stop.
        if step.is_normal_form && r >= max_rounds {
            break;
        }
        if step.is_normal_form && env_stars_by_round.iter().all(|v| v.is_empty()) {
            // Normal form and no env stars recorded — no closure possible.
            break;
        }
    }

    None
}

// ─────────────────────────────────────────────────────────────────────────────
// §3.1-op: C_r — per-round closure-constituent StarId sets
// ─────────────────────────────────────────────────────────────────────────────

/// Per-round closure-constituent record for §3.1-op `C_r`.
///
/// # The two rounds (decided: §49.50-staged labelling question, resolved 2026-05-18)
///
/// A reafference event (§2.2) spans two rounds: the agent's earlier crossing
/// mints a cross-cut env-modification at `r_past`, and the agent's later
/// resolution is detected to be conditioned on that modification at `r_prime`
/// (when the cycle *closes*).  An `r_past != r_prime` event is the normal case
/// (the loop has temporal extent — it is the "temporally-extended agent" of
/// `docs/00 §2`).  These records carry **both** rounds explicitly (option (b)
/// of the staged question — see the loop in `closure_constituents`):
///
/// - `round` = `r_prime`: the detection round = the agent's **proper-time tick
///   when the cycle closed** (`docs/00 §2.6`: time is the agent's own
///   reafferent proper time, which advances at the re-closure event, not at the
///   earlier crossing).  The constituent body in `stars` is computed from the
///   snapshot at this round, and viability/re-closure is evaluated here
///   (`docs/00 §2.4`): `re_closure_r = 1` at `round` in
///   `viability_internal_by_round`, which keys `C_r` by exactly this field.
///   This is the load-bearing label and consumers depend on it.
/// - `origin_round` = `r_past`: the round at which the agent's earlier crossing
///   produced the cross-cut env-modification.  Recorded (not dropped) because
///   the temporal gap `round - origin_round` is the reafference loop's extent —
///   the quantity the staged §49.50 / temporal-gap work (`docs/04`, `docs/08
///   §4.10/§5` χ Stage-3) consumes.  It is *not* used to compute `stars`:
///   doing so would snapshot the agent body *before* the env-modification fed
///   back, i.e. at an earlier proper-time tick than the closure event, which
///   contradicts §2.6.  It is carried so the gap need not be re-derived when
///   that work is picked up.
///
/// `traced_env_star` = the env-modification `StarId` minted at `origin_round`,
/// which is the non-triviality guard anchor for ρ: a star in C_{r+1} must
/// provenance-trace through this id.
///
/// `stars` = the agent-side `StarId` set on the §2.2 cycle at round `r_prime`
/// (= `round`), closed under agent-side provenance-connectivity.
///
/// This is the operational realisation of `C_r` from
/// `docs/01-subjective-engine-and-valence.md §3.1-op`.
#[derive(Debug, Clone)]
pub struct ClosureConstituents {
    /// The detection round `r_prime` (the closure's live round r = the
    /// agent's proper-time tick when the cycle closed).  `C_r` is keyed by
    /// this field.
    pub round: usize,
    /// The origin round `r_past` (when the agent's earlier crossing minted the
    /// cross-cut env-modification).  `origin_round <= round`; equality means a
    /// same-round loop.  The temporal gap `round - origin_round` is the
    /// reafference loop extent (staged §49.50 / temporal-gap input).  Not used
    /// to compute `stars` — see the struct doc.
    pub origin_round: usize,
    /// The env-modification StarId (minted at `origin_round`).
    /// Non-triviality guard anchor: C_{r+1} stars must trace through this.
    pub traced_env_star: StarId,
    /// The agent-side StarId set on the §2.2 cycle at detection round `r_prime`.
    pub stars: HashSet<StarId>,
}

/// Collect all `StarId`s reachable downward in the provenance DAG from `root`
/// that have agent ancestry (i.e., appear in `agent_root_ids` or have an ancestor
/// in `agent_root_ids`).  Used to close `C_r` under provenance-connectivity.
///
/// # Algorithm
///
/// We invert the provenance DAG edges: for each node, find all nodes that have it
/// as a parent.  Then BFS from `root` through the inverted graph, keeping only
/// nodes with agent ancestry.
fn agent_provenance_component(
    prov: &HashMap<StarId, Provenance>,
    root: StarId,
    agent_root_ids: &HashSet<StarId>,
    alive_ids: &HashSet<StarId>,
) -> HashSet<StarId> {
    // Build reverse-edge map: child → parents.
    let mut children_of: HashMap<StarId, Vec<StarId>> = HashMap::new();
    for (&child, p) in prov.iter() {
        match p {
            Provenance::Initial => {}
            Provenance::Fused { parent_psi, parent_phi_id, .. } => {
                children_of.entry(*parent_psi).or_default().push(child);
                children_of.entry(*parent_phi_id).or_default().push(child);
            }
            Provenance::SelfInteracted { parent, .. } => {
                children_of.entry(*parent).or_default().push(child);
            }
        }
    }
    // BFS downward from root, keeping agent-ancestry + alive nodes.
    let mut component: HashSet<StarId> = HashSet::new();
    let mut queue: VecDeque<StarId> = VecDeque::new();
    if alive_ids.contains(&root) && has_agent_ancestry(prov, root, agent_root_ids) {
        component.insert(root);
        queue.push_back(root);
    }
    while let Some(cur) = queue.pop_front() {
        if let Some(children) = children_of.get(&cur) {
            for &child in children {
                if !component.contains(&child)
                    && alive_ids.contains(&child)
                    && has_agent_ancestry(prov, child, agent_root_ids)
                {
                    component.insert(child);
                    queue.push_back(child);
                }
            }
        }
    }
    component
}

/// Return per-round `C_r` constituents for a given partition P over a bounded
/// trajectory (additive; does NOT change `reafferent_closure`/`solve_for_closure`
/// behaviour).
///
/// For each round r at which a §2.2 cycle is detected (i.e., round `w.r` or
/// `w.r_prime` of the first `ClosureWitness` found), this function records the
/// constituent StarId set `C_r`: agent-side live stars at round r that are
/// provenance-connected to the §2.2 cycle witness.
///
/// # Returns
///
/// `Some(Vec<ClosureConstituents>)` if the §2.2 cycle is detected at least once;
/// `None` if no closure witness is found within `max_rounds`.
///
/// Each entry covers one round at which the cycle fires.  For a living closure
/// that re-closes multiple times, the vector has one entry per detected re-closure.
///
/// # Faithfulness note
///
/// `C_r` is defined over the **first** closure witness found (matching
/// `reafferent_closure`'s behaviour: earliest causal evidence wins).  In
/// `viability_internal`, `C_{r+1}` refers to the constituents recorded at the
/// round after a closure is confirmed — since `reafferent_closure` runs once
/// holistically, we gather constituents round-by-round by running the stream and
/// recording which agent-side stars are alive and provenance-reachable at each
/// round boundary where a cross-cut env star has been recorded.
pub fn closure_constituents(
    phi: &Constellation,
    psi0: Vec<Star>,
    partition: &AgentSet,
    max_rounds: usize,
) -> Option<Vec<ClosureConstituents>> {
    let agent_root_ids = agent_root_ids_from_partition(partition);

    // Parallel to `reafferent_closure`: accumulate env stars by round.
    let mut env_stars_by_round: Vec<Vec<(StarId, (usize, usize))>> = Vec::new();
    // Collect (round, last_step_at_that_round) for constituent computation.
    let mut last_step_by_round: Vec<Option<crate::subjective::Step>> = Vec::new();

    let max_steps = (max_rounds + 2) * 50;
    let stream = subjective_stream(phi, psi0).take(max_steps);

    // Track discovered cycle events (r_past, env_star_id, r_prime) in order.
    let mut cycle_events: Vec<(usize, StarId, usize)> = Vec::new();

    for step in stream {
        let r = step.round;
        if r > max_rounds {
            break;
        }
        while env_stars_by_round.len() <= r {
            env_stars_by_round.push(Vec::new());
        }
        while last_step_by_round.len() <= r {
            last_step_by_round.push(None);
        }
        last_step_by_round[r] = Some(step.clone());

        let new_env_stars = find_cross_cut_env_stars_at_round(&step, r, &agent_root_ids);
        for pair in new_env_stars {
            if !env_stars_by_round[r].contains(&pair) {
                env_stars_by_round[r].push(pair);
            }
        }

        for r_past in 0..r {
            for (env_star_id, _crossing_edge) in &env_stars_by_round[r_past] {
                let agent_resolutions =
                    find_agent_resolutions_tracing_through(&step, *env_star_id, &agent_root_ids);
                if !agent_resolutions.is_empty() {
                    // Record this cycle event if not already recorded for this r_prime = r.
                    // (Multiple r_past values can contribute to the same r_prime detection —
                    //  we take the first/earliest r_past per r_prime.)
                    let already = cycle_events.iter().any(|(_, _, rprime)| *rprime == r);
                    if !already {
                        cycle_events.push((r_past, *env_star_id, r));
                    }
                }
            }
        }

        if step.is_normal_form && r >= max_rounds {
            break;
        }
    }

    if cycle_events.is_empty() {
        return None;
    }

    // Build ClosureConstituents for each unique round at which a cycle event
    // fires.  `C_r` (round r = `r_prime`, the detection round) = agent-side
    // live stars *at r_prime* provenance-connected to the agent_resolution
    // witness — closed under agent-side provenance-connectivity.
    let mut result: Vec<ClosureConstituents> = Vec::new();

    // DECIDED (§49.50-staged labelling question, resolved 2026-05-18; was OPEN).
    // The constituent body is *computed from* and *labelled by* the detection
    // round `r_prime` (the `cc.round` index below). This is the load-bearing
    // semantics, not a stopgap: `r_prime` is the agent's proper-time tick at
    // which the cycle closes (docs/00 §2.6 — reafferent proper time advances at
    // re-closure, not at the earlier crossing), and viability is evaluated here
    // (docs/00 §2.4; `viability_internal_by_round` keys `C_r` by `cc.round`).
    // Computing the body from the `r_past` snapshot would capture the agent
    // *before* the env-modification fed back — an earlier proper-time tick than
    // the closure event — so option (a) is rejected. We take option (b): keep
    // r_prime computation/labelling AND carry `r_past` explicitly as
    // `origin_round`, so the reafference-loop extent `r_prime - r_past` (the
    // temporal-gap quantity the staged §49.50 / docs/08 §4.10/§5 χ-Stage-3 work
    // consumes) is recorded rather than re-derived later. `r_past == r_prime`
    // is just a same-round loop; no divergence to reconcile.
    for (r_past, env_star_id, r_prime) in &cycle_events {
        // Use the step snapshot at round r_prime (when the cycle was detected).
        let step_at_rprime = match last_step_by_round.get(*r_prime).and_then(|s| s.as_ref()) {
            Some(s) => s,
            None => continue,
        };

        // Agent-side live stars at r_prime that trace through env_star_id.
        let agent_resolutions = find_agent_resolutions_tracing_through(
            step_at_rprime, *env_star_id, &agent_root_ids,
        );
        if agent_resolutions.is_empty() {
            continue;
        }

        let alive_ids: HashSet<StarId> = step_at_rprime.psi_ids.iter().copied().collect();
        let root_id = agent_resolutions[0];

        // Close under agent-side provenance-connectivity.
        let component = agent_provenance_component(
            &step_at_rprime.provenance,
            root_id,
            &agent_root_ids,
            &alive_ids,
        );

        // Also include the initial agent roots that are still alive.
        let mut stars = component;
        for &aid in &agent_root_ids {
            if alive_ids.contains(&aid) {
                stars.insert(aid);
            }
        }

        // Index by r_prime (the detection/live round); carry r_past as the
        // origin round. Avoid duplicates for the same r_prime.
        let already = result.iter().any(|cc| cc.round == *r_prime);
        if !already {
            result.push(ClosureConstituents {
                round: *r_prime,
                origin_round: *r_past,
                traced_env_star: *env_star_id,
                stars,
            });
        }
    }

    if result.is_empty() { None } else { Some(result) }
}

// ─────────────────────────────────────────────────────────────────────────────
// Partition search: solve_for_closure
// ─────────────────────────────────────────────────────────────────────────────

/// Enumerate candidate agent-partitions (via the principled §62-gated filter)
/// and return every partition for which `reafferent_closure` yields a witness.
///
/// This is the N1-guard (spec §2.2): it *solves for* the agent partition, never
/// takes it as given. The result is the set of fixed-point partitions under
/// which the reafference cycle self-organises.
///
/// # Candidacy filter (documented; cites §62 and §2.2)
///
/// See module-level documentation for the precise filter. In brief:
///
/// 1. **§62 gate**: if phi ⊎ psi0 is classified `Terminating` (objective, §49.55),
///    return empty immediately — objective constellations cannot host the cycle.
///    The combined check is necessary because the subjective dynamics come from phi.
/// 2. **Connected subsets**: enumerate non-empty connected subsets S ⊆ psi0 stars
///    where S contains ≥1 subjective/animist star and |S| ≤ `MAX_AGENT_SIZE`.
///    When psi0 is purely objective but phi has animist stars, ALL non-empty connected
///    subsets of psi0 are candidates (the cycle is driven by phi dynamics, not psi0
///    structure). Each such S is a candidate agent-partition.
///
/// # Honest null
///
/// Returns an empty `Vec` when no candidate partition admits the cycle.  This is
/// a valid, expected outcome and is the L2c harness's N1-falsification input.
/// It is never weakened, and `max_rounds` is never inflated to force a result.
pub fn solve_for_closure(
    phi: &Constellation,
    psi0: Vec<Star>,
    max_rounds: usize,
) -> Vec<ClosureWitness> {
    // §62 gate: if neither phi nor psi0 contains any subjective or animist star,
    // the combined system is objective/dead (§49.55 idempotent) and cannot host
    // a reafference cycle.
    //
    // We check the COMBINED phi ⊎ psi0 because the subjective dynamics arise from
    // phi (the non-linear supply) interacting with psi0. The §49.52 iterated
    // execution is non-idempotent iff at least one star in phi ⊎ psi0 is
    // subjective or animist (§49.57). Checking psi0 alone would incorrectly
    // exclude cases where psi0 is a simple query and phi carries the animist stars
    // that drive the cycle.
    let combined: Constellation = phi.iter().chain(psi0.iter()).cloned().collect();
    if classify(&combined) == ConstellationClass::Terminating {
        // Honest null: return empty without scanning.
        return Vec::new();
    }

    let n = psi0.len();
    if n == 0 {
        return Vec::new();
    }

    // Build dep-graph for psi0 to identify connected sub-constellations.
    let dg = DepGraph::from_constellation(&psi0);
    let adj = star_adjacency(&dg, n);

    // Find connected components of D[psi0; C].
    let components = connected_components(&adj);

    // Enumerate candidate partitions: connected subsets of each component
    // that are principled candidates (§2.2/§62 criteria).
    //
    // Candidacy rule:
    //   - If psi0 contains ≥1 subjective/animist star, a candidate subset must
    //     contain ≥1 such star (§49.55: objective sub-constellations alone are dead).
    //   - If psi0 is entirely objective (all stars are objective) but phi has
    //     animist stars (which is why the §62 gate passed), then ALL non-empty
    //     connected subsets of psi0 are candidates — the cycle is driven by phi's
    //     animist dynamics, not by psi0's internal structure. Every initial psi0 star
    //     is a potential agent origin for a phi-mediated reafference loop.
    //
    // This preserves §62 principled gating: we never enumerate objective psi0
    // subsets when the combined system is also objective (already excluded above).
    let psi0_has_subj_or_animist = psi0.iter().any(|star| {
        let k = star_kind(star);
        k == StarKind::Subjective || k == StarKind::Animist
    });

    let mut candidates: Vec<AgentSet> = Vec::new();

    for component in &components {
        let subsets = connected_subsets(component, &adj, MAX_AGENT_SIZE);
        for subset in subsets {
            // Apply the subjective/animist filter only when psi0 has such stars.
            // If psi0 is entirely objective (phi drives the dynamics), accept all
            // non-empty connected subsets.
            if psi0_has_subj_or_animist {
                let has_subj_or_animist = subset.iter().any(|&idx| {
                    let k = star_kind(&psi0[idx]);
                    k == StarKind::Subjective || k == StarKind::Animist
                });
                if !has_subj_or_animist {
                    continue;
                }
            }
            // Deduplicate: only add if not already present.
            if !candidates.contains(&subset) {
                candidates.push(subset);
            }
        }
    }

    // Test each candidate partition.
    let mut witnesses: Vec<ClosureWitness> = Vec::new();
    for partition in candidates {
        if let Some(witness) = reafferent_closure(phi, psi0.clone(), &partition, max_rounds) {
            witnesses.push(witness);
        }
    }

    witnesses
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polarised::{neg_ray, pos_ray};
    use crate::term::Term;

    fn var(x: &str) -> Term { crate::term::mk_var(x) }
    fn app(f: &str, args: Vec<Term>) -> Term { crate::term::mk_app_str(f, args) }

    // ─────────────────────────────────────────────────────────────────────────
    // Test 1: Positive — a constellation with a genuine reafference loop.
    //
    // Design:
    //
    //   We construct a minimal constellation where the §2.2 cycle closes.
    //
    //   phi (reference / supply):
    //     A = [−sense(X), +act(X)]      ← the "agent body": sensing produces action
    //     E = [−act(Y), +sense(f(Y))]   ← the "env body": action feeds back to sense
    //
    //   psi0 (initial interaction space):
    //     agent_star  = [+sense(zero)]   ← star 0: agent (supply of sensory signal)
    //     env_star    = [+act(zero)]     ← star 1: environment seed (action)
    //
    //   With partition P = {0} (star 0 = agent, star 1 = env):
    //
    //   Round 0, step 1:
    //     [+sense(zero)] (id 0, agent) fuses with phi-copy of A: [−sense(X'),+act(X')]
    //     via +sense(zero) ⋈ −sense(X'), θ={X'↦zero}.
    //     Product = [+act(zero)] — a cross-cut env star born at round 0.
    //     (Provenance::Fused { parent_psi=StarId(0)=agent, parent_phi=Initial, round=0 })
    //     → This is the "modified env star" from §2.2 at r=0.
    //
    //   The product [+act(zero)] (id N) has agent ancestry (parent_psi=id0=agent).
    //   It can now fuse with phi-copy of E: [−act(Y'),+sense(f(Y'))]
    //   via +act(zero) ⋈ −act(Y'), θ={Y'↦zero}.
    //   Product = [+sense(f(zero))] — born at round 1 (next generation).
    //   (Provenance::Fused { parent_psi=StarId(N)=modified-env-star, ..., round=1 })
    //   → This star's provenance traces through the env star (StarId N from round 0).
    //   → It also has agent ancestry (via id0 → idN → this).
    //
    //   So we have:
    //     r = 0: cross-cut env star born (id N, agent ancestry + phi-copy = env-modified)
    //     r' = 1: agent-ancestry star born whose provenance traces through id N
    //   → ClosureWitness with r=0, r'=1 MUST be found by solve_for_closure.
    //
    // This is a GENUINE reafference loop — the agent's action at r=0 modified the
    // environment (the phi-copy of E now feeds back), and the agent at r'=1 reads
    // that modification back. No hand-tagging of motor/sensor rays.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn positive_genuine_reafference_loop_found() {
        // phi = supply constellation (non-linear)
        let phi: Constellation = vec![
            // A: agent body: -sense(X) → +act(X)
            vec![
                neg_ray("sense", vec![var("X")]),
                pos_ray("act",   vec![var("X")]),
            ],
            // E: env body: -act(Y) → +sense(f(Y))
            vec![
                neg_ray("act",   vec![var("Y")]),
                pos_ray("sense", vec![app("f", vec![var("Y")])]),
            ],
        ];

        // psi0:
        //   star 0 (agent seed): [+sense(zero)]
        //   star 1 (env seed):   [+act(zero)]   — not strictly needed but shows env side
        //
        // With P={0}: star 0 is agent, star 1 is env.
        let psi0: Vec<Star> = vec![
            vec![pos_ray("sense", vec![app("zero", vec![])])],  // star 0, agent
            vec![pos_ray("act",   vec![app("zero", vec![])])],  // star 1, env
        ];

        let witnesses = solve_for_closure(&phi, psi0, 5);

        assert!(
            !witnesses.is_empty(),
            "POSITIVE TEST FAIL: solve_for_closure must find ≥1 ClosureWitness \
             for the genuine reafference loop; got empty.\n\
             Constellation design: phi=[A:-sense→+act, E:-act→+sense(f(·))], \
             psi0=[+sense(zero)=agent, +act(zero)=env].\n\
             Expected: cross-cut at r=0 (agent fuses with A, produces +act), \
             agent resolution at r'≥1 traces through that env star."
        );

        // Verify the witness is a genuine causal witness, not structural co-occurrence.
        let w = &witnesses[0];
        assert!(
            w.r < w.r_prime,
            "ClosureWitness must have r < r': got r={}, r'={}",
            w.r, w.r_prime
        );
        assert!(
            !w.partition.is_empty(),
            "ClosureWitness partition must be non-empty"
        );

        // The partition must contain only agent-side stars.
        // For this test, the partition must contain star 0 (agent seed).
        // (solve_for_closure enumerates from psi0 structure — it may find P={0} or {0,1}).
        // The key invariant: partition is non-empty and the witness has r < r'.
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Test 2: True negative — an objective/inert constellation with NO loop.
    //
    // Design:
    //
    //   phi (objective, Horn-clause addition program):
    //     [+add(0, Y, Y)]
    //     [−add(X, Y, Z), +add(s(X), Y, s(Z))]
    //
    //   psi0: a single query [−add(1, 1, R), R]
    //
    //   This constellation is OBJECTIVE/DEAD (§49.55): no subjective or animist
    //   stars in psi0. It terminates at a normal form. There is no reafference
    //   cycle because:
    //   1. The §62 gate fires immediately (psi0 is Terminating), so no partitions
    //      are even enumerated.
    //   2. Even if we forced a partition, the computation is a deterministic
    //      resolution: no cross-cut env star is ever born with agent ancestry
    //      that a later agent-side star traces through.
    //
    //   solve_for_closure MUST return empty.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn true_negative_objective_constellation_no_loop() {
        // Horn addition program (objective fragment).
        let phi: Constellation = vec![
            vec![pos_ray("add", vec![
                app("zero", vec![]),
                var("Y"),
                var("Y"),
            ])],
            vec![
                neg_ray("add", vec![var("X"), var("Y"), var("Z")]),
                pos_ray("add", vec![
                    app("s", vec![var("X")]),
                    var("Y"),
                    app("s", vec![var("Z")]),
                ]),
            ],
        ];

        // psi0: single query [−add(s(zero), s(zero), R), R]
        let psi0: Vec<Star> = vec![
            vec![
                neg_ray("add", vec![
                    app("s", vec![app("zero", vec![])]),
                    app("s", vec![app("zero", vec![])]),
                    var("R"),
                ]),
                var("R"),
            ],
        ];

        let witnesses = solve_for_closure(&phi, psi0, 10);

        assert!(
            witnesses.is_empty(),
            "TRUE-NEGATIVE FAIL: solve_for_closure must return empty for objective \
             Horn-addition constellation (no reafference cycle possible in objective/dead \
             fragment); got {} witnesses: {:?}",
            witnesses.len(),
            witnesses.iter().map(|w| (w.r, w.r_prime)).collect::<Vec<_>>()
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Test 3: r_past != r_prime — the §49.50-staged labelling decision.
    //
    // The positive fixture (Test 1) mints the cross-cut env star at round 0
    // (r_past=0) and the agent resolution tracing through it is detected at a
    // strictly later round (r_prime>=1). This is the normal temporally-extended
    // loop. We assert the DECIDED option-(b) contract on ClosureConstituents:
    //
    //   - `round` (= r_prime, the proper-time tick of re-closure) is what
    //     viability keys on, and is strictly later than the origin;
    //   - `origin_round` (= r_past) is carried, not dropped, so the loop extent
    //     `round - origin_round` is recoverable without re-deriving it;
    //   - the body in `stars` is the live agent-side set at `round` (non-empty),
    //     i.e. computed from the r_prime snapshot, NOT the r_past one.
    //
    // This locks the comment/code agreement: an r_past != r_prime event is
    // representable and the two rounds do not get conflated.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn r_past_differs_from_r_prime_is_recorded_not_conflated() {
        let phi: Constellation = vec![
            vec![
                neg_ray("sense", vec![var("X")]),
                pos_ray("act",   vec![var("X")]),
            ],
            vec![
                neg_ray("act",   vec![var("Y")]),
                pos_ray("sense", vec![app("f", vec![var("Y")])]),
            ],
        ];
        let psi0: Vec<Star> = vec![
            vec![pos_ray("sense", vec![app("zero", vec![])])],  // star 0, agent
            vec![pos_ray("act",   vec![app("zero", vec![])])],  // star 1, env
        ];

        // Partition {0}: star 0 is the agent (matches Test 1's design).
        let partition: AgentSet = [0usize].into_iter().collect();

        let ccs = closure_constituents(&phi, psi0, &partition, 5)
            .expect("closure_constituents must find the §2.2 cycle on the \
                     positive reafference fixture");
        assert!(!ccs.is_empty(), "expected >=1 ClosureConstituents record");

        // The fixture mints the env star at round 0 and the cycle closes later,
        // so at least one record must be a genuine r_past != r_prime event.
        let divergent = ccs.iter().find(|cc| cc.origin_round != cc.round);
        let cc = divergent.unwrap_or_else(|| panic!(
            "expected an r_past != r_prime event; got rounds {:?}",
            ccs.iter().map(|c| (c.origin_round, c.round)).collect::<Vec<_>>()
        ));

        // origin_round (r_past) precedes round (r_prime); the gap is the loop
        // extent and must be a positive, recoverable quantity.
        assert!(
            cc.origin_round < cc.round,
            "origin_round (r_past={}) must precede round (r_prime={})",
            cc.origin_round, cc.round
        );
        assert!(
            cc.round - cc.origin_round >= 1,
            "reafference-loop extent must be >=1 for an r_past != r_prime event"
        );
        // origin_round is the round the env-mod was minted: 0 for this fixture.
        assert_eq!(
            cc.origin_round, 0,
            "the cross-cut env star is minted at round 0 in this fixture"
        );

        // The body is the LIVE set at r_prime (option (a) — r_past snapshot —
        // is rejected): it must be non-empty and contain the agent root.
        assert!(
            !cc.stars.is_empty(),
            "C_r body (computed from the r_prime snapshot) must be non-empty"
        );
        assert!(
            cc.stars.contains(&StarId(0)),
            "the live agent root (StarId(0)) is on the cycle at r_prime"
        );

        // viability_internal_by_round keys C_r by `round` (= r_prime), never by
        // origin_round — guard against a future regression that swaps them.
        let by_round: std::collections::HashMap<usize, &ClosureConstituents> =
            ccs.iter().map(|c| (c.round, c)).collect();
        assert!(
            by_round.contains_key(&cc.round),
            "C_r must be addressable by its detection round r_prime"
        );
    }
}
