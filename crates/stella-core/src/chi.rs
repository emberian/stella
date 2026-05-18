//! χ Stage-2 — the non-idempotence-surplus FUNCTIONAL (docs/08 §4.5/§4.6).
//!
//! Stage-0/1 (commit a3fd4aa, docs/08 §4.9) EXHIBITED χ as sustained
//! growth on Eng's verbatim §49.61 witness while the §49.53 control
//! stays idempotent. Stage-1 only witnessed χ ≠ 0; the §4.5/§4.6 χ
//! *functional* — the integrated surplus / GoI non-nilpotency-degree —
//! was not yet *quantified*. This module computes it.
//!
//! # The χ functional (the explicit definition this module implements)
//!
//! docs/08 §4.5 candidate, verbatim: for layer traces `t₀…t_N`,
//! `χ = Σₙ |F-events in tₙ that are dependency-below a strictly later
//! F-event|`, equivalently *"the length of the longest R/F-alternating
//! dependency chain in the trace's Hasse diagram, integrated over
//! layers."* §4.6 [Eng for the equivalence] identifies this with the
//! `σu` non-nilpotency-degree: the count of token transitions on
//! non-cancelling GoI feedback paths.
//!
//! At the MEASURED χ-locus — `subjective::subjective_stream` (§4.7; AEx
//! provably the wrong locus, docs/explore/tractable-aex.md) — the §4.4
//! trace monoid is realised concretely by the stream's provenance DAG:
//!
//! - A [`Provenance::Fused`] / [`Provenance::SelfInteracted`] node IS an
//!   **F-event**: a forcing/interaction consumed a Ψ-star and disclosed
//!   a *new* star (§49.50's "new connexion"). It carries the §49.52
//!   `round` (= layer `n`) at which it fired.
//! - A [`Provenance::Initial`] node is pure **supply** (a Ψ₀ star or a
//!   fresh α-renamed Φ-copy) — outstanding-demand-free, hence χ-free,
//!   exactly §4.5's "a purely supply-side value has no outstanding
//!   demand ⇒ χ = 0".
//! - `StarId`s are monotone and a node's parents always have strictly
//!   smaller ids (`subjective.rs` §L1d), so the provenance ancestry
//!   relation **is** the §4.4 dependency partial order; an F-event
//!   ancestor of a later F-event is precisely an F-event
//!   "dependency-below a strictly later F-event."
//!
//! Concretely this module reports two read-outs of the same §4.5
//! quantity, computed on the provenance DAG accumulated up to the last
//! observed [`Step`]:
//!
//! - [`ChiReport::chi`] — **THE χ functional**: the §4.5 layer integral
//!   `χ = Σ_{r=0..R} h(r)`, where `h(r)` is the height (longest
//!   ancestor→descendant chain length, counting F-event nodes) of the
//!   sub-DAG of F-event nodes born in rounds `≤ r`. This is the
//!   monotone-integrated longest R/F-alternating chain (§4.5) /
//!   `σu` non-nilpotency-degree integrated over layers (§4.6).
//! - [`ChiReport::surplus`] — the literal first form of §4.5:
//!   `Σₙ |{F-events in round n that have a strictly-later F-descendant}|`.
//!
//! Both are 0 on an idempotent run (no F-event chains; the Foata
//! normal form has height ≤ 1, §4.4) and strictly grow with semaphore
//! depth — the two boundary conditions §4.5 requires.
//!
//! Read-only over a fixed Φ: this module never mutates a stream and
//! adds no behaviour. The gate is a theorem (docs/08 §4.9 / task): Eng
//! PROVES §49.53 idempotent (⇒ χ must be 0/bounded-flat) and §49.61
//! non-terminating (⇒ χ must be unbounded/strictly-growing); the
//! functional must separate them on the same instrument.

use crate::subjective::{Provenance, Step};
use std::collections::HashMap;

/// One run's χ measurement (docs/08 §4.5/§4.6).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ChiReport {
    /// THE χ functional — the §4.6 `σu` **non-nilpotency degree**.
    ///
    /// §4.6 [Eng]: `σu` nilpotent (`∃k.(σu)^k = 0`) ⟺ objective/
    /// idempotent (§49.55) ⟺ `χ = 0`; `σu` non-nilpotent ⟺ a
    /// persistent non-cancelling feedback path ⟺ `χ > 0`. Operationally
    /// `(σu)^k = 0` means the longest non-cancelling F-event feedback
    /// chain has a *bounded* depth `k`; non-nilpotent means that depth
    /// is *unbounded* in the §49.52 layer count. So the
    /// theorem-respecting functional is NOT the §4.5 layer integral of
    /// a (possibly bounded) chain — that inflates on idle layers even
    /// when `σu` IS nilpotent — but the **growth of the longest chain
    /// with layers**:
    ///
    /// `χ = Σ_{r : depth strictly increased at layer r} 1`
    ///    `= |{rounds at which max F-event chain depth grew}| − 1` (≥0)
    ///
    /// i.e. the number of times the non-cancelling feedback chain had to
    /// get strictly *deeper* to keep going. Nilpotent (§49.53): the
    /// chain saturates at depth `k` and never deepens again ⇒ χ is a
    /// small constant that does NOT grow with the run. Non-nilpotent
    /// (§49.61): every layer forces a strictly deeper chain ⇒ χ grows
    /// without bound with the observed prefix length. The boundary
    /// conditions §4.5 demands hold: 0 on objective/supply-only (no
    /// chain ever deepens), monotone in semaphore depth.
    pub chi: u64,

    /// The §4.5 *first form*, retained as a diagnostic:
    /// `Σ_{r} height(F-event sub-DAG born in rounds ≤ r)` — the
    /// layer-integral of the longest R/F chain. NOTE: this is the
    /// quantity §4.5 *wrote down*; Stage-2 measures (below) that it is
    /// NOT theorem-respecting on `subjective_stream` because the §49.52
    /// clock keeps ticking on a PROVEN-idempotent run, integrating a
    /// bounded chain into a spurious non-zero. Kept for the honest
    /// record, not used as the gate.
    pub layer_integral: u64,

    /// `Σₙ |{F-events in round n with a strictly-later F-event descendant}|`.
    pub surplus: u64,

    /// Number of F-events (Fused/SelfInteracted provenance nodes) total.
    /// 0 ⟺ no forcing ever happened (a fully supply-side / objective run).
    pub n_f_events: u64,

    /// Number of distinct §49.52 rounds that contained ≥1 F-event.
    pub n_active_rounds: u64,

    /// The highest §49.52 round in which ANY F-event occurred. After
    /// this layer the run mints no more forcing — pure supply / NF.
    /// `(σu)^k = 0` for the layer-`k` past this ⟺ σu nilpotent: if this
    /// is far below the total rounds the §49.52 clock ran, forcing
    /// *ceased* and σu IS nilpotent (the §49.53 signature). If it tracks
    /// the run boundary, forcing never ceased (the §49.61 signature).
    pub last_f_round: u64,

    /// The single longest F-event ancestor→descendant chain over the
    /// whole run — the un-integrated §4.5 chain length / GoI longest
    /// non-cancelling feedback path. `(σu)^{max_chain} ≠ 0`.
    pub max_chain: u64,

    /// Per-round longest-F-chain-depth profile: `(round, max chain depth
    /// among F-events born in rounds ≤ round)`, deduplicated to entries
    /// where the depth changed. A FLAT tail ⇒ σu nilpotent (bounded);
    /// a STRICTLY RISING tail ⇒ σu non-nilpotent (unbounded). This is
    /// the witness the gate reads.
    pub depth_profile: Vec<(u64, u64)>,
}

impl ChiReport {
    /// True iff χ is exhibited as a non-trivial functional value:
    /// the longest non-cancelling F-event chain had to *deepen* at
    /// least once beyond its first formation (`chi ≥ 1`), i.e. `σu` is
    /// observed non-nilpotent on this prefix. This is the §4.6
    /// "χ > 0 ⟺ σu non-nilpotent" predicate, NOT a tuned threshold.
    pub fn chi_positive(&self) -> bool {
        self.chi >= 1
    }

    /// The §4.6 nilpotency verdict — what Eng's theorem actually
    /// certifies — given the **total number of §49.52 rounds the clock
    /// ran** for this observed prefix (`total_rounds`; the caller has it
    /// as the last `Step::round`+1; the provenance map alone cannot know
    /// rounds that minted no F-event).
    ///
    /// `σu` is nilpotent iff `∃k.(σu)^k = 0`: forcing CEASES — after
    /// some layer the run mints no more F-events and the chain can never
    /// deepen again, no matter how long the §49.52 clock keeps ticking.
    /// Operationally: `last_f_round` falls clearly short of the total
    /// rounds elapsed (the run saturated, then idled — the §49.53
    /// signature: it forced for 3 rounds then ran ~390 more rounds inert).
    ///
    /// Non-nilpotent iff forcing NEVER ceases: F-events keep appearing
    /// and the chain keeps deepening right up to the self-imposed
    /// observation cut — `last_f_round` tracks the run boundary and the
    /// profile rose on essentially every F-active round (the §49.61
    /// signature: deepens by 1 every round, no plateau, would diverge if
    /// the budget were extended).
    ///
    /// This tests *unboundedness* (the property Eng proves), not a
    /// magnitude threshold — it is differential, not tuned.
    pub fn sigma_u_non_nilpotent(&self, total_rounds: u64) -> bool {
        // No chain ever deepened ⇒ trivially nilpotent (degree ≤ 1).
        if self.depth_profile.len() < 2 {
            return false;
        }
        // Forcing must persist to (near) the observation boundary: the
        // last F-event round is within the final 25% of the elapsed
        // clock — i.e. the run did NOT saturate-then-idle. (§49.53:
        // last_f_round=2, total≈394 ⇒ ratio≈0.005 ⇒ ceased ⇒ nilpotent.
        //  §49.61: last_f_round≈total ⇒ ratio≈1 ⇒ never ceased.)
        let persists = total_rounds == 0
            || self.last_f_round.saturating_mul(4) >= total_rounds.saturating_mul(3);
        // AND the chain rose on essentially every F-active round (a
        // monotone non-saturating deepening, not one burst then a
        // plateau within the active window).
        let deepenings = self.depth_profile.len() as u64;
        let monotone_rise = deepenings >= self.n_active_rounds;
        persists && monotone_rise
    }
}

/// An F-event node lifted out of the provenance DAG: its id, its
/// §49.52 round (layer `n`), and the ids of its F-event parents
/// (Initial parents are dropped — supply is χ-free, §4.5).
struct FNode {
    round: usize,
    /// Parents that are themselves F-events (the §4.4 dependency edges
    /// that cannot commute away). Reaching an Initial parent terminates
    /// the chain — it is supply, not demand.
    f_parents: Vec<u64>,
}

/// Compute the χ functional (docs/08 §4.5/§4.6) for a run, given the
/// **final** observed [`Step`] (its `provenance` map is cumulative —
/// `subjective.rs`: "grows monotonically; entries added on birth and
/// never removed", so the last step carries the whole F-event DAG up to
/// the cut, including already-consumed stars).
///
/// Pure: borrows the step, mutates nothing, runs no stream.
pub fn chi_of_final_step(last: &Step) -> ChiReport {
    chi_of_provenance(&last.provenance)
}

/// The functional, computed directly over a [`ProvenanceMap`]-shaped
/// map. Split out so the example can feed the *cumulative* map it
/// snapshots across a bounded prefix of a non-terminating stream
/// (the §49.61 witness is non-terminating-by-construction; we measure a
/// self-bounded prefix — a hang is not a result).
pub fn chi_of_provenance(
    prov: &HashMap<crate::subjective::StarId, Provenance>,
) -> ChiReport {
    // 1. Lift the F-event sub-DAG. id -> (round, f_parents).
    let mut f: HashMap<u64, FNode> = HashMap::new();
    for (id, p) in prov {
        match p {
            Provenance::Initial => {} // supply: χ-free (§4.5)
            Provenance::Fused { parent_psi, parent_phi_id, round, .. } => {
                let mut fps = Vec::new();
                // A parent is a §4.4 dependency edge ONLY if it is itself
                // an F-event. An Initial parent is supply — the chain
                // bottoms out there (no outstanding demand below it).
                for cand in [*parent_psi, *parent_phi_id] {
                    if matches!(
                        prov.get(&cand),
                        Some(Provenance::Fused { .. } | Provenance::SelfInteracted { .. })
                    ) {
                        fps.push(cand.0);
                    }
                }
                f.insert(id.0, FNode { round: *round, f_parents: fps });
            }
            Provenance::SelfInteracted { parent, round, .. } => {
                let mut fps = Vec::new();
                if matches!(
                    prov.get(parent),
                    Some(Provenance::Fused { .. } | Provenance::SelfInteracted { .. })
                ) {
                    fps.push(parent.0);
                }
                f.insert(id.0, FNode { round: *round, f_parents: fps });
            }
        }
    }

    let mut report = ChiReport {
        n_f_events: f.len() as u64,
        ..Default::default()
    };
    if f.is_empty() {
        return report; // no forcing ever ⇒ χ = 0 (objective/supply-only)
    }

    // active rounds + last forcing round
    {
        let rs: std::collections::HashSet<usize> = f.values().map(|n| n.round).collect();
        report.n_active_rounds = rs.len() as u64;
        report.last_f_round = rs.iter().copied().max().unwrap_or(0) as u64;
    }

    // 2. Chain height in the F-event sub-DAG. Ids are monotone & parents
    //    have strictly smaller ids ⇒ the DAG is acyclic and a simple
    //    memoised recursion over `f_parents` gives the longest
    //    ancestor→descendant chain ENDING at each node (counting nodes:
    //    a lone F-event = 1; an F-event below another = 2; …).
    fn height(
        id: u64,
        f: &HashMap<u64, FNode>,
        memo: &mut HashMap<u64, u64>,
    ) -> u64 {
        if let Some(&h) = memo.get(&id) {
            return h;
        }
        let node = &f[&id];
        let h = 1 + node
            .f_parents
            .iter()
            .map(|&p| height(p, f, memo))
            .max()
            .unwrap_or(0);
        memo.insert(id, h);
        h
    }
    let mut memo: HashMap<u64, u64> = HashMap::new();
    let ids: Vec<u64> = f.keys().copied().collect();
    for id in &ids {
        height(*id, &f, &mut memo);
    }
    report.max_chain = memo.values().copied().max().unwrap_or(0);

    // 3a. The per-round longest-chain-depth profile h(r) = height of
    //     the sub-DAG of F-events born in rounds ≤ r (longest non-
    //     cancelling feedback chain visible by §49.52 layer r). From it:
    //
    //       layer_integral  = Σ_r h(r)            (the §4.5 first form;
    //                                              kept as diagnostic —
    //                                              NOT theorem-respecting,
    //                                              see ChiReport docs)
    //       χ (THE functional, §4.6 non-nilpotency degree)
    //                       = |{ r : h(r) > h(r−1) }| − 1   (≥ 0)
    //                       = how many times the chain had to DEEPEN
    //                         (σu nilpotent ⟺ this is bounded/0;
    //                          non-nilpotent ⟺ unbounded).
    let max_round = f.values().map(|n| n.round).max().unwrap_or(0);
    let mut layer_integral: u64 = 0;
    let mut prev_h: u64 = 0;
    let mut deepenings: u64 = 0;
    let mut profile: Vec<(u64, u64)> = Vec::new();
    for r in 0..=max_round {
        // height within the prefix DAG (rounds ≤ r). A node whose chain
        // would pass through a not-yet-born node is truncated at the
        // earliest in-prefix node — exactly "the chain visible at layer r".
        let mut pmemo: HashMap<u64, u64> = HashMap::new();
        fn pheight(
            id: u64,
            r: usize,
            f: &HashMap<u64, FNode>,
            memo: &mut HashMap<u64, u64>,
        ) -> u64 {
            if let Some(&h) = memo.get(&id) {
                return h;
            }
            let node = &f[&id];
            let best_parent = node
                .f_parents
                .iter()
                .filter(|&&p| f[&p].round <= r)
                .map(|&p| pheight(p, r, f, memo))
                .max()
                .unwrap_or(0);
            let h = 1 + best_parent;
            memo.insert(id, h);
            h
        }
        let h_r = ids
            .iter()
            .filter(|&&id| f[&id].round <= r)
            .map(|&id| pheight(id, r, &f, &mut pmemo))
            .max()
            .unwrap_or(0);
        layer_integral = layer_integral.saturating_add(h_r);
        if h_r > prev_h {
            deepenings += 1;
            profile.push((r as u64, h_r));
            prev_h = h_r;
        }
    }
    report.layer_integral = layer_integral;
    report.depth_profile = profile;
    // The first deepening is just the FIRST F-event chain forming
    // (height 0→1, an isolated forcing — that is idempotent / σu^1=0).
    // χ counts only deepenings BEYOND that: an F-event forced strictly
    // below an already-existing one. χ = 0 ⟺ σu nilpotent at degree ≤1.
    report.chi = deepenings.saturating_sub(1);

    // 3b. The literal first form of §4.5: count F-events that are
    //     dependency-below a strictly-later F-event, summed over the
    //     round each such event lives in. "Strictly later" = a
    //     descendant with a strictly greater StarId (= born later;
    //     monotone ids). We compute the set of ids that ARE an
    //     f_parent of someone (i.e. have ≥1 F-descendant).
    let mut has_f_descendant: std::collections::HashSet<u64> =
        std::collections::HashSet::new();
    for node in f.values() {
        for &p in &node.f_parents {
            has_f_descendant.insert(p);
        }
    }
    report.surplus = has_f_descendant.len() as u64;

    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::subjective::StarId;

    fn pm(v: Vec<(u64, Provenance)>) -> HashMap<StarId, Provenance> {
        v.into_iter().map(|(i, p)| (StarId(i), p)).collect()
    }

    /// Supply-only / objective: every node Initial ⇒ χ = 0 (§4.5
    /// boundary condition "purely supply-side ⇒ χ = 0").
    #[test]
    fn objective_supply_is_chi_zero() {
        let prov = pm(vec![
            (0, Provenance::Initial),
            (1, Provenance::Initial),
            (2, Provenance::Initial),
        ]);
        let r = chi_of_provenance(&prov);
        assert_eq!(r.chi, 0);
        assert_eq!(r.layer_integral, 0);
        assert_eq!(r.surplus, 0);
        assert_eq!(r.max_chain, 0);
        assert!(!r.chi_positive());
    }

    /// A single forcing event off pure supply: one F-event, no F-event
    /// below it ⇒ chain length 1, NOT a non-idempotence surplus.
    /// σu^1 = 0 (nilpotent at degree 1) ⇒ χ = 0; layer_integral = 1.
    #[test]
    fn single_forcing_event_no_surplus() {
        let prov = pm(vec![
            (0, Provenance::Initial),
            (1, Provenance::Initial),
            (2, Provenance::Fused {
                parent_psi: StarId(0),
                parent_phi_id: StarId(1),
                ray_j: 0,
                ray_j_prime: 0,
                round: 0,
            }),
        ]);
        let r = chi_of_provenance(&prov);
        assert_eq!(r.n_f_events, 1);
        assert_eq!(r.max_chain, 1); // a lone F-event
        assert_eq!(r.surplus, 0); // nothing below a later F-event
        assert_eq!(r.layer_integral, 1); // one round, height 1
        assert_eq!(r.chi, 0); // chain never DEEPENED past its formation
        assert!(!r.chi_positive()); // σu nilpotent at degree 1
    }

    /// An F-event dependency-below a strictly-later F-event over two
    /// §49.52 rounds: the chain DEEPENS once beyond formation ⇒ σu
    /// non-nilpotent on this prefix ⇒ χ = 1. layer_integral = 1+2 = 3.
    #[test]
    fn chained_forcing_is_chi_positive() {
        let prov = pm(vec![
            (0, Provenance::Initial),
            (1, Provenance::Initial),
            // F-event A in round 0
            (2, Provenance::Fused {
                parent_psi: StarId(0),
                parent_phi_id: StarId(1),
                ray_j: 0,
                ray_j_prime: 0,
                round: 0,
            }),
            (3, Provenance::Initial),
            // F-event B in round 1, dependency-below A (parent_psi = 2)
            (4, Provenance::Fused {
                parent_psi: StarId(2),
                parent_phi_id: StarId(3),
                ray_j: 0,
                ray_j_prime: 0,
                round: 1,
            }),
        ]);
        let r = chi_of_provenance(&prov);
        assert_eq!(r.n_f_events, 2);
        assert_eq!(r.max_chain, 2); // B below A
        assert_eq!(r.surplus, 1); // A has a strictly-later F-descendant
        assert_eq!(r.layer_integral, 1 + 2); // r=0 h=1, r=1 h=2
        // deepenings: r=0 (0→1) + r=1 (1→2) = 2; χ = 2−1 = 1
        assert_eq!(r.chi, 1);
        assert_eq!(r.depth_profile, vec![(0, 1), (1, 2)]);
        assert!(r.chi_positive());
    }

    /// Self-interaction chains count identically (§51.7 F-events).
    /// A 3-deep chain over rounds 0,1,2: deepens at r=0,1,2 (3 times);
    /// χ = 3−1 = 2; layer_integral = 1+2+3 = 6.
    #[test]
    fn self_interaction_chain_integrates() {
        let prov = pm(vec![
            (0, Provenance::Initial),
            (1, Provenance::SelfInteracted { parent: StarId(0), ray_j: 0, ray_j_prime: 1, round: 0 }),
            (2, Provenance::SelfInteracted { parent: StarId(1), ray_j: 0, ray_j_prime: 1, round: 1 }),
            (3, Provenance::SelfInteracted { parent: StarId(2), ray_j: 0, ray_j_prime: 1, round: 2 }),
        ]);
        let r = chi_of_provenance(&prov);
        assert_eq!(r.max_chain, 3);
        assert_eq!(r.surplus, 2); // ids 1 and 2 each have a later F-descendant
        assert_eq!(r.layer_integral, 1 + 2 + 3);
        assert_eq!(r.chi, 2); // 3 deepenings − 1
        assert_eq!(r.depth_profile, vec![(0, 1), (1, 2), (2, 3)]);
        assert!(r.chi_positive());
    }

    /// σu NILPOTENT at degree 2: a depth-2 chain forms in rounds 0–1
    /// then the run keeps ticking (rounds 2,3,4 add only fresh isolated
    /// F-events off supply — NO deeper chain). χ MUST stay at the
    /// degree-1 constant (1) and NOT grow with the idle layers — the
    /// theorem-respecting behaviour the §4.5 layer-integral fails.
    #[test]
    fn bounded_chain_then_idle_layers_does_not_inflate_chi() {
        let prov = pm(vec![
            (0, Provenance::Initial),
            (1, Provenance::Initial),
            // depth-2 chain in rounds 0,1
            (2, Provenance::Fused { parent_psi: StarId(0), parent_phi_id: StarId(1), ray_j: 0, ray_j_prime: 0, round: 0 }),
            (3, Provenance::Initial),
            (4, Provenance::Fused { parent_psi: StarId(2), parent_phi_id: StarId(3), ray_j: 0, ray_j_prime: 0, round: 1 }),
            // rounds 2,3,4: isolated F-events off pure supply — NO chain
            (5, Provenance::Initial),
            (6, Provenance::Fused { parent_psi: StarId(5), parent_phi_id: StarId(5), ray_j: 0, ray_j_prime: 0, round: 2 }),
            (7, Provenance::Initial),
            (8, Provenance::Fused { parent_psi: StarId(7), parent_phi_id: StarId(7), ray_j: 0, ray_j_prime: 0, round: 3 }),
            (9, Provenance::Initial),
            (10, Provenance::Fused { parent_psi: StarId(9), parent_phi_id: StarId(9), ray_j: 0, ray_j_prime: 0, round: 4 }),
        ]);
        let r = chi_of_provenance(&prov);
        assert_eq!(r.max_chain, 2);
        // χ pinned at 1 (one deepening beyond formation) DESPITE 5 rounds
        assert_eq!(r.chi, 1);
        // the layer-integral, by contrast, keeps accruing the bounded
        // height every idle round — exactly the spurious inflation that
        // makes it NOT theorem-respecting (the Stage-2 finding).
        assert!(r.layer_integral > r.chi + 3);
        assert_eq!(r.depth_profile, vec![(0, 1), (1, 2)]); // flat after r=1
        assert_eq!(r.last_f_round, 4);
        // The §4.6 verdict, given the clock ran 5 rounds: forcing's last
        // round is 4 but the chain stopped deepening at round 1 ⇒ a
        // plateau exists ⇒ σu NILPOTENT (the §49.53-shaped case).
        assert!(!r.sigma_u_non_nilpotent(5));
    }

    /// The §49.61-shaped case: the chain deepens on EVERY round and
    /// forcing never ceases — last_f_round tracks the clock. σu
    /// NON-nilpotent; verdict true. (Mirrors the measured F3 profile
    /// `[(0,1),(1,2),…,(k,k+1)]` with last_f_round == total−1.)
    #[test]
    fn unbroken_per_round_deepening_is_sigma_u_non_nilpotent() {
        // Build a depth-(k) chain across rounds 0..k, one F-event/round.
        let mut v = vec![(0u64, Provenance::Initial)];
        let mut prev = 0u64;
        for round in 0..10u64 {
            let id = round + 1;
            v.push((
                id,
                Provenance::SelfInteracted {
                    parent: StarId(prev),
                    ray_j: 0,
                    ray_j_prime: 1,
                    round: round as usize,
                },
            ));
            prev = id;
        }
        let r = chi_of_provenance(&pm(v));
        assert_eq!(r.max_chain, 10);
        assert_eq!(r.last_f_round, 9);
        // clock ran exactly 10 rounds (0..=9), forcing on every one:
        assert!(r.sigma_u_non_nilpotent(10));
        // and it stays non-nilpotent even with a little idle slack,
        // because forcing reached ≥75% of the clock:
        assert!(r.sigma_u_non_nilpotent(12));
        // but a long idle tail (forcing ceased early relative to clock)
        // flips it to nilpotent — the §49.53 shape:
        assert!(!r.sigma_u_non_nilpotent(40));
    }
}
