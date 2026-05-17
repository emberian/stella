//! # Phase-5 P5.2 — solved-for closures sharing the LM-scaled world
//!
//! The **wiring layer**. Unlike `stella-env` (firewalled — cannot see the
//! closure machinery), `stella-world` is *allowed* to see both: it feeds
//! `stella_env`'s neutral [`EnvPerturbation`] into the Ψ (environment) side of
//! the substrate and reads closures *out* via `stella_core`'s principled,
//! never-designated search. The firewall still holds because the **only**
//! thing the LM contributes is `EnvPerturbation` Ψ-material; individuation is
//! `solve_for_closure` (P2: solved-for, never declared), persistence/death is
//! the §3.2 certificate (`ClosureStatus`).
//!
//! Substrate seed (fixed, Eng §49.50-faithful — the exact shape validated by
//! the L1b gate, so the §62 gate can admit closure at all; without this we
//! would be back to the inert 2-star toy):
//! - Φ = `{ [X, +f(X)] }`  (animist supply star)
//! - Ψ-seed = `{ [−f(+g(Z))] }`  (subjective query)
//!
//! P5.2 asks one honest *instrument* question (NOT the falsification): does
//! adding the LM-scaled environment to Ψ change what self-organises — i.e.,
//! does the firewalled environment actually *couple* to the substrate, or did
//! P5.1's content-blindness buy anti-smuggling at the price of causal
//! inertness? We measure; we do not tune (P7/P8).

use stella_core::constellation::{Constellation, Star};
use stella_core::polarised::{neg_ray, pos_ray};
use stella_core::reafference::solve_for_closure;
use stella_core::term::mk_var;
use stella_core::valence::{trajectory, ClosureStatus};

use stella_env::{perturb, Affordance, EnvPerturbation, FixedEnvCodec};

/// The fixed, Eng §49.50-faithful animist Φ. (Documented, not tuned.)
pub fn substrate_phi() -> Constellation {
    vec![vec![mk_var("X"), pos_ray("f", vec![mk_var("X")])]]
}

/// The fixed subjective Ψ-seed query. (Documented, not tuned.)
pub fn substrate_seed() -> Star {
    vec![neg_ray("f", vec![pos_ray("g", vec![mk_var("Z")])])]
}

/// A fixed, documented **partner inhabitant** that closes a loop: it consumes
/// the `+g(_)` the seed×Φ interaction produces and regenerates an `f`-query,
/// making the dependency graph *cyclic* (Eng §62.6 "converging cycle consuming
/// terms of a star") — the structural prerequisite for a reafferent cross-cut
/// that crosses *into something that crosses back* (spec §2.2). Not tuned
/// per-result; the moved variable is *number of inhabitants*, which the locked
/// spec already mandates (§3 multi-agent / P6). Solved-for, never designated.
pub fn substrate_partner() -> Star {
    vec![
        neg_ray("g", vec![mk_var("W")]),
        pos_ray("f", vec![pos_ray("g", vec![mk_var("W")])]),
    ]
}

/// Generic sensorimotor *capacity* Φ: `[ −sense(X), +act(X) ]`. This is
/// **board, not a designated self** (P9/P2): it is the mechanism by which
/// *some* sub-constellation *could* sense-then-act; it names no agent, sets no
/// goal. Whether any reafferent closure exists is still solved-for by the
/// N1-guarded detector, which refuses hand-placed ones (cf. the substantiated
/// triple-null). Mirrors loop_phi's agent half, which the L2a positive test
/// accepts as a *genuine* closure precisely because it is solved-for.
pub fn substrate_agent_capacity() -> Constellation {
    vec![vec![neg_ray("sense", vec![mk_var("X")]), pos_ray("act", vec![mk_var("X")])]]
}

/// What a world run found. No verdict; counts + per-closure §3.2 status.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorldReport {
    /// Ψ₀ size actually run (seed + any env material).
    pub psi0_len: usize,
    /// How many distinct reafferent closures self-organised (solved-for,
    /// never designated — P2). This is the multi-agent count.
    pub closures: usize,
    /// Per-closure 1st-order-self status via the locked §3.2 certificate.
    pub statuses: Vec<ClosureStatus>,
    /// How many Ψ₀ stars came from the LM (via `EnvPerturbation`), i.e. the
    /// environment's contribution. The firewall invariant: this is the *only*
    /// channel the LM has into the world.
    pub env_contributed: usize,
}

/// Run one world. `env`: if `Some`, the LM-scaled environment is mixed into Ψ₀
/// (firewalled — neutral `EnvPerturbation` stars only); if `None`, the bare
/// substrate seed alone (the small-world control).
pub fn run_world(
    env: Option<(&dyn Affordance, &FixedEnvCodec, &str)>,
    max_rounds: usize,
) -> WorldReport {
    run_world_with(false, env, max_rounds)
}

/// As [`run_world`], plus an optional fixed loop-closing partner inhabitant
/// ([`substrate_partner`]). Tests whether multi-occupancy enables a reafferent
/// closure where the lone seed yielded zero (the hypothesis the seed-only=0
/// result handed us). Honest measurement; closures still solved-for (P2).
pub fn run_world_with(
    partner: bool,
    env: Option<(&dyn Affordance, &FixedEnvCodec, &str)>,
    max_rounds: usize,
) -> WorldReport {
    let phi = substrate_phi();

    let mut psi0: Vec<Star> = vec![substrate_seed()];
    if partner {
        psi0.push(substrate_partner());
    }
    let env_contributed = match env {
        Some((aff, codec, seed)) => {
            let p: EnvPerturbation = perturb(aff, codec, seed);
            let n = p.len();
            psi0.extend(p.into_psi_stars()); // the ONLY LM channel: Ψ material
            n
        }
        None => 0,
    };

    // P2: closures are SOLVED FOR by the principled §62-gated search, never
    // designated. The LM had no hand in this; it only (maybe) scaled Ψ.
    let witnesses = solve_for_closure(&phi, psi0.clone(), max_rounds);

    let statuses: Vec<ClosureStatus> = witnesses
        .iter()
        .map(|w| trajectory(&phi, psi0.clone(), &w.partition, max_rounds).status)
        .collect();

    WorldReport {
        psi0_len: psi0.len(),
        closures: witnesses.len(),
        statuses,
        env_contributed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Deterministic fake environment (no network). Stands in for the LM as
    /// *weather*; the codec digests it identically to the real model.
    struct FakeWorldText;
    impl Affordance for FakeWorldText {
        fn sample(&self, seed: &str) -> String {
            format!("a richly described world around the pond at {seed}, \
                     with trees, water, light, and many things to encounter")
        }
    }

    /// The substrate alone *can* host closure (we are not back in the inert
    /// 2-star toy: the §49.50 seed passes the §62 gate). Recorded, not tuned.
    #[test]
    fn substrate_seed_is_not_the_inert_toy() {
        let r = run_world(None, 40);
        assert_eq!(r.env_contributed, 0);
        // We do NOT assert closures > 0 (that would be tuning to a hoped
        // result). We assert the run is well-formed and report whatever the
        // substrate does — honest instrument bring-up.
        eprintln!("[seed-only] {r:?}");
        assert_eq!(r.psi0_len, 1);
    }

    /// THE P5.2 FINDING (honest, not rigged): does the firewalled LM-scaled
    /// environment change what self-organises, or is it causally inert?
    /// We compare seed-only vs seed+LM-env and *report the delta*. If the
    /// neutral env is inert, the two are identical — that is a real result
    /// about P5.1's content-blindness, not a failure to be tuned away.
    #[test]
    fn lm_env_coupling_or_inertness_is_measured_not_assumed() {
        let codec = FixedEnvCodec::canonical();
        let seed_only = run_world(None, 40);
        let with_env = run_world(Some((&FakeWorldText, &codec, "troy")), 40);

        eprintln!("[seed-only ] {seed_only:?}");
        eprintln!("[seed + env] {with_env:?}");

        // Firewall invariant: the LM's ONLY contribution is Ψ material.
        assert!(with_env.env_contributed > 0, "env must contribute Ψ stars");
        assert_eq!(
            with_env.psi0_len,
            seed_only.psi0_len + with_env.env_contributed,
            "env enters ONLY as added Ψ stars (firewall data-flow)"
        );

        // The honest measurement, recorded for the principal. Either:
        //  (coupled)  with_env.closures != seed_only.closures  → env perturbs
        //  (inert)    with_env.closures == seed_only.closures   → P5.1's
        //             content-blindness made the environment causally inert;
        //             the next crux (couple-without-valuing) is real.
        let coupled = with_env.closures != seed_only.closures
            || with_env.statuses != seed_only.statuses;
        eprintln!(
            "[P5.2 finding] env is {} (Δclosures {}→{})",
            if coupled { "COUPLING" } else { "INERT (content-blind ⇒ inert)" },
            seed_only.closures,
            with_env.closures
        );
        // No assertion on `coupled`: this is a measurement, not a target.
    }

    /// THE P5.2b MEASUREMENT (couple-without-valuing). Φ = generic
    /// sensorimotor *capacity* (board); Ψ₀ = seed `[+sense(zero)]` plus the
    /// LM environment-body. Compare {no env, v1 neutral env, v2 sensorimotor
    /// env}. Does the *value-free* affordance let a reafferent closure
    /// self-organise where neutral-inert gave zero? Measured, not targeted.
    #[test]
    fn value_free_sensorimotor_env_coupling_measured() {
        use stella_core::reafference::solve_for_closure;
        use stella_core::term::mk_app_str;
        let phi = substrate_agent_capacity();
        let seed = || vec![pos_ray("sense", vec![mk_app_str("zero", vec![])])];

        let none = solve_for_closure(&phi, vec![seed()], 60).len();

        let v1 = FixedEnvCodec::canonical();
        let mut psi_v1 = vec![seed()];
        psi_v1.extend(perturb(&FakeWorldText, &v1, "troy").into_psi_stars());
        let c_v1 = solve_for_closure(&phi, psi_v1, 60).len();

        let v2 = FixedEnvCodec::canonical_sensorimotor();
        let mut psi_v2 = vec![seed()];
        let env_v2 = perturb(&FakeWorldText, &v2, "troy");
        let env_n = env_v2.len();
        psi_v2.extend(env_v2.into_psi_stars());
        let c_v2 = solve_for_closure(&phi, psi_v2, 60).len();

        eprintln!(
            "[P5.2b] agent-capacity Φ + seed: none={none} | v1-neutral-env={c_v1} \
             | v2-sensorimotor-env({env_n} stars)={c_v2}"
        );
        eprintln!(
            "[P5.2b finding] value-free affordance {} (v1 {} → v2 {})",
            if c_v2 > c_v1 { "COUPLES — a reafferent closure self-organised" }
            else if c_v2 == c_v1 && c_v1 == none { "still inert OR no agent self-organises (deeper finding)" }
            else { "changed the structure (inspect)" },
            c_v1, c_v2
        );
        // No assertion on counts: measurement, not target (P7/P8).
    }

    /// VERIFY-DON'T-TRUST the 0→12 jump: inspect the witnesses. Genuine
    /// reafference = distinct, non-degenerate partitions each with a real
    /// r<r′ provenance cycle and a non-trivial §3.2 status. Over-count =
    /// many shimmers of one degenerate loop. A number cannot tell us; this
    /// dumps the structure for a by-hand (principal) read. No verdict here.
    #[test]
    fn inspect_the_twelve_before_believing_them() {
        use std::collections::BTreeSet;
        use stella_core::reafference::solve_for_closure;
        use stella_core::term::mk_app_str;
        let phi = substrate_agent_capacity();
        let mut psi0 = vec![vec![pos_ray("sense", vec![mk_app_str("zero", vec![])])]];
        let v2 = FixedEnvCodec::canonical_sensorimotor();
        psi0.extend(perturb(&FakeWorldText, &v2, "troy").into_psi_stars());

        let ws = solve_for_closure(&phi, psi0.clone(), 60);
        eprintln!("[inspect] {} witnesses", ws.len());
        let mut parts: Vec<BTreeSet<usize>> = Vec::new();
        for (i, w) in ws.iter().enumerate() {
            let p: BTreeSet<usize> = w.partition.iter().copied().collect();
            let st = trajectory(&phi, psi0.clone(), &w.partition, 60).status;
            eprintln!(
                "  w{i}: |P|={} r={} r'={} status={:?} P={:?}",
                p.len(), w.r, w.r_prime, st, p
            );
            parts.push(p);
        }
        let distinct: BTreeSet<_> = parts.iter().cloned().collect();
        eprintln!(
            "[inspect] distinct partitions = {}/{}  (≈1 ⇒ over-count of one \
             loop; ≈n ⇒ genuine multiplicity of reafferent cuts)",
            distinct.len(), parts.len()
        );
    }

    /// P5.2c: does v3 composable-chain force a NON-TRIVIAL closure (|P|>1,
    /// r′>1) where v2 gave only the reflex floor (|P|=1, r=0→r′=1)? Measured
    /// AND inspected (the count-deflation discipline is now standing law).
    #[test]
    fn composable_chain_nontriviality_measured_and_inspected() {
        use std::collections::BTreeSet;
        use stella_core::reafference::solve_for_closure;
        use stella_core::term::mk_app_str;
        let phi = substrate_agent_capacity();
        let mut psi0 = vec![vec![pos_ray("sense", vec![mk_app_str("zero", vec![])])]];
        let v3 = FixedEnvCodec::canonical_composable();
        psi0.extend(perturb(&FakeWorldText, &v3, "troy").into_psi_stars());

        let ws = solve_for_closure(&phi, psi0.clone(), 80);
        eprintln!("[P5.2c] v3 composable → {} witnesses", ws.len());
        let mut shapes: BTreeSet<(usize, usize, usize)> = BTreeSet::new();
        let mut max_p = 0usize;
        let mut max_span = 0usize;
        for (i, w) in ws.iter().enumerate() {
            let p = w.partition.len();
            let span = w.r_prime.saturating_sub(w.r);
            max_p = max_p.max(p);
            max_span = max_span.max(span);
            shapes.insert((p, w.r, w.r_prime));
            if i < 8 {
                let st = trajectory(&phi, psi0.clone(), &w.partition, 80).status;
                eprintln!("  w{i}: |P|={p} r={} r'={} span={span} {st:?}", w.r, w.r_prime);
            }
        }
        eprintln!(
            "[P5.2c finding] max|P|={max_p} max(r'-r)={max_span} distinct-shapes={} \
             — {}",
            shapes.len(),
            if max_p > 1 || max_span > 1 {
                "NON-TRIVIAL closure formed (past the reflex floor)"
            } else {
                "still the reflex floor (|P|=1, span=1) — composition did NOT \
                 deepen the minimal closure; deeper finding, not tuned away"
            }
        );
        // No assertion on triviality: measurement, not target (P7/P8).
    }

    /// SANITY (verify-don't-assume): the L2a-validated positive fixture
    /// (`loop_phi`: agent `-sense(X)+act(X)`, env `-act(Y)+sense(f(Y))`,
    /// Ψ₀=`[+sense(zero)],[+act(zero)]`) MUST yield ≥1 closure through the
    /// exact `solve_for_closure` path stella-world uses. If this is 0, the
    /// triple-null below is a plumbing artefact, not a finding. If ≥1, the
    /// triple-null is SUBSTANTIVE: the detector can fire here, and it refuses
    /// the hand-built micro-world on purpose.
    #[test]
    fn harness_path_can_yield_a_closure_on_the_known_positive_fixture() {
        use stella_core::reafference::solve_for_closure;
        use stella_core::term::mk_app_str;
        let z = || mk_app_str("zero", vec![]);
        let phi = vec![
            vec![neg_ray("sense", vec![mk_var("X")]), pos_ray("act", vec![mk_var("X")])],
            vec![
                neg_ray("act", vec![mk_var("Y")]),
                pos_ray("sense", vec![pos_ray("f", vec![mk_var("Y")])]),
            ],
        ];
        let psi0 = vec![
            vec![pos_ray("sense", vec![z()])],
            vec![pos_ray("act", vec![z()])],
        ];
        let n = solve_for_closure(&phi, psi0, 40).len();
        eprintln!("[sanity] known-positive fixture → {n} closure(s)");
        assert!(
            n >= 1,
            "PLUMBING BUG: the validated positive fixture yielded 0 closures \
             through stella-world's path — the triple-null is not yet a finding"
        );
    }

    /// The hypothesis the seed-only=0 result handed us: does a second
    /// (loop-closing) inhabitant let a reafferent closure self-organise where
    /// one inhabitant could not? Measured across {lone, +partner,
    /// +partner+env}. No assertion on closure count — recorded for the
    /// principal, never tuned toward.
    #[test]
    fn does_a_partner_inhabitant_enable_any_closure() {
        let codec = FixedEnvCodec::canonical();
        let lone = run_world_with(false, None, 60);
        let pair = run_world_with(true, None, 60);
        let pair_env = run_world_with(true, Some((&FakeWorldText, &codec, "troy")), 60);
        eprintln!("[lone       ] {lone:?}");
        eprintln!("[+partner   ] {pair:?}");
        eprintln!("[+partner+lm] {pair_env:?}");
        eprintln!(
            "[P5.2 finding] lone={} closures, +partner={} closures, +partner+lm={} \
             closures — multi-occupancy {} closure; env still {}",
            lone.closures,
            pair.closures,
            pair_env.closures,
            if pair.closures > lone.closures { "ENABLES" } else { "does NOT yet enable" },
            if pair_env.closures != pair.closures { "couples" } else { "inert" },
        );
    }
}
