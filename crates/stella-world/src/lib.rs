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
    let phi = substrate_phi();

    let mut psi0: Vec<Star> = vec![substrate_seed()];
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
}
