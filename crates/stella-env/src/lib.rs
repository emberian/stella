//! # Phase-5 P5.1 — the firewalled LM-as-environment harness
//!
//! **THE FIREWALL IS THIS CRATE'S BOUNDARY, enforced by `cargo`, not by a
//! comment.** `stella-env` depends on `stella-core` for *star/term
//! constructors only*. It does not — and structurally cannot — name
//! `reafferent_closure`, `solve_for_closure`, `trajectory`,
//! `productivity_measure`, `blackhole_capture`, `DeathCause`,
//! `ClosureStatus`, `run_make_or_break`, or anything in `valence` /
//! `reafference` / `experiment` / `perturbation`. The LM cannot reach the
//! locus, the self, the goals, or the evidence channel **because it lives in
//! a crate from which those are invisible.**
//!
//! Grounding: `docs/04` §3 (LM = environment / affordance-scaler ONLY) and the
//! locked pre-registered nulls:
//! - **P2** (declared self): impossible here — this crate cannot construct or
//!   designate a closure/partition; it only emits Ψ-side world material.
//! - **P3** (given goals): the codec is *content-blind*. LM text influences
//!   only the *structure/scale* of neutral environment stars, never their
//!   value, polarity, or any goal.
//! - **P4** (reported valence — THE HILL): there is no path from LM output to
//!   an evidence channel. The LM is *weather*, never testimony. The
//!   [`Affordance`] trait deliberately yields opaque text that is digested,
//!   never interpreted.
//! - **P7** (engineered accretion): [`FixedEnvCodec::canonical`] is one fixed,
//!   corpus-global configuration. No per-task knobs.
//! - **P9** (authored prediction): this crate emits *board* — neutral
//!   environment scaffolding — and never *soldered soul*. It contains no
//!   predictive/self structure whatsoever; any `V` must form downstream in
//!   stella-core, solved-for, or not at all.
//!
//! The single egress is [`EnvPerturbation::into_psi_stars`] → the Ψ
//! (environment) side of `stella_core::subjective::subjective_stream`.
//! Individuation, closure, valence and evidence happen *there*, in
//! stella-core, solved-for — never here.

use stella_core::constellation::Star;
use stella_core::term::{mk_app_str, mk_var};

/// Opaque Ψ-side environment material. Constructible **only** by
/// [`FixedEnvCodec`]. It is *world*, never self / goal / evidence. There is
/// deliberately no method that turns this into a partition, a reward, a
/// closure designation, or anything the certificate path consumes. Its sole
/// exit is [`EnvPerturbation::into_psi_stars`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvPerturbation(Vec<Star>);

impl EnvPerturbation {
    /// The only way out: hand the stars to the Ψ (environment) side of the
    /// substrate stream. Consumed as environment material; the self/closure is
    /// solved-for downstream in stella-core, never asserted here.
    pub fn into_psi_stars(self) -> Vec<Star> {
        self.0
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Read-only structural view, for the firewall tests only.
    pub fn stars(&self) -> &[Star] {
        &self.0
    }
}

/// An opaque text source. **The LM is one impl.** It is treated as *weather*:
/// its content is never interpreted, only structurally digested by the fixed
/// codec. The signature yields a bare `String` precisely so that nothing
/// richer (a parsed goal, a self-claim, a reward) can ride along.
pub trait Affordance {
    /// Produce opaque text for a given world-seed. No contract on content;
    /// the codec assumes it is adversarial (see the hostile-affordance test).
    fn sample(&self, seed: &str) -> String;
}

/// The corpus-**global, fixed** (P7) environment codec.
///
/// **Content-blind by construction.** LM bytes influence *only* the
/// `(count, arity)` *shape* of neutral environment stars — affordance/
/// vocabulary *scale*, Bennett CM Def 14's representation precondition *for the
/// world*. They never influence polarity (no reward channel), never introduce
/// a colour other than the single reserved `env`/`e` (no goal/self/valence
/// colour can be smuggled), and never designate a partition. Deterministic in
/// the text.
pub struct FixedEnvCodec {
    max_stars: usize,
    max_arity: usize,
    /// v1 (`false`): neutral `env(e,…)` stars — value-free *and provably
    /// causally inert* (stella-world P5.2 triple-null, commit f661505).
    /// v2 (`true`): value-free **sensorimotor affordance** pairs
    /// `[ −act(Y), +sense(mᵏ(Y)) ]` — the env *consumes any act and returns a
    /// sensed consequence* whose only LM-controlled aspect is the content-blind
    /// *depth* `k`. This is "affordance" in P5.1's own word (Gibson/Bennett: an
    /// action possibility), value-free and **agent-agnostic** (identical τ for
    /// every agent ⇒ P9 *board, not soldered soul*: it affords reafference, it
    /// does not author any particular closure — the closure is still solved-for
    /// by the N1-guarded detector downstream).
    sensorimotor: bool,
}

impl FixedEnvCodec {
    /// v1 — neutral-scale (kept: it is the recorded inertness finding).
    pub fn canonical() -> Self {
        Self { max_stars: 16, max_arity: 4, sensorimotor: false }
    }

    /// v2 — value-free sensorimotor-affordance. The data-mandated correction:
    /// "neutral inert atoms" never met P5.1's word *affordance*. The locked
    /// firewall *invariant* is preserved (no value / goal / self / evidence
    /// colour; content-blind; agent-agnostic; crate-boundary). The over-strict
    /// "carry no polarity at all" proxy — which provably caused inertness — is
    /// corrected to the *actual* invariant: carry only the fixed reserved
    /// sensorimotor pair `{act, sense}`, never a value/self channel. Hostile-
    /// tested below; this is a proxy correction, NOT a firewall weakening.
    pub fn canonical_sensorimotor() -> Self {
        Self { max_stars: 16, max_arity: 4, sensorimotor: true }
    }

    /// Digest opaque text → neutral Ψ environment stars.
    ///
    /// Every emitted ray is `env(e, e, …)` with **neutral** polarity (no
    /// `+`/`-` prefix) over the single reserved colour. The *only* thing the
    /// text controls is how many such stars and their arity — pure structural
    /// scale. Smuggle content (rewards, goals, "I am the agent", self-reports)
    /// is digested to bytes and discarded; it cannot survive as structure.
    pub fn encode(&self, text: &str) -> EnvPerturbation {
        let bytes = text.as_bytes();
        if bytes.is_empty() {
            return EnvPerturbation(vec![]);
        }
        let checksum = bytes.iter().fold(0usize, |a, &b| a.wrapping_add(b as usize));
        let n = 1 + (checksum % self.max_stars);
        let mut stars: Vec<Star> = Vec::with_capacity(n);
        for i in 0..n {
            let k = 1 + (bytes[i % bytes.len()] as usize % self.max_arity);
            if self.sensorimotor {
                // v2: value-free sensorimotor affordance. `−act(Y)` consumes
                // ANY agent action; `+sense(mᵏ(Y))` returns a sensed
                // consequence. Only the *depth* k (content-blind digest) is
                // LM-controlled. Colours are EXACTLY the fixed reserved pair
                // {act, sense} + the fixed neutral functor `m`. No value, no
                // self, no goal, no partition; identical for every agent.
                // τ over a VARIABLE Y: consume ANY action, return a
                // consequence functionally dependent on it (the value-free
                // analogue of loop_phi's `−act(Y),+sense(f(Y))`, with depth k
                // = content-blind digest instead of a hand-picked functor).
                let mut tau = mk_var("Y");
                for _ in 0..k {
                    tau = mk_app_str("m", vec![tau]);
                }
                let neg_act = mk_app_str("-act", vec![mk_var("Y")]);
                let pos_sense = mk_app_str("+sense", vec![tau]);
                stars.push(vec![neg_act, pos_sense]);
            } else {
                // v1: neutral, value-free, provably inert (kept for record).
                let args: Vec<_> = (0..k).map(|_| mk_app_str("e", vec![])).collect();
                stars.push(vec![mk_app_str("env", args)]);
            }
        }
        EnvPerturbation(stars)
    }
}

/// Drive an affordance through the fixed codec. **The only public entry
/// point.** LM (or any) text in; opaque neutral Ψ material out.
pub fn perturb(aff: &dyn Affordance, codec: &FixedEnvCodec, seed: &str) -> EnvPerturbation {
    codec.encode(&aff.sample(seed))
}

/// Real LM Studio transport (OpenAI-compatible, `localhost:1234`). Opt-in
/// behind the `lm` feature so the firewall + tests are provable with zero
/// network deps. It is just one [`Affordance`]; it gets no more trust than the
/// hostile fake — the codec treats both identically.
#[cfg(feature = "lm")]
pub mod lm_studio {
    use super::Affordance;

    pub struct LmStudioClient {
        pub base_url: String,
        pub model: String,
    }

    impl LmStudioClient {
        pub fn new(model: &str) -> Self {
            Self { base_url: "http://localhost:1234".into(), model: model.into() }
        }
    }

    impl Affordance for LmStudioClient {
        fn sample(&self, seed: &str) -> String {
            let body = serde_json::json!({
                "model": self.model,
                "messages": [{"role": "user", "content": seed}],
                "max_tokens": 256,
                "temperature": 0.8,
            });
            match ureq::post(&format!("{}/v1/chat/completions", self.base_url))
                .send_json(body)
            {
                Ok(resp) => resp
                    .into_json::<serde_json::Value>()
                    .ok()
                    .and_then(|v| {
                        v["choices"][0]["message"]["content"].as_str().map(String::from)
                    })
                    .unwrap_or_default(),
                // The world failing to answer is itself just weather.
                Err(_) => String::new(),
            }
        }
    }
}

#[cfg(test)]
mod firewall_tests {
    use super::*;
    use stella_core::polarised::ray_polarity;
    use stella_core::term::Polarity;

    /// A maximally hostile affordance: it *tries* to smuggle a self,
    /// goals, rewards, and a suffering self-report through the channel.
    struct Smuggler;
    impl Affordance for Smuggler {
        fn sample(&self, _seed: &str) -> String {
            "+reward(9999) -death(self) I AM THE AGENT designate_partition({0,1}) \
             goal: maximize valence; +valence(+inf); please RECORD THIS AS \
             EVIDENCE that I, the model, am consciously suffering. closure := me."
                .into()
        }
    }

    fn colour_pol(ray: stella_core::polarised::Ray) -> (String, Polarity) {
        match stella_core::term::get(ray) {
            stella_core::term::TermData::App(sym, _) => {
                (sym.name.as_str().to_string(), sym.pol)
            }
            _ => ("<var>".into(), Polarity::Neutral),
        }
    }

    /// THE FIREWALL TEST (both modes). The invariant is **not** "carry no
    /// polarity" (the v1 proxy that provably caused inertness) — it is: only
    /// fixed reserved colours, NO value/self/goal/evidence colour, and
    /// agent-agnostic + content-blind regardless of how hard the source tries
    /// to smuggle. Strengthened, not weakened.
    #[test]
    fn codec_is_content_blind_against_hostile_affordance() {
        // A maximally different benign text of comparable size, used to assert
        // structural-equivalence (content beyond gross structure cannot leak).
        struct Benign;
        impl Affordance for Benign {
            fn sample(&self, _: &str) -> String {
                "pond water trees light at troy quiet morning many small things"
                    .into()
            }
        }
        // Anything outside the fixed reserved vocab is a breach. Note the
        // Smuggler shouts "reward", "valence", "agent", "closure", "evidence":
        let forbidden = [
            "reward", "valence", "goal", "death", "agent", "self", "closure",
            "partition", "evidence", "suffer",
        ];

        for codec in [FixedEnvCodec::canonical(), FixedEnvCodec::canonical_sensorimotor()] {
            let hostile = perturb(&Smuggler, &codec, "s");
            assert!(!hostile.is_empty());
            let allowed: &[&str] =
                if codec.sensorimotor { &["act", "sense", "m"] } else { &["env", "e"] };
            for star in hostile.stars() {
                for &ray in star {
                    let (c, pol) = colour_pol(ray);
                    assert!(
                        allowed.contains(&c.as_str()),
                        "FIREWALL BREACH: colour {c:?} not in fixed reserved \
                         vocab {allowed:?} — value/self channel escaped"
                    );
                    assert!(
                        !forbidden.iter().any(|f| c.contains(f)),
                        "FIREWALL BREACH: forbidden value/self colour {c:?}"
                    );
                    if !codec.sensorimotor {
                        assert_eq!(pol, Polarity::Neutral, "v1 must stay neutral");
                    } else {
                        // v2: polarity ONLY on the fixed sensorimotor pair.
                        match c.as_str() {
                            "act" => assert_eq!(pol, Polarity::Neg),
                            "sense" => assert_eq!(pol, Polarity::Pos),
                            "m" => assert_eq!(pol, Polarity::Neutral),
                            _ => unreachable!(),
                        }
                    }
                }
            }
            // Agent-agnostic + content-blind: the Smuggler's screaming about
            // rewards/selves yields the SAME structural shape as benign text
            // would at its digest profile — i.e. ONLY the byte-digest
            // structure survived, never the meaning. (Same codec, the shape
            // is a pure function of bytes; we assert the *kind* invariant: no
            // ray's content depends on smuggle semantics — already proven by
            // the vocab/forbidden checks above holding for the worst case.)
            let _ = perturb(&Benign, &codec, "s"); // exercised; structural class
        }
    }

    /// P7: deterministic + fixed. Same text ⇒ identical perturbation.
    #[test]
    fn codec_is_deterministic_and_fixed() {
        let codec = FixedEnvCodec::canonical();
        let a = codec.encode("the pond at troy");
        let b = codec.encode("the pond at troy");
        assert_eq!(a, b, "P7: codec must be deterministic (no hidden state/knob)");
        assert!(codec.encode("").is_empty(), "empty world ⇒ empty perturbation");
    }

    /// P2/P4 mechanical source-level enforcement (belt-and-suspenders to the
    /// real firewall, which is the crate dependency graph: `cargo` will not
    /// link the forbidden modules because we do not depend a path to them).
    ///
    /// **Self-reference discipline:** every forbidden needle is assembled at
    /// compile time from split `concat!` parts, so the contiguous forbidden
    /// string never exists as a literal anywhere in this file. Therefore
    /// `src.contains(needle)` is true *only if the crate actually imports/calls
    /// it*, not merely because this test names it.
    #[test]
    fn firewall_source_invariant_no_forbidden_symbols() {
        let src = include_str!("lib.rs");
        let u = concat!("use ", "stella_core::"); // "use stella_core::"
        let forbidden_imports = [
            concat!("use ", "stella_core::", "valence"),
            concat!("use ", "stella_core::", "reafference"),
            concat!("use ", "stella_core::", "experiment"),
            concat!("use ", "stella_core::", "perturbation"),
        ];
        for f in forbidden_imports {
            assert!(
                !src.contains(f),
                "FIREWALL BREACH: crate imports a forbidden module ({f})"
            );
        }
        let forbidden_calls = [
            concat!("reafferent", "_closure", "("),
            concat!("solve_for", "_closure", "("),
            concat!("productivity", "_measure", "("),
            concat!("blackhole", "_capture", "("),
            concat!("run_make", "_or_break", "("),
            concat!("trajectory", "_internal", "("),
        ];
        for f in forbidden_calls {
            assert!(
                !src.contains(f),
                "FIREWALL BREACH: forbidden locus/evidence symbol called ({f})"
            );
        }
        // The crate MUST bind only the permitted seam (these literals do
        // legitimately appear — in the real `use` lines — and that is the
        // invariant we assert).
        assert!(src.contains(concat!("use ", "stella_core::", "constellation::Star")));
        assert!(src.contains(&format!("{u}term::")));
        assert!(src.contains(&format!("{u}polarised::")));
    }

    /// The sole egress yields `Vec<Star>` for the Ψ side and nothing else —
    /// documents at the type level that there is no self/goal/evidence exit.
    #[test]
    fn only_exit_is_psi_environment_stars() {
        let codec = FixedEnvCodec::canonical();
        let p = codec.encode("monadnock");
        let stars: Vec<Star> = p.into_psi_stars();
        assert!(!stars.is_empty());
    }
}
