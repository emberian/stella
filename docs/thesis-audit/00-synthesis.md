# 00 — Thesis-audit synthesis + the measured re-aim

Consolidates the 5-agent Eng-thesis audit (`01`–`05` in this dir) with
the in-flight `data[0]` measurement. Tag: [Measured] [Audited] [Proto].

## The convergence (4 of 5 independent auditors + the measurement)

The single root finding, arrived at independently:

> **The objective/subjective classification — the fragment Eng's entire
> idempotence / valence / "dead-vs-charged" theory rests on — is absent
> as a ray predicate and MIS-DEFINED where it exists.** `star_kind`
> (`constellation.rs:26`) and `ray_colours` (`dep_graph.rs:18`) classify
> by **polarity sign-mixing**; Eng §48.7/§48.10 classifies by **colour
> nesting in arguments**. They are different fragments.

Why it is the critical path (each a separate audit, same prerequisite):

- **01 core-calculus**: the idempotence metatheorem (§49.55-57) is
  uncertified *and* would test the wrong fragment. Colour and polarity
  are conflated at the root (`ray_colours` = "pol ≠ Neutral").
- **02 execution-KAM**: AEx-vs-IEx is asserted, never demonstrated —
  Eng §74.11 *verbatim* "not IEx". The KAM path runs IEx+host loop; a
  faithful AEx exists (`execution.rs:319`) but is unwired. `is_subjective`
  does not exist.
- **03 valence-χ**: the §3.1 idempotence-loss⟺whistle proposition has
  never been run as designed; χ/trace-monoid/`is_subjective` entirely
  absent; docs/08 §7 (faithful AEx-layer sampling boundary) open.
- **measurement (ii)** (`examples/galaxy_layer_trace.rs`, commit
  `fd2241f`): the real per-`force_value`-layer recursion trace shows
  `distinct == len`, only a trivial bare-var whistle ⇒ **NOT the
  H2/KA2 signature**. But this is PROVISIONAL: sampled at an unproven
  §49.52 boundary over the wrong-definition fragment.

⇒ **The H1/H2/H3 termination-crosser question is not soundly answerable,
and docs/16's premise is not soundly assessable, until the
objective/subjective classifier is faithful to Eng's colour-nesting
definition.** That — not KA2, not interaction-nets, not more measurement
on the current basis — is the measured critical path.

Settled along the way:
- **2nd/3rd Futamura** (04): zero engine merit, purely expository;
  `SpecPhi::build` is a legitimate 1st-projection residual but
  "cogen-of-one" is a category error — drop it (docs/14/17 corroborated).
- **Σ(Φ)** (Σ0/1/2, shipped) and **χ-closure** (docs/08 §4.6, Eng
  citations verified verbatim-accurate by audit 03) stand.

## The staged re-aim (all small, falsifiable, oracle-gated, no perf change)

1. **Faithful colour-nesting objective/subjective classifier** per Eng
   §48.7/§48.10 — `is_subjective(ray)` / corrected `star_kind`. Fixes the
   root divergence (01); the kill-switch (03). Gates everything below.
2. **`aex_idempotent(Φ)` battery** (01's experiment): assert
   `AEx(AEx(Φ)) =α AEx(Φ)` on objective Φ and its *failure* on
   subjective — the §49.55-57 metatheorem, the docs/00 §6 pre-registered
   null. ~30 LOC, no engine change.
3. **AEx/IEx differential on the combinator core** (02's experiment):
   wire the existing faithful `execution::aex` vs `combinator` IEx,
   assert ɟ-readout equality on the docs/05 §4 battery. Discharges the
   §57.13/§74.11 obligation **and settles docs/08 §7** (yields the
   faithful AEx-layer boundary).
4. **Re-run measurement (ii)** at the now-faithful AEx boundary over the
   correctly-classified fragment → a *sound* H1/H2/H3 verdict; then, and
   only then, revise docs/16.
5. **Cut-elimination trajectory tap** (05's experiment): §67 has a
   *theorem-certified* normal form (§67.10) — the one ground-truth
   differential oracle for the whistle/χ machinery.

Out of scope (audited, recorded): the Autodidactic matrix-model /
RG-learning machinery (one corroborative citation in docs/00 §3, not an
implementation); KAM call/cc (binder-free galaxy.txt doesn't need it).

## Honest headline

The swarm + the cheap measurement found that the project was about to
diagnose galaxy termination on a substrate whose objective/subjective
classifier is not Eng's — invalidating the idempotence/valence/H
analysis it feeds. Fixing that classifier is small, is the forcing
function for four separate obligations, and is the real answer to
"what are we hamstrung by." This is faithfulness-as-feature paying for
itself: a foundational divergence caught by audit+measurement before it
drove a large wrong build.
