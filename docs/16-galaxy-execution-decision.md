# 16 — Galaxy-Execution Decision (synthesis of docs/12–15)

Decision record. Synthesises the four research surveys (docs/12 optimal/
interaction-net · 13 supercompilation/distillation/KA2 · 14 staged/Futamura
Σ(Φ) · 15 GoI/token) against the *measured* blocker and the faithfulness
discipline. Tags: [Built] [Measured] [Lit] [Proto].

## 1. The blocker, now triangulated (all four agree) [Measured]

Galaxy `data[0]` (one image) is a **long, NON-REDUNDANT, TRANSITION-COUNT**
reduction:
- NOT materialised-space bound — docs/15: `eval_forced` is *already* a
  GoI-optimal single-ray stack machine (Eng §57.19 KAM-as-constellation
  *is* the token machine; `iex_fast` *is* executing it). GoI as an
  executor would be strictly slower. Closed as a lever.
- NOT closed-subterm-redundant — Lever C memo, Built + proven, measured
  honest-negative (`b6c65d5`): does not crack `data[0]`.
- ⇒ Only a **step-count / asymptotic collapse** can make it terminate.
  Every per-step lever (`unify_fast` ✓2×, `find`, Σ(Φ), GoI) is bounded
  by docs/11 Fact-2: a constant per-step win cannot make a
  non-terminating-in-150s reduction finite.

## 2. Two falsifiable hypotheses for *why* it is Θ(N) transitions

| H | mechanism | lever | cost-to-build | falsifier |
|---|---|---|---|---|
| **H1** | redex-**family** redundancy: `s/b/c/δ` duplicate args; engine re-reduces each copy (closed-`TermId` memo provably can't see this — docs/12 §C.2) | **docs/12** optimal / interaction-net (Lafont/HVM2-style); galaxy binder-free ⇒ no oracle penalty ⇒ exp→poly | large (new net runtime) | net family-contractions vs ref steps diverge favourably as `s`/δ fan-out depth grows |
| **H2** | long **affine/structural recurrence** in the image generator | **docs/13** KA2 (whistle→generalise→fold); **substrate already [Built]**: `accel_detect`, `antiunify`, `evaluate`, `faithfulness` | small (kernel exists) | `accel_detect::detect_recurrence` whistles + guard-passes on the `data[0]` layer trace; `mul(13,9)` collapses |
| **H3** | genuinely irreducible (neither) | none here — deeper problem | — | both falsifiers fail ⇒ first-class N-KA-cover negative (report, don't retro-widen) |

H1 and H2 are not contradictory — they are competing diagnoses of the
*cause* of the Θ(N). The cause is an empirical fact about `data[0]`'s
real trace, **to be measured, not guessed** (the cardinal rule).

## 3. The decisive experiment (all four converge on this) [Proto→do-now]

A cheap, read-only, **bounded** measurement harness on `data[0]`'s actual
reduction (we already reach `data[0]` cheaply via the guided descent in
`examples/galaxy_data_probe.rs` — `[triple]/[flag]/[state]/[data]` force
in 4311/14/6/19 steps; only the final image force diverges):

1. **H2 probe (cheapest, highest-signal, uses [Built] infra):** run a
   *bounded* `eval_forced` on `data[0]`, capture the per-layer
   `readback_ray(final_ray)` trace, feed it to
   `accel_detect::detect_recurrence` (KG8). Whistle + sound-generalise +
   guard-pass ⇒ **H2 confirmed → build KA2** (fastest path; substrate
   exists). PRECONDITION: settle docs/08 §7 (is `final_ray` a faithful
   AEx-layer boundary, `galaxy.rs:864-893`) — instrument it in this same
   harness; if not, sample at true layer boundaries.
2. **H1 probe:** instrument the bounded reduction for redex-family
   duplication — does the count of re-entered `s/b/c/δ` copy-families
   grow super-linearly in fan-out depth while *distinct* work does not?
   Yes ⇒ **H1 → interaction-net (docs/12)**.
3. **transition-count vs space confirmation** (docs/15 Stage-0): steps
   grow, materialised term does not — confirms §1 (already implied by
   the Lever-C negative; cheap to re-confirm in the same harness).

Pick the termination-crosser **from this evidence**. KA2 is preferred-if-
applicable purely because its kernel is already Built (days not weeks);
interaction-net is the structurally-correct answer if H1, and a larger
build.

## 4. Orthogonal companion — ship beside, not instead [Proto]

**docs/14 Σ(Φ)** (first Futamura projection: defunctionalised-KAM
head-keyed closed transition table over Φ=405; 392 δ-heads → pure
node-splice, no scan/α-rename/unify/apply). The largest single
*per-step* lever — but explicitly NOT a termination-crosser. It
compounds multiplicatively with whichever H-lever wins, is lower-risk,
and deepens the already-[Built] `build_accel`/`RayIndex`. Sequence:
after the in-flight `unify`/`find`/Stage-2-3 attribution work, before/
parallel to the H-lever. `iex_spec` = a sibling fast tier, same
`psi_compatible` + reference-`iex` + deopt gate. Reject GRIN native
codegen (breaks the trusted/deopt boundary for a per-step constant);
keep strict-ops on `drive_strict` (the §49.50 ray-minting boundary).

## 5. Theory closure (not a lever) [Eng]

docs/15 §1–4: GoI nilpotency ≡ Eng §49.57 idempotence ≡ docs/08's
charge **χ = non-nilpotency of σu**. This identification is *tighter
than docs/08 itself states* and is [Eng]-grounded (§49.57 verbatim).
Action: fold into docs/08 as the §49.50-track theoretical closure (it
sharpens the make-or-break charge definition). No code.

## 6. Decision & order (faithfulness invariant unchanged)

Reference `iex`/`eval_forced` = oracle; `faithfulness::psi_compatible`
= the proven gate; every new tier is two-tier with deopt; honest
negatives are first-class (N-KA-cover). Then:

1. **NOW:** build + run the §3 discriminating harness (cheap, read-only,
   decisive, measure-don't-guess). Settle docs/08 §7 in it.
2. Build the indicated termination-crosser: **KA2** if H2 (substrate
   [Built] — fastest real galaxy-execution path); **interaction-net**
   (docs/12) if H1 (larger, structurally-correct).
3. **Σ(Φ)** (docs/14) as the compounding per-step companion — after
   in-flight unify/find/Stage-2-3, parallel-safe with (2).
4. Fold docs/15 §1–4 χ-closure into docs/08.

The honest headline: galaxy-execution is a **step-count problem**; the
survey eliminated the wrong levers (GoI, pure memo, pure per-step) and
left exactly two evidence-decidable candidates plus one compounding
companion — and one of the two (KA2) already has its kernel built. The
next action is a cheap measurement that picks between them with data.
