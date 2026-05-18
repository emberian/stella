# 16 — Galaxy-Execution Decision (synthesis of docs/12–15)

> **⚠ SUPERSEDED BY MEASUREMENT — read §7 first.** §1–6 are the
> *historical* survey reasoning (what was believed pre-measurement and
> why). The cheap discriminator of §3 was built and run; its premise
> (§1, "step-count problem") was **falsified, reopened, and resolved as
> a first-class N-KA-cover negative**. §7 is the authoritative
> conclusion + the re-aimed decision. §1–6 retained intact as the
> honest record of a hypothesis measurement overturned.

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

---

## 7. RESOLVED — measured outcome + re-aimed decision (authoritative) [Measured]

The §3 discriminator was built and run (cheap, read-only, bounded —
`examples/galaxy_data_discriminator.rs` + `galaxy_img_forcings.rs` +
`galaxy_img_stuck.rs` + `galaxy_layer_trace.rs` + `galaxy_h1_family.rs`).
Outcome, in order, each commit-pinned:

1. **§1's premise FALSIFIED, then a wrong conclusion RETRACTED (the
   discipline working).** `data[0]`'s force does ~1 isnil forcing,
   ~200 lazy steps, then `eval_forced` spins. First write-up said
   "§58/§60 unimplemented strict isnil" (`581bafb`); reading
   `drive_strict` refuted that — **isnil IS faithfully implemented**
   (`force_value` recursion). Retracted (`d6e584b`). The real blocker:
   the nested `isnil`/`force_value` recursion — *not* docs/16 §1's
   "long NON-REDUNDANT transition-count reduction." §1 reopened, not
   closed by assumption.

2. **The convergent root (5-agent thesis audit, docs/thesis-audit/00–05):
   the objective/subjective classifier was Eng-UNFAITHFUL** — a
   polarity sign-census, not §48.7/§48.10 colour-nesting. This, not a
   termination-crosser, was the measured critical path. Fixed:
   `star_kind_eng`/`ray_is_subjective` (step 1, `de71654`, conformance
   3/3, divergence pinned). Idempotence metatheorem made falsifiable
   on the *faithful* partition (step 2, `1bf21ac`): **§49.55 holds**;
   **§49.57 measured** — prototype `aex` is idempotent even on the
   subjective fragment ⇒ non-idempotence lives in
   `subjective::subjective_stream`, NOT `aex` (recorded boundary).

3. **The AEx-faithful diagnosis is INTRACTABLE, by measurement**
   (step 3, `f96b452`). Reference saturated-diagram AEx — `aex_full`,
   `aex_seminaive_full`, and copy-free `aex` — all fail
   `machine_stars + [+P(st(x,ε))]` (a ZERO-redex value) in 45 s. The
   7 KAM stars are mutually matchable ⇒ enumeration explodes with no
   reduction at all. Confirms `combinator.rs`'s own doc + Eng §57.13.
   ⇒ §57.13/§74.11 not dischargeable via reference AEx; **docs/08 §7
   (IEx-loop-NF = AEx-fixpoint) is NOT empirically establishable** —
   closed by measurement, not omission.

4. **The recurrence instrument is now CALIBRATED** (step 5, cherry-pick
   `f634f61`). The §67.10 *theorem-certified* cut-elim oracle proves
   `detect_recurrence` raises **no false-positive whistle** on a proven
   strongly-normalising trajectory. Specificity established (not
   sensitivity) — the soundness anchor the open-ended probes lacked.

5. **BOTH termination-crosser candidates MEASURED-NEGATIVE:**
   - **H1** (redex-family redundancy → interaction-net, docs/12):
     `c8cb09e` — duplicated/distinct ratio ≡ **1.00** at every depth
     across δ / all-Splice / `s/b/c` while work grows ~6–9×. Zero
     re-reduced α-equal redex families. *Not* redex-family-redundant;
     consistent with the Lever-C closed-subterm negative (`b6c65d5`).
   - **H2** (affine/structural recurrence → KA2, docs/13): the
     calibrated `detect_recurrence` on the per-`force_value`-layer
     IEx trajectory shows `distinct ≡ len`, only a trivial bare-var
     whistle ⇒ no foldable recurrence.

**Conclusion — docs/16's own pre-registered §2 H3 / N-KA-cover
negative, now realised and recorded (no retro-widening):** on every
tractable, faithfully-instrumented axis — closed-subterm (Lever C),
redex-family (H1), affine/structural recurrence on the calibrated IEx
trajectory (H2) — `data[0]`'s force exhibits **no exploitable
redundancy and no foldable recurrence**, and the AEx-faithful route is
provably intractable. **Neither survey termination-crosser
(interaction-net nor KA2) is justified by evidence.** Caveats kept
attached, not waved: the H2 reading is the *IEx trajectory* (not the
§49.52 AEx-layer — §7 closed by measurement); calibration gives
*specificity, not sensitivity*; the prefix is bounded (the divergence
self-stops at the wall). Honest ceiling, stated as such.

### Re-aimed decision (supersedes §6)

- **No termination-crosser is built.** docs/12 interaction-net and
  docs/13 KA2 are both evidence-negative for `data[0]`. The §6 plan
  ("build the indicated crosser") is void — there is no indicated
  crosser; the indication is the N-KA-cover negative.
- **Σ(Φ)** (docs/14, the per-step companion) **shipped & proven**
  (Σ0/1/2, `016e8ee`/`224d602`/`90f34c0`) — it was always the
  companion, never the cure; unaffected, stands.
- The faithful-reproduction + diagnose-the-blocker thread is **CLOSED
  here** with this recorded negative. The arc's durable product is a
  *platform*: a fast faithful two-tier engine + Σ(Φ) + a §67.10-
  calibrated recurrence instrument + an executable/falsifiable form of
  Eng's §48.7/§49.55/§49.57 metatheory + the measured §49.57 boundary.
- **Pivot: past-Eng.** The next frontier is the one Eng himself did
  not reach — the §49.50 / valence / **χ** track (docs/08, explicitly
  [Proto]; "Eng has no χ"). Its prerequisites (faithful
  objective/subjective classifier; calibrated whistle; located
  non-idempotence) were precisely what steps 1/2/5 cleared — so it is
  now tractable for the first time, and is the engine-merit-justified
  §49.50 staged track the spec always deferred to here. docs/15 §1–4
  χ-closure already folded (docs/08 §4.6, `b42c290`); the §49.57
  boundary records *where* χ's non-idempotence must be measured
  (`subjective_stream`, not `aex`).

The honest headline (revised): galaxy `data[0]` is, on every
faithfully-measurable axis, a genuine deep non-redundant
non-recurrent computation; the survey's two termination-crossers are
both evidence-negative and the AEx-faithful diagnosis is provably
intractable — a first-class recorded negative. The arc's value is the
*calibrated faithful platform* it produced, and the decision is to
**graduate**: stop treating galaxy-termination as the goal, pivot to
the now-tractable past-Eng §49.50/χ frontier.
