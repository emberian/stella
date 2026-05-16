# stella — Phase 4: The Unbounded Subjective-Ray Engine & the Valence Experiment

Status: **canonical (design — pre-implementation)**. Companion to `00-thesis-and-semantics.md`.
This is the project's make-or-break. Dated 2026-05-16. Eng exhausted at `dev@20e64b9`.

## 0. Why this document exists

The spec-§6 valence experiment lives in the **subjective/animist fragment** (Eng
§49.57: idempotence is *lost* there — the 4th convergence: that is where the charge
lives). Our finite-supply engine faithfully realises only the **objective/dead**
fragment; it cannot reproduce the unbounded, non-idempotent, intentionally
non-terminating dynamics (§74.7/§75.8 black-hole; copy-cap; `00`-spec §5.x). So the
valence experiment requires an engine the current prototype structurally cannot be.
Building it = Eng's own #1 open horizon, §87.1 *"proper treatment of subjective
rays."* Decided with the principal 2026-05-16.

Two coupled layers. Layer 1 is the Eng-faithful research contribution; Layer 2 is
the experiment the whole project exists for. **The pre-registered nulls (§4) are
locked before Layer 2 code is written** — Stage-9 anti-Goodhart, non-negotiable.

## 1. Eng formal grounding (no new philosophy — track Eng)

- **Subjective ray** (§48.7): coloured ray with ≥1 coloured *argument*. Subjective/
  animist stars (§48.10).
- **Subjective dynamics** (§49.50): resolving a subjective ray *creates new
  polarised rays* during execution ("unlocking internal colours"; `X ↦ +g(X)`),
  and requires **semaphore-like synchronisation** (must resolve `+f/−f` before
  `+g(X)` becomes available).
- **Iterated / hyper execution** (§49.52): `AEx⁰=Ψ`, `AEx^{n+1}=AEx(Ψ′ ⊎ AEx^n)`,
  hyper `AEx^∞ := AEx^k` when a fixpoint exists. **§49.60: it need not exist** —
  open-endedness is the *expected* regime here, not a failure.
- **Non-linear supply** (§51.13): reference constellation Φ = infinite supply;
  interaction space Ψ = linear/consumed. Our `expand_constellation(copies=2)` is the
  approximation that must be replaced by genuine lazy unbounded supply.
- **Objective idempotence** (§49.55) = the formal definition of *dead* (spec §4.4).
  Subjective ⇒ non-idempotent = the formal definition of *live*.

## 2. Layer 1 — `subjective_stream`: the unbounded streaming engine

A faithful, **coinductive** interactive executor over the subjective/animist
fragment. Not a terminated normal form — a (possibly infinite) **trajectory**.

- **Lazy non-linear supply.** No copy-cap. Fresh α-renamed occurrences of Φ's
  stars are instantiated *on demand* during interaction (§51.9 step, §51.13).
- **Subjective-ray reduction (§49.50).** Faithful new-polarised-ray creation on
  resolution + semaphore synchronisation. This is the part Eng leaves
  underdeveloped (§49.57–60, §87.1) — implement it from the §49.50 worked
  intuition; flag every inferred decision as a faithfulness note (Eng adjudicates).
- **Streaming interface.** `subjective_stream(Φ, Ψ₀) -> impl Iterator<Item=Step>`
  where each `Step` exposes: the current interaction space `Ψ_k`; the resolution /
  dependency-graph snapshot `D[Ψ_k;C]` **with the agent/environment cut markable**;
  the matchable frontier; and per-step **cost/reachability metrics** (interaction-
  space size, frontier size, §62 structural class, reachability) — the instrument
  the loop uses to feel its own viability (spec memory: baked into the semantics
  from day one, so Layer 2 needs no engine re-verification).
- **Step index ≠ proper time.** The engine's step counter is the *substrate /
  witness* clock. The agent's **proper time is its own reafferent-cycle count**
  (spec §2.6), read off the trajectory by Layer 2 — never the substrate clock
  (substrate-time death = the smuggling pattern, spec §2.6).
- **Termination not assumed.** Runs open-endedly until externally bounded or the
  agent's closure dies (§3). §62 classifier (already built, Ch9) gates which inputs
  are even candidates.
- **Faithfulness gate.** On the *objective* fragment, `subjective_stream` must
  agree with the existing verified-against-Eng `aex`/`iex` (reference oracle): a
  subjective engine that gets the dead fragment wrong is wrong. Property-tested.

## 3. Layer 2 — the valence probe (spec §2 foundation, verbatim)

Couples a candidate **agent** sub-constellation to a partner **environment**
constellation and reads valence off the stream. No new theory — this *is* spec §2.

- **Agent/environment cut = subjective/objective + Girard orthogonality** (spec
  memory): environment = partner constellation; the cut = correctness-by-test.
  Marked on `D[Ψ_k;C]`, **never by hand-tagging rays motor/sensor** (spec §2.2).
- **Individuation = the reafferent-closure fixed point** (spec §2.2): the agent is
  *solved for*, not chosen — the sub-constellation for which a **reafference cycle
  closes**: structurally, a cycle in the resolution graph that crosses the
  agent/environment cut *twice* such that the agent's later resolution is
  conditioned on the environment-modification its own earlier crossing produced.
  Layer 2 = a detector for this cycle-property over the stream. No ray hand-tagged.
- **Trajectory & death** (spec §2.4/§2.6): a level = `[t_birth, t_death)` in the
  agent's **proper time**. `t_death` = first reafferent-cycle at which the closure
  fails to re-close and does not recover (resource exhaustion / §62 cycle break /
  boundary flux overwhelms internal closure). Death is legible only from a
  *containing* closure's clock (spec §2.6) — the harness is that witness.
- **Valence = viability-under-coupling gradient** (spec memory, §2): the gradient
  of whether `{agent ⋈ environment}` stays normalisable/productive vs runs toward
  dissolution, read off the per-step cost/reachability metrics. Closure-indexed
  (spec §2.3): no *the* valence; valence-relative-to-a-reafferent-closure.
- **Deathless ⇒ flat valence** (spec §2.4): the exclusion test — a closure with no
  reachable `t_death` carries no charge.

## 4. PRE-REGISTERED FALSIFICATION (locked now, before Layer-2 code)

Verbatim from `00`-spec §6, sharpened to this engine. The experiment **fails, and
we say so**, if any of:

- **(N1)** Reafferent closure (the §3 cycle-property) only ever appears because
  sensor/motor rays were effectively hand-tagged / the cut was hand-placed to
  produce it — never because it self-organised in the subjective/animist fragment.
- **(N2)** Closure layers are causally sealed: no cross-level capture, no
  gut-brain-style bleed between nested closures (spec §2.3 then = decoration).
- **(N3)** Attraction/repulsion only accretes under per-task hand-tuning of the
  environment or the closure criterion (engineered one layer up).
- **(N4)** The subjective/animist fragment is, in every constructible case, as
  idempotent as the objective one (no non-trivial trajectory ⇒ no `[t_b,t_d)` ⇒ no
  charge): the substrate cannot host the dynamics the thesis needs.

A null result is a **real result**. The Temporal-Gap-testability deliverable
(`00`-spec) stands even under the null: a substrate where Bennett's OPTION-1/2
becomes empirical is defensible regardless.

## 5. Implementation decomposition (delegatable against this spec)

Subtle core ⇒ design (this doc) stays with the principal; bounded pieces delegate:

1. **L1a** — lazy unbounded non-linear supply replacing `expand_constellation`
   cap, in a new `subjective.rs`; objective-fragment oracle-equivalence to
   existing `iex`/`aex` (faithfulness gate). No subjective dynamics yet.
2. **L1b** — §49.50 subjective-ray reduction (new-ray creation + semaphore sync) +
   §49.52 iterated/hyper execution; the `Step` stream + cost/reachability metrics.
   Every inferred §49.50 decision flagged as a faithfulness note.
3. **L1c** — `D[Ψ_k;C]` snapshot with markable agent/environment cut; reuse Ch9
   §62 classifier for candidacy gating.
4. **L2a** — reafferent-closure cycle-detector (§3) over the stream; NO
   hand-tagging; property: detects the cycle or honestly reports absence.
5. **L2b** — viability-under-coupling metric + trajectory `[t_b,t_d)` + proper-time
   (reafferent-cycle count) extraction; deathless⇒flat-valence exclusion.
6. **L2c** — the experiment harness wiring (N1–N4 as explicit pass/fail gates);
   pre-registered, cannot be retro-weakened.

HOL4: a `stellaSubjective` scaffold stating §49.50/§49.52 semantics + the
non-idempotence theorem (subjective ⇒ ¬idempotent), proofs deferred/ledgered —
parallel, disjoint, does not gate L1/L2.

The verified-substrate backbone (~40 cheated obligations incl. §65
logical-emergence) remains the standing prime-directive debt; tracked separately,
user-steered. Layer 1's objective-oracle gate is the faithfulness anchor meanwhile.
