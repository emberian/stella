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

### 2.1 L1b converged operational semantics (2026-05-16, with principal)

The §49.50/§49.52 inference — adjudicated, now canonical, not open:

- **(1) New polarised-ray creation is NOT a new rule.** It is standard fusion +
  substitution where (i) bare-variable rays are *retained* in stars (never
  dropped), and (ii) matchability is *recomputed every step*, so a variable ray
  that a subjective fusion's substitution binds to a coloured term *enters the
  matchable frontier*. Grounded verbatim in Eng §49.50's example
  (`[−f(+g(X))] ⋈ [X,+f(X)]` ⟹ `θ={X↦+g(X)}` ⟹ residual `X` becomes `+g(X)`).
  Implementation = ensure the engine does (i)+(ii); "bare `Var` non-matchable"
  means *until substituted to a coloured term*, NOT *dropped*.
- **(2) The semaphore is emergent, not a primitive.** `+g(X)` is unavailable
  until `+f/−f` interact *because it does not exist as a surface ray until the
  f-fusion's substitution creates it*. Ordering is automatic under (1). No locking
  mechanism is designed or needed.
- **(3) Proper-time tick (the one real inference, adjudicated):** ONE tick of the
  agent's proper time (spec §2.6) := one Eng §49.52 iterated-execution round
  (`AEx^n → AEx^{n+1}`) in which the agent's subjective rays cross the
  agent/environment cut and the modified environment feeds back so the §2.2
  reafference cycle-property closes once. Faithful to both §49.52's iteration
  structure and spec §2.6 (proper time = reafferent-cycle count, never substrate
  steps). The `Step` stream exposes both the substrate step index (witness clock)
  and the reafferent-round index (the agent's proper time).

### 2.2 §2.2-detection converged (2026-05-16, with principal): provenance, not structure

Spec §2.2's reafference cycle — *"the agent's later resolution is conditioned on
the environment-modification its own earlier crossing produced"* — is an
irreducibly **causal/temporal** property across the trajectory, NOT a static graph
property. L1c's per-step cut/boundary-flux cannot establish causal conditioning;
inferring it from structural co-occurrence *is* the N1 failure mode (reading
closure into structure). Therefore, adjudicated canonical:

- **L1d (new prerequisite, before L2a):** the subjective engine tracks
  **derivation provenance through fusion** — each star/ray carries which prior
  fusions/substitutions produced it. Additive instrumentation (like L1c):
  observationally transparent, must not change stream behaviour, regression-gated
  on the existing subjective + objective-oracle tests.
- **§2.2 cycle = a provenance pattern:** ∃ rounds r < r′ and a candidate
  agent-partition P such that an agent→env cross-cut interaction at round r whose
  substitution modifies an environment star, and an agent resolution at round r′
  whose **provenance traces through that modified environment star**. The cycle is
  *causal*, decided over provenance, never over structural recurrence alone.
- **N1 structurally guarded:** L2a never takes the cut as given. It runs the
  detector over a **principled, Ch9-§62-gated enumeration** of candidate
  partitions and *solves for* the partition admitting the cycle (the fixed point,
  spec §2.2 — Girard-bi-orthogonality flavour). The harness (L2c) pre-registers:
  N1 falsifies iff a closure only ever appears under hand-engineered
  partitions/environments, never one the dynamics single out.

Updated decomposition (§5): **L1a✓ L1b✓ L1c✓ → L1d (engine provenance) → L2a
(provenance+cut cycle-detector + partition-search) → L2b (viability /
trajectory / proper-time) → L2c (harness, N1–N4 pre-registered gates).**

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
