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

### 3.1 Viability redefined — closure-internal, not global (2026-05-16, principal-directed; supersedes the L2b global proxy)

**The confound that forced this.** L2b measured `viability = 0.4·norm(psi_size) +
0.4·norm(frontier_size) + 0.2·norm(boundary_flux) + 0.1·§62` — a property of the
*ambient constellation*, not of *the closure*. Any perturbation that changes star
count moves it; the deathless-era `t_death=cap−2` and the perturbation-confound
(`perturbing_env` padding the very counts the proxy sums) are the same disease:
the proxy moving for reasons unrelated to the closure's self-maintenance. A global
bulk measure can never be a viability measure. Preserved-not-deleted: the L2b
proxy and its results stay on record (`docs/02`); this redefinition is the
canonical viability from here.

**Canonical definition.** A reafferent closure's **viability at round r** is the
*integrity of its own reafferent self-maintenance*, intrinsic to the closure,
measured from L1d provenance — NOT from ambient size:

1. **Re-closure (binary/graded):** does the §2.2 cycle re-close at round r —
   the agent's later resolution still genuinely provenance-traces through the
   env-modification its own earlier crossing produced (L1d `traces_through`)? A
   degrading closure re-closes later, more weakly, or intermittently before (if
   ever) failing.
2. **Self-reproduction fraction `ρ_r ∈ [0,1]`:** of the closure's stars at round
   r+1, the share whose provenance traces back **through the closure's own cycle
   at round r** (genuine self-causation) versus arising from generic ambient Φ
   supply (persistence-by-accident). `viability_r := f(re-closure_r, ρ_r)`,
   globally fixed `f`, no per-case tuning.

**Why this is right (and confound-immune):**

- **Intrinsic.** Adding unrelated noise stars cannot change whether the closure's
  *own* cycle re-closes or its self-reproduction fraction. The perturbation
  confound dies at the root; an invariant control shows no response *by
  construction*, making M2/M3 actually test their intent.
- **Faithful to §3** ("normalisable/productive vs runs toward dissolution"):
  dissolution = `ρ_r → 0` / cycle stops re-closing.
- **Faithful to §2.4-amended:** *invariant ⇒ flat* becomes **`ρ ≡ 0` ⇒ flat** —
  the deathless bureaucracy persists with **zero self-reproduction** (it never
  closes a reafferent cycle; it endures by inertia), so it is correctly flat,
  re-grounding the exclusion on *self-causation*, not on death. An
  eternal-but-perturbable closure has `ρ > 0` that perturbation can drive down:
  **eternal valence = the perturbation-response gradient of `ρ`/re-closure
  fidelity.** Death (viability floor) = `ρ` permanently 0 / cycle permanently
  fails — a special case, not the source of charge.
- **Cap-artifact dead at the root:** `ρ_r` and re-closure are *per-round
  intrinsic ratios*; a run ending does not lower them — only genuine disruption
  does. `viability` cannot track `max_rounds`.

The perturbation-response harness (L2c-redux) is rebuilt against THIS viability,
with the mandatory invariant-control (objective reference: `ρ ≡ 0`, must show no
response — else the metric is still confounded and M3 fires). M1–M5 text is
**unchanged**; this is a strengthening of the *instrument* against a
false-positive confound, locked before the rebuilt harness. Integrity: a
confound-fix that makes a positive *harder*, never easier — anti-Goodhart,
always permitted; `docs/02` and the M1–M5 pre-registration stand untouched.

## 4. PRE-REGISTERED FALSIFICATION (locked now, before Layer-2 code)

Verbatim from `00`-spec §6, sharpened to this engine. The experiment **fails, and
we say so**, if any of:

**Superseded-but-preserved.** The deathless-era nulls (N1–N4) and the run that
fired none-yet-was-actually-null-under-deathless⇒flat are preserved verbatim in
`docs/02-phase4-first-run.md`; that result stands as history and is NOT retconned.
The set below is the **reformulated (invariant⇒flat) pre-registration**, locked
2026-05-16 *before any re-run code*, per §2.4-amended. The experiment **fails / is
a null** if any of:

- **(M1) Smuggled individuation.** The reafferent closure — or any
  perturbation-response — only ever appears because rays were effectively
  hand-tagged or the agent/environment cut hand-placed; never self-organised via
  the principled Ch9-§62 partition search on the non-rigged Eng-own corpus.
- **(M2) Invariance — the core discriminator, replacing deathless⇒flat.** The
  self-organised closure is *invariant*: under a perturbing/adversarial
  environment its viability does not respond beyond noise — it cannot be driven
  up or down by the coupling. Invariant ⇒ flat ⇒ no charge.
- **(M3) Artifact, not response — the disclosed tightening, now first-class &
  pre-registered.** A genuine viability response must be **cap-invariant** (vary
  `max_rounds`/supply ⇒ it does NOT track the cap — the explicit fix for the
  deathless-era `t_death = cap−2` artifact) **and** **perturbation-tracking**
  (vary perturbation strength ⇒ the response tracks it). Failing either ⇒
  artifact ⇒ null.
- **(M4) Engineered one level up.** The perturbation-response only accretes under
  per-task hand-tuning of the viability metric, environment, or partition. The
  metric/rule must be globally fixed across the entire corpus (structurally
  enforced); M4 fires iff that invariant is violated.
- **(M5) Cross-level sealed (carried; honestly may be Undetermined).** Closure
  layers causally sealed — no cross-level capture/bleed (§2.3). If no corpus
  member has nested closures, M5 is **Undetermined**, never coerced to "passed".

Non-falsification = none of M1–M4 fire (M5 may be Undetermined) **and** a
self-organised closure exhibits a cap-invariant, perturbation-tracking,
globally-fixed-metric, non-hand-tagged viability response. Corpus adds Eng's own
§79/§80 `ω`-weight (an Eng-built, non-reafference, *eternal* valence-like scalar)
as a non-rigged member.

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
