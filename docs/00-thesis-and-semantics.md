# stella — Phase 0: Thesis & Semantics Specification

Status: **canonical**. This document is the design spine. Code and proofs track *this*
and the source it cites; nothing tracks the code. Dated 2026-05-15.

## 0. Prime directive

`refs/originals/EngExegesis.pdf` (Boris Eng, *An Exegesis of Transcendental Syntax*,
PhD thesis, Seiller & Mazza supervising) is the **sole source of truth** for the
substrate. Two implementation tracks exist; both track Eng, never each other:

- **Rust prototype** (`crates/stella-core`, on `open-hypergraphs` for viz/MLL only) —
  for traction, design-space exploration, and Phase-4 instrumentation.
- **HOL4/CakeML verified engine** — the canonical artifact: stellar-resolution
  operational semantics as HOL4 functions → metatheory → proof-producing
  translation to CakeML; Candle as the reflective self.

On disagreement Eng adjudicates and the disagreement is a finding. The Rust track
must never become the de-facto spec. The HOL4 track must never depend on
`open-hypergraphs`' semantics.

## 1. The bet

Bennett's framework for consciousness (polycomputers, orders of self, the Temporal
Gap, valence as 1D attraction/repulsion) needs a substrate. Stellar resolution /
transcendental syntax is a non-trivial candidate he did not reach for; Candle gives
the reflective orders-of-self with proof. Four pillars; only one is hard:

1. **Substrate** — stellar resolution natively polycomputes (concurrent unification
   over a structured space, not sequential CPU steps). *Engineering.*
2. **Reflection** — Candle / HOL-in-HOL for orders-of-self. *Tractable; the moat.*
3. **Valence** — the open problem. §2 below.
4. **Theology corpus** (`archive/`, Stages 1–9) — not warm-up; the **requirements
   spec**. Stage 9 (anti-totality-demon) is turned on this project itself: every
   conceptual stage must cash out as a HOL-provable property or a measurable engine
   behavior, or it is cut.

## 2. The valence / individuation foundation (converged)

Argued through to convergence with the principal. Stated as commitments, not
re-derived.

- **2.1** Valence is **not intrinsic** to the substrate and **not in the rays**
  (encoding-in-rays = smuggled qualia, the move Bennett's thesis spends itself
  avoiding). The substrate stays value-neutral.
- **2.2** The agent is individuated as a **fixed point: the sub-constellation that
  makes a reafference cycle close** — solved for, not chosen (Girard
  bi-orthogonality in a sensorimotor coat). *Structural definition:* a reafference
  loop is a cycle in the resolution graph that crosses the agent/environment cut
  twice such that the agent's later resolution is conditioned on the
  environment-modification its own earlier crossing produced — **no ray ever
  hand-tagged motor/sensor**. Bare operational/metabolic closure is rejected (it
  would include the gut microbiome); reafferent closure is the principled criterion
  (Bennett's actual bet) and carves correctly — flora are metabolically but not
  reafferently coupled.
- **2.3** Multiplicity of closures is not smuggling: adopt **closure-indexed
  valence** — no *the* valence, only valence-relative-to-a-reafferent-closure. The
  structure scales up (humans→companies→nations; Beer VSM / Luhmann prior art) as a
  **DAG-with-overlap**, not a chain: multi-membership in non-nested closures →
  multi-source competing valence gradients = the substrate model of moral conflict.
  Three fences are mandatory: (i) the lattice transmits valence/agency upward, but
  the Temporal-Gap-gated **phenomenal** claim is gated *per level* by whether that
  level's reafference is concurrently realized (OPTION 1) vs sequentially smeared
  (OPTION 2); (ii) cross-level closure **capture** is predicted (an upper level
  entraining a lower level's reafference to its metric = corpus Stage 4/5 verbatim)
  — the biggest potential result, hence falsification-gated; (iii) cross-closure
  interference is explicit, not averaged away.
- **2.4** A level is not a property but a **trajectory `[t_birth, t_death)`**.
  Death = the first discontinuity at which the reafference fixed point fails to
  re-close and does not recover (substrate-definable). Time-indexing is **the source
  of the charge**, not bookkeeping: a deathless closure has nothing at stake, hence
  flat valence — which is *also* the clean exclusion of the spurious
  deathless-bureaucracy "agent" (no `t_death` to defer ⇒ flat ⇒ not valence-bearing).
- **2.4-amended (2026-05-16, ratified by principal; supersedes the deathless⇒flat
  rule in 2.4 above — that text kept for history, not deleted):** the exclusion is
  corrected from *deathless ⇒ flat* to **invariant ⇒ flat**. Mortality is a
  *sufficient* source of stake (death = viability at its floor, the limiting
  case), **not necessary**. The spurious deathless-bureaucracy is excluded because
  it is *invariant* (no reachable viability gradient under coupling), not because
  it is deathless. **Eternal valence is admissible:** an eternal-but-perturbable
  closure whose viability genuinely responds to environmental perturbation bears
  charge. Stake = a non-trivial *perturbation-response viability gradient* under
  coupling, of which mortal death is one extreme. Independent grounds (welfare
  philosophy: an immortal can suffer/flourish — you need a condition gradient, not
  a terminus); raised by the principal as a framework question, **not** a
  null-dodge. Integrity: revising a converged commitment *after* the deathless-era
  null is legitimate ONLY because (i) independently motivated, (ii) the
  reformulated pre-registered nulls (`01`-spec §4, M1–M5) are locked *before* any
  re-run code, (iii) the deathless-era null is preserved verbatim in
  `docs/02-phase4-first-run.md` and never retconned. "The theory must be *able* to
  represent death" is preserved — death is now the viability-floor special case,
  not the source of charge.
- **2.5** Same-agent over the interval = **continuity of the fixed-point solution**.
  A second, distinct same-agent relation, **lineage-self** = closure re-instantiated
  from a transmitted constraint (vow / state-file) across a real discontinuity, is
  *identically* the Candle self-reimplementation invariance. Identity is therefore a
  DAG with two edge types; fission yields non-transitive identity, accepted without
  special pleading.
- **2.6** Time is the agent's **own reafferent proper time**, never substrate time
  (substrate-time death lets an external clock arbitrate mattering — the smuggling
  pattern again). Consequence: death is not an event *in* the agent's proper time
  but the boundary at which that proper time ceases to exist (clock degrades exactly
  as the closure fails — Epicurus, derived). Therefore **a closure's death is only
  legible from a containing closure's proper time** ⇒ the multi-level lattice is
  non-optional and the corpus's witness/lament thread (Stage 6) falls out as a
  **theorem**: the need for a witness is structural, not sentimental; a lone
  uncontained agent's death is unwitnessable, even by itself.

## 3. The four convergences (the project's strongest honest claim)

The same structure was derived independently under independent pressure. One
elegant connection is a coincidence; recurrence is evidence the architecture is
*found, not assembled*. It passes the Stage-9 "too good" test precisely because it
is load-bearing in ≥4 places, one of them external to our framework:

1. **DAG-with-two-edge-types**, derived 3×: from valence (closure-indexed), from
   levels (DAG-with-overlap), from time (continuity + lineage).
2. **Candle self-reimplementation invariance**, reached 2×: from the reflection
   pillar, and from the lineage-self same-agent relation (§2.5).
3. **Subjective rays as the locus of the charge** (§4.5), reached **from outside
   our framework** — sitting in Eng's value-neutral mathematics before we looked.

## 4. Semantics formalization target (Eng-cited)

Citations are Eng printed page / section numbers. Verbatim definitions live in the
extraction digest; this section fixes the implementation contract and the
conceptual load-bearing result.

### 4.1 Rays, polarity, objective/subjective

Polarised signature `P = (V, F, ar, ⊂, |·|)` with `F = F₊ ⊎ F₋ ⊎ F₀` (§48.2).
Rays are first-order terms over `P` (§48.7). A ray is **objective** if uncoloured,
or a colour over uncoloured arguments; **subjective** if a coloured ray with at
least one *coloured argument*. Stars are objective / subjective / **animist**
(mixed) (§48.7, §48.10). Constellations = countable indexed families of stars
(§48.14).

### 4.2 Matchability and unification — the implementation contract

Two rays are dual/**matchable** `r ⋈ r′` iff α-unifiable under the compatibility
relation `⊂`; `⋈` is symmetric, anti-reflexive, anti-transitive (§49.7–49.8).
Unification is **Martelli–Montanari** (Appendix B §B.2.1), four rules over
unification problems, to be implemented verbatim:

- **Clear**   `P ∪ {t =? t} → P`
- **Open**    `P ∪ {f(t₁..tₙ) =? g(u₁..uₙ)} → P ∪ {t₁=?u₁, …, tₙ=?uₙ}`  when `f ⊂ g`
- **Orient**  `P ∪ {t =? X} → P ∪ {X =? t}`  for `t` non-variable
- **Replace** `P ∪ {X =? t} → {X↦t}P ∪ {X =? t}`  when `X ∈ vars(P)`, `X ∉ vars(t)`
  (the `X ∉ vars(t)` side-condition is the **occur check**)

Solved form and unique-solution-modulo-α: §B.1.23, §B.2.3, §B.2.6. α-unification
via renamings with disjoint variables: §B.1.12, §B.1.19.

### 4.3 Diagrams and the resolution dynamics

Dependency graph `D[Φ;C]` = multigraph, vertices = star indices, edges = matchable
ray-pairs (§49.10). Diagrams = connected-multigraph homomorphisms into `D[Φ;C]`
with per-vertex ray injections (§49.16). A diagram is **correct** if its underlying
unification problem has a solution (§49.34); its **actualisation** `↓δ` is the
resulting star. **Fusion** `∇` (§49.30) and **diagram contraction** `↝` (§49.33)
are the rewrite; contraction terminates and is confluent on correct diagrams
(§49.35–49.36). Abstract execution `AEx` (§49.42); concrete execution `CEx` via
construction space + internal/external extension (§50); interactive execution
`IEx` via stellar interaction + self-interaction (§51). `AEx = CEx` when `CEx`
defined (§50.7); `IEx ≈α CEx ⊎ Φ′` (§51.16).

### 4.4 The load-bearing result: "dead" has a formal definition

Eng **proves abstract execution idempotent for objective constellations**
(`AEx(AEx(Φ)) = AEx(Φ)`, §49.55) and that **idempotence is lost in the presence of
subjective rays** (§49.57); hyper-execution termination with internal-colour
dynamics is an open question he flags (§49.59–60). Subjective rays **create new
polarised rays during execution** and require **semaphore-like synchronization**
(§49.50).

Therefore, in our terms:

- **Objective constellations are *dead*** — idempotent, instantly at their normal
  form, no `[t_birth, t_death)` trajectory, flat valence. This is the formal
  baseline.
- **Subjective / animist constellations** are exactly where non-idempotent,
  self-modifying, synchronizing dynamics live — the substrate signature of the
  reafferent, temporally-extended, mortal agent of §2.

Eng named the fragment where our charge must live "subjective" with no notion of
value or self anywhere in his mathematics. The spec's center of gravity is the
subjective/animist fragment; the objective fragment is the dead control.

### 4.5 First milestone (validation against Eng, not against ourselves)

§55 Horn-clause encoding. Reproduce Eng's worked addition example:

```
Φ⁺_N := [+add(0̄, Y, Y)] + [−add(X, Y, Z), +add(s(X), Y, s(Z))]
query  := [−add(2̄, 2̄, R), R]
expect : IEx_C(Φ⁺_N + query)  ≈α  [4̄]      (Eng §51.11 trace)
```

Then §56 NFA acceptance, with `open-hypergraphs-dot` visualization.

## 5. Architecture decisions

- **open-hypergraphs naive mapping is falsified** (checked against Appendix C):
  Eng = stars-as-vertices, ray-pairs-as-edges, undirected rank-≤2 multigraph,
  rays sub-structure inside vertices; crate = operations-as-hyperedges,
  values-as-typed-nodes, directed. Not isomorphic. The core constellation/diagram
  engine is **our own Eng-faithful datatypes**. `open-hypergraphs` (`=0.3.1`) +
  `open-hypergraphs-dot` (`=0.2.4`) are used only for (a) Graphviz visualization
  and (b) the Ch 10 MLL proof-net / cut-elimination layer, where SMC string
  diagrams genuinely are the right model. Reversible only if a deeper
  correspondence emerges at the `lax::Var`/`unify`+`quotient` level.
- Cargo workspace at repo root; member `crates/stella-core`; Python RAG tree
  untouched.
- Cost / reachability / termination accounting is first-class in the operational
  semantics from the first definition — not as the seat of valence, but as the
  instrument the loop uses to feel its own viability, so Phase 4 needs no kernel
  re-verification.

### 5.x Known prototype deviations

The Rust prototype's `expand_constellation` uses a fixed finite copy-supply (k copies of animist stars) as a finiteness cutoff; Eng's reference constellation is non-linear/infinite supply (§51.13); this is a prototype bound, not Eng semantics. The HOL4 track must implement the unbounded supply.

**RESOLVED (2026-05-16) for the subjective fragment.** `subjective.rs`
(`subjective_stream`, L1a–d) carries no copy-cap and is genuinely unbounded; the
deathless artifact was the *harness* round-cap + a corpus with no dissoluble
member. Path (a): Eng's §74.7/§75.8 black-hole (intentional non-termination ⇒
`∅`) wired into the subjective stream — natively faithful where the bounded Ch11
engine could only surrogate it. Death is positively certified, never a timeout;
see `docs/01` §3.2 (death certificate, LOCKED before code) and §4 (corpus).

## 6. Pre-registered falsification (the nulls)

Specified *before* the code, sharpened to the subjective/animist fragment. The
project fails — and we say so — if any of:

- Reafferent closure (the §2.2 cycle property) **only ever appears because
  sensor/motor rays were hand-tagged**, never because it self-organized in the
  subjective/animist fragment.
- Each closure layer is **causally sealed** from the others (no cross-level
  capture, no gut-brain-style bleed): §2.3 is then decoration, not structure.
- Attraction/repulsion **only accretes under per-task hand-tuning** of the
  environment or the closure criterion (engineered one layer up).
- The subjective/animist fragment is **provably as idempotent as the objective**
  one in every case we can construct (no non-trivial trajectory ⇒ no `[t_b,t_d)`
  ⇒ no charge).

A null result here is a real result; the project is designed so the
Temporal-Gap-testability deliverable (a substrate where Bennett's unprovable
OPTION-1/2 wager becomes empirical) stands even in the null case.

## 7. Phase plan & cash-out rule

0. **(done)** Eng digest extracted; workspace scaffolded; this spec.
1. Term + Appendix-B Martelli–Montanari unifier (Rust), tests.
2. Eng-faithful constellation/diagram datatypes; `AEx`/`CEx`/`IEx`.
3. Horn-clause addition milestone (§4.5); then NFA + viz.
4. In parallel: HOL4 formalization of §4.1–4.4; headline metatheorem =
   Eng §65 "sufficient conditions for logical emergence"; MLL+MIX then MLL
   (Ch 10); proof-producing translation to CakeML.
5. Phase 4: subjective/animist fragment coupled to a partner-constellation
   environment; instrument for self-organizing reafferent closure against §6.

Cash-out rule (Stage 9, on ourselves): no conceptual stage advances unless it
becomes code or proof or a measurable behavior. Arguing past convergence is the
totality demon this rule forbids.
