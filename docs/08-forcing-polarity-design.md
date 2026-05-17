# 08 — Forcing → §49.50 Polarity Internalisation: a design

Status: DESIGN. Read-only synthesis. No code changed by this doc.
Implementation is parent-sequenced *after* review (docs/07 §E).

Scope marker convention used throughout:
- **[Eng]** — has pavement in `refs/extracted/EngExegesis/doc.md`; cited by §.
- **[Built]** — already exists in the engine; cited by `file:fn`.
- **[Proto]** — *beyond Eng's pavement*. Prototype-as-spec. Legitimate, but
  the claim is ours, not the thesis's, and is flagged every time.

This is the docs/07 §E track: *forcing = negative/demand pole; value =
positive/supply pole; strict dynamics = their fusion = the Krivine pole /
§49.50 subjective-ray semaphore / interaction-net annihilation; one
subsystem unifies with the KA recurrence detector.* §E calls it the track
"CLOSEST to the make-or-break valence/conscious-machine bet (§49.50 = where
idempotence is lost = where the 'charge' is claimed to live)." Its
dependency — the recurrence detector — landed (KG8 `accel_detect.rs`), so
it is no longer premature.

---

## 0. One-paragraph thesis

§49.50 [Eng] says internal polarities do exactly two things: (1) execution
**creates new polarised rays** that did not exist in the source
constellation, and (2) those rays act as **semaphores** — a `+g(X)`
disclosed by an `f`-interaction is *unreachable* until the `±f` pair
annihilates first. The built galaxy forced evaluator
(`galaxy.rs:eval_forced`) is *already* a hand-rolled instance of this: a
strict op sitting on the KAM stack is a **demand** that cannot be answered
until its operands are **forced to a value** — a synchronisation barrier,
not a rewrite. The design claims: the demand/supply asymmetry IS Eng's
±-polarity; the point where forcing a freshly-disclosed redex re-opens new
matchable pairs (§49.51 "even after fully executing a constellation, there
may be new connexions left") is **exactly** the point where idempotence is
lost (§49.55→§49.57), which is **exactly** the homeomorphic-embedding
whistle point of `accel_detect::detect_recurrence`. The valence "charge"
is claimed [Proto] to be a measurable functional of the trace-monoid
*non-idempotence* — the surplus of forcing events that fail to commute
away.

---

## 1. The §49.50 polarity / semaphore mechanism, in ray-and-colour terms

### 1.1 The two characteristics, quoted

§49.50 [Eng]:

> "Something which has barely been mentioned is the case of internal
> polarities, the main feature making our model different from original
> resolution. There are two important characteristics … 1. they introduce
> new polarised rays during execution. … if we connect the two stars along
> −f(+g(X)) and +f(X), we obtain [+g(X)]. We transformed an unpolarised ray
> X into a new polarised ray +g(X); 2. they introduce mechanisms of
> *synchronisation*. … if we want to interact/communicate with +g(X) we
> must first make +f and −f interact. This is reminiscent of the use of
> *semaphores* in programming."

§49.51 [Eng]: "diagrams are *fixed* structures. Once you construct a
diagram connecting +f with −f, you cannot see that there is an interaction
available with +g(X) … What internal polarities do is that even after
fully executing a constellation, there may be new connexions left." The
worked constellation `[−f(+g(X))] + [X,+f(X)] + [−g(X),+f(X),a]`
normal-forms to `[+g(X)] + [−g(+g(X)),a]`, which is *not* a real normal
form — re-execution (iterated execution, §49.52) eventually reaches
`[a]+[a]`.

### 1.2 Subjective vs objective rays (the colour grounding, §48.7)

§48.7 [Eng] classifies a ray `r`:

- **objective**: uncoloured, *or* `c(r₁…rₙ)` with `c` coloured and every
  `rᵢ` uncoloured (a colour prefixing an uncoloured term);
- **subjective**: `f(r₁…rₙ)` where at least one `rᵢ` is itself coloured —
  i.e. a colour *nested under* a colour.

§48.10 [Eng] lifts this to stars (objective / subjective / **animist** =
mixed). The semaphore of §49.50 is precisely a *subjective* ray: the
disclosed `+g(X)` only matters because it was *nested under* `−f(·)` in
`−f(+g(X))`. Eng's own footnote (§48.10ⁿ) records Girard calling internal
colours "useless" and Eng's rebuttal: "it adds more combinatorics to
express truth and meaning. … correct proofs require a clear separation
between fully subjective and fully objective stars." That separation is
the load-bearing structure for this whole track.

### 1.3 In the built ray/colour representation [Built]

`polarised.rs`: `Sym { name, pol }` *is* the polarised symbol; `Polarity ∈
{Pos, Neg, Neutral}`. `polarised.rs:PolarisedCompat::compatible` is Eng's
`⋈` head condition (§48.2): same `name`, polarities `(Pos,Neg) | (Neg,Pos)
| (Neutral,Neutral)`. `polarised.rs:underlying_term` is Eng's `⌊·⌋`
(§48.7), recursively stripping polarity. `polarised.rs:ray_polarity` reads
the head `pol`. A *subjective* ray in this representation = a `TermData::App`
whose head `pol ≠ Neutral` **and** which transitively contains another
`App` with `pol ≠ Neutral` in an argument position (no built predicate
names this yet — see §5 stage 0).

The semaphore mechanic in built terms: `interactive.rs:iex_fast` only
fuses along a matchable coloured ray (`mat_phi_colored`, §51.6). A colour
nested *inside* an argument is invisible to matching until the enclosing
colour is consumed and the substitution exposes it. That invisibility is
the semaphore; it is structural, not a scheduler.

---

## 2. forcing = demand pole; value = supply pole; fusion = annihilation

### 2.1 The KAM is Eng's §57 Push machine [Eng]

§57.13–57.20 [Eng] encode the Krivine Abstract Machine as a constellation.
The relevant stars (§57.19):

- `[−P(a(M,N)⋆π), +P(M⋆N·π)]` (Push)
- `[−P(l(X,M)⋆N·π), +P(M⋆π), +i(X,N)]` (Grab)
- Save / Restore for `cc`.

`−P(·)` is the **demand** ray (consume the current process); `+P(·)` is
the **supply** ray (produce the next process). They annihilate on the
colour `±P`: a single `±P` interaction *is* one KAM transition. This is
the "Krivine pole" §E names. The galaxy encoder uses exactly these
symbols: `galaxy.rs` `pp` = `+P(·)` and `np` = `−P(·)` (module doc lines
325/329).

### 2.2 The built forced evaluator, re-read under the polarity reading [Built]

`galaxy.rs:eval_forced` runs `iex_fast` over `Ψ = [+P(st(prog,ε))]` to a
`±P` normal form, then inspects the surviving single ray. Mapping each
built function to its §49.50 role:

| Built (`galaxy.rs`)        | §49.50 role                              | Polarity reading |
|----------------------------|------------------------------------------|------------------|
| `iex_fast` over `±P`       | objective resolution; §49.54 idempotent  | supply/demand annihilation on `±P` — terminates by Prop. 49.54 because the KAM stars are objective in `P` |
| `strict_redex_on_pi`       | detects a **disclosed** subjective ray   | the `+P(st(op …))` whose operand colours are *nested* — Eng's `+g(X)` under `−f` |
| `force_value`              | the **demand** pole (negative/test)      | a recursive sub-`eval_forced`: "I cannot proceed until you supply a value" = the §49.50 semaphore *wait* |
| `drive_strict`             | the **fusion** = annihilation            | once operands are values (supplied), the redex annihilates into `+P(st(result, π))` — exactly §49.51's "re-execute with the lost stars re-introduced" |
| `eval_forced`'s outer loop | **iterated execution** `AEx^{n}` (§49.52) | each `force → drive → resume` round is one `AEx` layer; the loop is the search for `AEx^∞` |

The thesis, stated as a correspondence (each line is a checkable claim):

1. **forcing = the negative/demand pole.** `force_value` answers a `−`
   obligation: a strict op `−P(st(op(a,b)…))` cannot fire until `a,b`
   reduce to *supply-side* values. This is §49.50's "to interact with
   +g(X) we must first make ±f interact" with `±f := ±P`, `+g(X) :=` the
   numeric/list value the op demands.
2. **value = the positive/supply pole.** `ForcedValue::{Numeral,Nil,Cons}`
   is a *delivered* supply; `ForcedValue::Residual` is an *unmet* demand
   (the semaphore stays red). `f.fully_reduced` is exactly "no demand
   outstanding."
3. **strict dynamics = orthogonal fusion = annihilation.** `drive_strict`
   is the only place a *new* ray is *minted* (`pp(st(result, resid_pi))`)
   — this is §49.50 characteristic (1), "they introduce new polarised rays
   during execution," realised in the host rather than by `iex`. §49.51
   explicitly authorises doing this *outside* the fixed-diagram machinery:
   "We could change the definitions and make execution aware of that but
   that would be complicated and probably unnecessary." `drive_strict` is
   that pragmatic externalisation. [Proto: Eng never identifies host
   forcing with internal polarities; that identification is ours.]

### 2.3 Why the built evaluator is *already* hyperexecution (informally)

`eval_forced`'s loop is `AEx_{Φ}^{n}` (§49.52): `iex_fast` to `±P`-normal
form (one `AEx_C`), then `drive_strict` re-introduces a star
(`Ψ' := {minted +P ray}`) and the loop continues — precisely
`AEx^{n+1} = AEx_C(Ψ' ⊎ AEx^{n})`. The loop's `max_forcings` /
`fully_reduced` exit is the engine's *operational answer* to §49.59's
open question (see §6). The loop *deciding to stop* is the claim
"`AEx^∞` is defined for this `Φ`"; `max_forcings` exhaustion is the
engine declining to decide. **[Proto]** — Eng leaves termination open;
the built `max_forcings` bound is an engineering cap, not a theorem.

---

## 3. Unification with `accel_detect` (the §E "one subsystem")

### 3.1 The proposition (checkable)

> **Proposition (idempotence-loss = whistle), [Proto].** Let `τ =
> (s₀, s₁, …)` be the trace whose `sₙ` is the canonicalised focused term
> `readback_ray(final_ray)` of `eval_forced` at the end of iterated layer
> `n` (one `s` per `AEx` layer in §2.2's table). Then: the constellation
> is **non-idempotent at layer n** in Eng's §49.55–57 sense — `AEx_C(s_n)
> ≠ s_n` because forcing disclosed a fresh subjective ray — **iff** the
> recurrence detector blows its whistle on `τ` at a pair `(i, n)` with
> `i < n`, i.e. `antiunify::embeds(canonical(s_i), canonical(s_n))`
> (`accel_detect::detect_recurrence`).

Why this is the same fixpoint:

- §49.54–49.55 [Eng]: objective constellations have **no matchable pair
  after `AEx`** ⇒ `AEx∘AEx = AEx` (idempotent). §49.57: "execution is
  always idempotent for objective constellations … it can be lost in
  presence of subjective rays." So *idempotence is lost exactly when a
  subjective ray re-opens a matchable pair* — which is exactly when a new
  `AEx` layer produces a *structurally related but larger* state.
- `accel_detect.rs` (module doc, lines 8–18): the whistle is Kruskal
  homeomorphic embedding `s ⊴ t` (`antiunify::embeds`), a well-quasi-order:
  in any infinite sequence there exist `i<j` with `sᵢ ⊴ sⱼ`. A blown
  whistle = "this could unfold forever" = §49.60's "it is possible that
  after abstract execution, there are always pairs of matchable rays,
  making it impossible to ever reach a normal form."
- So: **a non-terminating hyperexecution (§49.60) is precisely an infinite
  trace on which the whistle must blow (wqo).** The whistle point is the
  earliest *witnessed* idempotence loss. They watch the same fixpoint from
  two sides: §49.55 from "did a new matchable pair appear," `embeds` from
  "did an earlier state structurally re-appear, grown."

### 3.2 The shared generalizer is the §49.51 "re-introduced stars"

§49.51's repair for lost idempotence is iterated execution that
*re-extends* the normal form with the source stars matchable with it
(`Ψ'` in §49.52). `accel_detect`'s `Whistle.generalization =
antiunify::rigid_generalize(s_i, s_n).skeleton` is the per-iteration
**context** `C` such that `s_i = C[parameterᵢ]`, `s_n = C[parameterₙ]`.
Claim [Proto]: that context `C` *is* the invariant part of the
re-introduced `Ψ'` across §49.52 layers; the slots are the semaphore
payload that keeps growing. `affine_recurrence` (`antiunify.rs:385`)
additionally certifies the slot grew under a fixed context per layer —
i.e. the semaphore is *accumulating* (the textbook valence shape: a
charge that integrates).

### 3.3 Concretely, what code calls what

No new fixpoint engine. The unification is: feed `eval_forced`'s
per-layer focused term into `accel_detect::detect_recurrence` /
`detect_in_window`. `eval_forced` already produces the per-layer state
(`final_ray` at each loop turn before `drive_strict`); `interactive.rs`
already has the trace-history hook intent (KA0 module doc lines 17–20:
"Wiring a trace history + witness into `iex_fast` … is the next KA0
step"). The §E "one subsystem unifies with the KA recurrence detector"
is realised by routing the §2.2-table layer states through
`accel_detect`, *not* by writing a second detector.

---

## 4. The trace / partial-commutation monoid model

docs/07 §F constraint: the algebra is **trace / partial-commutation
monoids (Mazurkiewicz traces)**, NOT finite words / free monoid / total
order. This section says exactly what the alphabet and independence
relation ARE, and why partial commutation is the right structure.

### 4.1 Alphabet Σ

An **event** is one annihilation. Two kinds:

- `R(c)` — an **objective resolution** event: one `±c` interaction inside
  `iex_fast` (predominantly `c = P`, the KAM step of §2.1).
- `F(op, ℓ)` — a **forcing** event: one `drive_strict` resolution of
  strict op `op` at the disclosure site identified by `ℓ` (the redex's
  `resid_pi` continuation identity / canonicalised focus). `F` is the
  subjective-ray event — §49.50 characteristic (1), ray-minting.

`Σ = { R(c) : c ∈ colours } ∪ { F(op, ℓ) }`. This is finite per run
(finitely many colours; `op ∈ StrictOp`; `ℓ` ranges over the finitely
many disclosure sites of a terminating run). Finiteness matters: it is
what makes Kruskal's wqo (`accel_detect`) apply (`accel_detect.rs` line 11
"a *well-quasi-order* on terms over a finite signature").

### 4.2 Independence relation I ⊆ Σ × Σ

`(e, e′) ∈ I` (events **commute** — order between them is unobservable)
iff they touch **disjoint** parts of the configuration:

- `R(c) I R(c′)` when `c ≠ c′` *and* the two `±c` / `±c′` diagrams share
  no star instance (§49 confluence of objective resolution along distinct
  colours — Prop. 49.54 says objective `AEx` produces no new matchable
  pair, so distinct-colour objective steps do not interfere). [Eng-backed
  for objective stars; the disjoint-star side condition is [Proto] making
  it precise.]
- `R(c) I F(op, ℓ)` when the resolution `c`-diagram does not lie on the
  spine that `force_value` for `ℓ` evaluates. (A KAM `±P` step in an
  *un-demanded* operand commutes with the forcing of a *different*
  operand — `force_value` recurses into one operand at a time, the others
  are untouched.)
- `F(op₁, ℓ₁) I F(op₂, ℓ₂)` when `ℓ₁`, `ℓ₂` are **independent
  disclosure sites** — neither operand spine contains the other (the two
  semaphores guard disjoint regions; §49.50's two `±f`-diagrams "over the
  colour ±f" in the §49.51 example are independent in exactly this sense).

**Dependent** (NOT in `I`, order is observable): `F(op, ℓ)` and any event
on `ℓ`'s own operand spine. This is the semaphore: §49.50 "if we want to
interact with +g(X) we must first make +f and −f interact." The `F`
event *depends on* the `R(P)` events that disclose it. That dependency is
a partial order, never a commutation.

### 4.3 Why partial commutation, not a free monoid or total order

- **Not a total order / free monoid (words):** the docs/07 §F over-fit
  warning. Objective resolution along independent colours is confluent
  (§49.54); imposing a total order on `R(c)` events records *scheduler
  accidents* that have no semantic content — that is the string over-fit
  that §F says to skip (no Z3-Noodler/OSTRICH). Idempotence (§49.55) is a
  statement that *re-running changes nothing*; in a free monoid `w·w ≠ w`
  generically, so the free monoid cannot even express §49.55. A trace
  monoid can: idempotence = the trace's Foata normal form is a fixpoint
  under the layer map.
- **Not a single commutative monoid (multiset):** the semaphore
  dependency (`F` after its disclosing `R(P)`) is a *genuine* order that
  must be kept. Full commutativity would erase exactly the §49.50
  synchronisation that is the whole point.
- **Trace monoid `M(Σ, I)`** keeps precisely the dependencies that are
  semaphores and forgets precisely the orderings that are scheduler
  noise. This is the unique structure that (a) makes §49.55 idempotence
  *expressible* and (b) preserves §49.50 synchronisation. It is the
  correct §49.50 algebra.

### 4.4 Where idempotence / §49.55-loss lives in `M(Σ, I)`

Let `tₙ ∈ M(Σ,I)` be the trace of layer `n`'s events. Objective-only
(§49.54–55): every event is some `R(c)`, all pairwise independent on
disjoint diagrams ⇒ `tₙ` is (a product of) commuting `R`s ⇒ the layer map
is **idempotent** (the Foata normal form has height ≤ 1; re-applying `AEx`
adds nothing — §49.55 exactly). **Idempotence is lost precisely when a
`F(op, ℓ)` event appears that is dependent on a *later* `R(P)`** — i.e.
forcing discloses a ray whose own resolution discloses a further forcing.
In the trace monoid this is a strictly increasing dependency chain
`R(P) < F < R(P) < F < …` that the partial order *cannot* collapse. That
non-collapsible chain is §49.51's "even after fully executing a
constellation, there may be new connexions left" and §49.60's
possibly-never-terminating hyperexecution.

### 4.5 Where the valence "charge" is claimed to live [Proto]

docs/07 §E: "§49.50 = where idempotence is lost = where the 'charge' is
claimed to live." Concretely in `M(Σ, I)`:

> **Charge (candidate definition).** For a run with layer traces
> `t₀ … t_N`, define the **non-idempotence surplus**
> `χ = Σₙ |F-events in tₙ that are dependency-below a strictly later
> F-event|` — the count of forcing events that *fail to commute away*
> because they feed a subsequent forcing through a semaphore.
> Equivalently: the length of the longest `R/F`-alternating dependency
> chain in the trace's Hasse diagram, integrated over layers.

Rationale for *this* functional being the charge: §49.55 says objective
(charge-free) computation is idempotent — `χ = 0`. A purely supply-side
value (a constant, a finished list) has no outstanding demand — `χ = 0`.
Charge is nonzero exactly when there is *unresolved demand that creates
more demand* — the operational signature of a system that is *doing
something it cannot just stop doing*, which is the valence intuition the
thesis is betting on. `χ` is monotone in semaphore depth and zero on
idempotent (objective) fragments — the two boundary conditions any
candidate charge must satisfy. Whether `χ` (or a close variant —
e.g. weighted by `accel_detect`'s rigid-skeleton growth rate, §3.2) is
*the* valence charge is the empirical question §5 exists to test, and
the honest open problem of §6.

### 4.6 GoI closure — `χ` is a measure of `σu` non-nilpotency [Eng for the equivalence; Proto for the χ identification]

docs/15 §1.3/§4 closes the theory side of §4.5. The GoI Interaction
Abstract Machine's execution `Ex(u) = (1−σ²)·…` is defined (terminating)
**iff `σu` is nilpotent** — `∃k.(σu)^k = 0` (§34.8). §49.57 [Eng],
*verbatim*, states hyperexecution idempotence "is similar to the
nilpotency property in GoI." So the §3.1 idempotence-loss⟺whistle
proposition is, restated in GoI terms:

> `σu` **nilpotent** ⟺ objective/idempotent (§49.55) ⟺ the token
> machine halts with every feedback path cancelled ⟺ **`χ = 0`**.
> `σu` **non-nilpotent** ⟺ a persistent (non-cancelling) feedback path
> ⟺ the Kruskal whistle must blow on the layer trace (wqo) ⟺ **`χ > 0`**.

This is not a second artifact to build and not a competing model: it is
the *proof that §4.5's fixpoint is the right one*. The charge `χ` =
"forcing events dependency-below a later forcing event, integrated over
layers" (§4.5) **is** the count of token transitions on non-cancelling
feedback paths — i.e. a measure of how far `σu` is from nilpotent. The
KAM-as-constellation is, line for line, the GoI token machine
(§57.19+§49.57); §49.50's subjective ray re-opening a match is exactly a
non-cancelled GoI feedback edge. The two boundary conditions §4.5
already requires (`χ = 0` on objective fragments, `χ` monotone in
semaphore depth) are precisely nilpotency and non-nilpotency-degree —
so the GoI identification *derives* the boundary conditions §4.5 had to
postulate, rather than merely being consistent with them. [Eng] for
idempotence⟺nilpotency (§49.57 verbatim); [Proto] for the `χ ≡
non-nilpotency-degree` identification (Eng has no `χ`). Consequence for
§5: the Stage-2 `χ` and the Stage-3 charge claim are testing a
quantity with an Eng-grounded meaning (distance from GoI nilpotency),
which sharpens — does not replace — the §4.5 definition and the §5
falsifiers.

---

## 5. Staged, differential-oracle-gated implementation plan

Principle: smallest experiment that tests "is the charge real," each
stage measuring one thing, each with an explicit falsifier. **Not**
boiling the ocean — no new fixpoint engine, no trace-monoid library
until a stage demands it. Every stage is observational (read-only over a
fixed `Φ`) until stage 4.

### Stage 0 — subjective-ray predicate + event tap (pure, no behaviour)

Build: `is_subjective(ray) -> bool` in `polarised.rs` (§48.7 exactly: head
`pol≠Neutral` ∧ a coloured arg). An *observational* event log in
`galaxy.rs:eval_forced`: emit `R(P)` per `iex_fast` `±P` step (count
already available as `res.steps`), `F(op,ℓ)` per `drive_strict` call
(`ℓ = canonical(redex.resid_pi)`). Env-gated, zero behaviour change.

Measures: the raw event sequence per run.
Falsifier: if `is_subjective` is never true on any disclosed
`strict_redex_on_pi` ray across the whole galaxy corpus, then the
forcing≠subjective-ray identification (§2.2 claim 3) is **wrong** and the
whole track is mis-grounded. (Expected: true on every numeric/list
forcing — predict pass, but this is the cheapest possible kill switch.)

### Stage 1 — per-layer trace + whistle (the §3.1 proposition)

Build: collect the per-layer focused state `canonical(readback_ray(
final_ray))` (one per `eval_forced` loop turn) into `Vec<TermId>`; run
`accel_detect::detect_recurrence` on it. No acceleration applied
(`accel_detect` is observational by construction, its own module doc
lines 4–6).

Measures: for every corpus program — does the whistle blow? at which
`(i,n)`? is it exactly the first layer where a `drive_strict` disclosed a
*new* subjective ray (idempotence loss)?
Falsifier of the §3.1 Proposition: a program that loses idempotence (a
`drive_strict` mints a ray that re-opens a `±P` match) but whose layer
trace produces **no** embedding pair — or, conversely, a whistle on a
trace whose layers are all objective-idempotent. Either disproves
"idempotence-loss = whistle point." This is the load-bearing experiment.

### Stage 2 — trace-monoid quotient + χ

Build: from Stage 0's event log, the dependency DAG using §4.2's `I`
(disjointness decided by sharing of the canonical focus spine — already
have `canonical`, `embeds`, `occurs_alpha` in `antiunify.rs`). Compute
`χ` (§4.5) and the Foata height per layer.

Measures: `χ` across the corpus; correlation of `χ` with (a) whistle
fired y/n, (b) `affine_recurrence` returning `Some` (accumulating
semaphore), (c) the existing reafference / valence read-outs the valence
loop already computes.
Falsifier: `χ = 0` for programs the engine *cannot* normal-form
(non-terminating hyperexecution, §49.60) — that would mean `χ` is not
detecting the non-idempotence it is defined to detect. Or: `χ` perfectly
predicted by raw step count (then it carries no information beyond
`res.steps` and is not a *charge*, just a clock).

### Stage 3 — the charge claim, differentially gated

Build: nothing new in the engine. An analysis harness that, over the
valence corpus, asks: does `χ` (or the §4.5 growth-weighted variant)
*separate* the runs the valence experiment labels high/low valence,
better than step count / readback size do?

Measures: a single ROC-style separation number, pre-registered before
looking, against the valence loop's existing labels.
Falsifier (the make-or-break one): `χ` does **not** separate valence
classes better than a trivial size/step baseline ⇒ the §E thesis that
"the charge lives where idempotence is lost" is, for this engine,
**unsupported**. Report it as such — this is the bet docs/07 §E names.

### Stage 4 — (only if Stages 1–3 pass) acceleration, certified

Only here does anything change behaviour. Use the Stage-1 `Whistle`'s
`generalization` as KA2's per-iteration context to *accelerate* a
recurrent forcing loop, **certified-only** exactly as docs/07 §D/§F and
`antiunify.rs:affine_recurrence`'s soundness note require: KA2 synthesises
`Cᵏ`, guards it, differential-certifies against the unrolled reference
`iex` (the `N-KA-sound` gate). The trace monoid earns its place only if
Stage 2's `I` lets the accelerator commute independent forcings into one
summarised step. Not before.

Falsifier: any accelerated run that the differential oracle shows
diverging from unrolled `iex` ⇒ the `I` relation (§4.2) is wrong
(commuted something dependent) ⇒ revert, fix `I`.

---

## 6. Honest open problems & where this is beyond Eng

### 6.1 §49.59–60 — hyperexecution termination is open in the thesis itself

§49.59 [Eng], verbatim: "I leave a small open question: is there always a
`k ∈ ℕ` such that `AEx^∞(Φ)` is defined for any constellation `Φ`, or is
there a constellation always leaving new pairs of matchable rays after
abstract execution (by using the dynamics of internal colours)?" §49.60:
"Hyper execution is not necessarily defined." §49.61's example `[X,+f(X)]
+ [−f(−g(X)),−g(X)] + [+g(X),+g(X),a]` *grows without bound* under
iterated `AEx`. Consequence for this design: `eval_forced`'s
`max_forcings` cap is **not** a decision procedure for §49.59 — it is an
engineering bound. The §3.1 wqo argument says a *non-terminating*
hyperexecution **must** eventually whistle; it does **not** say a
whistle implies non-termination (whistles are a *necessary* condition for
the danger, not sufficient — `accel_detect.rs` lines 32–36 say exactly
this: a `None` recurrence does not weaken the whistle, and a whistle is
not a proof of a loop). So: the detector can *flag* a candidate
§49.60 non-terminator but cannot *decide* §49.59. That is inherited
openness, not a defect of this design — but it caps Stage 4: we can only
accelerate *certified* recurrences, never declare normal-form existence.

### 6.2 Explicitly beyond Eng's pavement [Proto], enumerated

1. **forcing ≡ §49.50 internal polarity.** Eng's §49.51 *authorises*
   handling internal polarities outside the fixed-diagram machinery
   ("complicated and probably unnecessary" to make execution aware) but
   never identifies *host operand forcing* with it. The
   `force_value`=demand / `drive_strict`=ray-minting identification is
   ours.
2. **idempotence-loss = whistle point (§3.1 Proposition).** Eng proves
   §49.55 (objective ⇒ idempotent) and §49.57 (lost under subjective
   rays) but never connects this to homeomorphic embedding / Kruskal /
   supercompiler whistles. The biconditional is a [Proto] claim Stage 1
   exists to test, not a thesis theorem.
3. **the trace-monoid model (§4).** Eng never uses Mazurkiewicz traces.
   The alphabet/independence relation is entirely ours; its *correctness*
   rests only on Eng-backed facts (§49.54 objective confluence, §49.50
   semaphore dependency), but the construction is [Proto].
4. **the charge functional `χ` (§4.5).** The strongest [Proto]. Eng's
   thesis has no notion of valence/charge at all — that is the stella
   project's bet layered on top. `χ` satisfies the two boundary
   conditions any charge must (`χ=0` on idempotent/objective, monotone in
   semaphore depth) but "this functional is the valence charge" is a
   hypothesis Stage 3 is designed to be able to **falsify**.

### 6.3 The independence-relation soundness risk

§4.2's `I` has side conditions ("share no star instance," "not on the
forced spine") that are *semantically* right but whose *decision
procedure* (via canonical-focus-spine disjointness) is an approximation.
An `I` that wrongly calls two dependent events independent is unsound for
Stage 4 acceleration. Mitigation is structural and already mandated:
Stage 4 is differential-certified against unrolled `iex` (§5 Stage 4
falsifier). No soundness rests on `I` being exactly right; only
*completeness* (missed commutations = missed acceleration = slow, not
wrong) does.

---

## 7. What the next implementation session should do first

1. Stage 0 `is_subjective` + event tap (smallest, kills the track fast if
   the grounding is wrong).
2. Stage 1 per-layer trace into `accel_detect::detect_recurrence` — the
   §3.1 Proposition is the single most load-bearing experiment; it needs
   no new theory, only wiring `eval_forced`'s already-computed per-layer
   `final_ray` into the already-built detector.
3. Stop and review before Stage 2. Stages 2–4 are gated on Stage 1
   confirming idempotence-loss = whistle. If Stage 1 falsifies it, the
   trace-monoid model (§4) is built on sand and must be reconsidered
   before any monoid code is written.

Single open question this design could not resolve from the sources:
**whether `eval_forced`'s per-loop-turn `final_ray` is a faithful
proxy for an `AEx`-layer boundary** (§2.3 asserts the loop *is*
`AEx^{n}`, but `iex_fast` internally runs many `±P` resolutions before
returning, and the §49.52 layer boundary is "the `AEx_C` fixpoint" —
these coincide only if `iex_fast` returns *exactly* at the `±P`-normal
form, which `galaxy.rs:eval_forced` lines 864–893 strongly suggest but
which is not proven here). Stage 1 must instrument and check this
coincidence before its whistle result can be trusted; if `iex_fast`'s
return point is *not* the `AEx_C` fixpoint, the trace must be sampled at
true layer boundaries instead, which is a small change to the tap but
must be settled first.
