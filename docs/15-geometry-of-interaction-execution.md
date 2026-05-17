# 15 — Geometry-of-Interaction / Token-Machine Execution for the galaxy

Status: RESEARCH SYNTHESIS. Read-only. No code changed by this doc.
One of four parallel reduction-technology surveys (docs/12 interaction
combinators, docs/13 supercompilation, docs/14 staged compilation,
**docs/15 this** GoI/token machine). Harvested → docs/16 decision.

Scope-marker convention (as docs/08):
- **[Eng]** — pavement in `refs/extracted/EngExegesis/doc.md`, cited by §.
- **[Built]** — exists in the engine; cited `file:line`/`file:fn`.
- **[Proto]** — beyond Eng's pavement / beyond the codebase. Our claim,
  flagged every time.

---

## 0. One-paragraph verdict (full argument in §6)

A Geometry-of-Interaction token machine is *exactly on-thesis* — Eng's
whole programme is post-GoI transcendental syntax, and the KAM-as-
constellation Eng gives in §57.19 [Eng] **is already a token machine**
(`±P` is the GoI token; `π` is the GoI stack; the engine never has to
"adopt" GoI, it is running a token machine now). **But** the GoI token
machine does **not** solve the measured `data[0]` blocker, because the
measured blocker (docs/07 §B b6c65d5, §A1) is a *long non-redundant*
reduction — the answer requires Θ(N) genuine token transitions for N
the reduction length, and a token machine pays one machine step per
transition with **worse** constant factor than `iex_fast`, not fewer
steps. GoI's space win (don't materialise the term) is **already had**
by this engine — `eval_forced` already never materialises a normal-form
term graph; it threads a KAM stack `π` and inspects a single surviving
ray (`galaxy.rs:650` `single_ray`, `:890` `eval_forced`). The blowup
that defeats `data[0]` is **time (transition count)**, not materialised
intermediate term space, so the GoI sidestep does not apply. GoI is the
correct *theoretical lens* on the §49.50 design (§5 makes the
correspondence precise and it is tight) but it is **not** the
galaxy-execution path. The galaxy-execution path is step-count
reduction: docs/13 (supercompilation/§49.50-acceleration) or docs/14
(staged compilation), not docs/15.

---

## 1. What a GoI token machine is, and the precise stellar correspondence

### 1.1 The IAM, quoted [Eng]

§36.3 [Eng]: a proof-structure `S=(V,E,in,out,ℓ_E)`; an IAM configuration
is a tuple `(d, v, π)` — `d ∈ {⊼,⊻}` the token *direction*, `v` the
current vertex, `π` a *stack* `π ::= ∅ | l·π | r·π`. Reversible
transition rules route the token; "the combination of push and pop will
cancel `l*l` and `r*r` so to reproduce the algebra `L*`" (§36.3). §36.1
[Eng]: "the graph rewriting of proof-structure is *not necessary*: the
execution of proofs and programs can be done by a process of exploration
of a structure … it is possible to reduce λ-terms *without syntactic
transformation*. Actual duplication is not necessary." That is the
entire GoI value proposition: **execution = a token's trajectory through
a fixed net; the net is never rewritten; the term is never built.**

§33/§34.7 [Eng]: the *execution formula* `Ex(u,σ) = (1−σ²)u(1−σu)⁻¹
(1−σ²)`, defined (terminating) iff `σu` is **nilpotent** — `∃k.(σu)^k=0`
(§34.8). §49.57 [Eng] explicitly: idempotence of hyperexecution "is
similar to the nilpotency property in GoI." This is the load-bearing
bridge for §5.

### 1.2 The stellar / Krivine token machine — *already built* [Eng]+[Built]

The decisive structural fact: Eng **already gives the token machine for
this engine**. §57.19 [Eng], the KAM-as-constellation:

```
[−P(a(M,N)⋆π), +P(M⋆N·π)]                 (Push)
[−P(l(X,M)⋆N·π), +P(M⋆π), +i(X,N)]        (Grab)
[−P(cc⋆M·π),    +P(M⋆ k_π·π)]             (Save)  …
```

This *is* the IAM specialised to the λc syntax tree (Eng even cites
§36.5 [Eng] "machine for lambda-terms … one transition for λ-terms
corresponds to several transitions of the IAM"). The correspondence is
exact, not analogical:

| GoI / IAM (§36.3) | Stellar / KAM-constellation (§57.19) | Built |
|---|---|---|
| token direction `d ∈ {⊼,⊻}` | ray polarity: `+P` = token going down (supply/produce next process), `−P` = token going up (demand/consume current) | `polarised.rs:ray_polarity`, `term.rs Polarity` |
| token *position* `v` | the focused term `M` in `+P(st(M,π))` | `galaxy.rs:655 st_inner` |
| token *stack* `π` | the KAM stack `π` (`N·π`, `eps`) — *literally the same `π`* | `galaxy.rs` `pp`/`np`/`st`, §1 module doc 325/329 |
| one IAM transition `⤳` | one `±P` annihilation (fusion on colour `P`) | `interactive.rs:451 fuse`, `:1086 iex_fast_inner` |
| net `S` (fixed, never rewritten) | the reference constellation `Φ` (non-linear, fixed for the whole run — `interactive.rs:13` "Φ … infinite supply", `:1033 build_accel` "pure function of Φ") | `galaxy.rs:417 prim_stars` ∪ `:398 delta_star` |
| token routing (no graph rewrite) | `iex_fast` consuming the *linear* `Ψ` against the *non-linear* `Φ` — `Ψ` is the token, `Φ` is the net | `interactive.rs:1016 iex_fast` |
| Ex defined iff `σu` nilpotent (§34.8) | `AEx^∞` defined iff idempotence reached (§49.57–58) | (the §49.59 open problem) |

**This is the central finding of this doc:** the engine is *not missing*
a GoI token machine. `iex_fast` over the §57.19 `±P` stars **is** the
GoI/IAM execution of this program. `Φ` is the fixed net; `Ψ = [+P(st(
prog,ε))]` is the initial token configuration (`galaxy.rs:897`); each
`±P` fusion is one token transition; `eval_forced`'s loop is the token
run. There is no "compile Φ + entry into a net" step to do — §57.19 + the
δ-star encoding (`galaxy.rs:24` module doc) **is** that compilation, and
it is **[Built]**.

### 1.3 The §49.50 dynamics ARE the token dynamics — precisely

docs/08 §0/§1 reads §49.50 [Eng] as: (1) execution mints new polarised
rays; (2) a disclosed `+g(X)` is a **semaphore**, unreachable until the
`±f` pair annihilates. In GoI terms this is *exactly* the token machine's
**stack discipline**:

- §49.50 ray-minting (`−f(+g(X))` ⋈ `+f(X)` ⇒ `[+g(X)]`) ↔ IAM **push**:
  the token entering a connective pushes `l`/`r` onto `π` (§36.3). The
  new polarised ray *is* the deeper net position the token can now reach.
- §49.50 semaphore ("to interact with `+g(X)` we must first make `±f`
  interact") ↔ IAM **pop discipline**: the token cannot read the inner
  position until the matching push/pop on `π` cancels (`l*l → 1`, §36.3).
  The semaphore *is* the GoI stack: `+g(X)` is reachable only after the
  `±f` annihilation pops the guarding frame. docs/08 §1.3 already names
  this: "A colour nested *inside* an argument is invisible to matching
  until the enclosing colour is consumed … That invisibility is the
  semaphore; it is structural, not a scheduler." That is *verbatim* the
  GoI claim that execution is path/stack-controlled, not rewrite-
  controlled.
- §48.7 subjective vs objective rays [Eng] ↔ GoI **persistent vs
  cancelled paths** (§35.9–35.15 [Eng]: a path is regular iff its weight
  `ω(ρ)≠0`; regular = persistent = preserved by cut-elim). An objective
  constellation has no subjective ray ⇒ §49.54 no matchable pair after
  `AEx` ⇒ idempotent (§49.55) ⇒ token paths are all straight/non-
  re-opening ⇒ GoI `σu` nilpotent. A subjective ray re-opens a match
  (§49.57) ⇒ a non-cancelled feedback path ⇒ potential non-nilpotency.
  **The §49.55-idempotence ⟺ GoI-nilpotency identification is Eng's own
  (§49.57 verbatim), and it is the same fixpoint docs/08 §3.1 routes
  through `accel_detect::embeds`.**

**Answer to required item (4): yes, GoI is the concrete realisation of
docs/08's forcing-polarity design — and the identification is tighter
than docs/08 itself states.** docs/08 §2.1 calls the `±P` annihilation
"the Krivine pole"; §1.2 here shows that pole *is* the IAM token. The
idempotence-loss⟺whistle proposition (docs/08 §3.1) is, in GoI language,
"the execution formula `Ex(u,σ)` fails to be defined ⟺ `σu` is not
nilpotent ⟺ a persistent feedback path exists ⟺ the Kruskal whistle
must blow on the layer trace (wqo)". docs/08's charge `χ` (§4.5: the
non-idempotence surplus) is, precisely, **a measure of the
non-nilpotency of `σu`** — the count of token transitions on
non-cancelling feedback paths. This is the cleanest available statement
of docs/08 §4.5 and it is a GoI statement. [Proto] for the χ
identification (Eng has no χ); [Eng] for idempotence⟺nilpotency.

---

## 2. The asymptotic argument for the MEASURED blocker — GoI does NOT help

This is the section that decides the verdict. Be exact about what the
blocker is.

### 2.1 What the blocker actually is [Built, measured]

docs/07 §A1, b6c65d5 [Built, measured negative]: Lever C (memoised graph
reduction, `is_ground`-gated, value-identical — `galaxy.rs:849 FORCE_MEMO`,
docs/11 §C) was implemented and **does not crack `data[0]`** (still
non-terminating in 150 s). The recorded conclusion: "the galaxy image
payload is *not* redundancy-bound; it is a **genuinely long non-redundant
reduction**." docs/11 §A Fact-2: a constant-factor win "multiplies a
non-terminating-in-150 s reduction by a constant and it is still
non-terminating. The >10× is therefore necessarily algorithmic."

So the blocker decomposes as:

- **NOT** materialised-intermediate-term *space*. `eval_forced` already
  never builds a normal-form term graph: it keeps `Ψ` as a single
  process star (`galaxy.rs:897,954` `psi = vec![vec![new_ray]]`), threads
  the KAM stack `π`, and inspects one surviving ray (`single_ray :650`,
  `st_inner :655`, `readback_ray :796`). It is *already* a stack-machine,
  not a term-rewriter accumulating a blown-up term. Memo (Lever C) only
  helped re-forcing of *shared* structure; the negative result proves the
  reduction is **not** dominated by re-materialised shared subterms.
- **IS** transition *count*. `data[0]` requires Θ(N) genuine,
  non-redundant KAM/`±P` transitions for large N (galaxy lists are
  "millions of `cons` cells deep", `galaxy.rs:45` module doc; the
  image-data spine is a long arithmetic/list computation). Each is real
  work the answer depends on; none is redundant (Lever C disproved
  redundancy-bound).

### 2.2 Why a GoI token machine cannot reduce that count [Proto, decisive]

The GoI/IAM space argument (§36.1, §36.6 [Eng]) is: *don't materialise
the term; route a token instead — bounded space.* Two independent
reasons this does not unblock `data[0]`:

1. **The space win is already realised.** §2.1: `eval_forced` is already
   a token/stack machine that does not materialise the term. A GoI
   re-implementation would buy the *same* space profile the engine
   already has. There is no blown-up materialised term for GoI to *not*
   build — docs/08 §1.3, `galaxy.rs:890` confirm the engine is already
   token-shaped. **GoI's distinguishing advantage is a no-op here.**
2. **Token count = transition count, with a worse constant.** A token
   machine computes the answer in **exactly one token traversal per
   reduction step** the answer depends on (IAM: one `⤳` per net edge
   crossed; §36.5 even notes one λ-transition = *several* IAM
   transitions). For a *non-redundant* reduction of length N the token
   crosses Θ(N) edges — the **same Θ(N)** the engine already pays as
   `res.steps`. Worse: §36.6 [Eng], verbatim and damning — *"Using the
   GoI for λ-calculus has the particularity of executing by analysis of
   a static structure … This seems space-efficient **but the complexity
   is hidden in how the machine is treated (in particular, the data
   accumulated in stacks).**"* The token's `π`/`σ`/`δ` stacks (§36.4
   exponentials) grow with the *same* information `eval_forced`'s `π`
   already carries; the IAM additionally **re-walks** the net for each
   reversible transition (§36.3), a classic GoI pathology: GoI's constant
   factors are notoriously bad (token re-traversal where graph reduction
   does one rewrite). For a Θ(N) non-redundant reduction GoI is Θ(N)
   token steps × a *larger* per-step constant than the existing `±P`
   fusion. It is **strictly worse** than `iex_fast` on the measured
   blocker.

> **Asymptotic verdict.** GoI converts term *space* to token *time*. The
> `data[0]` blocker is already time-bound (transition count), not
> space-bound (the engine is already token-shaped; memo proved
> non-redundant). Trading the space you already have for *more* time is
> the wrong direction. **GoI does not avoid the `data[0]` blowup; it
> re-pays it with a worse constant.**

The only thing that helps a *long non-redundant* reduction is **fewer
steps** — i.e. *summarising* a recurrent sub-run into a closed form
(docs/13 supercompilation/distillation, docs/11 Lever D KA2) or
*specialising* the interpreter so each remaining step is O(1) (docs/14
Lever B Futamura). GoI is neither: it is a faithful re-encoding of the
*same* step sequence. (Note: GoI *optimal-reduction* sharing — §29.29,
§36.1 "actual duplication not necessary" — is real, but that is the
*interaction-combinator* line of docs/12, which shares *redexes*, not
the IAM token machine of this doc. docs/12, not docs/15, owns that
lever.)

---

## 3. Faithfulness

The faithfulness story for GoI is the *easiest* of the four surveys, for
the same reason GoI does not help: there is **nothing new to make
faithful**. `iex_fast` over the §57.19 `±P` stars already *is* the token
machine (§1.2). The reference oracle `iex` (`interactive.rs:861`) is the
spec-exact KAM-constellation execution; `iex_fast` is its byte-/result-
equivalent jet, already gated.

- **`psi_compatible` [Built, proven]** (`faithfulness.rs:115`): ɟ-conceal
  + α-canonical multiset compare of the two final interaction spaces;
  "no false compatible" (`faithfulness.rs:41` §A.4). A GoI execution that
  is genuinely the §57.19 token run produces the *same* `Ψ` as
  reference `iex` by construction (it is the same `±P` resolution
  sequence in a different presentation) ⇒ `psi_compatible(iex, goi)`
  trivially green. This is the docs/11 §C.3 "P-MEMO is value identity"
  argument again: a faithful GoI machine changes presentation, never the
  computed normal form.
- **Two-tier** (docs/11 §B.4 / §F): reference `iex` always; the GoI path
  only in the fast tier, `psi_compatible`-gated per corpus, with
  reference `iex` as the differential oracle (`evaluate.rs`
  `OracleMode`/`OracleStatus` [Built]).
- **Deopt:** any `psi_compatible` red ⇒ fall back to reference
  `iex_fast`/`eval_forced` (the existing two-tier deopt path).
- **Where GoI semantics could diverge — the one real risk:** the IAM is
  defined for the **multiplicative** fragment with clean push/pop
  cancellation (§36.3); the §36.4 **exponential** machine (boxes,
  copies, the `δ`/`σ` stacks) is "simplified and incomplete" by Eng's
  own statement, and §35.18 [Eng] flags "**no exact preservation of
  exponential paths**" — the GoI does not perfectly track duplication.
  Galaxy is binder-free combinator code (`galaxy.rs:8` module doc) so
  there are no λ-boxes, but the combinator stars (S/C/B duplicate their
  argument) are *exponential-flavoured* (non-linear use). A naive IAM
  encoding could **diverge on a duplicating combinator** (the classic
  GoI exponential-path imprecision). Mitigation is structural and
  already present: we would not write a fresh IAM — we would keep using
  the §57.19/`prim_stars` constellation (which handles duplication
  correctly via Φ's non-linear fresh-copy semantics, `interactive.rs:95
  freshen_star`), so the divergence risk is *avoided by not
  re-implementing the machine*. Which is also why GoI buys nothing: the
  faithful GoI machine **is** the engine.

Result-equivalence requirement (must compute the SAME normal form): met
trivially **iff** we do not re-implement — i.e. there is no faithful GoI
artifact distinct from the current engine to gate. A *distinct* hand-
written IAM would re-open the §35.18/§36.4 exponential-path soundness
problem for the duplicating combinators, an unforced error.

---

## 4. The §49.50 unification — stated precisely

Required item (4), precisely. **GoI is the theoretical *characterisation*
of the §49.50 forcing-polarity design; it is not a new *implementation*
of it.** Exactly:

1. **Identity of dynamics.** The §49.50 `±f`-semaphore = the IAM stack
   discipline (§1.3). The `±P` annihilation = one IAM token transition
   (§1.2). `eval_forced`'s `force → drive_strict → resume` loop
   (`galaxy.rs:890`) = the IAM run; `drive_strict` minting
   `+P(st(result,π))` (`:788`) = §49.50 characteristic (1) ray-minting =
   the token push. docs/08 §2.2's whole correspondence table is, line
   for line, a GoI token-machine table. [Eng-grounded via §57.19+§49.57;
   the host-forcing=ray-mint identification is docs/08's [Proto], not
   weakened or strengthened here.]
2. **Identity of the termination condition.** §49.57 [Eng] *verbatim*:
   hyperexecution-idempotence "is similar to the nilpotency property in
   GoI." So docs/08's idempotence-loss ⟺ whistle proposition (§3.1) **is**
   "GoI `σu` non-nilpotent ⟺ Kruskal whistle (wqo)". The charge `χ`
   (docs/08 §4.5) = a measure of `σu` non-nilpotency = the count of token
   transitions on non-cancelling feedback paths. **State precisely:** `χ
   = 0` ⟺ `σu` nilpotent ⟺ objective/idempotent ⟺ the token machine
   halts with all paths cancelled; `χ > 0` ⟺ a persistent feedback path
   ⟺ §49.60 possibly-never-terminating hyperexecution. This is the
   sharpest available formulation of docs/08 §4.5 and it is GoI's.
3. **Consequence for the project.** The §49.50-track *implementation* is
   **not** "build a GoI machine" (the machine exists — §57.19/`iex_fast`).
   It is docs/08's *staged plan* (Stage-0 `is_subjective` predicate +
   event tap → Stage-1 per-layer whistle → χ). GoI supplies the *proof
   that that plan's fixpoint is the right one* (nilpotency = idempotence,
   Eng's own §49.57), not a different artifact to build. **docs/15's
   contribution to the §49.50 track is conceptual closure, not an
   implementation path.**

---

## 5. Staged, falsifiable plan (and ordering vs docs/11–14)

Because §1.2's finding is "the GoI machine is already built", the staged
plan is *not* "implement a token machine" — that would be rebuilding
`iex_fast` worse (§2.2, §3). The only falsifiable thing GoI proposes that
the engine does not already do is a **GoI nilpotency / persistent-path
early-detector** as a *diagnostic* (an alternative read on the docs/08
whistle), and an honest Stage-0 to **measure whether GoI's space claim
is even relevant** to `data[0]`.

### Stage 0 — falsify GoI relevance on ONE small closed term [the kill switch]

Build: nothing new in the engine. A read-only harness: take one small
closed combinatory term (e.g. `S K K x` reducing to `x`, or a 3-deep
Church-numeral add) already in the corpus; run `eval_forced`
(`galaxy.rs:890`); record `res.steps` (= token transition count, §1.2)
**and** peak `Ψ` size / peak `π` depth (`galaxy.rs` already single-ray;
instrument the existing loop, env-gated like `STELLA_GALAXY_TRACE`
`:867`). Verify `psi_compatible(iex(Φ,Ψ₀), eval_forced result)` green
(it is the same engine — predicted trivially green; this checks the
*measurement harness*, not a new machine).

Measures: (a) token-step count vs reduction length; (b) peak materialised
space.
**Falsifier of the whole docs/15 thesis-as-implementation:** if peak
materialised space is already **O(reduction depth)** and step count is
**Θ(reduction length)** — which §2.1 predicts from `galaxy.rs:890`'s
single-ray structure — then GoI's space-for-time trade has **no slack to
exploit** (the engine is already at GoI's space profile) and GoI is
**confirmed not a galaxy-execution lever**. Predicted: confirms. This is
the cheapest possible disproof and it should be run *first of the four
surveys' Stage-0s* because it is the one most likely to cleanly remove an
option (low cost, decisive).

### Stage 1 — (only if Stage 0 surprises) GoI persistent-path detector

ONLY if Stage 0 unexpectedly shows the engine materialising super-linear
space (it should not): a GoI-flavoured `σu`-nilpotency probe as a second
opinion on docs/08 §3.1's `accel_detect` whistle — feed the per-layer
trace and additionally check for a non-cancelling token feedback path.
This is a *diagnostic alternative*, never an executor. Falsifier:
disagreement with `accel_detect::detect_recurrence` on the docs/08
Stage-1 corpus ⇒ one of the two is wrong; reference `iex` adjudicates.

### Ordering vs docs/11/12/13/14

- **docs/15 (this) is the lowest-priority *executor* candidate** and
  should be *de-prioritised as a galaxy-execution path* by docs/16. Its
  Stage 0 is high-value as a **measurement that constrains the other
  three** (it pins down that the blocker is step-count, not space) — run
  Stage 0 early, then shelve docs/15 as an executor.
- **docs/11 Lever C** (memo): done, proven insufficient (the premise of
  this whole swarm).
- **docs/11 Lever D / docs/13** (KA2 / supercompilation, O(N)→O(1) on the
  recurrent core): **the actual fix** for a long non-redundant reduction
  — *fewer steps*. docs/08's whistle substrate (`accel_detect.rs`
  [Built]) is its enabler, and §4 here shows GoI proves that substrate's
  fixpoint is the right one.
- **docs/14 Lever B** (Futamura/staged compile of fixed Φ=405):
  complementary — makes each remaining step O(1); compatible with
  D/13.
- **docs/12** (interaction combinators / optimal reduction): the *other*
  reading of "don't duplicate" (§29.29/§36.1) — shares redexes, not just
  subterms. Distinct from docs/15's token machine; docs/12 may help if
  `data[0]` has redex-level (not subterm-level) sharing that Lever C's
  subterm memo missed. That is docs/12's question, not docs/15's.

**Recommended order: docs/15 Stage-0 (measurement, decisive, cheap)
FIRST → it confirms step-count blocker → then docs/13/Lever-D is the
executor, docs/14/Lever-B sharpens per-step, docs/12 is the fallback if
redex-sharing exists. docs/15 is not on the executor critical path.**

---

## 6. Honest risks & verdict

### 6.1 Risks (all point the same way)

- **GoI constant factors are notoriously bad.** §36.6 [Eng] says it
  outright: complexity "hidden in how the machine is treated (… data
  accumulated in stacks)". A GoI executor would be *slower* per step than
  `iex_fast`, on a blocker that is already step-count-bound. This is not
  a tunable risk; it is structural to token machines.
- **Subjective-ray / exponential-path imprecision (§35.18, §36.4 [Eng]).**
  The IAM does not exactly preserve exponential paths; galaxy's
  duplicating combinators are exponential-flavoured. A hand-written IAM
  re-opens a soundness problem the current Φ-based engine does not have.
  Unforced.
- **§49.59–60 termination openness [Eng].** Eng leaves open whether
  `AEx^∞` is always defined (§49.59); §49.60 "hyper execution is not
  necessarily defined"; §49.61 gives a constellation that grows without
  bound. In GoI language this is exactly "`σu` need not be nilpotent."
  **This does not *block* GoI specifically** — it blocks *every* executor
  equally (it is a property of the computation, not the machine), and
  `data[0]` is known to *have* a finite answer (the protocol decoded
  correctly, docs/07 §B "Correctness is DONE"; it is *slow*, not
  divergent). So §49.59–60 is not the `data[0]` blocker. But it does mean
  GoI offers **no termination guarantee** the engine lacks — GoI does not
  decide §49.59 any more than `max_forcings` does (docs/08 §6.1).

### 6.2 Verdict

**Is GoI THE galaxy-execution path?** No.

**Is GoI the §49.50-track implementation?** No — but it is the §49.50
track's *correct theoretical characterisation*. The §49.50
implementation is docs/08's staged plan over the *already-built* `±P`
machine; GoI (Eng's own §49.57 nilpotency = idempotence) proves that
plan's fixpoint is the right one and gives the cleanest statement of the
charge `χ` (= non-nilpotency of `σu`). That is real conceptual value,
**zero** new code.

**A theory-elegant-but-impractical option, or genuinely right?**
Theory-elegant, genuinely *true* (the engine *is* a GoI token machine —
§57.19/`iex_fast`), and **impractical as an executor** because: (1) the
GoI space advantage is already realised by `eval_forced`'s single-ray
stack-machine structure; (2) the measured `data[0]` blocker is *long
non-redundant transition count* (Lever-C-disproved-redundancy, docs/07
§A1 b6c65d5), and a token machine pays the same Θ(N) transitions with a
*worse* constant (§36.6 [Eng]); (3) re-implementing it would reintroduce
exponential-path soundness risk for no speed gain.

**Honest bottom line.** GoI is the right *lens* and the wrong *lever*.
Its highest-value contribution is **negative and clarifying**: docs/15
Stage-0 cheaply *confirms* the blocker is step-count not materialised-
space, which is the single most useful fact for choosing among docs/12/
13/14. The galaxy executor is step-count reduction — docs/13/Lever-D
(supercompilation/KA2 on the recurrent core) sharpened by docs/14/
Lever-B (Futamura) — for which docs/08's whistle substrate is the
enabler and §4's GoI argument is the correctness rationale. docs/15
should be **closed as an executor candidate** and **harvested as the
theoretical closure of the §49.50/docs/08 track**.

---

## Final answers to the required questions

- **Load-bearing recommendation:** Do **not** build a GoI/token executor.
  Run docs/15 Stage-0 (cheap, read-only, ~1 harness file, env-gated like
  `galaxy.rs:867`) *first among the four surveys* to confirm the
  `data[0]` blocker is transition-count not materialised-term-space;
  then pursue docs/13 / docs/11-Lever-D (step-count reduction:
  supercompilation/KA2 on the recurrent core) as the executor, with
  docs/14/Lever-B (Futamura) sharpening per-step cost. Harvest docs/15's
  §1–§4 as the theoretical closure of the §49.50/docs/08 track (GoI
  nilpotency = Eng's §49.57 idempotence; χ = non-nilpotency of `σu`).
- **Biggest risk:** The seductive but false intuition that "GoI never
  materialises the term, so it sidesteps the blowup." It is false here
  because (a) `eval_forced` (`galaxy.rs:890`) *already* never
  materialises the term — it is a single-ray stack machine — and
  Lever-C's measured negative (docs/07 §A1) proved the blocker is
  *non-redundant transition count*, not materialised space; (b) §36.6
  [Eng] states GoI's cost is merely *hidden in the stacks* with a worse
  constant. Mistaking GoI for a space lever would burn an
  implementation cycle re-deriving `iex_fast` slower and re-opening
  §35.18 exponential-path soundness — for zero asymptotic gain.
- **Does this make galaxy's `data[0]` actually execute? NO.** A GoI
  token machine pays the same Θ(N) non-redundant transitions as the
  current engine with a strictly worse per-step constant; it removes no
  steps and the engine is already at GoI's space profile. `data[0]`
  needs *fewer steps* (recurrence summarisation / staged compilation),
  which GoI does not provide.
