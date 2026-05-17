# 10 — Open-Hypergraph Data-Parallel Substrate Reframe (design, read-only)

Status: DESIGN. No code changed. Implementation parent-sequenced (§5).
Claim tags: **[Built]** = in tree & tested · **[Spec]** = Eng / paper text ·
**[Lit]** = the Wilson–Zanasi paper / `open-hypergraphs` 0.3.1 source ·
**[Proto]** = this doc's proposed construction, not yet built.

Question this doc decides: should the stella stellar-resolution **substrate**
(term store + constellation + the `iex` rewrite loop), not merely its
unifier, be reframed onto the data-parallel open-hypergraph (OHG)
string-diagram representation of *Data-Parallel Algorithms for String
Diagrams* (arXiv 2305.01041), implemented at
`/Users/ember/hellas/open-hypergraphs` (= the `open-hypergraphs = "=0.3.1"`
crate stella-core already depends on, `crates/stella-core/Cargo.toml:7`)?

Headline up front (defended in §3, §5): the three parked engine threads —
**B3** lock-free store, **data-parallel layered rewriting**, **§49.50
internal-polarity dynamics** — do *not* fully collapse into one substrate.
Two of them (B3 + parallel layering) share an array representation and are a
genuine joint lever; the third (§49.50 ray-minting / semaphores) is a
*dynamic* the static OHG string diagram does **not** model and must stay in
the imperative `iex` loop. The reframe is worth a **Stage 0 prototype**, is
**not** worth blocking on, and **sits beside** (does not subsume) docs/09's
B3 deferral and the parallel-forcing front.

---

## 1. The correspondence, made precise [Spec]

### 1.1 What the OHG library actually represents [Lit]

An `OpenHypergraph<K,O,A>` (`src/strict/hypergraph/object.rs:22-27`,
`src/strict/open_hypergraph/arrow.rs`) is a cospan of a `Hypergraph` with
two boundary maps. The `Hypergraph` is **four parallel arrays**, not a
pointer graph:

- `w : SemifiniteFunction<K,O>` — node (wire) labels, one per wire.
- `x : SemifiniteFunction<K,A>` — hyperedge (operation) labels, one per edge.
- `s : IndexedCoproduct<K,FiniteFunction<K>>` — a **segmented array**:
  for each edge, the ordered list of its source wire-ids.
- `t : IndexedCoproduct<K,FiniteFunction<K>>` — same for target wires.

A `FiniteFunction` is just `{ table: array of usize, target: usize }`
(`src/finite_function/`). An `IndexedCoproduct` is `{ sources: lengths,
values: flat concatenation }` — the classic CSR / array-of-structs-as-
struct-of-arrays layout. **Everything is `Vec<usize>` (the `VecKind`
backend) or any array backend** (`src/array/`). This is the data-parallel
representation: structural ops are segmented scans / `gather` / `scatter` /
`bincount` over flat integer arrays (`src/strict/graph.rs:54-213`), with no
per-node allocation and no pointer chasing.

### 1.2 The map onto stellar resolution [Spec/Proto]

| Stellar resolution (Eng / stella) | Open hypergraph (paper / crate) |
|---|---|
| Star `Φ[i]` (§48.10) = vector of rays [Built `constellation.rs:12`] | a hyperedge `x[i]` with its incidence (`s`/`t` segment) [Lit] |
| Ray `r` = a `TermId` (`polarised.rs:13`) [Built] | a typed half-edge / port: an entry in the edge's `s` or `t` segment, wire label = the ray's term [Proto] |
| Polarity `+`/`−`/`0` of head sym (`term.rs:48-55`) [Built] | port **orientation** (source-leg vs target-leg) + label-type tag [Proto] |
| Polarised compat `⊂` (§48.2, `polarised.rs:97-111`): same neutral name, opposite/both-neutral polarity [Built] | the **typing condition** on a composable port pair [Proto] |
| `matchable r ⋈ r′` = α-unifiable under `⊂` (§49.7, `polarised.rs:173-183`) [Built] | a *candidate* wire-merge: two ports may be glued iff their labels unify under `⊂` [Proto] |
| Fusion `φ₁ ^{j,j'}∇ φ₂` (§49.30, `interactive.rs:457-488`): θ = mgu, return `θ(φ₁−{j}) ⊎ θ(φ₂−{j'})` [Built] | hypergraph **composition along matched ports** = a pushout/coequalizer that quotients the two glued wires and substitutes θ (`Hypergraph::pushout_along_span`, `src/strict/hypergraph/object.rs:166-207`; `apply_smc_rewrite`, `src/strict/open_hypergraph/rewrite.rs:175-270`) [Lit] |
| A constellation Φ / interaction space Ψ (§48.14) [Built] | one open hypergraph: all stars as edges, shared variables as shared wires [Proto] |
| One `iex` step (§51.9, `interactive.rs:536-584`) [Built] | one **SMC rewrite** `apply_smc_rewrite` with `lhs` = the matched ray pair, `rhs` = the fused remainder [Lit/Proto] |

The fit is real and not superficial: the crate's own λ-calculus framing
(README:14) and its rewrite machinery (`SmcRewriteRule`,
`apply_smc_rewrite`, the experimental `rewrite` module) is *exactly* a
term-graph rewrite engine, and stellar fusion **is** term-graph rewriting
with a unification side-condition.

### 1.3 Where it is faithful, and where it bends [Spec — be exact]

**Faithful (the objective fragment).** For *objective* stars (all rays
positive-or-neutral, `constellation.rs:26-35`, `StarKind::Objective`),
fusion is the textbook hyperedge-glue + substitution. θ is an mgu; the
crate's pushout/coequalizer (`pushout_along_span`) quotients the two glued
wires and is the categorical realization of "apply θ and drop the two
consumed rays". `psi_compatible` (§4) tolerates exactly the
α/name freedom the coequalizer introduces. **Within the confluent objective
/ Horn fragment the OHG model is a faithful static representation of a
constellation and its reachable fusions.** This is the SLD-complete,
§55.6-deterministic fragment `iex` already targets (`interactive.rs:794`).

**Bends — three precise points where the static string diagram is NOT the
engine:**

1. **The unification side-condition is not categorical structure.** In the
   crate, `SmcRewriteMatch::new` (`rewrite.rs:102-123`) requires a
   *convex subgraph morphism* with **syntactically equal** labels — there
   is no unifier in the loop. Stellar matchability is α-unification under
   `⊂` (`polarised.rs:173`), strictly richer than label equality. So an
   OHG rewrite step is faithful only if a *stella-supplied* θ is computed
   first and the rewrite is performed on the θ-instantiated diagram. The
   OHG library gives the *schedule and the gluing*, **not the matching**.
   The unifier stays stella's. (This is why §5 says the reframe and the
   docs/09 unifier rework are orthogonal — different organs.)

2. **Subjective / animist rays = §48.7 reflexive rays are dynamic, not
   static.** A *subjective* ray is `f(r₁…rₙ)` where some `rᵢ` is itself
   coloured (docs/08:76, `polarised.rs`/`constellation.rs` `StarKind`).
   The OHG node label `O` is a *fixed* value; a subjective ray's coloured
   operand is a ray that **only acquires its match set once execution has
   disclosed it** (docs/08:25-45, §49.50 characteristic (1): execution
   *introduces new polarised rays*). A static `OpenHypergraph` cannot
   contain an edge that does not exist yet. The OHG model captures the
   **objective fragment exactly** and the subjective fragment **only after
   each disclosure** — i.e. one OHG snapshot per AEx layer, never one
   diagram for the whole run.

3. **§49.50 semaphore ordering = ray-minting is a step dynamic.** The
   §49.50 mechanism (docs/08:25-104): a `+g(X)` under a `−f` *cannot*
   interact until `+f`/`−f` annihilate first; annihilation **mints** the
   newly-exposed ray. This is `drive_strict` in built code (docs/08:151,
   the sole ray-minting site) and the imperative `iex_fast` consume/extend
   loop (`interactive.rs:1079-1099`). The OHG `apply_smc_rewrite` rewrites
   a *given* diagram; it has no notion of "this edge becomes matchable
   only after that edge is consumed". That ordering is precisely the
   docs/08 §4.2 **dependency relation** of the trace monoid — it lives in
   the rewrite *driver*, not in the static diagram.

**Net [Spec]:** OHG faithfully models the **objective fragment as a static
diagram** and a **per-layer snapshot of the subjective fragment**. It does
**not** model ray-minting or the §49.50 semaphore order. Any reframe that
claims to capture the whole engine in one diagram is unfaithful; a reframe
that uses OHG **per AEx layer**, with stella minting rays and computing θ
between layers, is faithful on the same fragment `iex` is confluent on.

---

## 2. The data-parallel lever [Lit→Spec]

### 2.1 What Wilson–Zanasi layering computes [Lit]

`strict::layer::layer` (`src/strict/layer.rs:20-31`) runs a data-parallel
Coffman-Graham / Kahn topological layering (`graph::kahn`,
`src/strict/graph.rs:54-132`) over the operation-adjacency relation
`operation_adjacency` (`graph.rs:14-21`). It returns `layer : X → L`
assigning every operation (edge) an integer **layer**, computed with
`bincount` / `scatter_sub_assign` / `gather` over the frontier — a fully
array-parallel BFS-by-indegree (`graph.rs:84-129`). `layered_operations`
(`layer.rs:40-50`) inverts it to `Vec` of arrays: layer `i` is the array
of operations with **no dependency on each other**.

The key semantic fact (`src/strict/eval.rs:60-108`, the
`// TODO: evaluate all 'ops' in parallel` at `eval.rs:104`,
`tests/layer/layer_eval.rs:69-82`): **all operations within one layer are
mutually independent and may be applied in any order / simultaneously**;
the layered evaluator's per-layer `apply` is a single `scatter_assign`
over the whole layer's outputs (`eval.rs:96-103`). That is the data-
parallel payoff: not thread-rayon necessarily, but **SIMD/array batch
application of an entire independent rewrite layer in one pass**, with all
incidence updates as segmented gather/scatter.

This **is** the docs/08 §4 trace-monoid structure realized as code: the
independence relation `I` (docs/08:261-287) = "no path between the two
operations in the adjacency DAG" = exactly what `kahn` puts in the same
layer. docs/08 already argued the right theory is partial-commutation /
Mazurkiewicz traces, not words; Wilson–Zanasi layering is the *executable
Foata-normal-form* of that trace.

### 2.2 Quantified against stella's MEASURED profile [Built]

docs/09:13-17 — `STELLA_KS_PROF=1` on the **galaxy Φ=405** reduction:

- `fuse ≈ 82%` of wall, of which `unify ≈ 53%` of total, `subst ≈ 5%`
- `find ≈ 15%`, `freshen ≈ 3%`.

What the layering lever can and **cannot** touch — stated plainly:

- **A single unification is sequential and does NOT parallelize.** The
  53%-of-total `unify` cost is Martelli–Montanari on one term pair inside
  one `fuse_theta` (`interactive.rs:466`). It is intrinsically sequential
  (occurs-check, walk). The OHG layering buys **nothing** here. This is
  docs/09's lever, not this doc's; **the two must not be conflated** (§5).
- **Independent fusions in one rewrite layer parallelize.** One `iex`
  step (`interaction_step`, `interactive.rs:558-581`) emits a *sum* of
  summands: one fusion per `(iₖ,jₖ) ∈ mat_Φ^C` plus the self-interactions.
  These summands are **mutually independent** (each pushes an independent
  star, `interactive.rs:569,577`) — they are one OHG layer. So is the
  galaxy image-data cons-children case (docs/07:225-232: forcing
  `data[0]` independently of `data[1]…`): independent sub-reductions =
  independent edges = one layer. **The lever is across the summand-fan and
  across independent sub-reductions, never inside one unify.**
- **`find ≈ 15%`** (`mat_phi_c_accel` candidate enumeration,
  `interactive.rs:893`) is a `gather`/`bincount` over the head-index — this
  is *already* the array-shaped operation OHG would express, and it
  parallelizes per-redex; modest, real, secondary to fuse.
- **`fuse`'s `subst ≈ 5%`** (`theta.apply` over the residual rays,
  `interactive.rs:471-485`) is embarrassingly parallel across the rays of
  the fused star and across the independent summands — array `apply`. This
  is a genuine OHG-shaped win but it is only the 5% slice.

**Phase verdict:** OHG accelerates the **fan-out structure of a step**
(summands, residual-ray substitution, candidate gather) and **independent
sub-reductions across layers** — call it the `subst`+`find`+step-fan
envelope, realistically the non-`unify` ~30–47% after the docs/09 unifier
lands. It does **not** accelerate the single hottest inner kernel (one
unify). The honest expected ceiling: a layered substrate is a multiplier
on the *post-unifier* profile, contingent on the fan being wide (galaxy:
~400 δ-stars ⇒ wide `mat` fans — favorable; Horn add: narrow ⇒ negligible).

---

## 3. The unifying-substrate hypothesis [Proto]

Claim under test: an OHG array / `FiniteFunction` representation of
term+constellation *simultaneously* (a) replaces `RwLock<TermStore>` with
a lock-free data-parallel array store (B3), (b) enables data-parallel
layered rewriting, **and** (c) realizes the §49.50 interaction-net /
annihilation dynamics directly. **Verdict: (a)+(b) collapse into one
substrate; (c) does NOT. Honest, not hand-waved:**

**(a) ⊕ (b) — yes, genuinely one substrate.** The term store
(`term.rs:241-284`) is *already* morally `{ vec: Vec<TermData>, map:
interner, ground: Vec<bool> }` behind a per-call `RwLock` — an append-only
arena. The OHG `Hypergraph`'s `w`/`x`/`s`/`t` arrays are the *same shape*.
A representation where a term is an index into parallel arrays
(`tag[]`, `sym[]`, `args_off[]`, `args[]`) is **simultaneously**: the B3
lock-free append-only store (docs/07:283-284 "deepest residual constant
factor, per-node `RwLock`") *and* the substrate the Wilson–Zanasi
segmented-scan algorithms operate on. B3 and parallel-layering are the
**same array refactor seen from two angles** — that is a real
consolidation and the strongest argument for the reframe. (docs/09:630-642
deferred B3 *deliberately* to keep the unifier perf delta attributable;
that deferral is about *sequencing*, not about whether the consolidation
is real — it is.)

**(c) — no.** §49.50 dynamics are *not* a representation, they are a
*reduction strategy*: ray-minting (`drive_strict`, the sole minting site,
docs/08:151), the semaphore wait (`force_value` = demand pole,
docs/08:136), and the dependency order that is `F(op,ℓ)` depending on its
disclosing `R(P)` events (docs/08:282-287). The OHG `apply_smc_rewrite`
is a *single static rewrite of a given diagram*. It has no minting, no
demand pole, no semaphore. You can *represent* each post-disclosure
snapshot as an OHG; you cannot *get the dynamics for free* from the OHG
algebra. The interaction-net analogy in docs/08 is structural (annihilation
= composition along a matched port) but the **net's reduction order is the
trace-monoid dependency**, which OHG layering *consumes as input* (the
adjacency DAG) and does not *generate*. So (c) stays in the imperative
driver. Claiming otherwise would be the kind of incantatory
"one-substrate-unifies-everything" overreach the project explicitly bans.

**Therefore the headline is two-thirds true and stated as such:** B3 and
data-parallel layered rewriting **are** one substrate (the array term/edge
arena). The §49.50 dynamics are **not** subsumed by it; they remain a
driver on top, and the driver's *dependency relation* is what the layering
needs as input (computed by stella's matchability, not by OHG).

---

## 4. The faithfulness crux [Built gate]

A parallel-layer rewrite schedule applies all independent fusions in a
layer **simultaneously**, reordering reductions versus the reference
`iex`'s deterministic leftmost / depth-first scan
(`interactive.rs:812-836`: first applicable `(i,j)`).

**The exact proposition that must hold [Proto]:**

> **P-OHG.** Let `Φ ⊢ Ψ` be a configuration. Let `iex(Φ,Ψ)` be the
> reference leftmost result and `iex_layer(Φ,Ψ)` the result of applying,
> at each step, the *entire* Wilson–Zanasi independent layer of
> applicable redexes (each with stella's own θ) instead of the single
> leftmost one. Then `psi_compatible(iex(Φ,Ψ).psi,
> iex_layer(Φ,Ψ).psi)` holds for every corpus, where `psi_compatible` is
> the proven (`faithfulness.rs:115-119`) ɟ-concealed α-canonical
> **multiset** result-equivalence validator.

Why this is the right proposition and the right instrument:

- Stellar resolution's answer **set** is schedule-invariant **in the
  confluent objective / Horn fragment** (§55.6; this is exactly why
  `iex_tabled` already certifies result-equivalence not byte-identity,
  `interactive.rs:1011-1013`, `faithfulness.rs` B0a). A layer schedule is
  just another order over confluent independent steps ⇒ same answer
  multiset. P-OHG should hold there by the same argument that makes
  `iex_tabled` sound.
- **Where confluence fails it is NOT obviously schedule-invariant.** With
  subjective rays / forcing (§49.50), step order changes *which rays get
  minted when* (docs/08:282-287 dependency, not commutation). Two
  schedules can disclose different subjective rays and — outside the
  confluent fragment — reach different normal forms or different
  termination behaviour (§49.57: idempotence is *lost* with subjective
  rays; §49.59-60 termination is open). **What is lost where confluence
  fails: P-OHG can legitimately be `false`, and then the layer schedule is
  simply not a valid jet for that corpus** — exactly as docs/09's fast
  unifier is gated, the layer substrate is gated by the *same* instrument
  and *falls back to reference `iex`* when the gate is red. The design
  must not pretend the reorder is always safe; it must **detect** when it
  is not, via P-OHG, and degrade.
- **Same instrument as the unifier rework, by construction.** This is the
  load-bearing point: the reframe introduces **no new trusted code in the
  faithfulness path**. `psi_compatible` (just proven, `faithfulness.rs`,
  B0a/B0b tests `faithfulness.rs:309-438`) is the *identical* gate
  docs/09 uses for `unify_fast`. Reference `iex` (`interactive.rs:801`)
  stays the untouched differential oracle. The layered substrate is a new
  *fast tier* exactly like `iex_fast`/`unify_fast`: never reachable from
  the reference path, gated by `psi_compatible(iex, iex_layer)` per corpus
  plus a true-NF assertion (mirrors `iex_tabled_result_eq_iex`,
  `interactive.rs:1508-1544`). No gate is invented; the non-negotiable
  one is reused.

---

## 5. Honest verdict + staged falsifiable plan

**Is it worth doing?** Partially and conditionally **yes** — but as the
B3+layering array-substrate consolidation (§3 a⊕b), *not* as a
"reframe everything onto string diagrams" move, and *not* now.

**When — strict ordering (it must not block or confound docs/09):**

- docs/09 **Stage 1 `unify_fast`** touches the *inner unify kernel* (53%
  of total, sequential, `interactive.rs:466`). This doc's lever touches
  the *step fan / substitution / store* (the other envelope). **Different
  organs, different files, different falsifiers.** If both move at once,
  the galaxy Φ=405 KS-PROF delta becomes un-attributable — the exact
  staged-falsifier violation docs/09:632-638 forbids for B3. **Therefore:
  this work is sequenced strictly AFTER docs/09 Stage 1 lands and its
  `unify` % drop is measured and attributed.** It is the natural successor
  to docs/09's *deferred* B3 (docs/09:630-642), now reframed: B3 is not
  just "remove the lock", it is "adopt the array substrate that *also*
  enables layering". Same before/after discipline, its own attribution.
- It **sits beside, does not subsume**, the docs/08 parallel-forcing /
  §49.50 front. That front owns the *dynamics* (ray-minting, the
  dependency relation); this doc's substrate *consumes* that dependency
  relation as the adjacency DAG it layers. They compose; neither replaces
  the other. Explicitly: this does **not** subsume docs/09's B3 deferral
  (it *is* the principled re-homing of it) and does **not** subsume the
  §49.50 work (it depends on it for the dependency order).

**Staged plan — each stage a measurable falsifier, no code until parent
sequences it:**

- **Stage 0 (non-invasive prototype, the decision gate).** Pick ONE
  corpus already in `faithfulness.rs` (`horn()` `:217`, then `binarith()`
  `:244`, then bounded `galaxy()` `:259`). Outside the engine: encode that
  corpus's *objective-fragment* constellation as a lax
  `open_hypergraphs::lax::OpenHypergraph` (the crate is already a dep;
  `lib.rs:53` smoke test shows the API), run `strict::layer::layer` to get
  the independent-layer schedule, drive fusion **in layer order with
  stella's own θ**, and assert
  `psi_compatible(iex(corpus).psi, layer_driven.psi)` using the existing
  proven validator. **Falsifier:** if `psi_compatible` is `false` on the
  *objective* Horn/binarith corpora (the confluent fragment), the whole
  reframe is unsound and stops here — that is the cheap kill. **Second
  falsifier:** measure constant-factor overhead of the array
  representation vs the hash-cons sharing already exploited
  (`term.rs:218-221` `Arc<[TermId]>` O(1) structural sharing; the OHG
  `Vec<usize>` incidence does *not* share subterms the way hash-consing
  does). If Stage 0 on a realistic (galaxy-shaped, wide-fan) input is not
  *faster* on the non-unify envelope, the lever is theoretical and the
  project stops at Stage 0 with a recorded negative.
- **Stage 1 (array term store = B3, gated).** Replace `RwLock<TermStore>`
  with the append-only array arena (the §3 a⊕b substrate), behind the
  fast tier only; reference `iex` untouched. **Falsifier:** all
  `faithfulness.rs` B0a/B0b + `iex_*_result_eq_iex` gates green;
  `STELLA_KS_PROF` galaxy Φ=405 — the per-node-`RwLock` constant factor
  measurably shrinks with **no `unify` % change** (proving it is the
  store, not the algorithm — the attribution discipline docs/09:632-638
  demands).
- **Stage 2 (layered rewrite for the step fan, gated).** Apply
  Wilson–Zanasi layering to the summand-fan + independent sub-reductions
  (§2.2). **Falsifier:** `psi_compatible(iex, iex_layer)` per corpus +
  true-NF; KS-PROF shows the `subst`+`find`+step-fan envelope drops on
  wide-fan galaxy; **no improvement on narrow Horn is expected and is not
  a failure** (it is the predicted shape). Any `psi_compatible` red ⇒ that
  corpus falls back to reference `iex`; the substrate is a jet, never the
  oracle.
- **Stage 3 (only if Stages 0–2 all pass with attributed wins).**
  Integrate with the §49.50 driver: the driver supplies the dependency
  DAG per AEx layer; the substrate layers within it. **Falsifier:** the
  combined system still `psi_compatible` with reference on all corpora
  including subjective/forcing ones, *or* documents precisely the
  non-confluent corpora where it must fall back.

Each stage's negative is publishable as a recorded negative; none is
allowed to proceed on a red `psi_compatible`.

---

## 6. Risks / open

- **Subjective-ray dynamics vs static diagrams [Spec].** The sharpest
  risk and the §1.3/§3(c) crux: OHG is a *static* string diagram; §49.50
  ray-minting is *dynamic*. Mitigation: OHG used **per AEx layer**, never
  one diagram for the run; the driver mints. If even per-layer snapshots
  cannot be kept in sync with `drive_strict`'s minting cheaply, Stage 3
  fails and the substrate is objective-fragment-only (still useful for
  galaxy's δ-heavy objective KAM, docs/08:134).
- **Does layering preserve the §49.50 semaphore order? [Proto].** Only if
  the dependency relation fed to `kahn` *includes* the semaphore
  dependency `F(op,ℓ) ▷ R(P)` (docs/08:282-287). Wilson–Zanasi `kahn`
  layers a *given* adjacency; it cannot invent the semaphore edge. The
  semaphore order must be **encoded as adjacency by stella** before
  layering. If it is not, the layer schedule will reorder across a
  semaphore and P-OHG goes red on subjective corpora — which the gate
  catches, but it means the lever is objective-fragment-restricted unless
  the dependency encoding is done correctly. Open: is encoding the
  semaphore as a hyperedge dependency cheap and faithful? Unknown
  pre-Stage-0.
- **Array constant factors vs hash-cons sharing [Built risk].** stella
  already exploits maximal structural sharing: `TermId` is a u32 handle,
  `App` args are `Arc<[TermId]>` (`term.rs:218-221`), `get` is O(1)
  refcount bump, `is_ground` is cached (`term.rs:246-277`). The OHG
  `IndexedCoproduct` incidence is flat `Vec<usize>` with **no automatic
  subterm sharing** — galaxy's huge ground δ-bodies (docs/07:248-250)
  are shared once in the hash-cons store but would be *materialized
  per occurrence* in a naïve OHG wire array. This is a real risk that the
  array win is eaten by lost sharing. Stage 0's second falsifier exists
  precisely to measure this before any commitment.
- **`open-hypergraphs` 0.3.1 maturity / experimental APIs [Lit].** The
  rewrite machinery that the reframe most needs — `SmcRewriteRule`,
  `SmcRewriteMatch`, `apply_smc_rewrite`, `pushout_along_span` — is
  **gated behind `#[cfg(feature = "experimental")]`**
  (`src/strict/open_hypergraph/mod.rs:3-11`,
  `src/strict/hypergraph/object.rs:166`). The stable surface is
  layering + eval + lax construction (the `lib.rs:53` smoke test uses only
  stable lax). README:31-46 explicitly flags experimental APIs as
  opt-in/unstable. Depending on experimental rewrite for the trusted-
  adjacent fast tier is a maturity risk; mitigation: Stage 0 uses only
  **stable** `layer` + stella's own fusion (no `apply_smc_rewrite`),
  deferring any experimental-API dependence to Stage 2+ where it is
  gated by `psi_compatible` anyway.
- **The README's λ-calculus claim is not demonstrated in-repo [Lit].**
  README:14 lists "Programs in the λ-calculus" but the only evaluation
  tests (`tests/eval/eval.rs`, `tests/lax/eval.rs`,
  `tests/layer/layer_eval.rs`) evaluate **polynomial circuits**, not
  λ-terms or β-reduction. There is no in-tree reduction-engine analog to
  validate against; the correspondence in §1 is sound on first principles
  (term-graph rewrite) but the library has **not** itself been exercised
  as a reduction engine. Lower confidence accordingly; Stage 0 is the
  first real test of the library in this role.

---

### One-line decision

The OHG array representation is a genuine **B3 + data-parallel-layering**
consolidation (two parked threads, one array substrate) gated by the
already-proven `psi_compatible`; it is **not** a capture of §49.50
dynamics and **not** a unifier accelerant; do it **after** docs/09
Stage 1, as a Stage-0-gated prototype, falling back to reference `iex`
wherever confluence (hence `psi_compatible`) fails.
