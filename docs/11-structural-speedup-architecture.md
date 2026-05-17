# 11 — Structural Speedup Architecture: the path to a reachable galaxy frame

Status: DESIGN / RESEARCH synthesis. No code changed. Implementation
parent-sequenced (§F). Decides the engine's path to a **reachable galaxy
first frame** and a **>10× speedup that is algorithmic, not constant-factor**.

Claim tags: **[Built]** = in tree & tested · **[Lit]** = paper / literature ·
**[Proto]** = this doc's proposed construction, not yet built.

The faithfulness instrument is fixed and already proven: every fast tier is
gated by `faithfulness::psi_compatible` (`faithfulness.rs:115-119` [Built],
Stage-0 forensic-verified, docs/07 §J2) against reference `iex`
(`interactive.rs:861` [Built]) as the differential oracle, plus the
reference `iex`/`eval_forced` unrolling as the per-instance oracle. This is
the two-tier verified-speculative-runtime model (docs/07 §H, docs/09). No new
trusted code enters the faithfulness path anywhere below.

---

## A. The measured case that >10× must be structural

Two facts ground every design decision here.

**Fact 1 — per-step constant-factor tuning is exhausted.** Post-Stage-1b on
the galaxy constellation Φ=405 (`STELLA_KS_PROF`, docs/07 §D / docs/09):
total ≈ 0.018 s; `unify` dropped 53% → 9% once the near-linear `unify_fast`
(`unify_fast.rs` [Built], gated `iex_fast_result_eq_iex` via
`psi_compatible`) replaced Martelli–Montanari in the two fast-tier call sites
(`interactive.rs:524` `fuse_theta_fast`, `:575` `self_interact_fast`). The
residual dominant phase is `find` (discrimination matching, ≈30%) but in
absolute terms `find` is ~5 ms. Driving `find` to *zero* caps at ~1.05× of
total. **No constant-factor lever on the existing per-step loop can yield
10×.** Bounded.

**Fact 2 — the galaxy image payload does not terminate even at 2×.**
`crates/stella-core/examples/galaxy_data_probe.rs` [Built] forces the ICFP
protocol spine faithfully and cheaply (`force(entry)`→`cons(flag=0,_)` 4311
steps; tail fields tens of steps each, all `fully_reduced=true`). Forcing a
*single image element* `data[0]` does **not** terminate in 150 s at
fuel=2M / maxf=100k (docs/07 §B KG6c) — no panic, no dead-end, just past
engine speed. A constant-factor win (indexing, lock-free store,
data-parallel layering per docs/10) multiplies a non-terminating-in-150 s
reduction by a constant and it is still non-terminating. **The >10× is
therefore necessarily algorithmic.**

Which lever attacks which axis:

| Axis of cost | Lever | What it removes |
|---|---|---|
| **per-step cost** (re-scan/unify/fuse 405 stars every step) | **B. Φ-specialization** (1st Futamura projection) | the generic interpreter's O(\|Φ\|) per-step interpretive overhead → O(1) per-head dispatch |
| **redundant sub-reduction** (massively shared closed structure re-forced from scratch on every cons-spine visit) | **C. Memoized graph reduction** (call-by-need + global hash-consed NF cache) | exponential re-forcing of shared subterms → linear |
| **number of steps** (a recurrent arithmetic/list core unrolled O(n) times) | **D. KA2 speculative trace acceleration** | the O(n) unrolled run of a detected recurrence → O(1)/O(log n) closed form |

B and C make the galaxy frame *reachable* (they collapse the
re-forcing/interpretive explosion that is the literal KG6c blocker). D is the
unbounded lever and the one that most directly removes the asymptotic that no
constant factor can touch.

---

## B. Lever 1 — Φ-specialization (the first Futamura projection)

### B.1 The opportunity [Built facts]

The galaxy constellation Φ is **fixed for the whole run**: 13 prim stars
(`galaxy.rs:417` `prim_stars` — Push + `i t f s c b cons car cdr nil` +
isnil×2) ∪ 392 δ-stars (`galaxy.rs:398` `delta_star`,
`[ −P(st(:N,π)), +P(st(body•,π)) ]`). The generic resolution interpreter
re-derives, every single step, the same facts about these 405 stars:

- `iex_fast_inner` (`interactive.rs:1086`) re-scans Ψ for a matchable ray,
  calls `any_match_accel` → `mat_phi_c_accel` (`:315`) which does, per
  candidate, `fp_unifiable` + `matchable_fast` α-unification against Φ rays;
- on the chosen redex, `produce_stars_fast` (`:942`) α-renames the whole Φ
  star (`alpha_rename_star_fast`), then `fuse_fast` runs `unify_fast` to
  recompute θ and `theta.apply` over the residual rays.

But the *structure* of each Φ star is statically known and never changes:

- A **δ-star** `[ −P(st(:N,π)), +P(st(body•,π)) ]` is, semantically, the
  pure rewrite rule `:N ↦ body•` with the stack variable `π` threaded
  unchanged. Its θ on a redex `+P(st(:N, σ))` is *always* the trivial
  `{π ↦ σ}` — there is no general unification to discover; the head `:N` is
  a ground nullary atom, `body•` is a ground closed term (`term.rs:250`
  `ground` bit is set; `Substitution::apply` already returns it in O(1)).
- **Push** (`galaxy.rs:423`) is exactly spine-unwind: `a(M,N)⋆π ↦ M⋆(N·π)`,
  a pure structural deconstruction, no unification.
- **Combinator stars** (`combinator.rs:147` `machine_stars` S/C/B/I/T/F and
  the galaxy lowercase analogues in `prim_stars`) are closed graph-splice
  transitions: `s⋆x·y·z·π ↦ (xz)(yz)⋆π` etc. — fixed-arity stack pops + a
  fixed contractum template with the popped operands substituted. Again no
  general unification: the LHS is `head ⋆ dot(x,dot(y,dot(z,π)))`, matching
  is a deterministic spine walk binding `x,y,z,π` positionally.

This is precisely the GraalVM/Truffle observation made explicit in docs/07
§H: **the reference interpreter `iex` is the language specification; the
optimizing tier is its specialization.** Specializing the interpreter to a
fixed program is the **first Futamura projection** (Futamura 1971,
*Partial Evaluation of Computation Process*; Jones/Gomard/Sestoft, *Partial
Evaluation and Automatic Program Generation*, 1993): `mix(interp, Φ)` =
`target` — a residual program that is the interpreter with all
Φ-dependent dispatch pre-resolved. [Lit]

### B.2 The artifact [Proto]

A **compiled per-head transition table / closure machine** `Σ(Φ)`, built
once per fixed Φ (the natural extension of `build_accel`,
`interactive.rs:1033`, which already pre-derives the Φ-only `RayIndex`):

- **Key:** the head symbol of the focused term in `+P(st(M,π))` (the atom
  reached after Push unwinds `M` to a non-`a` node — exactly
  `galaxy.rs:504` `spine_head`'s leftmost atom). The store is hash-consed
  (`term.rs:241`), so the head atom's `Sym` is an interned key.
- **Value:** a closed *transition closure* per head:
  - δ-head `:N` → `SpliceRule { contractum: body•_TermId, arity: 0,
    stack: passthrough }`: emit `+P(st(body•, π))` directly. **No
    unification, no α-rename** (`body•` is closed ground; π is the live
    continuation, copied by handle).
  - combinator head `c` (arity `k` from a static table) →
    `SpliceRule { pop: k, template: contractum_skeleton }`: pop `k` stack
    frames into `x₁…xₖ`, instantiate the fixed contractum template
    (`combinator.rs:169-184`) by positional substitution, push the result.
  - `a`-head (an application node still on the focus) → the Push transition:
    `M⋆π ↦ headof(M)⋆(argsof(M)…·π)`, a pure structural rule.
  - strict-op head (`add mul eq lt div neg isnil`) → the
    `strict_redex_on_pi` → `drive_strict` path (`galaxy.rs:601,728`)
    unchanged: this is the disclosed §60 intrinsic, the verified
    speculative-runtime *jet*, kept exactly as is.

`Σ(Φ)` is a pure function of Φ (same contract as `IexAccel`,
`interactive.rs:1023-1032`): build once, reuse for the whole run.

### B.3 Per-step complexity collapse

Generic step (today): O(\|Φ\|) candidate enumeration + α-unification per
candidate + per-redex α-rename of the matched Φ star + general `unify_fast`
+ `theta.apply` over residual rays. Specialized step: O(1) head-keyed
dispatch + (for δ) a single handle splice with **no unifier call and no
α-rename** + (for combinators) a fixed-arity pop and template instantiation.
The interpretive O(\|Φ\|) factor and the per-step general-unification factor
**both vanish on the δ-/combinator-/Push fragment**, which is the entire
galaxy control skeleton (docs/07 §B KG4b: "galaxy's combinator/control
skeleton executes faithfully"). Expected per-step cost collapse on that
fragment: roughly ×\|Φ\|-shaped on the `find`/`mat` envelope and the removal
of the dominant per-step α-rename+unify, i.e. the largest single per-step
win available — but it is still a **per-step (constant-per-step) lever**: it
makes each step cheap, it does not by itself reduce the *number* of steps
(that is D).

### B.4 Faithfulness proposition + certification

> **P-SPEC.** Let `iex(Φ,Ψ)` be the reference leftmost result and
> `Σ(Φ)`-driven `iex_spec(Φ,Ψ)` the specialized reducer. Then for every
> corpus `psi_compatible(iex(Φ,Ψ).psi, iex_spec(Φ,Ψ).psi)` holds
> (`faithfulness.rs:115`).

Why it is sound and cheap to certify: `Σ(Φ)` is *result-equivalent to `iex`
on Φ by construction* because each transition closure is the **literal
denotation** of the corresponding Φ star (the δ-star *is* `:N ↦ body`; the
combinator star *is* its contractum template). It is a partial evaluation of
the same rules, not a re-implementation — the classic "the residual program
is the interpreter specialized, equivalence is the Futamura correctness
theorem" [Lit]. The gate is the *same* `psi_compatible` the unifier rework
uses; reference `iex` stays the untouched oracle; `iex_spec` is a new fast
tier exactly like `iex_fast`/`iex_tabled`, never reachable from the
reference path, falling back to reference `iex` on any red gate (mirrors
`iex_fast_result_eq_iex` `interactive.rs:1530`,
`iex_tabled_result_eq_iex` `:1593`).

Tag: **[Proto]** (the table builder), built **on** [Built] substrate
(`build_accel`, `RayIndex`, hash-cons head keys, the ground bit).

---

## C. Lever 2 — Memoized graph reduction (call-by-need + global hash-consed NF cache)

### C.1 The opportunity = the literal KG6c blocker [Built facts]

The term store is hash-consed (`term.rs:241-308`): a `TermId` is a u32
handle, structural equality ≡ `TermId` equality, `App` args are `Arc<[TermId]>`
(`term.rs:220`) so identical subterms are shared once. Therefore:

> Under a **fixed Φ**, the forced normal form of a **closed** subterm is a
> deterministic pure function of its `TermId`.

Galaxy's image payload is built from massively **shared** structure: the
δ-bodies are huge ground terms reused across the cons-spine; the protocol
list re-applies the same closed sub-expressions. `galaxy_data_probe`
(`galaxy_data_probe.rs:68` `step_cons`) and `decode_forced`'s recursive
descent re-run `eval_forced` *from scratch* on every cons cell and every
visit of a shared child. That re-forcing of shared closed structure is
**the actual reason `data[0]` does not terminate** — it is exponential in
the sharing depth (`galaxy_decode.rs:248-256` states exactly this). A first
cut of this is being implemented by the parent concurrently in the
*decoder* (`galaxy_decode.rs:257` `memo: FxHashMap<TermId,TermId>`,
`deep_decode` `:282-290`). **This doc specifies the GENERAL engine-level
version.**

### C.2 The artifact [Proto]

A sound NF cache at the engine level, not the decoder level:

- **What is memoized:** `eval_forced(Φ, t, …) ↦ readback_ray(final_ray)`
  (and, inside it, `iex_fast`'s forced WHNF of closed subterms) keyed by the
  input `TermId` `t`.
- **Key:** the hash-consed `TermId` of the closed input term (O(1), already
  interned). This is the same key the decoder prototype uses, lifted to
  `galaxy::force_value`/`eval_forced` (`galaxy.rs:684,858`) so *every*
  forced sub-evaluation of a closed term — not only decoder-visited ones —
  hits the cache.
- **Scope:** per outermost `eval_forced` invocation under one fixed Φ
  (per-call, no cross-Φ staleness — `galaxy_decode.rs:256` already argues
  this; the engine-level version uses the same per-Φ lifetime, optionally
  promoted to a per-run cache since Φ is fixed for the whole galaxy run).
- **Closedness invariant (the soundness crux):** the cache entry is keyed
  and trusted **only when `t` is closed** — i.e. `term.rs:250` `ground` bit
  set (variable-free). For a closed `t` under a deterministic confluent
  reduction the forced NF is unique and independent of context, so reuse is
  *the same value*. An open term's forced NF depends on the ambient
  substitution and **must not** be cached (§G). The ground bit is already
  computed at intern time in O(1) — the invariant is a single existing
  predicate, not new analysis.

### C.3 Complexity + faithfulness

On shared-structure workloads (galaxy's image payload is the paradigm) the
cache turns **exponential re-forcing → linear** in the number of *distinct*
closed subterms (`galaxy_decode.rs:253-254`). This is what makes `data[0]`
*reachable*: KG6c's non-termination-in-150 s is re-forcing the same shared
δ-bodies along every cons path; memoizing collapses that to one force per
distinct subterm.

> **P-MEMO.** For closed `t` under fixed Φ, the memoized result equals the
> recomputed result *identically* (same `TermId`), because the cached value
> *is* the value the reference would compute — memoization changes *when*,
> never *what*.

Result-equivalence is therefore **trivial**: it is not a speculative jet
that could be wrong, it is value identity for the closed fragment. The gate
is still `psi_compatible(iex, iex_memo)` per corpus for defense-in-depth and
to *detect* an accidental cache of a non-closed term (which would show up as
a `psi_compatible` red and fall back). Reference `iex`/`eval_forced`
unrolled remains the oracle.

Tag: **[Proto]** at engine level; **[Built]** as the decoder-level first
cut (`galaxy_decode.rs:257-290`).

---

## D. Lever 3 — KA2 speculative trace acceleration on the detected recurrence

### D.1 The opportunity [Built substrate]

The whole substrate is built:

- `accel_detect.rs` [Built]: `detect_recurrence`/`detect_in_window`
  (`:94,:114`) — the Kruskal homeomorphic-embedding **whistle**
  (`antiunify::embeds`, a wqo: any infinite trace must whistle), plus the
  **sound generalizer** `is_sound_generalization` (`:190`, the verified
  one-directional α-subsumption — docs/07 §A0 records the substantive
  correctness fix) and `Whistle.recurrence` =
  `antiunify::affine_recurrence` (`:81`, the accelerable-affine-step
  nominator).
- `evaluate.rs` [Built]: the KG7 LIVE differential oracle
  (`OracleMode`/`OracleStatus`) — the Goodhart-guarded
  result-equivalence check a search-driven jit path needs.
- `faithfulness::psi_compatible` [Built, proven].
- docs/05 §9 [Spec, LOCKED]: KA2 pre-registered —
  `synthesize+guard+differential-cert Cᵏ` stars; `S₍ₜ₊δ₎ = C[Sₜ]` with
  `C` an affine/structural context ⇒ synthesize closed form `Cᵏ` (k
  symbolic, Z3 solves-for-k on the exact LIA fragment, docs/07 §C); guard
  (the accelerated star fires only when the live config matches the
  recurrence invariant); fall back (ordinary reduction otherwise — no
  speedup, no unsoundness); differential-certify (unrolled reference `iex`
  is the oracle; divergence ⇒ discard).
- docs/08 §3.1 [Proto, design-complete]: the checkable Proposition
  **idempotence-loss at AEx-layer n ⟺ `detect_recurrence` whistles on the
  per-layer trace** — wqo-justified, the single load-bearing experiment.

### D.2 The artifact [Proto]

Detect the recurrent core in the galaxy arithmetic/list payload and replace
its O(n) unrolled run with an accelerated transition:

1. **Trace.** Tap the per-AEx-layer trace `τ = (s₀,s₁,…)`,
   `sₙ = canonical(readback_ray(final_ray))` at the end of `eval_forced`'s
   iterated layer n (`galaxy.rs:858` loop; docs/08 §2.2 / §E "is
   `final_ray` a faithful AEx-layer-boundary proxy?" is the
   resolve-first open question — Stage-1-instrument it or the whistle is
   untrustworthy).
2. **Detect.** `detect_recurrence(τ)` → `Whistle { earlier i, later n,
   generalization C, recurrence }` (`accel_detect.rs:94`). `C` =
   `rigid_generalize(sᵢ,sₙ).skeleton` is the per-iteration context;
   `recurrence: Some` (the `affine_recurrence` certificate) marks the
   pair as an accelerable affine step (the add-/mul-pumping closed form,
   docs/05 §9 benchmark-zero = `mul(13,9)`).
3. **Synthesize.** From `sᵢ = C[paramᵢ]`, `sₙ = C[paramₙ]` solve for the
   closed form `Cᵏ` (k symbolic) — Z3 on the LIA/affine fragment
   (docs/07 §C: Z3 stays oracle/validator *outside* the trusted core;
   yes ⇒ accept jet, unknown/timeout ⇒ fallback).
4. **Guard + deopt.** Emit an accelerated star that fires only when the
   live config matches the recurrence invariant (`is_sound_generalization`
   `accel_detect.rs:190` is the exact subsumption gate — strictly stronger
   than the embedding whistle, the right asymmetry for a soundness gate);
   otherwise fall back to ordinary reduction. Deopt on guard miss.
5. **Differential-cert.** The accelerated ɟ-result must
   `psi_compatible` the unrolled reference `iex`/`eval_forced`
   (`evaluate.rs` live oracle); divergence ⇒ discard the jet (N-KA-sound,
   docs/05 §9; Goodhart-forbidden).

### D.3 Complexity + faithfulness

This is the **unbounded** lever: an O(n) recurrent run (the deep recursive
binary `mul`/list fold that is `mul(13,9)`'s fuel-class failure, docs/05 §9
benchmark-zero) collapses to O(1)/O(log n) via the closed form `Cᵏ`. It is
the lever that *most directly* makes the galaxy frame reachable because the
KG6c image-data payload is exactly arithmetic/list recursion past current
engine speed (docs/07 §B KG6c: "the recurrent-reduction shape the KG8
whistle detector / KG9 §49.50 design target").

> **P-KA2.** For every accelerated trace, the accelerated ɟ-result is
> `psi_compatible` with the unrolled reference `iex` (the per-instance
> oracle, `evaluate.rs`), AND `Cᵏ ≡ k`-unroll is discharged by Z3
> schematic induction on k for the affine/structural class (docs/05 §9 —
> the accelerated star is a *derived lemma, not an axiom*; later
> HOL4-checkable, docs/07 §G).

Soundness is local + empirical + (where Z3 closes it) symbolic; the
undecidable question ("does this program have accelerable loops") sits only
on the *coverage/speedup* path, never the *soundness* path — the
PyPy/LuaJIT/HVM discipline (docs/05 §9). Reference `iex` unrolled = truth.

Tag: **[Proto]** (KA2 not started, docs/07 §C); **[Built]** detector +
generalizer + oracle + validator substrate.

---

## E. How they compose + the honest ceiling

The three levers attack three orthogonal axes (§A table) and **multiply**:

- **B** cuts per-step cost by ~×k (k ∼ the interpretive/\|Φ\|-shaped factor
  + the eliminated per-step α-rename+general-unify on the δ/combinator
  fragment). It does not change the number of steps.
- **C** removes redundant sub-reductions: on the shared galaxy payload it
  turns exponential re-forcing into linear — this is not a constant factor,
  it is an asymptotic class change on shared-structure workloads, and it is
  *the* lever that takes `data[0]` from non-terminating-in-150 s to
  terminating.
- **D** collapses the recurrent run itself: O(n) unrolled → O(1)/O(log n)
  per detected affine recurrence — the unbounded lever.

Composition order matters and is favorable: B makes each residual
(non-accelerated, non-cached) step cheap; C ensures B's cheap steps are not
re-executed on shared structure; D removes whole O(n) families of steps that
B would otherwise still pay per-step and C would only dedup, not collapse.
They are independent organs (B = the reducer, C = the result cache, D = the
step-count collapse) so their wins compose roughly multiplicatively on the
galaxy payload, which is δ-heavy (B-favorable), massively shared
(C-favorable), and arithmetic/list-recursive (D-favorable).

**Honest compound estimate.** The galaxy first frame's blocker is *not* a
2× problem; it is a "does it terminate at all in human time" problem (Fact
2). The realistic claim is therefore **categorical, not a clean scalar**:
B+C make `data[0]` *reachable* (the dominant effect is C's
exponential→linear on shared structure, which is unbounded in the sharing
depth and is what crosses the termination boundary); D then delivers the
**>10× and beyond** on the recurrent arithmetic/list cores (unbounded in the
recurrence length n). A defensible compound figure on the galaxy payload is
**well over 10×** — but the load-bearing honest statement is that the win is
*structural* (a complexity-class change on the two axes that matter:
redundant sub-reduction and step count), so a single scalar understates it
where sharing/recurrence is deep and overstates it on non-shared,
non-recurrent residue. **Honest ceiling:** B is bounded (a per-step constant,
≤ ~\|Φ\|-shaped, the §A Fact-1 wall applies to B *alone*); C's win is bounded
by the actual sharing in the payload (high for galaxy, ~0 for a linear
non-shared term); D's win is bounded by how much of a real trace exhibits
guard-passing affine recurrence (docs/05 §9 N-KA-cover: if essentially no
real galaxy trace does, report it as a first-class negative — do **not**
retro-widen the recurrence class to manufacture hits). Non-structured
residue runs at B+C speed with no D win — no risk, just no further speedup.

---

## F. Staged, falsifiable plan + ordering vs in-flight work

Hard constraint: must **not** confound the in-flight `find` lever
(docs/07 §D / docs/09 §E) or the docs/09 Stage-2/3 attribution. The galaxy
Φ=405 `STELLA_KS_PROF` before/after delta must stay attributable per lever
(the docs/09:632-638 / docs/10 §5 staged-falsifier discipline). Therefore
the three levers here are sequenced **after** the in-flight `find`/Stage-2/3
unifier work lands and its `find`% drop is measured and attributed — none of
B/C/D touches the inner unify kernel or the `find` discrimination index, so
they are different organs, but they must still land one at a time with their
own KS-PROF attribution.

**Highest galaxy-frame ROI first = C (memoized graph reduction).** It is the
lever that directly attacks the literal KG6c blocker (re-forced shared
structure), its soundness is *trivial* (value identity for closed terms, not
a speculative jet), and a first cut already exists in the decoder
(`galaxy_decode.rs:257`) — lifting it to the engine level is the lowest-risk,
highest-reachability move. Then B (makes the now-deduped steps cheap), then
D (collapses the recurrent cores — highest ceiling, highest risk).

- **Stage C0 — engine-level NF cache, gated.** Lift the closed-subterm
  memo from `deep_decode` into `eval_forced`/`force_value`
  (`galaxy.rs:684,858`), keyed by `TermId`, trusted only for `ground`-bit
  closed terms. **Falsifier:** `psi_compatible(iex, iex_memo)` green on
  all `faithfulness.rs` corpora (`horn` `:217`, `binarith` `:244`, bounded
  `galaxy` `:259`) + the deliberately-cached-open-term negative the
  validator must catch; **galaxy `data[0]` now terminates** within a sane
  budget (the categorical falsifier — the whole point). KS-PROF: re-forcing
  count drops, no `unify`/`find`% change (attribution: it is the cache, not
  the algorithm).
- **Stage B0 — `Σ(Φ)` specialized reducer, gated.** Build the per-head
  transition table as an extension of `build_accel`; drive the δ/Push/
  combinator fragment via `Σ(Φ)`; strict ops keep `drive_strict`.
  **Falsifier:** `psi_compatible(iex, iex_spec)` green on all corpora;
  KS-PROF galaxy Φ=405 — per-step cost drops with the per-step α-rename+
  general-unify on the δ fragment measurably eliminated, **no change to the
  number of steps** (proving it is the per-step lever, not D). Any red ⇒
  that corpus falls back to reference `iex`.
- **Stage D0 — KA2 on the detected recurrence, gated.** Resolve docs/08
  §E first (is `final_ray` a faithful AEx-layer-boundary proxy?
  `galaxy.rs:864-893` — instrument or the whistle is untrustworthy). Then
  `detect_recurrence` on the galaxy arithmetic/list payload trace →
  synthesize `Cᵏ` (Z3, parent-owned `Cargo.toml` change when KA2 starts,
  docs/07 §C) → guard + deopt → differential-cert vs unrolled `iex`.
  **Falsifier:** docs/05 §9 benchmark-zero `mul(13,9)` terminates fast and
  correctly via acceleration (the pre-registered KA2 success criterion);
  N-KA-sound (any divergence from unrolled reference ⇒ revert);
  N-KA-cover (no real galaxy trace exhibits a guard-passing affine
  recurrence ⇒ first-class negative, no retro-widening).

Each stage's negative is a publishable recorded negative; none proceeds on a
red `psi_compatible`. Ordering rationale: C is reachability + trivial
soundness + already-prototyped; B is the largest *bounded* per-step win and
must be measured with no step-count change to stay attributable vs D; D is
the unbounded lever and the riskiest (synthesis/guard soundness, coverage).

---

## G. Honest risks

- **Φ-specialization breaks on subjective rays / §49.50 dynamics.** `Σ(Φ)`
  is sound exactly on the *objective* δ/Push/combinator fragment (the
  confluent, schedule-invariant fragment, §55.6, that `iex_tabled` already
  certifies result-equivalence on). It does **not** model §49.50
  ray-minting (`drive_strict` is the sole minting site, docs/08:151) or the
  semaphore order (a `+g(X)` under `−f` cannot interact until `+f`/`−f`
  annihilate, docs/08 §1). The strict-op fragment is *deliberately left on
  `drive_strict`* in B.2 precisely because that is where the static-vs-
  dynamic boundary is (the same boundary docs/10 §1.3 and docs/08 draw).
  Specializing past that boundary would be unfaithful; `psi_compatible`
  catches it (P-SPEC red ⇒ fall back) but the design must not pretend the
  δ-table covers subjective dynamics — it covers the control skeleton only.
- **Memo soundness for non-closed terms (the sharpest C risk).** The cache
  is sound *only* for closed (`ground`-bit) terms; an open term's forced NF
  depends on the ambient substitution and caching it by `TermId` alone is
  unsound. Mitigation: gate every cache write on the existing O(1)
  `ground` bit (`term.rs:250`); the deliberately-cached-open-term negative
  in Stage C0's falsifier exists specifically to prove the gate catches a
  violation. The decoder prototype is sound because it only ever forces
  closed protocol subterms; the engine-level lift must enforce the
  invariant explicitly, not inherit it by luck.
- **KA2 guard soundness.** The accelerated star is an axiom only if the
  guard is exact. `is_sound_generalization` (`accel_detect.rs:190`) is the
  one-directional subsumption (`∃θ. canonical(g)·θ ≡ canonical(x)`),
  strictly stronger than the embedding whistle — the correct soundness
  asymmetry, and the substantive correctness fix docs/07 §A0 records (it is
  *not* `embeds`, which would be unsound here). Residual risk: the
  synthesized `Cᵏ` itself; mitigated by Z3 schematic induction on k
  (symbolic, stronger than per-instance) + the unrolled differential
  oracle + deopt-on-mismatch + N-KA-sound revert. Z3 stays outside the
  trusted core (unknown/timeout ⇒ fallback, never accept).
- **Open-hypergraphs / data-parallel relation (does this subsume docs/10?).**
  No, and it must be stated plainly. docs/10's OHG array substrate is a
  **constant-factor** lever (B3 lock-free store + data-parallel layering of
  the step-fan / independent sub-reductions) — docs/10 §2.2 itself states it
  "does **not** accelerate the single hottest inner kernel" and is "a
  multiplier on the *post-unifier* profile." By §A Fact 2 a constant-factor
  multiplier cannot make a non-terminating-in-150 s reduction terminate.
  So docs/10 **sits beside** this doc, not under it: it composes as a
  constant-factor multiplier *after* B/C/D have made the frame reachable
  (its data-parallel layering of independent sub-reductions is in fact a
  natural amplifier of C's deduped independent forces). The three structural
  levers here are what cross the termination boundary; docs/10 then widens
  the result. Neither subsumes the other; conflating them would re-introduce
  exactly the "90s-incrementalism dressed up as a 10×" the project bans.
- **Attribution confound (process risk).** B/C/D each change a different
  axis; if two move at once the galaxy Φ=405 KS-PROF delta becomes
  un-attributable (the docs/09/10 staged-falsifier violation). The §F
  ordering (C, then B, then D, each with its own falsifier and the explicit
  "no step-count change for B / no algorithm change for C" attribution
  check) is load-bearing, not ceremony — it is how the >10× claim stays
  evidence-driven rather than asserted.

---

### One-line decision

The >10× and the reachable galaxy frame are structural: **C** (engine-level
hash-consed NF memoization of closed subterms — turns the KG6c
exponential re-forcing linear, trivially sound, do it FIRST) → **B**
(Φ-specialization / first Futamura projection — collapses the per-step
interpretive + α-rename+unify cost on the fixed δ/Push/combinator skeleton)
→ **D** (KA2 speculative acceleration of the detected affine recurrence —
the unbounded lever, O(n)→O(1)). All three gated by the proven
`psi_compatible` + reference `iex`/`eval_forced` oracle, falling back to
reference wherever the gate is red; docs/10's constant-factor OHG lever sits
beside, composing after, never subsuming.
