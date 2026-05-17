# 14 — Staged Compilation / Partial Evaluation of the Resolution Interpreter w.r.t. the Fixed Galaxy Φ

Status: READ-ONLY RESEARCH SYNTHESIS. No code changed. This sharpens docs/11
Lever B (Φ-specialisation / first Futamura) into a concrete construction with
file:line citations, an honest asymptotic verdict for the MEASURED blocker,
and a staged falsifiable plan. Claim tags as docs/11: **[Built]** = in tree &
tested · **[Lit]** = literature · **[Proto]** = proposed here, not built.

Faithfulness instrument is fixed and proven: every fast tier is gated by
`faithfulness::psi_compatible` (`faithfulness.rs:115` [Built], Stage-0
forensic-verified docs/07 §J2) against reference `iex`
(`interactive.rs:861` [Built]) as the differential oracle. No new trusted
code enters the faithfulness path.

---

## 0. The measured blocker, restated precisely

`data[0]` (one galaxy image element) does **not** terminate in 150 s at
fuel=2M/maxf=100k (docs/07 §B KG6c; docs/11 §A Fact-2). Two committed
results bound the design:

- Stage-1b `unify_fast` (`unify_fast.rs` [Built], wired at the exactly two
  fast-tier seam sites `interactive.rs:524 fuse_theta_fast`, `:575
  self_interact_fast` via the `Solve` fn-pointer `:461`) gave a measured
  galaxy Φ=405 **~2.0× total**, `unify` 53%→9%. A per-step constant-factor
  lever.
- Lever C memoised graph reduction (`galaxy.rs:861 FORCE_MEMO`, `:698`
  `is_ground`-gated [Built]) is value-identical, zero regressions, and
  **measured NOT to crack `data[0]`** (docs/07 NEXT-ACTIONS §3, commit
  b6c65d5): the payload is a genuinely long *non-redundant* reduction over
  the FIXED Φ (405 stars: `galaxy.rs:417 prim_stars` 13 + `:398
  delta_star` 392). Redundancy memo proven insufficient.

So the residual cost is **a long sequence of distinct steps**, each paying
the generic interpreter's per-step interpretive tax. Staged compilation
attacks the *per-step cost of that sequence* — it is, like unify_fast, a
**per-step lever**. This doc is honest about that up front (§2, §6 verdict).

---

## 1. The concrete compiled artifact and its construction from Φ + the interpreter

### 1.1 What the generic interpreter pays per step [Built, file:line]

The fast-tier loop `iex_fast_inner` (`interactive.rs:1086`) per step does:

1. `psi_csyms(&psi)` (`:422`) — recompute Ψ colour set (`T_PSICS`).
2. selection scan `:1121` — for each ray, `any_match_accel(accel,phi,r,&psi_cs)`
   (`:352`): colour gate, then `accel.idx.candidates(name,pol)`
   (`index.rs:100`, the head-bucketed `RayIndex`), then per candidate
   `fp_unifiable` (`:392`) + `matchable_fast` α-unification (`T_FIND`,
   measured ≈30% post-Stage-1b, docs/11 §A Fact-1).
3. on the chosen redex `produce_stars_fast` (`:942`): for each
   `mat_phi_c_accel` hit, `alpha_rename_star_fast(&phi[ik],counter)`
   (`:181`, `T_FRESH`) renames the WHOLE matched Φ star, then `fuse_fast`
   (`:527`) runs `unify_fast` + `theta.apply` over all residual rays
   (`T_FUSE`/`T_UNIFY`/`T_SUBST`).

`build_accel` (`interactive.rs:1033` [Built]) already pre-derives the
Φ-only `RayIndex` + `phi_csyms` ONCE per fixed Φ — it is *already a partial
pre-computation of Φ-dependent dispatch*, and a pure function of Φ
(`:1023-1032` reuse contract). It is a **first, shallow** Futamura
specialisation (the head-index is `mix`'s residual dispatch table). The
artifact below is its deep completion.

### 1.2 The static structure of each Φ star (the partial-evaluation opportunity)

Every Φ star's shape is statically known and never changes (docs/11 §B.1,
verified here against source):

- **δ-star** `[ −P(st(:N,π)), +P(st(body•,π)) ]` (`galaxy.rs:398-404`).
  `ref_atom(d.name)` (`:338`) is a ground nullary atom; `enc(&d.body)`
  (`:349`) is a closed ground term (`term.rs:267-274`: the `ground` bit is
  set at intern time iff all args ground; δ-bodies are var-free). The only
  variable is the shared stack var `π`. On a redex `+P(st(:N,σ))` the MGU
  is *always* the trivial `{π ↦ σ}`. **There is no general unification to
  discover and no α-rename needed** (`body•` is closed; `Substitution::apply`
  returns a ground subterm in O(1) — `term.rs:247`). This is literally the
  rewrite rule `:N ↦ body•`.
- **Push** `[ −P(st(a(M,N),π)), +P(st(M,N·π)) ]` (`galaxy.rs:423` /
  `combinator.rs:151`): pure spine-unwind `a(M,N)⋆π ↦ M⋆(N·π)`, a
  structural deconstruction, no unification.
- **Combinator/prim stars** `i t f s c b cons car cdr nil` + the two
  value-guarded `isnil` rules (`galaxy.rs:425-468`; uppercase analogues
  `combinator.rs:147 machine_stars`): fixed-arity stack pops + a fixed
  contractum template with popped operands positionally substituted
  (`s⋆x·y·z·π ↦ (xz)(yz)⋆π`). No general unification — a deterministic
  spine walk binding `x,y,z,π` positionally. The galaxy control skeleton
  is exactly this fragment (docs/07 §B KG4b: "galaxy's combinator/control
  skeleton executes faithfully").
- **strict-op head** (`add mul eq lt div neg isnil`): NOT in `prim_stars`;
  resolved by `strict_redex_on_pi`→`drive_strict` (`galaxy.rs:601,746`).
  This is the disclosed §60 intrinsic / verified-speculative jet — left
  exactly as is (it is the static/dynamic boundary, §3, §6).

### 1.3 The artifact: Σ(Φ) — a compiled per-head transition table [Proto]

`Σ(Φ)`: a closed, head-keyed transition table built once per fixed Φ as the
deep extension of `build_accel` (same pure-function-of-Φ contract,
`interactive.rs:1023-1032`):

- **Key.** The leftmost spine-head atom of the focused term in `+P(st(M,π))`
  — exactly `galaxy.rs:504 spine_head`'s returned `SymName` (interned u32,
  `term.rs:133 SymName`; hash-consed store `term.rs:220 Arc<[TermId]>`).
  This is the same key class `RayIndex` already buckets on (`index.rs:42
  IndexKey(SymName,Polarity)`).
- **Value.** One closed `Transition` per resolvable head, derived by
  partial-evaluating the generic step against that Φ star:
  - **δ-head `:N`** → `Subst { contractum: body•_TermId }`. Step ≡ replace
    the ray with `+P(st(body•, π))` where `π` is the live continuation
    copied by `TermId` handle. **No `mat_phi_c_accel` scan, no
    `alpha_rename_star_fast`, no `unify_fast`, no `theta.apply`** — the
    entire `produce_stars_fast` body collapses to one node splice. (392 of
    405 stars are δ.)
  - **Push (`a`-head on focus)** → `Unwind`: `M⋆π ↦ headof(M)⋆(args…·π)`,
    a pure structural rewrite of the focus/π pair. No unification.
  - **combinator head `c`** (static arity table `combinator.rs` /
    `galaxy.rs:425-468`) → `Splice { pop: k, template }`: pop `k` `dot`
    frames off π into `x₁…xₖ`, instantiate the fixed contractum skeleton
    by positional substitution, push. No general unification (positional).
  - **strict-op head** → `Jet`: dispatch unchanged to
    `strict_redex_on_pi`→`drive_strict` (`galaxy.rs:601,746`). The
    speculative-runtime intrinsic, untouched (§3).
- **Driver** `iex_spec`: a new fast tier exactly like `iex_fast`/
  `iex_tabled` (`interactive.rs:1074`), structurally a mirror of
  `iex_fast_inner` whose per-step body is `Σ(Φ).get(spine_head(focus))`
  → apply the closed `Transition`. Reference `iex` (`:861`) stays the
  untouched oracle; `iex_spec` is never reachable from the reference path;
  it falls back to reference `iex` on any red `psi_compatible` (mirrors
  `iex_fast_result_eq_iex` `:1530`, `iex_tabled_result_eq_iex` `:1593`).

**Construction = the first Futamura projection, mechanised.**
`Σ(Φ) = mix(step_iex, Φ)`: each `Transition` is the residual of
specialising the generic step function (`produce_stars_fast` +
`mat_phi_c_accel` + `fuse_fast`) to one statically-known Φ star, with all
Φ-dependent control (which bucket, which star, the α-rename, the unifier
call) pre-resolved at table-build time. It is **defunctionalisation +
closure conversion of the abstract machine** (Ager–Danvy line [Lit]): the
galaxy reducer *is* a KAM (docs/05 §5; the `st`/`dot`/Push triple
`galaxy.rs:314-336` is the Krivine `(code, stack)` pair), so deriving a
compiled KAM whose per-instruction dispatch is a closed table over Φ's
heads is the textbook "compile the abstract machine" step. The δ-fragment
is the *defunctionalised continuation*: each `:N` is a first-class
"apply this closed body" closure, the table is its `apply`.

Tag: **[Proto]** (the `Σ(Φ)` builder + `iex_spec` driver), built **on**
[Built] substrate (`build_accel`, `RayIndex`, `spine_head`, hash-cons
`SymName` keys, the `ground` bit).

### 1.4 GRIN / whole-program assessment [Lit, honest scoping]

GRIN (Boquist) — whole-program lazy graph-reduction compilation: eval/apply
collapse, pointer tagging, defunctionalisation, call-pattern specialisation,
aggressive inlining. **What transfers:** the *defunctionalisation* and
*call-pattern specialisation* core is exactly §1.3 — Σ(Φ) is a
per-call-pattern (per-head) specialised dispatch, and the δ-fragment is the
defunctionalised tag-dispatch GRIN's whole-program tag analysis would
produce. **What does NOT transfer / is not worth it here:** GRIN's value is
*compiling to native code* (LLVM backend, register-allocated heap nodes).
This project's faithfulness contract requires the reducer to remain the
stellar engine over Φ with `iex` as a live differential oracle (docs/07 §H
verified-speculative-runtime); emitting native code would (a) move the
trusted boundary, (b) break the two-tier deopt story, (c) be a
disproportionate engineering cost for a per-step constant. **Verdict:
adopt GRIN's defunctionalisation/call-pattern-specialisation idea as Σ(Φ)
(an interpreted closed table); do NOT pursue GRIN-style native codegen.**
The Truffle/GraalVM model (docs/07 §H) is the right one: Σ(Φ) is the
"compiled tier", `iex` is "the interpreter is the spec", and the table is
the partial-evaluation residual — no native backend needed for the win.

---

## 2. Which Futamura projection / staging is worth it, and the asymptotic + constant-factor it buys

- **1st projection** `mix(iex,Φ) = Σ(Φ)` — a compiled galaxy. **WORTH IT.**
  Cheap (a table builder, the natural completion of `build_accel`),
  directly attacks the measured per-step tax on the δ/Push/combinator
  fragment that is the entire galaxy control skeleton.
- **2nd projection** `mix(mix,iex)` — a compiler (galaxy-source → reducer).
  **NOT worth it.** Φ is fixed and built once per run; there is exactly one
  program. A reusable compiler buys nothing the 1st projection's
  build-once table does not, and adds a self-application machinery the
  faithfulness gate would have to re-cover. Skip.
- **3rd projection** — a compiler-compiler. **Irrelevant** here (no family
  of interpreters). Skip.

**Asymptotic, honest.** Σ(Φ) does **not** change the *number* of steps —
that is docs/13 (supercompilation) / docs/11 Lever D (KA2). It changes the
*cost of each step* on the δ/Push/combinator fragment:

| per step, generic (today) | per step, Σ(Φ) |
|---|---|
| `psi_csyms` rebuild + selection scan over Ψ | head lookup `Σ(Φ).get(spine_head)` = O(1) |
| `any_match_accel`/`mat_phi_c_accel`: bucket walk + `fp_unifiable` + `matchable_fast` per candidate (`T_FIND`, ≈30%) | eliminated for δ/combinator (head IS the dispatch; no candidate set) |
| `alpha_rename_star_fast` of the matched Φ star (`T_FRESH`) | eliminated for δ (body closed) / O(arity) positional for combinators |
| `unify_fast` + `theta.apply` over residual rays (`T_FUSE`, `T_UNIFY`, `T_SUBST`) | eliminated for δ (MGU is `{π↦σ}`, applied by handle) / positional splice for combinators |

So Σ(Φ) collapses, on the δ-dominated galaxy skeleton, essentially the
**entire post-`psi_csyms` per-step envelope** (`find` + `freshen` + `fuse`
+ `unify` + `subst`) to an O(1) head dispatch + a handle splice. Constant
factor: this is the **largest single per-step lever available** — it
removes the dominant residual phase `find` (≈30%, the in-flight lever's
target, capped at ~1.05× as a *tuning* lever per docs/11 Fact-1 but here
*structurally eliminated* on the δ fragment, not tuned) PLUS the per-step
α-rename and the general-unify call that unify_fast only made *near-linear*
rather than *absent*. A defensible per-step figure on the δ/Push/combinator
fragment is well above the residual ~1.05× `find` ceiling and above the
~2× unify_fast delivered, because unify_fast still pays α-rename + a
unifier call + `theta.apply` per step that Σ(Φ) deletes outright for the
392 δ-stars. Order-of: the per-step cost on the δ fragment goes from
"scan+rename+unify+apply" to "lookup+splice".

**The honest verdict for the MEASURED blocker (REQUIRED §2 answer).**
Σ(Φ) is a **per-step-cost lever, like unify_fast — it makes `data[0]`
*faster, not finite*.** It multiplies a non-terminating-in-150 s reduction
by a (large) constant and the reduction is still a long non-redundant
sequence. **It does NOT make `data[0]` terminate by itself.** docs/11 §A
Fact-2 is exact and applies to Σ(Φ): a constant-per-step win cannot cross
the termination boundary. What makes the frame *reachable* is step-count
collapse — docs/13 supercompilation and/or docs/11 Lever D (KA2
recurrence acceleration, O(n)→O(1)). Σ(Φ) makes every residual
(non-collapsed) step cheap, which **compounds multiplicatively** with a
step-count lever (§4) and is a large standalone engine-merit win, but the
load-bearing honest statement is: **compilation alone is necessary-for-fast,
not sufficient-for-the-frame.**

---

## 3. Faithfulness: result-equivalence to `iex`, two-tier, deopt, specialisation soundness

**P-SPEC (the proposition, sharpened from docs/11 §B.4).** Let `iex(Φ,Ψ)`
be the reference leftmost result and `iex_spec(Φ,Ψ)` the Σ(Φ)-driven
reducer. For every corpus, `psi_compatible(iex(Φ,Ψ).psi,
iex_spec(Φ,Ψ).psi)` (`faithfulness.rs:115`, multiset of α-canonical
ɟ-concealed visible stars).

**Why the specialisation denotes the same constellation semantics
(soundness of `mix`).** This is *not* a re-implementation that could drift;
it is a partial evaluation, and equivalence is the Futamura correctness
theorem [Lit] instantiated:

- A δ-`Transition` *is* the literal denotation of the δ-star: the star
  `[ −P(st(:N,π)), +P(st(body•,π)) ]` fused against `+P(st(:N,σ))` yields
  exactly `+P(st(body•,σ))` because the MGU of `st(:N,π)` and `st(:N,σ)`
  is `{π↦σ}` and `body•` is closed (ground bit, `term.rs:267`) so
  `theta.apply(body•) = body•`. The `Subst` transition emits precisely
  this. Equality is *definitional*, provable by inspection of the one
  rule, not empirical.
- A combinator `Transition` is the positional instantiation of the fixed
  contractum template (`galaxy.rs:425-468` / `combinator.rs:169-184`) —
  again the literal star semantics, since those stars have no non-π
  variables shared across rays in a way the generic unifier resolves
  differently from a positional pop.
- Push `Unwind` is the verbatim `galaxy.rs:423` rule.

So Σ(Φ) is sound *by construction on the δ/Push/combinator fragment*; the
`psi_compatible` gate is defense-in-depth (it would catch a builder bug,
e.g. a mis-extracted contractum or a wrong arity) exactly as it gates
unify_fast — same instrument, same oracle, no new trusted code.

**Two-tier + deopt.** `iex_spec` is a sibling of `iex_fast`/`iex_tabled`
(`interactive.rs:1041-1076`), reached only via the fast path, never from
reference `iex` (`:861`, hard-codes `unify`/`fuse`, statically
un-contaminable — docs/09 §C, the `Solve` fn-pointer seam `:461` is the
only fast/ref divergence and is not on the reference functions). Deopt:
any head not in Σ(Φ), or any `psi_compatible` red on a corpus, falls back
to reference `iex` for that run — identical discipline to
`iex_fast_result_eq_iex` (`:1530`). The strict-op `Jet` is **not**
specialised; it stays on `drive_strict` (`galaxy.rs:746`), which is the
existing disclosed §60 verified-speculative intrinsic with its own
oracle gate (docs/07 §B KG4b: legitimate intrinsic, not debt). Σ(Φ)
adds no new speculation — it is value-identical PE of the confluent
objective fragment, strictly weaker (safer) than the existing jet.

---

## 4. Honest relation to docs/11 Lever B, docs/12, docs/13

- **docs/11 Lever B — SHARPENED, not superseded.** This doc *is* Lever B
  made concrete: §1.3 names the artifact (`Σ(Φ)` = closed per-head
  `Transition` table), gives the exact construction (defunctionalised KAM
  / `mix(iex,Φ)`, the natural completion of `build_accel`
  `interactive.rs:1033`), the file:line collapse (§1.1→§2 table), the
  Futamura-projection selection (§2: 1st only), and the soundness proof
  shape (§3: definitional per-rule, not empirical). It also **corrects an
  over-optimism in docs/11 §E**: docs/11 lists B as one of three levers
  that "multiply" to a ">10× and reachable frame"; this doc states plainly
  that B *alone* is a per-step constant and does NOT reach the frame
  (docs/11 §E's own "Honest ceiling: B is bounded" is the correct
  reading; the headline "B+C+D well over 10×, frame reachable" is carried
  by C/D, not B). Lever B's honest role: the largest per-step multiplier,
  a standalone engine-merit win, a **compounding** factor under a
  step-count lever.

- **docs/12 (interaction nets) — ORTHOGONAL, compounding.** Interaction
  nets / data-parallel layered rewriting (the docs/10 OHG substrate, and
  the Lafont interaction-combinator encoding Eng §87.5 flags as unrealised)
  is a *parallelism/representation* lever: it speeds the step-fan and
  independent sub-reductions by a constant factor (docs/11 §G: "does NOT
  accelerate the single hottest inner kernel … a multiplier on the
  post-unifier profile"). Σ(Φ) makes each net-interaction cheap; an
  interaction-net layer would then run those cheap interactions in
  parallel. **Neither subsumes the other**; they compose as independent
  organs (Σ(Φ) = the per-step reducer, IN = the parallel scheduler over
  it). Both are constant-factor and neither crosses the termination
  boundary alone.

- **docs/13 (supercompilation) — COMPLEMENTARY, the step-count partner;
  partial overlap with Σ(Φ).** Supercompilation (driving + generalisation
  + folding the recurrent core) is the **step-count** lever — it is what
  *does* cross the termination boundary for a long non-redundant reduction,
  by collapsing the recurrent skeleton into a residual program (this is
  also docs/11 Lever D / KA2's role: `accel_detect.rs:94 detect_recurrence`
  [Built] + `affine_recurrence` closed-form, O(n)→O(1)). Honest overlap:
  the *first* Futamura projection (Σ(Φ)) and supercompilation are points
  on the same partial-evaluation spectrum — supercompilation is "partial
  evaluation with information propagation + generalisation across the
  unfolding", and the limit of a sufficiently aggressive supercompiler of
  `iex` w.r.t. Φ subsumes Σ(Φ) (the residual program would inline the
  per-head dispatch). **But they are NOT redundant here:** Σ(Φ) is cheap,
  total, definitionally sound, and ships now as a fast tier; a galaxy-scale
  supercompiler is the harder, riskier, step-count-collapsing artifact.
  The pragmatic decomposition: **Σ(Φ) makes each step cheap (this doc);
  supercompilation/KA2 makes the number of steps small (docs/13 / Lever
  D). They compound multiplicatively and Σ(Φ) is the lower-risk first
  half.** Σ(Φ) is *subsumed in the limit by* a perfect supercompiler but
  is *not subsumed in practice* — it is the tractable, immediately-sound
  slice.

Summary: **B is sharpened (this doc); IN is orthogonal/compounding (const
factor); supercompilation/D is complementary and the actual
frame-reacher (step count), partially subsuming B only in the
theoretical limit.**

---

## 5. Staged, falsifiable plan + ordering vs in-flight work

Hard constraint (docs/11 §F, docs/09/10 staged-falsifier discipline): must
NOT confound the in-flight `find` lever or the docs/09 Stage-2/3 unifier
attribution. Σ(Φ) does not touch the inner `unify` kernel or the `find`
discrimination index — it *eliminates* them on the δ fragment — so it is a
different organ, but it must still land alone with its own KS-PROF
attribution. **Ordering:** strictly **after** the in-flight `find`/
Stage-2/3 unifier work lands and its `find`% drop is measured and
attributed (so the Σ(Φ) delta is not confounded with a concurrent `find`
change), and it must NOT be co-landed with docs/11 Lever C engine-level
lift or Lever D (each a separate axis, separate falsifier).

**Stage-0 (the single load-bearing experiment).** Compile the δ+Push
fragment of ONE corpus (the bounded-galaxy entry corpus
`faithfulness.rs:259`, plus `combinator`/`binarith`) to `Σ(Φ)`:

1. Build `Σ(Φ)` for that Φ (δ + Push only first; combinator heads next;
   strict-op heads stay `Jet`→`drive_strict`).
2. `iex_spec` driver; run the corpus.
3. **Falsifier A (soundness):** `psi_compatible(iex, iex_spec)`
   (`faithfulness.rs:115`) GREEN on all standing corpora (`horn` `:217`,
   `binarith` `:244`, bounded `galaxy` `:259`, `combinator`) **plus** a
   deliberately-wrong-`Transition` negative (e.g. a δ-body off-by-one or a
   swapped combinator template) the gate MUST flag red — exactly the
   wrong-unifier-falsifier discipline docs/09 Stage-1 used. Any red on a
   real corpus ⇒ that corpus falls back to reference `iex`; a wrong-table
   negative that passes ⇒ Stage-0 fails, do not proceed.
4. **Falsifier B (it is the per-step lever, NOT a step-count lever —
   attribution):** KS-PROF galaxy Φ=405 (`STELLA_KS_PROF=1`,
   `interactive.rs:1173 ks_report`) before/after: per-step `find` +
   `freshen` + `fuse` envelope on the δ fragment measurably collapses,
   and **the number of steps is UNCHANGED** (Σ(Φ) must not alter step
   count — if it does, the table is not result-equivalent and Falsifier A
   should already be red). This keeps it attributable vs docs/13/Lever D.
5. **Falsifier C (the categorical honest test):** measure `data[0]` under
   `iex_spec`. **Pre-registered expected result: it is FASTER but STILL
   does not terminate** in a sane budget (consistent with §2 / docs/11
   Fact-2). Reporting "Σ(Φ) made data[0] terminate" would actually be
   *surprising* and would mean the payload was per-step-bound not
   step-count-bound — record it honestly either way; the expected
   recorded outcome is a first-class **negative for the frame, positive
   for engine throughput**.

**Stage-1.** Add combinator-head transitions; re-run Falsifiers A/B.
**Stage-2.** Promote Σ(Φ) to the per-run cache (Φ fixed for the whole
galaxy run, same lifetime contract as `build_accel`
`interactive.rs:1023-1032`); compose with the Lever-C `FORCE_MEMO`
(`galaxy.rs:861`) and (later) Lever-D KA2 — measure the compound, each
landed and attributed singly.

**Ordering vs the in-flight set (explicit):** unify/`find`/Stage-2-3 FIRST
(in flight, must not confound) → **Σ(Φ) Stage-0/1** (this doc, the largest
per-step win, lands here) → Lever C engine-level lift → Lever D / KA2 (the
step-count / frame-reacher, highest risk, docs/11 §F, docs/08 §E
`final_ray`-proxy resolved first). Σ(Φ) is sequenced before D because it
is definitionally sound (lower risk than KA2's synthesised closed form)
and makes D's residual non-collapsed steps cheap.

---

## 6. Honest risks + verdict

- **Σ(Φ) does NOT crack the measured blocker (the headline risk of
  over-claiming).** It is a per-step lever. By docs/11 §A Fact-2 a
  constant-per-step win cannot make a non-terminating-in-150 s reduction
  finite. Mitigation: this doc states it everywhere (§0, §2 verdict, §5
  Falsifier C pre-registers the expected negative). The value is real but
  it is engine-throughput + compounding-under-D, NOT "the frame".
- **Subjective-ray / §49.50 dynamics resist static specialisation
  (soundness boundary — cross-ref docs/08/10).** `drive_strict`
  (`galaxy.rs:746`) is the **sole ray-minting site** (docs/08:151, §1) —
  §49.50 subjective-ray semaphore dynamics live there and ONLY there, not
  in the δ/Push/combinator skeleton. Σ(Φ) deliberately leaves every
  strict-op head as a `Jet`→`drive_strict` (§1.3, §3): the
  static/dynamic boundary is exactly the docs/08 §1 / docs/10 §1.3
  semaphore boundary. Specialising past it (e.g. pre-folding a strict op's
  forced operand) would be unfaithful because the §49.50 minting/semaphore
  order is schedule-sensitive (docs/08 §F: trace/partial-commutation
  monoid, NOT a commutative multiset). `psi_compatible` would catch a
  violation (P-SPEC red ⇒ fall back) but the design must not pretend Σ(Φ)
  covers subjective dynamics — it covers the **objective confluent
  control skeleton** only (the same fragment `iex_tabled` already certifies
  result-equivalent, docs/11 §G). This is a *scoping* discipline, not a
  defect: Σ(Φ) is sound exactly where it claims to be.
- **Specialisation soundness (builder correctness).** The risk is a buggy
  table builder (mis-extracted δ-body, wrong combinator arity/template),
  not a wrong *theory* — the PE is definitionally equivalence-preserving
  (§3). Mitigation: the Stage-0 deliberately-wrong-`Transition` negative
  (§5 Falsifier A) the gate must flag, identical to docs/09's
  wrong-unifier falsifier; the `ground`-bit check (`term.rs:313`) gates
  the "δ-body is closed ⇒ `theta.apply` is identity" assumption (an open
  δ-body — there are none in galaxy, but assert it — would make the
  trivial-MGU shortcut unsound, exactly the docs/11 §G memo-soundness
  crux, reused here).
- **Binary size / compile time / build cost.** Σ(Φ) is **data, not
  generated code** (an interpreted closed table — §1.4 rejects GRIN
  native codegen precisely to avoid this). 405 entries; build cost is one
  pass over Φ (= `build_accel` cost class, already paid). No binary-size
  or rustc-compile-time risk. The only cost is the table-build time, which
  is amortised once per run (Φ fixed) — strictly cheaper than the
  per-call `IexAccel::build` the valence-loop hoisting already optimised
  (docs/07 §A, commit 308189f).
- **Attribution confound (process risk).** If Σ(Φ) co-lands with the
  in-flight `find` lever or Lever C/D, the galaxy Φ=405 KS-PROF delta
  becomes un-attributable (docs/09/10 staged-falsifier violation). §5
  ordering + Falsifier B ("no step-count change") is load-bearing, not
  ceremony.

### Verdict

Build **Σ(Φ)** (the first Futamura projection, mechanised as a
defunctionalised KAM transition table over Φ's heads — §1.3), sequenced
after the in-flight unify/`find` work, with the Stage-0 falsifiers of §5.
It is the **largest single per-step lever available**: it structurally
eliminates the `find`+`freshen`+`fuse`+`unify`+`subst` per-step envelope on
the 392-δ + Push + combinator galaxy control skeleton, definitionally
result-equivalent to `iex` by the Futamura correctness theorem (§3, gated
by the proven `psi_compatible` + reference oracle + deopt). It is cheap
(data not codegen), low-risk (definitional PE, strictly weaker than the
existing §60 jet), and compounds multiplicatively with the step-count
lever. The **biggest risk** is *mis-selling it*: like unify_fast it is a
per-step-cost lever — it makes `data[0]` materially faster but **does NOT
make it terminate**; the galaxy frame is reached only by the step-count
collapse (docs/13 supercompilation / docs/11 Lever D KA2), for which Σ(Φ)
is the compounding, lower-risk, ship-first companion.

**Does this make galaxy's `data[0]` actually execute (terminate)?**
**NO** — not by itself. Σ(Φ) makes every step on the δ/Push/combinator
skeleton dramatically cheaper (the largest per-step win, well above the
~2× unify_fast and the ~1.05% `find` ceiling) and compounds with the
step-count lever, but `data[0]` is a long *non-redundant* reduction and a
constant-per-step win cannot cross the termination boundary (docs/11 §A
Fact-2). Termination of `data[0]` requires a step-count lever
(supercompilation / KA2 recurrence acceleration, O(n)→O(1)); Σ(Φ) is its
necessary, lower-risk, multiplicatively-compounding companion, not its
substitute.
