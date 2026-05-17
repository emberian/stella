# 13 — Supercompilation / Distillation: can whole-program transformation make galaxy `data[0]` execute?

Status: RESEARCH synthesis. No code changed. Read-only over the built engine,
docs/05 §9 (KA2 spec, LOCKED), docs/07 §C, docs/08 §3.1/§6, docs/11 (Levers
B/C/D), `accel_detect.rs`/`antiunify.rs`/`galaxy.rs`/`evaluate.rs`/
`faithfulness.rs`.

Claim tags: **[Built]** in tree & tested · **[Lit]** paper · **[Proto]**
proposed here, not built.

---

## 0. The measured situation (the only thing that matters first)

- Lever C (memoised graph reduction) is **[Built]** and **measured**: commit
  `b6c65d5`/`b72f229`, `galaxy.rs:846-895` (`FORCE_MEMO`, `is_ground`-gated,
  cleared at `TR_DEPTH==0`). docs/07:461-467 records the **honest negative**:
  it is value-identical, zero regressions, and it **does not crack `data[0]`**
  — still non-terminating in 150 s.
- The load-bearing consequence, verbatim from docs/07:465: *"the galaxy image
  payload is **not redundancy-bound**; it is a genuinely long **non-redundant**
  reduction."* Hash-consed sub-result reuse (CSE / memoisation / common-graph
  sharing) is *provably exhausted* on this workload.
- This is precisely the regime where shallow deforestation, tabling, and
  call-by-need sharing have nothing left to give, and the *only* remaining
  structural lever is one that **changes the number of reduction steps as a
  function of input size** — i.e. removes interpretive layering and collapses
  *recurrent* (not redundant) computation. That is the supercompilation /
  distillation question, and it maps onto the project's pre-registered Levers
  **B** (Φ-specialisation = 1st Futamura) and **D** (KA2 = recurrence
  acceleration).

The galaxy reduction has three composable cost axes (docs/11 §A); C killed
the redundancy axis with no frame. What remains: **per-step interpretive
overhead** (B) and **step count of a recurrent core** (D). Distillation is
the literature name for the strongest form of the latter — and the honest
finding of this doc is that *only the D-class lever can change the asymptotic
that the C negative exposed*, B alone cannot.

---

## 1. Supercompilation / distillation over THIS engine — concrete construction

### 1.1 The supercompiler loop, instantiated on built components

A positive supercompiler (Sørensen–Glück–Jones; Turchin) is the fixpoint of
four operations: **drive** (symbolic execution), **whistle** (detect
dangerous growth), **generalise** (abstract the whistled pair), **fold**
(tie the recurrence into a residual program). Every one of these already
exists in tree:

| Supercompiler op | Built engine realisation | file:line | Tag |
|---|---|---|---|
| **drive** (one-step symbolic reduction) | `eval_forced` loop = iterated `AEx_Φ` (`iex_fast` to `±P`-NF, then `drive_strict` mints the next layer) | `galaxy.rs:890-960`; docs/08 §2.3 | [Built] |
| **trace** (the config sequence to scan) | per-AEx-layer `sₙ = canonical(readback_ray(final_ray))` | `galaxy.rs:904-914` (`final_ray`); docs/08 §3.1/§E | [Proto] tap |
| **whistle** (Kruskal homeomorphic embedding, a wqo) | `accel_detect::detect_recurrence` → `antiunify::embeds` | `accel_detect.rs:94`, `antiunify.rs:142` | [Built] |
| **generalise** (the abstracting context `C`) | `Whistle.generalization = rigid_generalize(sᵢ,sₙ).skeleton` | `accel_detect.rs:76-82`, `antiunify.rs:321` | [Built] |
| **soundness of the generalisation** | `is_sound_generalization` = one-directional α-subsumption `∃θ. canonical(g)·θ ≡ canonical(x)` (strictly stronger than the embedding whistle) | `accel_detect.rs:135-199` | [Built] |
| **affine-step nomination** (the accelerable shape) | `antiunify::affine_recurrence` (embedding-gated + rigid + per-slot whistle) | `antiunify.rs:385-423` | [Built] |
| **fold** (tie recurrence → residual program) | KA2 synthesised guarded `Cᵏ` star; deopt fall-back | docs/05 §9, docs/11 §D.2 | [Proto] not started |
| **faithfulness of the residual** | `psi_compatible` (multiset result-equiv) + two-tier + live diff oracle | `faithfulness.rs:115`, `evaluate.rs:220-266` | [Built] |

The supercompiler is therefore **not new infrastructure** — it is wiring the
already-built whistle+generaliser onto the already-built `eval_forced` driver
trace, plus a residualiser (the only genuinely unbuilt piece). docs/08 §3.3
states this explicitly ("No new fixpoint engine"). The whistle is
*observational by construction* (`accel_detect` module doc lines 4-6): driving
is unchanged; the transformation is the fold step alone.

### 1.2 What galaxy specifically is — and why this is second-Futamura-flavoured

galaxy = the ICFP-2020 "Message from Space" interaction machine: 392 δ-stars
`[ −P(st(:N,π)), +P(st(body•,π)) ]` (`galaxy.rs:398` `delta_star`) + 13 prim
stars (Push + `{i,t,f,s,c,b,cons,car,cdr,nil,isnil}` + arith, `galaxy.rs:417`
`prim_stars`). The δ-stars are a *fixed program* (the alien protocol
interpreter) over a *fixed* Φ; the image generator is the recurrent
arithmetic/list construction this protocol drives.

Two Futamura readings, both relevant:

- **B = first projection.** `mix(iex, Φ_galaxy) = target`: specialise the
  generic resolution interpreter to the fixed 405-star Φ → a per-head
  transition table. This removes the *interpretive* O(|Φ|) re-scan +
  per-redex α-rename + general `unify_fast` on every step
  (docs/11 §B.3). It is a **per-step** collapse: each step gets cheap, the
  *number* of steps is unchanged.
- **Supercompiling "`iex` applied to Φ applied to the galaxy entry"** is a
  *whole-program* collapse closer to the **second** Futamura projection in
  spirit: it does not just specialise the interpreter to the program, it
  specialises the *interpreter-running-the-program-on-this-input-shape* and
  folds the recurrence the protocol machine generates. This is where the
  step-count asymptotic can change — and it is the only thing that can,
  given the C negative.

Distillation (Hamilton 2007/2009, *Distillation: extracting the essence of
programs*; Hamilton–Jones) is the strengthening of supercompilation that
generalises/folds **over the driven graph itself rather than over flat term
sequences**, which is exactly what lets it achieve *superlinear* speedups:
it can fold a recurrence whose accumulator is itself built by a nested
recurrence (the case positive supercompilation only linearly improves). For
galaxy that nesting is precisely "the protocol interpreter loop, each turn of
which forces an arithmetic/list sub-recurrence" — a two-level recurrence.
[Lit]

---

## 2. The asymptotic argument for the measured blocker

### 2.1 What B removes, and why B alone is provably insufficient

B (Φ-specialisation) removes the *interpretive* factor: per step it replaces
O(|Φ|)-candidate-scan + α-rename + general unification with O(1) head dispatch
+ a closed splice (docs/11 §B.3, `galaxy.rs:398/417` show δ/Push/combinator
are pure structural rules with trivial θ). Asymptotically B takes total cost
from `Θ(steps · |Φ|·u)` to `Θ(steps · 1)` where `u` is the per-step unify
cost. **`steps` is unchanged.** docs/11 §A Fact-2 is the proof of
insufficiency: the payload "does not terminate even at 2×"; multiplying a
non-terminating-in-150 s reduction by any constant (B's win is a constant
per-step factor, bounded by |Φ|, docs/11 §E "B is bounded") leaves it
non-terminating. **B makes each step cheap; it cannot make `data[0]`
terminate.** (B is still worth doing — it is the largest *bounded* win and it
makes D's residual-and-fallback steps cheap — but it is not the galaxy path.)

### 2.2 The precise condition on galaxy's recurrent core, and what D collapses

The C negative says the long reduction is **non-redundant**: distinct closed
subterms, each forced once, no reuse to harvest. A non-redundant reduction of
length `n` can still be **recurrent**: the sequence of focused configs
`s₀,s₁,…,sₙ` is non-repeating yet **structurally self-embedding** — `sᵢ ⊴ sⱼ`
for `i<j` under Kruskal embedding, with `sⱼ = C[paramⱼ]`, `sᵢ = C[paramᵢ]`,
`C` a fixed context and `paramⱼ` the *grown* (not repeated) accumulator. This
is the textbook accumulating-parameter recurrence: each `sⱼ` is genuinely new
(so C/memo finds nothing) yet each is the previous one *grown by a fixed
context* (so the whistle fires and a closed form exists). `antiunify.rs:385`
`affine_recurrence` is exactly the predicate for this shape; its own test
(`accel_detect.rs:266-299`) drives the accumulating `add`-unfold
`add(sX,Y,sZ) → add(s(sX),Y,s(sZ))` — galaxy's binary `add`/`mul`/list-cons
core is the same shape at scale.

> **Asymptotic claim (the load-bearing one), [Proto].** If galaxy's
> image-data core is an affine/structural recurrence — `sₙ = Cⁿ[s₀]` for a
> fixed context `C` with an affine accumulator (the add-/mul-pumping closed
> form, docs/05 §9) — then supercompilation/distillation **provably
> collapses** the Θ(n)-step unrolled reduction to the closed form: Θ(1) when
> the accumulator value is computed by the host arith jet, Θ(log n) when it
> is computed by the binary-numeral recurrence itself. This is a
> **complexity-class change in step count**, not a constant factor — exactly
> the lever the C negative proves is the only one that can cross the
> termination boundary.

This is conditional, and the condition is the empirical crux: **does galaxy's
real `data[0]` trace actually exhibit a guard-passing affine/structural
recurrence?** docs/05 §9 N-KA-cover and docs/11 §E name this precisely: if
essentially no real galaxy trace does, that is a *first-class negative*, not a
licence to widen the recurrence class. The honest position: the *mechanism*
provably collapses the recurrent case; whether galaxy's core *is* that case is
unproven and is Stage-0's job to settle on a small galaxy-shaped term first.

**Is distillation the stronger thing we actually want?** Yes, with a caveat.
Positive supercompilation linearly improves and folds *single-level* loops;
its whistle/generalise/fold is exactly the built `accel_detect` + KA2-`Cᵏ`
machinery. The galaxy core is plausibly **two-level** (protocol loop ×
inner numeral/list recurrence). Distillation's superlinear claim comes
precisely from folding the *nested* recurrence (generalising over the driven
graph, not the flat trace) — turning an effectively exponential interpreted
unrolling into a polynomial/linear residual. So the *target* is distillation;
the *first build* is the KA2 single-recurrence special case, because (a) it is
fully spec'd and substrate-built, (b) it is the necessary inner kernel of any
distiller anyway, and (c) it is independently falsifiable on the
`mul(13,9)` benchmark-zero before the harder nested case.

### 2.3 Is KA2 a special case of supercompilation? Is distillation stronger?

- **KA2 ⊂ supercompilation.** KA2 (docs/05 §9, docs/11 §D) = detect one
  whistled affine pair → synthesise guarded `Cᵏ` → deopt → differential-cert.
  That is *exactly* one whistle+generalise+fold cycle of a supercompiler
  restricted to the affine/structural recurrence class, with the fold realised
  as a guarded speculative star rather than a re-derived residual function.
  KA2 is supercompilation's fold step, made a verified speculative jet
  (PyPy/LuaJIT/HVM discipline, docs/05 §9). It is *narrower* than full
  positive supercompilation (single recurrence, affine slots only) and much
  narrower than distillation (no nested-recurrence folding).
- **Distillation ⊃ positive supercompilation ⊃ KA2.** Distillation is the
  strongest: it folds the recurrence-of-recurrences and is the one with a
  *superlinear* theorem. It is what we ultimately want for a two-level
  protocol-over-arithmetic machine. But it is also the least bounded, has the
  hardest termination story (its own whistle on the driven graph), and is not
  spec'd here.

**Honest ordering:** build the KA2 special case first (spec'd, substrate-built,
falsifiable on benchmark-zero), measure whether galaxy's core is single- or
multi-level recurrent, and *only then* decide if the distillation
generalisation (nested fold) is required to reach the frame. Do not build a
distiller speculatively before KA2 demonstrates the inner kernel works and
before the trace evidence shows nesting is the actual blocker.

---

## 3. Faithfulness — the residual must be result-equivalent to `iex`

The residual program (the synthesised `Cᵏ` star, or a distilled residual
function) is the only thing that can be unsound. The built faithfulness stack
covers it at four layers, none new:

1. **The generalisation is sound by a proven predicate.**
   `is_sound_generalization(g, instances)` (`accel_detect.rs:190`) decides
   `∀x∈instances. ∃θ. canonical(g)·θ ≡ canonical(x)` — one-directional
   α-subsumption (`matches`, `accel_detect.rs:135`), **strictly stronger than
   the embedding whistle** (every match is an embedding, not conversely —
   the correct soundness asymmetry, the substantive fix docs/07 §A0 / docs/11
   §G record). The whistle may over-fire (it is only a wqo alarm); the
   *gate* that lets a residual be emitted is subsumption, which cannot. A
   degenerate bare-variable `g` is set-theoretically sound but flagged by
   `is_trivial_generalization` (`accel_detect.rs:203`) and, more importantly,
   the disjoint-structure case *never whistles* so no bogus `g` is even
   produced (`accel_detect.rs:404-438` pins this).
2. **The guard makes the speculative star total.** The accelerated `Cᵏ` star
   fires only when the live config matches the recurrence invariant
   (`is_sound_generalization` is the exact guard); otherwise **deopt** to
   ordinary reduction — no speedup, no unsoundness (docs/05 §9 soundness
   contract; docs/11 §D.2 step 4). Soundness is local + guarded, never a
   global decidability claim.
3. **Per-instance differential certification (N-KA-sound).** The accelerated
   ɟ-result must `psi_compatible` the **unrolled reference `iex`/
   `eval_forced`** (`evaluate.rs` live `OracleMode`/`OracleStatus`,
   `evaluate.rs:220-266`; the Goodhart-guarded check `faithfulness.rs:115`
   `psi_compatible` = `conceal_and_filter` → `antiunify::canonical` →
   **multiset** equality, decision-only, no witness retained, Stage-0
   forensic-verified docs/07 §J2). Divergence ⇒ discard the jet, never keep
   (Goodhart-forbidden, docs/05 §9 N-KA-sound). Reference `iex` is the
   untouched spec oracle; the residual is a fast tier exactly like
   `iex_fast`/`iex_tabled`, never reachable from the reference path
   (docs/11 §D.3).
4. **Two-tier + symbolic (N-KA-sound, the stronger tier).** Z3 discharges
   `Cᵏ ≡ k`-unroll by schematic induction on `k` over the exact LIA/affine
   fragment — *symbolic, stronger than the per-instance oracle*, making the
   accelerated star **a derived lemma, not an axiom** (docs/05 §9; docs/07
   §C). Z3 stays oracle/validator **outside** the trusted core:
   yes ⇒ accept jet; unknown/timeout ⇒ fall back to reference; ref engine =
   truth (docs/07 §C, docs/11 §G).

The N-KA-sound deopt is therefore: guard-miss → ordinary reduction;
per-instance `psi_compatible` red → discard jet + reference result; Z3
unknown → fallback. At no point does a wrong residual produce a kept result.
This is the verified-speculative-runtime model (docs/07 §H), already proven
as an instrument.

---

## 4. KA2 vs full supercompilation vs distillation — which to build

| | Coverage | Soundness story | Termination of the *transformer* | Build cost | Spec status |
|---|---|---|---|---|---|
| **KA2** (the fold step, affine class) | single affine/structural recurrence | guard + per-instance diff + Z3 lemma | trivial (one whistled pair, no transformer fixpoint) | low (substrate Built; only synth + Z3 unbuilt) | **LOCKED spec docs/05 §9** |
| **Positive supercompilation** | single-level recurrences generally | same gate, residual = re-derived function | needs its own whistle to terminate driving (have it: `accel_detect`) | medium (residualiser + driving loop) | not spec'd |
| **Distillation** | nested recurrence-of-recurrences; *superlinear* | same gate over the driven graph | hardest — whistle on the driven graph, the §49.59-60 open problem bites | high | not spec'd |

**Recommendation: build KA2.** Rationale: it is the only one with a LOCKED
spec and a Built substrate (`accel_detect` + `antiunify::affine_recurrence` +
`evaluate` oracle + `psi_compatible`); it is the *necessary inner kernel* of
both supercompilation and distillation (you cannot distil without first being
able to fold one affine recurrence soundly); it is independently falsifiable
on `binarith.rs:410-411` benchmark-zero `mul(13,9)` (docs/05 §9 KA2 success
criterion) *before* any galaxy commitment; and its honest tradeoff is
explicit — KA2 covers exactly the affine/structural fragment, the
non-structured residue runs at B+C speed with no win and **no risk**
(docs/11 §E).

Then **measure** on the galaxy trace whether the core is single- or
multi-level recurrent. If single-level affine: KA2 is sufficient and *is* the
galaxy path. If the trace shows a *nested* recurrence KA2's single `Cᵏ`
cannot fold (the protocol-loop-over-arith two-level shape, §2.2), that is the
empirical trigger — and *only then* — to spec the distillation
generalisation (graph-level fold). Do not pre-build the distiller; let the
trace evidence decide, exactly as docs/05 §9 N-KA-cover mandates (no
retro-widening to manufacture hits).

**Z3's role (docs/07 §C, docs/05 §10.6):** three jobs, all outside the
trusted core — (1) **solve-for-k**: given `sᵢ=C[paramᵢ]`, `sₙ=C[paramₙ]`,
solve the LIA constraint for the symbolic iteration count / closed-form
accumulator; (2) **guard discharge**: prove the guard predicate is exactly the
recurrence invariant on the affine fragment; (3) **lemma validator**: discharge
`Cᵏ ≡ k`-unroll by schematic induction on k (the derived-lemma claim, feeds
deferred HOL4, docs/07 §G). Strictly: yes ⇒ accept; unknown/timeout ⇒
fallback to reference; never accept on unknown. `z3` crate is a parent-owned
`Cargo.toml` change *when KA2 starts* (docs/07 §C, docs/11 §F Stage D0).

---

## 5. Staged, falsifiable plan + ordering vs docs/11/12

The ordering is **constrained by docs/11 §F** (attribution: B/C/D each move a
different cost axis; ≥2 at once destroys the galaxy Φ=405 KS-PROF
attribution) and by the C negative (C is done; B and D are what remain).

- **Stage S0 — detect+generalise on a SMALL galaxy-shaped recurrent term
  (no behaviour change).** Build the per-AEx-layer trace tap:
  `sₙ = canonical(readback_ray(final_ray))` at each `eval_forced` loop turn
  (`galaxy.rs:904-914`). **Resolve docs/08 §E / §7 open question FIRST**: is
  `final_ray`'s return point exactly the `AEx_C` fixpoint, i.e. a faithful
  AEx-layer boundary? (`galaxy.rs:864-893` strongly suggests but does not
  prove it; if not, sample at true layer boundaries — small tap change, must
  be settled or the whistle is untrustworthy, docs/08 §7.) Then run
  `detect_recurrence` on a *small* galaxy-shaped recurrent term (binary
  `mul`/list-cons fold = benchmark-zero `mul(13,9)`, `binarith.rs:410`).
  **Falsifier:** the whistle does not fire, or `affine_recurrence` returns
  `None`, on a term that *is* an accumulating recurrence ⇒ the detector/
  generaliser does not see galaxy's shape ⇒ first-class negative, the whole
  D-track is mis-grounded. (This is also docs/08 Stage 1, the single
  load-bearing experiment for the idempotence-loss ⟺ whistle proposition —
  the *same* tap; do it once.)
- **Stage S1 — synthesise + guard + differential-cert the residual (KA2),
  on benchmark-zero only.** From `sᵢ=C[paramᵢ]`, `sₙ=C[paramₙ]` synthesise
  `Cᵏ` (Z3 solve-for-k); emit guarded star + deopt; differential-cert vs
  unrolled `iex`/`eval_forced` (`evaluate.rs`). **Falsifier (the
  pre-registered KA2 success criterion, docs/05 §9):** `mul(13,9)`
  terminates fast and correctly via acceleration; N-KA-sound (any divergence
  from unrolled reference ⇒ revert, not keep). This is `psi_compatible` vs
  unrolled `iex` exactly as the prompt requires, on a small term, before any
  galaxy commitment.
- **Stage S2 — galaxy trace evidence + go/no-go.** Run S0's tap on the real
  `data[0]` trace. Measure: single-level affine recurrence (KA2 sufficient)
  vs nested (distillation needed) vs no guard-passing recurrence at all
  (**N-KA-cover first-class negative — report, do not retro-widen**,
  docs/05 §9 / docs/11 §E).
- **Stage S3 — apply to galaxy `data[0]`, gated.** Only if S2 shows a
  guard-passing recurrence. `psi_compatible(iex, iex_accel)` green on all
  corpora (`faithfulness.rs:217` horn / `:244` binarith / `:259` bounded
  galaxy) + galaxy `data[0]` terminates within a sane budget (the
  categorical falsifier — the whole point). KS-PROF: step count drops
  (proving it is the D step-count lever, distinct from B's per-step lever).

**Ordering vs docs/11 §F / docs/12:** docs/11 §F says C → B → D by
reachability-ROI. The C negative *changes this*: C is done and did **not**
reach the frame, so reachability now rests on D (the only asymptotic lever
left), not B (bounded, §2.1). Honest revised ordering: **S0/S1 (KA2 kernel
on benchmark-zero, parallel-safe — touches neither the `find` lever nor the
unify kernel) → S2 (galaxy trace evidence) → B (Φ-spec, makes D's
residual/fallback steps cheap, still worth its bounded win) → S3 (D on
galaxy)**. B and D stay one-at-a-time with their own KS-PROF attribution
(docs/11 §F is load-bearing, not ceremony). docs/08's Stage 0/1 is the
*same trace tap* as S0 — unify the work, do not build two taps (docs/08 §3.3,
docs/07 §E).

---

## 6. Honest risks + verdict

**Risks:**

- **Generalisation over-fires (false whistle).** The Kruskal embedding is a
  wqo: it *must* eventually fire on any infinite trace, including
  non-accelerable ones (`accel_detect.rs:32-36`). Mitigation is structural and
  built: the whistle only *nominates*; the *gate* is `is_sound_generalization`
  (subsumption, strictly stronger) + the guard + the differential oracle. An
  over-fire costs a wasted synthesis + a guard that never matches + fallback —
  slow, never wrong.
- **Generalisation under-fires (misses galaxy's shape).** `affine_recurrence`
  is *conservative* (`antiunify.rs:380` "necessary-condition filter"): a
  decreasing-counter or non-affine recurrence does **not** whistle pairwise
  on a finite prefix (`accel_detect.rs:289-298` pins exactly this). If
  galaxy's core is recurrent but not affine/structural, KA2 finds nothing →
  N-KA-cover negative. This is the single biggest *coverage* unknown and is
  exactly what Stage S2 exists to settle. **Do not retro-widen the recurrence
  class to manufacture a hit** (docs/05 §9, docs/11 §E — pre-registered).
- **§49.59-60 hyperexec-termination is open in the thesis itself.** docs/08
  §6.1: a *non-terminating* hyperexecution must eventually whistle (wqo), but
  a whistle does **not** imply non-termination (necessary, not sufficient).
  The detector can *flag* a candidate §49.60 non-terminator but cannot
  *decide* §49.59. Consequence: KA2/distillation can **accelerate a certified
  recurrence** but can **never declare normal-form existence** — the residual
  is sound *when it fires under guard*, the transformer cannot prove the
  whole reduction terminates. For galaxy this is fine (we want a faster route
  to the same NF, not a termination proof); for a full distiller it is the
  hard wall (its own driving-graph whistle inherits this openness). Inherited
  openness, not a defect — but it caps the claim.
- **Non-confluence / subjective rays.** B's Φ-table is sound only on the
  *objective* δ/Push/combinator fragment; `drive_strict` is the sole
  §49.50 ray-minting site and is deliberately left un-specialised
  (docs/11 §G, `galaxy.rs:728`). Supercompiling *past* the static/dynamic
  boundary (folding across a forcing semaphore) would be unfaithful; the
  trace-monoid independence relation `I` (docs/08 §4.2) that would let an
  accelerator commute independent forcings is **[Proto]** with approximate
  side-conditions (docs/08 §6.3) — completeness-only risk (missed
  commutation = missed speedup, not wrong), backstopped by the differential
  oracle. The residual must not fold a dependent semaphore chain; the
  N-KA-sound oracle catches it if it does.
- **`final_ray` may not be a true AEx-layer boundary** (docs/08 §7, the one
  open question that doc could not resolve). If `iex_fast` does not return
  exactly at the `±P`-NF, the trace is sampled at the wrong points and the
  whistle is untrustworthy. Must be instrumented and settled in Stage S0
  before any synthesis is trusted.

**Verdict.** This is **the** galaxy-execution path *for the step-count axis*,
and it is the **only** structural lever the C-negative leaves standing for
that axis — it is not a marginal compounding lever, it is the asymptotic one.
But it is *conditional and not yet evidenced*: the mechanism (KA2 fold,
generalising to distillation if the core is nested) **provably** collapses an
affine/structural recurrent reduction from Θ(n) steps to Θ(1)/Θ(log n)
(§2.2), and that is precisely the class of asymptotic the C negative proved
is the only one capable of crossing galaxy's termination boundary. Whether
galaxy's real `data[0]` core *is* a guard-passing affine/structural (or
nested) recurrence is **unproven** and is the live empirical question — Stage
S2's job, with N-KA-cover pre-registered as an honest first-class negative if
it is not. B remains worth building (largest bounded per-step win, makes D's
residual/fallback cheap) but is *not* the galaxy path — bounded constant
factors cannot terminate a non-terminating-in-150 s reduction (docs/11 §A
Fact-2, the C-negative's logical twin).

**Does this make galaxy's `data[0]` actually execute? Conditional yes.** If —
and only if — galaxy's image-data core is a guard-passing affine/structural
recurrence (single-level ⇒ KA2 suffices; nested ⇒ distillation's graph-level
fold required), then the construction in §1, gated by §3's built
faithfulness stack, provably collapses its Θ(n) non-redundant reduction to a
Θ(1)/Θ(log n) residual and `data[0]` renders. The mechanism is sound and the
substrate is built; the recurrence's *existence in the real galaxy trace* is
the one unproven premise, and Stage S2 is designed to confirm or falsify it
without retro-widening.
