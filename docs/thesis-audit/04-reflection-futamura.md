# 04 — Reflection / Self-Formalisation vs. the Futamura/Σ(Φ) Work

READ-ONLY AUDIT. No code or other docs were modified. Cross-checks the
self-formalisation / proof-producing-reflection source material against this
repo's first-Futamura artifact (`Σ(Φ)`/`SpecPhi`/`iex_spec`), and assesses
2nd/3rd-projection feasibility *from the source framing's own terms*.

Sources read:
- `refs/extracted/SelfFormalization/doc.md` (Kumar, Arthan, Myreen, Owens —
  *Self-Formalisation of HOL*, J. Automated Reasoning 2016; 39pp).
- `refs/extracted/ProofProducingReflection/doc.md` (Kumar et al. — *Proof-
  producing reflection for HOL*, 16pp).
- `refs/extracted/transcendental_syntax/doc.md` (Abrusci & Pistone — Girard's
  transcendental-syntax program; the meta-theory frame for stellar
  resolution).
- Codebase: `crates/stella-core/src/spec_phi.rs`,
  `crates/stella-core/src/interactive.rs`
  (`spec_realise` :995, `iex_spec` :1234, `iex_fast_inner` :1259,
  `IexAccel.spec` :291, the differential gate `iex_spec_result_eq_iex`
  :1787).
- Docs: `docs/14` (Σ(Φ) design), `docs/16` (galaxy-execution decision),
  `docs/17` (Σ(Φ) impl plan), `docs/07` §§ on docs/14/17.

Terminology note. The brief calls the source corpus "Eng". The actual
documents are the **CakeML/HOL self-formalisation line** (Harrison →
Kumar/Myreen/Arthan/Owens) plus **Girard transcendental syntax** as the
stellar-resolution meta-theory. I audit those. Where the brief says "Eng's
own framing" I read it as "the framing those documents establish."

---

## 0. Executive verdict (the answer, then the argument)

The reflection / self-formalisation material does **not** formally ground a
partial-evaluation / Futamura reading of stellar resolution — it is a
*different axis of self-reference* (a logic modelling its own
**provability/soundness**, not a program specialising its own **evaluator**).
What it *does* legitimately supply is (i) the **refinement-stack discipline**
(spec ⊑ implementation, every layer gated by a proven invariant) that the
repo already instantiates as `iex` = oracle / `psi_compatible` = the proven
gate / `iex_spec` = the refined tier with deopt; and (ii) a sharp,
independently-stated reason the 2nd/3rd Futamura projections are *not* worth
building here. `SpecPhi::build` **is** a legitimate first-projection residual
("cogen-of-one" is the wrong phrase — see §3). A genuine self-applicable
partial evaluator is **technically encodable but of essentially expository
value only** for this engine.

---

## (a) Does the reflection material formally ground / constrain a Futamura
reading of stellar resolution?

**No formal grounding; a strong methodological constraint; one genuine
theoretical connection.**

1. **Not formal grounding — the two self-references are orthogonal.**
   The Futamura hierarchy is about a *specialiser* `mix` such that
   `mix(interp, src) = target`, `mix(mix, interp) = compiler`,
   `mix(mix, mix) = cogen`. It is a statement about *staging an evaluator*.
   The self-formalisation papers are about a logic L expressing the
   *semantics and soundness of L's own inference system* inside L
   (`SelfFormalization` §1, §5; the soundness theorem
   "every provable sequent is true"). `ProofProducingReflection` adds the
   reflection principle "if `⌜φ⌝` is provable then `φ`" via an inner model
   under a large-cardinal assumption. None of this quantifies over an
   *interpreter being specialised to a fixed program*; there is no `mix`,
   no residual program, no Futamura projection in the source material.
   The repo's own docs/14 §1.3 derive the Futamura reading from the
   **Ager–Danvy / GRIN / supercompilation** line, *not* from these papers —
   correctly. The reflection corpus neither licenses nor blocks the Σ(Φ)
   construction; it is simply about a different kind of self-application.

2. **The genuine connection is the refinement stack, and the repo already
   honours it.** `SelfFormalization` Fig. 1 is a 3-layer refinement:
   set-theoretic semantics ⊨ ⊐ relational inference system ⊢ ⊐ monadic
   kernel ⊐ synthesised CakeML, each layer linked by a *proved* invariant
   ("if run in a good state on good arguments, terminates in a good state
   with good results"), and the synthesis step is **proof-producing** (a
   certificate theorem per kernel function, §6.2). This is *exactly* the
   discipline `Σ(Φ)` is built under: reference `iex` is the trusted spec,
   `faithfulness::psi_compatible` is the proven invariant, `iex_spec` is the
   refined tier, and the gate is two-tier with **deopt** to `iex` on any red
   (`docs/17` §3; `interactive.rs:1787` `iex_spec_result_eq_iex`). The
   constraint the source material *does* impose, read honestly: a
   specialised tier is only admissible if it is **refinement-gated against
   an untouched oracle by a proven invariant**, and ideally the equivalence
   is *definitional per-rule*, not merely empirically tested. docs/14 §3
   already makes the per-rule definitional argument (δ-`Transition` *is* the
   literal denotation of the δ-star; MGU is trivially `{π↦σ}`; `body•`
   ground). This is the source material's actual normative content for the
   Futamura work, and it is satisfied — though see Gap 1: the repo's
   equivalence evidence is *test-corpus α-equivalence + `psi_compatible`*,
   which is **weaker** than the source standard of a machine-checked
   per-rule refinement theorem.

3. **The Girard transcendental-syntax connection is real and the deeper
   one.** `transcendental_syntax/doc.md` lines 35–50: à la Curry, proofs
   are *operators / graphs* under geometry-of-interaction; correctness is an
   **internal** completeness ("a net which refutes all refutation can be
   sequentialised" — internal, not via outer counter-models). Stellar
   resolution *is* the à-la-Curry substrate: stars/rays are the untyped
   operators, Ψ is the test battery, `psi_compatible` is the internal
   acceptance. This is the meta-theory that *does* license the move "the
   interpreter is the spec; a compiled tier is a partial-evaluation residual
   gated by an internal test" (docs/07 §H GraalVM/Truffle framing). It is
   philosophically aligned with Futamura-as-internal-staging, but it is a
   *frame*, not a theorem that grounds the projections. Honest reading: the
   transcendental-syntax document supplies the *legitimacy of internal
   testing as correctness* (so `psi_compatible`-gating is not a hack but the
   intended epistemology); it does not supply a partial-evaluation theorem.

**Bottom line for (a):** no formal grounding of a Futamura reading; a real
methodological constraint (refinement-gated, ideally definitional
equivalence) that the repo meets at the engineering level but not at the
machine-checked-theorem level the source sets as the gold standard; and a
genuine but frame-level (not theorem-level) alignment via transcendental
syntax that legitimises internal-test-gated specialisation.

---

## (b) Is `SpecPhi::build` legitimately a 1st-projection residual /
"cogen-of-one"?

**Yes, it is a legitimate first-projection residual. "Cogen-of-one" is the
wrong term and should not be used.**

1. **It is a genuine first Futamura projection, mechanised.** `mix(iex, Φ)`
   ≈ `SpecPhi::build(Φ)`: `SpecPhi::build` (`spec_phi.rs:98`) walks the
   fixed Φ once and emits a closed, head-keyed `Transition` table —
   `Delta(body)`, `Unwind`, `Splice{params,body}` — the residual of
   specialising the generic resolution step (`produce_stars_fast` +
   `mat_phi_c_accel` + α-rename + `fuse_fast`) to each statically-known Φ
   star. The driver `iex_spec` (`interactive.rs:1234`) consumes that
   residual per step (`spec_realise` :995, dispatched at the chosen redex
   :1094–1105). Construction is a pure function of Φ, built once, the deep
   completion of the already-[Built] `build_accel`/`RayIndex` (docs/14
   §1.3). This squarely matches the first projection: *specialise the
   interpreter to a fixed source program → a target program*. The
   classification is **structural, not name-heuristic** (`spec_phi.rs:11–22`
   doc; `classify` :111), which is what makes it a partial *evaluation*
   rather than a re-implementation.

2. **Why "cogen-of-one" is the wrong term — and the precision matters.**
   "cogen" is the *third* projection (`mix(mix, mix)`): a *compiler
   generator* — a program that, given an interpreter, emits a compiler. A
   "cogen specialised to one interpreter" would be a *compiler* (the 2nd
   projection), not a residual program. `SpecPhi::build` is neither: it is
   the **output of the 1st projection for one source program Φ** — i.e. a
   *compiled program*, the target. It is also *not itself* `mix`: it does
   not take an interpreter as input; it hard-codes the structural shape of
   the resolution step inside `classify`/`spec_realise`. So the precise
   status is: `SpecPhi::build` = a **hand-written, Φ-general first-projection
   residualiser** (a `mix` partially-applied-and-fused for *this one
   interpreter*, `iex`'s step relation), whose *output* `SpecPhi` is the
   first-projection residual (the compiled Φ). docs/14 §1.3's phrase
   "`Σ(Φ) = mix(step_iex, Φ)`" is accurate; docs/14 §1.3's gloss
   "defunctionalisation + closure conversion of the abstract machine
   (Ager–Danvy line)" is the correct technical identification (the galaxy
   reducer is a KAM; the δ-fragment is the defunctionalised continuation,
   the table is its `apply`). I find no over-claim in docs/14/17 on this
   point — they consistently call it the **1st projection** and explicitly
   reject 2nd/3rd (docs/14 §2, docs/17 §0). The only correction is
   terminological hygiene: do not let "cogen-of-one" enter the vocabulary;
   `SpecPhi::build` is *the residualiser for one interpreter*, `SpecPhi` is
   *the residual*, and there is exactly one source program.

3. **One honest caveat on the residual claim.** A *pure* first-projection
   residual would not consult Φ at run time at all. `iex_spec` still drives
   the generic redex *selection* (`mat_phi_c_accel` over the live Ψ) and
   only swaps the *realisation* step to the closed `Transition`
   (`interactive.rs:1090–1118`: spec fires at `iex_fast`'s own chosen
   `(ik,jk)`). So `SpecPhi` is a residual of the *production/fusion* phase,
   not of *selection*. This is a deliberate, sound scoping (it is what keeps
   step-count identical to `iex_fast` — the per-step-lever proof, gate (2)
   at :1809/:1830/:1865) — but it means the residual is *partial*: the
   compiled tier still pays generic selection cost. That is correctly
   disclosed in docs/14 §2's "per-step lever, not step-count lever" verdict,
   but the *residual-completeness* nuance (selection is not residualised) is
   worth stating explicitly — see Gap 2.

**Bottom line for (b):** legitimate 1st-projection residual, correctly
framed in docs/14/17 as the 1st projection only; "cogen-of-one" is a
category error and should be dropped; the residual is honestly *partial*
(production-side, not selection-side) and that should be said in those words.

---

## (c) Honest feasibility + value of a self-applicable PE (2nd) and cogen
(3rd) for this engine

**Feasible to encode; payoff is essentially expository, not engine-merit.
docs/14 §2 and docs/17 §0 already reach this verdict; the source material
independently *reinforces* it.**

1. **What a real 2nd projection would require here.** `mix(mix, iex)` needs
   `mix` itself to be a **first-class program in a language `mix` can take
   as data and specialise** — i.e. the resolution step `iex` would have to
   be reified as an *object-level program* (a constellation, or an explicit
   interpreter term) and `mix` would have to be a self-applicable
   specialiser written in that same object language, with a binding-time
   analysis over `iex`'s own structure. Concretely: (i) reify `iex_fast`'s
   step relation as data (today it is Rust control flow inside
   `iex_fast_inner` :1259 — `classify`/`spec_realise` *hard-code* its
   shape); (ii) write a general online/offline partial evaluator over that
   reified interpreter with a BTA separating the static Φ from the dynamic
   Ψ; (iii) self-apply it. Stellar resolution is actually a *good* substrate
   for (i)–(ii) in principle — it is a uniform rewrite system, and docs/13
   (supercompilation) is the information-propagating generalisation of
   exactly this. But the engine has **exactly one source program** (the
   fixed galaxy Φ, built once per run — docs/14 §2, docs/17 §0). A reusable
   *compiler* (2nd projection) buys nothing the build-once `SpecPhi::build`
   table does not already deliver, and it re-introduces a self-application
   machinery that `psi_compatible` + the refinement gate would have to
   re-cover from scratch (new trusted surface — exactly what docs/16 §6's
   invariant forbids without a fresh staged falsifier).

2. **3rd projection (cogen) is irrelevant here.** A compiler-compiler pays
   off only with a *family of interpreters*. There is one interpreter
   (`iex`) and one source (Φ). docs/14 §2 says this plainly ("Irrelevant
   here (no family of interpreters). Skip.") and I concur with no
   reservation.

3. **The source material independently reinforces "expository only".** The
   self-formalisation papers' entire payoff is *epistemic confidence in a
   trusted kernel*, achieved by **refinement to a proven spec**, not by
   self-application for performance (`SelfFormalization` §1: "effort spent
   verifying the theorem prover multiplies outwards"; §8: self-verification
   "skating along the barriers" — explicitly bounded by Gödel II, and the
   value is *confidence*, not speed). Translated to the engine: the value of
   making `mix` self-applicable here would likewise be **epistemic /
   expository** — "the engine can stage *itself*" is a nice meta-circular
   story (and aligns with transcendental syntax's internal-completeness
   aesthetic) — but the source line is itself a cautionary example that
   self-application's payoff is *understanding and trust*, not throughput,
   and that it must be paid for with new assumptions (there: a large
   cardinal; here: a new trusted self-application path). `ProofProducing
   Reflection` §1's "asymmetric reflection principle" point is the sharp
   analogy: each layer of self-reference costs a strictly stronger
   assumption and **cannot be reused at the next layer for free**. A 2nd
   projection here is the engine analogue of that asymmetry — it would
   demand its own refinement gate that the 1st-projection gate does not
   discharge. Honest value assessment: **the payoff is real but purely
   expository/meta-theoretic; the engine-merit payoff is zero over
   `SpecPhi::build`**, and the source material is itself evidence that
   chasing it for anything but understanding is mis-aimed.

4. **Where a *bounded* self-applicable experiment would have genuine value.**
   Not for speed, but as a **faithfulness amplifier**: if `iex`'s step
   relation were reified as a constellation `I_Φ` and `SpecPhi`'s residual
   re-derived by *running stellar resolution on `I_Φ` itself* (resolution
   specialising resolution), then "the residual is correct" becomes "the
   residual is the normal form of an internal reduction gated by the same
   `psi_compatible`" — i.e. the definitional-equivalence argument of
   docs/14 §3 would be *mechanised inside the engine* rather than argued in
   prose. That is the only 2nd-projection-flavoured artifact with
   non-expository value, and its value is **stronger faithfulness evidence**
   (closing Gap 1), not performance. It is the engine's honest analogue of
   the source line's proof-producing synthesis.

**Bottom line for (c):** 2nd projection encodable but engine-merit-pointless
(one program, one interpreter; re-introduces trusted surface); 3rd
irrelevant (no interpreter family); the source material independently frames
self-application's payoff as epistemic, not performant, and as
strictly-assumption-costing — corroborating docs/14 §2 / docs/17 §0. The one
worthwhile self-application-shaped artifact is a *faithfulness*
mechanisation, not a speed lever.

---

## (d) Encodable experiments + infra

All read-only-designed; each its own staged falsifier per docs/16 §6
discipline. None of these is required for the Σ(Φ) ship path — they are
*evidence/understanding* artifacts.

- **E1 (closes Gap 1, highest value): per-rule definitional-equivalence
  certificate, not just corpus α-equivalence.** Today the gate is
  `psi_compatible` + test-corpus `stars_alpha_equiv` + step-count identity
  (`interactive.rs:1787`). The source standard (`SelfFormalization` §6.2
  proof-producing certificate per kernel function) is a *per-construct*
  refinement theorem. Encodable analogue: for each `Transition` variant,
  emit a machine-checkable lemma object asserting `spec_realise(...)` ≡ the
  generic `alpha_rename + fuse_fast + theta.apply` result, *symbolically*
  over a fresh-var skeleton (not per corpus). Infra: a property test /
  proptest-style generator over Φ-star shapes already exists in spirit in
  the `iex_spec_result_eq_iex` corpora; promote it to a shape-quantified
  symbolic check. Falsifier: a deliberately wrong `Splice` template the
  symbolic check must reject (the corpus falsifier at :1874 already does
  this for `Delta`; generalise to symbolic).

- **E2 (closes Gap 2): residual-completeness instrumentation.** Add a
  read-only counter (behind the existing `#[cfg(test)] SPEC_HITS` :965
  pattern) splitting per-step cost into *selection* (`mat_phi_c_accel`,
  not residualised) vs *realisation* (`spec_realise`, residualised), on the
  galaxy Φ=405 KS-PROF run. Quantifies exactly how *partial* the residual
  is and bounds the achievable Σ(Φ) win — directly informs whether a
  selection-side residual (a per-Φ specialised `RayIndex` dispatch) is the
  next per-step lever. Falsifier: if selection cost is negligible, Gap 2 is
  cosmetic; if dominant, Σ(Φ)'s headline per-step claim is over-stated.

- **E3 (the only 2nd-projection-flavoured artifact, expository+faithfulness):
  resolution-specialises-resolution.** Reify `iex`'s step relation as a
  constellation `I` (a metacircular stellar interpreter — the engine
  already has the combinator/KAM encoding machinery in `combinator.rs` /
  `galaxy.rs`). Run `iex(I, Φ-as-data)` and check the produced residual is
  `psi_compatible` with `SpecPhi::build(Φ)`. This is `mix` *as a
  constellation*, self-applied through the engine's own reducer. Value:
  **mechanises docs/14 §3's definitional-equivalence argument inside the
  engine** (faithfulness, not speed). Honest scoping: do NOT report any
  wall-clock number from E3 — it will be slower; its only deliverable is
  the `psi_compatible` green/red and the meta-circular closure.
  Pre-registered expected result: green, slower, expository.

- **E4 (cheap, supports (a)): transcendental-syntax internal-test framing
  note.** A short cross-ref folding `transcendental_syntax` lines 35–50
  (internal completeness = "refutes all refutation") into docs/07 §H's
  GraalVM framing, making explicit that `psi_compatible`-gating *is* the
  intended internal-test epistemology (so the gate is not a pragmatic hack
  but the meta-theory's notion of correctness). No code. Pure theory
  closure, analogous to docs/16 §5's χ-closure fold.

---

## The three highest-value gaps (returned verbatim in the summary)

**Gap 1 — Equivalence evidence is below the source's gold standard.** The
Σ(Φ) faithfulness story is *test-corpus α-equivalence + `psi_compatible` +
step-count identity* (`interactive.rs:1787`). The self-formalisation line's
standard (and the one its refinement discipline implies the repo should aim
for) is a **per-construct, machine-checkable refinement certificate**
(`SelfFormalization` §6.2). docs/14 §3 argues definitional per-rule
equivalence *in prose*; it is not mechanised. This is the single biggest
delta between "engineering-faithful" and "the source material's bar". Close
via E1 (symbolic, shape-quantified per-`Transition` certificate).

**Gap 2 — The first-projection residual is silently partial (production-side
only); selection is not residualised, and this is not stated in those
words.** `iex_spec` still pays generic redex *selection* cost
(`mat_phi_c_accel` over live Ψ, :1084); only *realisation* is residualised
(`spec_realise`, :1094). docs/14 §2's "per-step lever" verdict is correct
but the *residual-completeness* limit (and hence the ceiling on the Σ(Φ)
win) is not quantified anywhere. Close via E2.

**Gap 3 — "cogen-of-one" / self-applicability is a latent framing trap.**
The brief's own phrasing ("cogen-of-one") is a category error
(cogen = 3rd projection; `SpecPhi::build` is a 1st-projection residualiser
for one interpreter). docs/14/17 are currently *clean* on this — but there
is no written statement closing the door, and the source material's
asymmetric-reflection lesson (`ProofProducingReflection` §1: each
self-reference layer costs a strictly stronger assumption, non-reusable) is
exactly the argument that should be recorded so a future reader does not
chase 2nd/3rd projections for illusory engine merit. Close via E4 + a
one-paragraph "no 2nd/3rd projection, and why (one program, one interpreter,
asymmetric-assumption cost)" note in docs/14 §2 (flagged, not edited here).
