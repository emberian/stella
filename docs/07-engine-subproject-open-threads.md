# Engine subproject — OPEN THREADS LEDGER (pre-compaction snapshot 2026-05-17)

Durable state of the stella-combinator / KS / KG / KA engine arc, so nothing
is lost across compaction. Canonical subproject spec = `docs/05` (§1–7 LOCKED;
§8 KS architecture; §9 Axis-2-reborn). This file = the live thread list.

## Commits this session (engine/galaxy/KA arc; interleaved w/ user's parallel commits)
ca5731d K1 combinator core · 880cb84 K2a arith · caf3531 K2b strict-prim
trichotomy · 33dfcee KG1a binary arith + KS Tier-0 + measurement infra ·
2615d42 KS LeverA+discrimination (binarith x8) · c575bfa KS B1 matchable_fast
(binarith x12 / combinator x4) · f07ec49 KS B2-store Arc+RwLock · 1a3c259
de Bruijn Var=Named|Idx · 9fc8987 docs/05 §9 spec · 82b4b63 KA0 substrate
(canonical/lgg/affine_recurrence) · 539d6eb KG2+KT harvest (galaxy loader +
combinator fuzz) · ce8ee55 KG3a probe · 4e66adf KG3b lazy prim layer (galaxy
→371-step NF) · 3901671 KG3c isnil measured · cf28558 KA1 tabling (retained
infra, NOT default) · d549387 KA0 rigid-AU+Kruskal-embedding · 73091f1 KG1b
signed binary arith · 614476c KG3c slice2 arith-forcing + reprioritization.

Measured KS speedups (release, faithful, vs original reference): binarith/Horn
~12×, combinator ~3–4×. All differential-gated (reference `iex` = oracle;
`iex_eq_iex_fast` byte-identical, `iex_tabled_result_eq_iex` result-equiv,
20k `matchable_fast` fuzz, antiunify 6/6).

## A. IN FLIGHT (must harvest on completion)
- **IexAccel-caching subagent** `a253857384cc7bd43`, worktree, on
  `interactive.rs`. Adds `iex_fast_with_accel`/`iex_tabled_with_accel` +
  pub accel build so the valence loop builds the head-index ONCE per fixed Φ
  (kills per-call `IexAccel::build` for millions-of-small-execs). On
  completion: cp file, forensic-verify (`iex_eq_iex_fast`,
  `iex_tabled_result_eq_iex`, `mat_accel_eq_mat_ref`, combinator/arith green +
  the micro-bench numbers), clean worktree, commit. Disjoint from galaxy.rs.

## B. GALAXY SPINE — reprioritized, the next concrete deliverable
Measured arc: blocked@5 → KG3b lazy prims → **371-step true NF, NO strict
stall** (isnil AND arith "blockers" were BOTH census artifacts = unapplied
data, not redexes; `find_blocked_*` precise-redex detection ≠ head-census —
recurring lesson). Forcing driver (`galaxy::eval_forced`, disclosed §60,
isnil + sbinarith arith) BUILT, faithful, additive, 7/7 — but galaxy doesn't
need it to reduce (0 forcings/0 arith_ops, fully_reduced=true). `div` NOT
auto-forced (KG1b: stellar div past KS frontier even at −1/2).
**NEXT = faithful FULL-RESULT DECODER (= rendering path = validation oracle):**
decode the whole process ray (NOT `focus`/`st_inner` — output lives on the
continuation π), decode ICFP cons/nil list-of-(x,y), check vs the known
`(nil,(0,0))` reference vector, rasterize. **Honest open risk:**
fully_reduced=true means "no blocked isnil/arith redex", NOT "correct
output"; the 371-step NF may be correct OR a degenerate non-redex state
(wrong entry/protocol/missing-rule manifesting as wrong-NF) — the decoder
is what reveals which. This one deliverable = correctness oracle + maturity
demo + answers "does galaxy execute."

## C. KA TRACK
- KA0 substrate done + rigid-AU/Kruskal-embedding + one-unital-NULLARY caution
  (antiunify.rs). KA1 = retained infra, NOT a default: net-negative on
  non-variant single runs (per-star canonical-key tax); **its true home is
  the valence evolutionary loop** (variant-dense) — needs (a) cheap
  incremental key, (b) cross-run/persistent table. Serialized after the
  IexAccel agent (both touch interactive.rs; one-writer rule).
- KA2 NOT started. Z3-reshaped: Z3 = solve-for-k + guard discharge on exact
  LIA fragment + **lemma validator** (Cᵏ ≡ k-unroll via induction/SMT —
  symbolic, stronger than per-instance oracle; feeds deferred HOL). z3 crate
  = Cargo.toml = PARENT when KA2 starts. Z3 stays oracle/validator OUTSIDE
  trusted core (yes⇒accept jet; unknown/timeout⇒fallback; ref engine=truth).
  KA2 speculation during a valence search must be **certified-only** (see D).

## D. PARKED ENGINE ITEMS (several re-homed as VALENCE-CRITICAL)
- per-call IexAccel caching = the in-flight agent (A).
- KA1 cheap-key + cross-run table — valence-critical; after A.
- rayon over constellation populations — valence-critical (was "capstone").
- **Differential oracle wired LIVE into any search-driven jit path** —
  experiment-validity-critical: an evolutionary search maximizing viability
  WILL find & amplify any unfaithful fast path (Goodhart at substrate level)
  → evolve fake-viable agents. Faithfulness IS part of experiment validity.
- lock-free `get` / append-only stable store (B3) — deepest residual constant
  factor (per-node RwLock), pure-perf, pervasive.
- triangular/union-find substitution in `fuse` — biggest per-fuse factor.
- deeper term indexing (discrimination/fingerprint beyond fp_unifiable) —
  matters at galaxy Φ scale (~400 δ-stars).
- a clean fast `evaluate(constellation)→{NF, closure/viability readout}` API
  the valence search drives millions of times (subjective/reafference/valence
  modules are the fitness side).

## E. FORCING → §49.50 POLARITY INTERNALISATION (nearest the valence thesis)
The elegant deep redesign: forcing = negative/test/demand pole, value =
positive/supply pole, strict dynamics = their orthogonal fusion = Krivine
pole / §49.50 subjective-ray semaphore / interaction-net annihilation; one
subsystem unifies with the KA recurrence detector. Parked behind the
pragmatic disclosed driver (built). **Right theory here = trace /
partial-commutation monoids**, NOT words. This track is the one CLOSEST to
the make-or-break valence/conscious-machine bet (§49.50 = where idempotence
is lost = where the "charge" is claimed to live).

## F. THEORY-MODULO CONCLUSION
NOT finite words/strings (over-fit the prompt seed; SKIP Z3-Noodler/OSTRICH/
SeCo string tooling). Engine should be modulo: α (have), associativity/unit
of `a`/`dot` spine-stack constructors (rigid AU, **ONE-unital only** —
AU-modulo-≥2-units is NULLARY; caution baked into antiunify.rs), linear
arithmetic in the KA2 summarizer (Z3 does Presburger/affine — do NOT
hand-roll), trace-monoid later for the §49.50 frontier (E).

## G. HOL4 / VERIFIED SUBSTRATE
Deferred to next-quarter (user's call). Deferral VINDICATED: synthesize
lemmas later from the observational-equivalence corpus the differential
oracle is accumulating (CCLemma / directed-lemma-synthesis); Z3-validated
KA2 lemmas feed it. Defer-and-accumulate is the literature-endorsed strategy.

## H. STRATEGIC FRAME (load-bearing for next session)
- Engine is BOTH (1) a first-class artifact — world's only/foremost stellar
  resolution engine; GraalVM-caliber ambition; **Eng is in a Signal group
  chat with the user** ⇒ external/publishable; faithfulness-as-feature is
  what makes it credible to Eng — AND (2) valence-thesis-CRITICAL: the
  valence experiment = LOTS of execution + search + EVOLUTION over symbolic
  forms ⇒ engine speed/throughput/faithfulness is prerequisite. Earlier
  "side-quest vs critical path" framing is RESOLVED: it is both.
- Two co-equal driving workloads: **galaxy** (maturity/credibility; deep
  single run) + **valence-evo** (thesis; millions of small executions under
  mutation; faithfulness-under-adversarial-search). They stress the engine
  differently and BOTH drive the roadmap.
- GraalVM/Truffle map: ref `iex`="interpreter is spec"/oracle; `iex_fast`=
  optimizing tier; KA1/KA2=self-opt/OSR; verified-jet+differential+deopt =
  Graal speculation/deopt BUT we additionally *validate* ⇒ a **verified
  speculative runtime** (the novel, Eng-relevant contribution; operationalizes
  Eng §49.59-60 hyperexec-termination & §87.2 subjective-rays open problems).
- Maturity gaps = first-class roadmap (not afterthoughts): runs flagship
  end-to-end (galaxy), perf methodology + bench corpus, designed tiering +
  deopt boundaries, observability/tooling, the interactive+rendered galaxy
  demo.

## I. DISCIPLINE REGIME (agreed, lighter)
Beyond-Eng = prototype-IS-spec (legitimate; mark which side of Eng's
pavement). Rigor = differential oracle + measurement + honest negatives
(mostly mechanized — not ceremony). DROP pre-registered-null larp for routine
engine work. KEEP heavy pre-registration ONLY for the valence/agency thesis
claims (there it's existential, the project's whole credibility — not larp).
Z3 allowed where it helps. Process learnings: NEVER put `git stash` cycles in
killable bg jobs (caused a scare); never two write-agents same file; ≤2
concurrent write-agents (RAM); worktree-harvest + parent forensic-verify
(never trust self-report); "blockers" keep turning out to be census artifacts
— always confirm via precise-redex detection, not head-census.

## J. OUTSTANDING DOC TODO
`docs/05` needs a strengthen-only §10/§11 addendum folding in: the
valence-workload reprioritization (H), the two-workloads frame, the lighter
regime (I), the Z3 affordance (C), the galaxy reprioritization (B: decoder=
rendering=oracle), the §49.50-polarity track (E), the theory-modulo
conclusion (F). (Was deferred "to next checkpoint" — still owed.)

## NEXT ACTIONS (priority order)
1. Harvest IexAccel agent (A) on completion — forensic-verify, commit.
2. Galaxy full-result decoder = rendering = validation oracle (B) — the
   de-risked spine deliverable; resolves the honest open risk.
3. Fold this into `docs/05` §10 (J).
4. Then: KA1 cheap-key+cross-run table (D, valence) → rayon (D) → KA2
   (C, Z3) with certified-only-during-search; §49.50-polarity (E) as the
   thesis-nearest deep track.
