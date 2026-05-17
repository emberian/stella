# 12 — Optimal / Interaction-Net Reduction: does it execute galaxy's `data[0]`?

Status: RESEARCH synthesis. No code changed. Read-only. Decides whether
**interaction-combinator / HVM-style reduction** is the path to executing
the galaxy image payload, a compounding lever beside docs/11 B/C/D, or a
dead end for the *measured* blocker.

Claim tags: **[Built]** = in tree & tested (file:line) · **[Lit]** =
paper / external system · **[Proto]** = this doc's proposed construction.

The faithfulness instrument is fixed and proven and is **not** modified by
anything here: every fast tier is gated by
`faithfulness::psi_compatible` (`faithfulness.rs:115-119` [Built]) against
reference `iex` (`interactive.rs:861` [Built]) / the
`eval_forced`/`force_value` unrolling (`galaxy.rs:890,685` [Built]) as the
differential oracle. No new trusted code enters the faithfulness path.

---

## A. The measured blocker, restated precisely

`galaxy_data_probe.rs` [Built] forces the ICFP protocol spine cheaply
(`force1`/`step_cons`, `galaxy_data_probe.rs:61-89`): the
`(flag,newState,data)` triple and its tail fields each force in tens to a
few thousand steps with `fully_reduced=true`. Forcing one image element
`data[0]` (`galaxy_data_probe.rs:91-96`) does **not** terminate at
fuel=2M / maxf=100k — no panic, no dead-end, just past engine speed
(docs/11 §A Fact 2, docs/07 §B KG6c).

docs/11 Lever C — engine-level hash-consed NF memoisation — is **built**
and live (`galaxy.rs:846-862` `FORCE_MEMO`, `:694-703` lookup gated on
`crate::term::is_ground`, `:732-734` write). Its module doc (`galaxy.rs:850`)
asserts memoisation collapses "exponential re-forcing → linear" on shared
structure. The frame's commission text and docs/11 §F both record the
load-bearing empirical fact: **with Lever C committed, `data[0]` is still a
genuinely long *non-redundant* reduction.** Memoisation shares *subterms*
(`TermId`-keyed NF cache); it does nothing when the long reduction is *not*
re-forcing the same closed subterm but doing fresh, distinct rewrite work
of large length. That is the residual the levers in docs/11 do not cross by
construction:

- B (Φ-specialisation) is a **per-step constant** (docs/11 §B.3, §E
  "honest ceiling": B alone hits the §A Fact-1 wall).
- C (memoisation) is bounded by *sharing*; the measured statement is that
  `data[0]`'s residual length is not sharing-bound — C already applied.
- D (KA2 acceleration) collapses an O(n) **affine** recurrence to a closed
  form, *iff* a guard-passing affine recurrence exists in the trace
  (docs/11 §G N-KA-cover risk; docs/05 §9 benchmark-zero = `mul(13,9)`).

The open question this doc answers: is there a reduction *discipline* —
not a cache, not a constant factor, not a recurrence summariser — that
asymptotically collapses a long, non-redundant, non-affine reduction by
sharing **reduction work itself**? That discipline is Lévy-optimal /
interaction-net reduction.

---

## B. Why optimal reduction is categorically different from Lever C

The crucial distinction, stated once and exactly:

- **Memoisation (Lever C) shares *results* of *closed subterms*.** Key =
  hash-consed `TermId` of a `is_ground` term; hit returns the already-
  computed NF (`galaxy.rs:698-703`). It can only fire when the *same
  closed term* is forced twice. It shares **structure**.
- **Optimal (Lévy) reduction shares *redexes* — units of reduction
  *work* — including work on terms that are not yet, and may never
  individually be, closed or even fully formed.** Lévy's theorem [Lit]:
  there is a reduction strategy in which no redex "family" (a redex and
  all its duplicate copies created by substitution/copying) is ever
  contracted more than once. Lamping's algorithm / the Bologna Optimal
  Higher-order Machine (BOHM) / Lambdascope / Asperti–Guerrini's *abstract
  algorithm* [Lit] realise this with a *graph* in which a shared
  sub-computation is reduced **once** and the result is threaded to all
  its sharers, even when those sharers demanded it in different contexts.

The galaxy relevance: `data[0]`'s long reduction is, structurally, the
ICFP image interpreter (a fixed combinator program from `galaxy.txt`)
applied to a deep, *non-repeating* unfold. Lever C sees no repeated
*closed subterm* (that is precisely the measured "non-redundant"
finding). But the **combinator program is massively self-applicative**:
`s`/`b`/`c` duplicate their argument (`prim_stars`, `galaxy.rs:431-444`:
`s x y z → (xz)(yz)` copies `z`; the δ-stars splice large shared bodies
under `Push`). Every `s`-style duplication in a *naïve* graph creates two
copies of `z` that are then **reduced independently from scratch** — the
exact work-duplication Lévy-optimal reduction was invented to remove and
that subterm-memoisation **cannot** see, because the two copies of `z` are
in different reduction states / different surrounding contexts and never
become the *same closed `TermId`* until (if ever) both finish. This is the
mechanism by which a reduction can be "long and non-redundant" to a
subterm cache yet **highly redundant in redex-family terms**. Optimal
reduction is the only lever in scope that attacks *that* axis.

**This is a fourth, orthogonal axis** not in docs/11's §A table:

| Axis | Lever | Removes |
|---|---|---|
| per-step cost | B (Φ-spec) | interpretive O(\|Φ\|) + α-rename/unify per step |
| redundant *subterm* re-forcing | C (memo) | exponential re-force of shared **closed** structure |
| number of steps (affine) | D (KA2) | O(n) affine recurrence → closed form |
| **redundant *redex-family* work** | **E (this doc)** | **re-reduction of duplicated-but-not-closed sub-computations (`s`/`b`/`c`/δ copy fan-out)** |

---

## C. The compilation Φ → interaction net (concrete, exact)

The correspondence is unusually clean **because galaxy is binder-free**.
For λ-calculus, Lamping/BOHM need fan/bracket/croissant "oracle" nodes
purely to manage the *scope of binders* under sharing — the entire
hard, slow, bookkeeping-heavy part of optimal reduction. **Galaxy has no
binders**: `galaxy.rs:1-13` module doc — "binder-free objective program …
the KAM-escape encoding (§57.16, `−i` row deleted) applies verbatim";
`combinator.rs:7-13,46-48` — "Bracket-abstracted combinators have **no
binders**, so the capture problem cannot arise … Every star carries
**zero `i`-rays**". This is the ideal case: galaxy compiles to a
**Lafont interaction net** (or directly to interaction combinators /
HVM2's node set) with **no oracle layer at all** — pure first-order
graph rewriting with a fixed set of binary agents and the *symmetric,
local, strongly-confluent* interaction rules of Lafont's system [Lit].

### C.1 The map (stars/rays/fusion ↔ agents/ports/rewrite)

| Stellar (Eng / stella, [Built] file:line) | Interaction net ([Lit] / [Proto]) |
|---|---|
| Process ray `+P(st(M,π))` (`galaxy.rs:326`) | the single active wire = the net's principal "focus" port [Proto] |
| Application node `a(M,N)` (`galaxy.rs:314`) | an **APP** agent, principal port up-spine, aux ports `M`,`N` [Proto] |
| KAM stack `M·π` `dot` (`galaxy.rs:318`) | the net is *applicative*, not stack-threaded: `Push` (`galaxy.rs:423`) is *not a rule*, it is the trivial re-rooting of the focus onto APP's principal port — it **vanishes** as an agent interaction [Proto, key] |
| δ-star `[−P(st(:N,π)),+P(st(body•,π))]` (`galaxy.rs:398`) | a **DEF\_N** agent (nullary principal); its single rule `DEF_N ▷ ★ ⇒ ⟨body•⟩` splices the *shared* compiled net of `body•` (one canonical copy, pointer-shared) [Proto] |
| Combinator `i` `i x → x` (`galaxy.rs:425`) | **I** agent; rule `I▷APP ⇒ wire-through` (a Lafont ε/identity-style rule) [Proto] |
| `t x y → x`, `f x y → y` (`galaxy.rs:427,429`) | **K**-like erase-one agents: `T▷·` keeps arg 1, **erases** arg 2 via an ERA (Lafont eraser ε) on the dropped subnet [Proto] |
| `s x y z → (xz)(yz)` (`galaxy.rs:431`) | **S** agent whose rule introduces a **DUP** (Lafont δ duplicator) on `z`: the *only* non-linear rule; DUP is exactly the interaction-combinator sharing node [Proto, load-bearing] |
| `c`,`b`,`cons`,`car`,`cdr`,`nil` (`galaxy.rs:436-455`) | linear rewiring agents (no DUP, no ERA except `nil`/projection) — pure local rules [Proto] |
| Fusion `φ₁ ^{j,j'}∇ φ₂` with θ=mgu (`interactive.rs:518-528` `fuse_theta_fast`) | **interaction-net rewrite**: an active pair (two agents connected principal-to-principal) is replaced by its rule's net. Because galaxy is binder-free and δ/combinator LHSs are *linear ground patterns*, θ is **always trivial/structural** (docs/11 §B.1 proves exactly this: δ-θ is the trivial `{π↦σ}`, combinator match is a positional spine walk) ⇒ **no unifier in the hot loop** [Proto, follows from Built §B.1] |
| `iex_fast` leftmost scan + step (`interactive.rs:1121-1163`) | the interaction-net **reduction loop**: pick any active pair (Lafont: order-irrelevant — strong confluence), apply its rule [Lit/Proto] |
| §49.50 ray-minting `drive_strict` (`galaxy.rs:746-789`) | **not** an interaction-combinator rule — an *external* agent (numeric oracle); see §F [Proto] |

### C.2 The asymptotic claim for `data[0]`

The DUP node (from `s`, and from any δ-body that uses its argument
non-linearly) is the entire game. In the **naïve / current** engine,
`s x y z → (xz)(yz)` (`galaxy.rs:431-434`) literally *constructs two
syntactic copies* of `z` (`a(a(x,z),a(y,z))` — `z` appears twice). Both
copies are then forced independently. If `z` is itself a large unevaluated
sub-computation (it is, pervasively, in the image interpreter), the engine
**reduces `z` twice** — and recursively, every `s` inside `z`'s reduction
doubles again. This is the textbook exponential that **Lévy-optimal /
interaction-net reduction removes**: the DUP agent reduces `z` **once** and
*incrementally duplicates only the already-computed normal-form fragments*
as they are produced (the Lafont δ commutes with constructors lazily), so
the shared sub-computation is performed exactly once per redex *family*,
not once per *copy* [Lit, Lévy/Lamping optimality theorem].

> **Asymptotic [Proto, literature-grounded].** Let `data[0]`'s reduction
> have a redex-family DAG of size `F` whose naïve (copy-then-reduce) tree
> unfolding has size `T`. Subterm memoisation (Lever C) reduces `T`'s
> *closed-subterm* repeats but leaves the `s`/δ copy fan-out: `T` can be
> exponential in the `s`-duplication depth while `F` is polynomial.
> Interaction-net reduction performs **O(F)** interactions (each redex
> family contracted once — Lévy optimality), i.e. it can be an
> **exponential → polynomial** class change on exactly the workload
> docs/11's "long non-redundant" finding describes, on an axis (redex-
> family sharing) that **no Lever B/C/D touches**.

The honest qualifier (kept, not buried): optimality bounds the number of
*family* contractions, **not** total work — the classic Asperti–Mairson
result is that the *bookkeeping* (oracle) can itself be non-elementary
*for λ-calculus*. **The binder-free galaxy case dodges the Asperti–Mairson
penalty entirely**: there is no oracle (no binder scopes to track), only
Lafont DUP/ERA on a first-order graph, whose total cost is provably linear
in the number of interactions [Lit, Lafont interaction combinators —
local, bounded-degree, strongly confluent]. So for galaxy specifically the
optimality bound is the *real* bound, not a misleading family count. **This
is the single strongest structural argument in the whole survey** and the
reason this lever is not a constant factor.

### C.3 Relation to docs/08 §49.50 "forcing = annihilation"

docs/08 §2.2 already names this: `iex_fast` over `±P` is "supply/demand
annihilation on `±P`"; `drive_strict` is "the fusion = annihilation";
§2.2 explicitly maps "strict dynamics = orthogonal fusion =
annihilation." docs/08 §3 (`accel_detect`) and §4 (trace monoid) build the
**dynamic** theory. The interaction-net model here is the **operational
realisation of docs/08's annihilation framing for the *objective*
fragment**: a `±P` annihilation *is* an interaction-net active-pair
rewrite; Lafont's "annihilation" (two identical agents meeting principal-
to-principal cancel) and "commutation" (different agents duplicate past
each other) are *exactly* §49.50's annihilate-vs-mint dichotomy. **For the
objective δ/Push/combinator skeleton the interaction-net model is the
*right* framing — sharper than docs/10's generic open-hypergraph (OHG)
layering** (see §E). It is not a competing metaphor; it is docs/08's
annihilation made into a reduction algorithm with an optimality theorem
attached.

---

## D. Faithfulness: net reduction must equal reference `iex`

The net is a **new fast tier**, identical in status to `iex_fast` /
`iex_tabled` / Lever C: never reachable from the reference path, gated per
corpus, deopt to reference on any red.

> **P-NET [Proto].** Let `iex(Φ,Ψ)` (resp. `eval_forced` for the forced
> galaxy case) be the reference result and `iex_net(Φ,Ψ)` the result of
> compiling Φ→net, reducing the net to interaction normal form, and
> reading back. Then `psi_compatible(iex(Φ,Ψ).psi, iex_net(Φ,Ψ).psi)`
> (`faithfulness.rs:115`), and for the forced case the readback decodes
> `psi_compatible` with the `eval_forced`/`force_value` unrolling
> (`galaxy.rs:890,685`).

Why this is sound and certifiable:

1. **The objective fragment is confluent (the soundness floor).** Galaxy's
   δ/Push/combinator skeleton is the confluent objective fragment
   `iex_tabled` already certifies result-equivalence (not byte-identity)
   on (`constellation.rs:26-33` `StarKind::Objective`; docs/10 §1.3,
   docs/11 §G). Lafont interaction nets are **strongly confluent by
   construction** (local rules, unique normal form). Two confluent systems
   computing the same rewrite relation have the same normal form ⇒ P-NET
   holds on the objective fragment *by the same argument that makes
   `iex_tabled` sound*. `psi_compatible`'s conceal+α-canonical multiset
   compare (`faithfulness.rs:85-118`) tolerates exactly the variable-name
   / scaffolding freedom the net readback introduces.

2. **Where it can diverge — stated, not hidden.** (a) **Strategy.**
   Reference `iex_fast` is *leftmost* (`interactive.rs:1121-1132`: first
   matchable `(i,j)`). Net reduction picks active pairs in *any* order
   (Lafont order-irrelevance). On the confluent objective fragment the
   *normal form* is identical, but **non-termination behaviour is not
   strategy-invariant**: leftmost may reach a normal form where an eager
   net diverges on a dead sub-net, or vice versa (the classic optimal-
   reduction "wasteful on erased redexes" failure — DUP can duplicate work
   into a subnet that ERA later deletes). Mitigation: ERA must be eager
   (Lafont erasure interacts immediately), and the readback gate catches a
   *wrong* normal form; a *non-terminating* net is caught by the same
   fuel/budget honest-stop the engine already uses (`eval_forced`
   `max_forcings`, `galaxy.rs:933-938`). (b) **Subjective rays.** Outside
   the confluent fragment (`StarKind::Subjective`/`Animist`,
   `constellation.rs:32-33`), step order changes *which rays get minted*
   (docs/10 §4, docs/08 §4.2 dependency). P-NET can legitimately be
   `false` there; then the net is simply not a valid jet for that corpus
   and falls back — exactly as docs/10 §4 / docs/11 §G already specify for
   their levers. The design must **detect**, not assume.

3. **Same instrument, no new trusted code.** `psi_compatible` (proven,
   `faithfulness.rs:115-119`) is reused verbatim; reference `iex` /
   `eval_forced` stay the untouched oracle; deopt mirrors
   `iex_fast_result_eq_iex` / `iex_tabled_result_eq_iex`
   (`interactive.rs:1530,1593` per docs/11 §B.4). This is the
   non-negotiable two-tier model (docs/07 §H, docs/09), unchanged.

---

## E. Data-parallelism: HVM-style parallel interaction vs docs/10 OHG layering

This is where the survey delivers a sharp verdict against docs/10's
framing for *this* workload.

- **HVM2 / Bend (Taelin et al., 2020s) [Lit]** is an interaction-
  combinator runtime whose reduction is *intrinsically* parallel: active
  pairs are independent by the locality of interaction-net rules, so a
  worklist of redexes is reduced by N workers with no global
  synchronisation, **and** it carries Lamping-style optimal sharing. It is
  the existence proof that "optimal sharing" and "massively data-parallel"
  are the **same substrate**, not a trade-off.
- **docs/10's OHG layering** computes a Coffman–Graham/Kahn topological
  *layering* of a *given static* hypergraph and batch-applies independent
  edges per layer (docs/10 §2.1). docs/10 §2.2 is honest that this is a
  **constant-factor** lever on the *post-unifier* profile and "does **not**
  accelerate the single hottest inner kernel"; docs/10 §6 and docs/11 §G
  both conclude it cannot cross a non-termination boundary.

**Which is right for the galaxy blocker: the interaction-net model, not
OHG layering.** The reason is precise and is the load-bearing comparison:

- OHG layering parallelises a **fixed** diagram's independent edges. It
  *consumes* the dependency DAG (docs/10 §3(c), §5: "the substrate
  *consumes* that dependency relation"). It does **not** change the
  *amount of reduction work* — it reorders it. By docs/11 §A Fact 2 a
  reorder of non-terminating-in-150s work is still non-terminating.
- Interaction-net reduction **changes the amount of work** (Lévy
  optimality, §C.2: O(F) family contractions vs O(T) naïve), *and* its
  parallelism is a *free consequence* of the same locality (HVM2),
  *and* its sharing (DUP) is the very thing OHG's `Vec<usize>` incidence
  arrays **destroy** (docs/10 §6 "array constant factors vs hash-cons
  sharing" risk: OHG "materialises per occurrence" the shared δ-bodies
  galaxy shares once — the *opposite* of what `data[0]` needs).

**Verdict for §E:** docs/10's OHG layering is a constant-factor multiplier
on the wrong axis for `data[0]`; the interaction-net model is the
asymptotic lever *and* subsumes the data-parallelism docs/10 chases (HVM2
proves layering falls out of interaction locality for free, with sharing
*preserved* not destroyed). docs/10 is not wrong — it is correctly scoped
as a post-reachability constant-factor widener; it simply is **not** the
lever that executes `data[0]`. Interaction nets are.

---

## F. §49.50 / subjective rays: objective fragment only

Honest boundary, identical to where docs/08 §1.3 / docs/10 §1.3 / docs/11
§G all draw it:

- The interaction-net model captures the **objective** δ/Push/combinator
  skeleton **exactly** (§C.3: it *is* docs/08's annihilation made
  algorithmic, and that fragment is `StarKind::Objective`,
  `constellation.rs:26-31`).
- It does **not** model §49.50 ray-minting. `drive_strict`
  (`galaxy.rs:746-789`) is the sole minting site (docs/08:151); it forces
  operands via `force_value` (`galaxy.rs:685`) and injects a *new* `+P`
  ray. In interaction-net terms `drive_strict` is an **external interface
  agent / numeric oracle** wired to the net's strict-op site — *not* a
  Lafont rule. This is structurally the same concession docs/11 §B.2 makes
  ("strict-op head … kept exactly as is" on `drive_strict`) and docs/10
  §3(c) makes ("(c) — no … §49.50 dynamics are not a representation, they
  are a reduction strategy").
- Lafont **annihilation vs commutation** is the static-structural shadow
  of §49.50 **annihilate-then-mint**; the *minting* (a new ray that did
  not exist) is the **dynamic** the static net cannot contain, exactly
  docs/10 §1.3 point 2–3 and docs/08 §4.2's semaphore dependency. The net
  is correct **per AEx layer** between mintings; the driver mints. Same
  static-vs-dynamic boundary as docs/10/08 — this doc does not move it and
  must not pretend to.

Consequence: the lever's *guaranteed* domain is the objective image-
interpreter skeleton — which is **precisely `data[0]`'s reduction**
(`galaxy_data_probe.rs:91`: forcing one image element is δ/Push/combinator
unfold; the arithmetic that needs `drive_strict` is the `arith_ops` slice,
reported separately, `galaxy_data_probe.rs:93`). The blocker is in the
lever's faithful domain. Subjective/forcing dynamics ride on top via the
same `drive_strict` external-agent boundary, gated by P-NET / fallback.

---

## G. Staged falsifiable plan

Hard constraint (identical discipline to docs/10 §5 / docs/11 §F): must
**not** confound the in-flight `find`/unify (docs/09) work or docs/11
B/C/D attribution. The net is a different organ (a whole alternative
reducer for the objective fragment); it lands with its own KS-PROF /
`psi_compatible` attribution, **after** Lever C is measured (C is built
and is the cheap reachability floor; the net is the asymptotic ceiling and
the bigger build).

- **Stage-0 — one corpus, compile→reduce→`psi_compatible` (the decision
  gate, non-invasive).** Outside the engine: take `combinator.rs`'s
  battery first (`combinator.rs` tests, smallest closed binder-free terms
  — `S T T x`, the church-pair car/cdr), then `faithfulness.rs`'s
  `binarith`/bounded `galaxy` corpora (`faithfulness.rs:244,259`). Compile
  Φ→interaction net (the §C.1 map; **no DUP-correctness shortcuts**),
  reduce to interaction NF, read back, assert
  `psi_compatible(iex(corpus).psi, net.psi)` with the proven validator.
  **Falsifier 1 (soundness kill):** any `psi_compatible` red on the
  *objective confluent* corpora ⇒ the §C.1 rule map (specifically the
  DUP/ERA rules for `s`/`t`/`f`) is wrong ⇒ stop, fix, or abandon.
  **Falsifier 2 (the whole point):** instrument *family contractions* vs
  the reference's *step count* on a galaxy-shaped input with deep `s`/δ
  copy fan-out (the `combinator.rs` `skk`/church-pair scaled up, or a
  bounded slice of `data[0]`'s subnet). If net family-contraction count is
  **not asymptotically below** reference step count as fan-out depth
  grows, the lever is theoretical for galaxy and the project stops here
  with a recorded negative — *exactly* docs/10 §5 Stage-0's
  "theoretical ⇒ recorded negative" discipline.

- **Stage-1 — engine fast tier `iex_net`, gated.** Wire the net reducer as
  a fast tier behind `psi_compatible`, parallel to `iex_fast`/`iex_tabled`
  (deopt mirrors `interactive.rs:1530,1593`). **Falsifier:**
  `psi_compatible(iex, iex_net)` green on all `faithfulness.rs` corpora
  (`horn :217`, `binarith :244`, bounded `galaxy :259`); KS-PROF galaxy
  shows the `s`/δ copy fan-out work eliminated with **no change to
  reference oracle behaviour** (attribution: it is the net, not B/C/D).

- **Stage-2 — the categorical falsifier: `data[0]` terminates.** With
  Lever C already committed (`galaxy.rs:846`) and the net tier on, run
  `galaxy_data_probe.rs`'s `data[0]` force (`:91-96`). **Falsifier /
  success criterion:** `data[0]` reaches `fully_reduced=true` (or a
  decoded image) within a sane budget where Lever-C-alone did not — the
  single load-bearing experiment of this whole doc. Negative is
  publishable: if the net *also* does not terminate `data[0]`, then
  galaxy's residual is neither subterm-redundant *nor* redex-family-
  redundant *nor* affine-recurrent, and the blocker is genuinely D's
  unbounded-lever territory or beyond — report as a first-class negative,
  do not retro-widen.

- **Stage-3 — HVM-style parallel reduction (only if 0–2 pass).** Parallel
  active-pair worklist (the §E free-parallelism). **Falsifier:** still
  `psi_compatible`; speedup attributable and *additional* to the
  Stage-1/2 sequential-net win; **no improvement on narrow corpora is
  expected and is not a failure** (predicted shape, as docs/10 §5
  Stage-2).

Ordering vs in-flight: strictly **after** the docs/09 `find`/unify Stage-2/3
lands and is attributed (docs/10 §5, docs/11 §F constraint — un-confounded
KS-PROF), and **after** Lever C's `data[0]` reachability is measured (so
the net's contribution is attributable as *the redex-family axis*, not
conflated with C's subterm axis). The net does **not** touch the unify
kernel or the `find` index — different organ, same discipline.

---

## H. Honest risks + the realistic verdict

**Risks (evidence-driven, not hedging):**

1. **DUP correctness is the entire soundness load.** The `s`-rule's DUP
   (Lafont δ) and the `t`/`f`/`nil`-rule ERA must be *exactly* the Lafont
   rules or sharing is unsound (duplicates a redex incorrectly →
   wrong NF). Mitigation: it is **first-order, binder-free** (galaxy has
   no `i`-rays — `combinator.rs:46-48,328-340` *tests* this), so DUP/ERA
   are the textbook finite Lafont rule set with **no oracle**, the case
   where interaction combinators are *provably* sound and linear-cost
   [Lit]. Stage-0 Falsifier-1 is the cheap kill if the map is wrong.
2. **Optimality is family-count, not wall-clock, in general.** For
   *λ-calculus* the oracle bookkeeping can dominate (Asperti–Mairson). The
   binder-free galaxy case **specifically** has no oracle (§C.2) — but
   this must be *measured*, not assumed: Stage-0 Falsifier-2 measures
   family contractions vs steps directly. If galaxy's `data[0]` somehow
   needs scope-like sharing the combinator encoding hides, the penalty
   could resurface. Low probability given `combinator.rs`'s zero-`i`-ray
   proof, but it is the residual theoretical risk.
3. **Erasure/strategy non-termination divergence (§D.2a).** An eager net
   can loop where leftmost `iex` halts (work duplicated into a
   later-erased subnet). Mitigation: eager ERA + the existing honest fuel
   stop + P-NET catches *wrong* (not merely *slower*) results. This caps
   the lever: like docs/11 D it can only *accelerate*, never *decide*
   normal-form existence (docs/08 §6.1 inherited §49.59 openness).
4. **Subjective fragment out of scope (§F).** The net is objective-only;
   `drive_strict` stays the external minting agent. Same boundary as
   docs/08/10/11 — not a new risk, but it means the net executes the
   *image-unfold skeleton* of `data[0]`, with arithmetic still on the
   disclosed §60 host path (`galaxy.rs:746`). That is the correct,
   already-accepted faithfulness boundary, not a gap this doc opens.
5. **Build cost / maturity.** A correct interaction-net reducer + readback
   is a substantially bigger build than Lever C (which is ~40 lines and
   *done*). HVM2 exists as a reference design [Lit] but is not a
   dependency; this is a from-scratch in-tree reducer. It is the largest
   single build in the docs/10/11/12 arc.

**Realistic verdict.**

Interaction-combinator / HVM-style reduction is **the** structurally
correct lever for the *measured* blocker — and it is a **compounding**
lever, not an alternative to docs/11 B/C/D:

- It attacks a **fourth axis** (redex-family work-sharing, §B) that B
  (per-step), C (closed-subterm sharing), and D (affine recurrence)
  **provably do not touch**. The measured finding — `data[0]` is "long
  and *non-redundant*" *after* Lever C — is precisely the signature of a
  reduction that is redundant in **redex-family** terms while not
  redundant in **closed-subterm** terms. That is the optimal-reduction
  sweet spot.
- Galaxy being **binder-free** removes the one thing that makes optimal
  reduction usually not worth it (the Asperti–Mairson oracle penalty):
  `combinator.rs` *proves in-tree* there are zero `i`-rays
  (`combinator.rs:328-340`), so the net is pure linear-cost Lafont with no
  oracle. The correspondence is not analogical; it is exact, and docs/08
  §2.2 already named it ("fusion = annihilation"). The interaction-net
  model is the **right** operational framing for the objective fragment —
  sharper than docs/10's generic OHG layering, which is a constant-factor
  reorder that destroys the very sharing `data[0]` needs (§E).
- It is **gated by the identical proven instrument** (`psi_compatible` +
  reference oracle, §D), so it carries the same near-zero faithfulness
  risk as every other fast tier; the soundness load is concentrated in a
  finite, testable, binder-free rule set with a Stage-0 cheap kill.

It is **not** a guaranteed win and **not** a dead end: the single
unresolved empirical question is Stage-0 Falsifier-2 — does galaxy's
`data[0]` actually exhibit deep `s`/δ redex-family redundancy (the §C.2
mechanism), or is its length genuinely irreducible (in which case only D's
unbounded acceleration, or nothing in this arc, helps)? That is a *cheap,
falsifiable, non-invasive* experiment, and it is the right next probe
after Lever C's reachability is measured.

---

### One-line decision

The path to executing galaxy's `data[0]` is the **binder-free
interaction-net / HVM-style reducer**: it attacks the one axis — redex-
family work-sharing — that docs/11 B/C/D structurally cannot, it is the
*exact* (not analogical, and oracle-free because galaxy has no binders)
operational form of docs/08's "forcing = annihilation," it subsumes
docs/10's data-parallelism for free while *preserving* the sharing OHG
destroys, and it is gated by the same proven `psi_compatible` + reference
oracle; sequence it after Lever C's measured reachability with the
non-invasive Stage-0 family-count falsifier as the cheap decision gate.
