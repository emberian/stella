# Is a tractable *faithful* AEx possible for `machine_stars`?

**Verdict: NO (with one narrow conditional, stated and then closed).**
Query-directed / demand-driven saturated-diagram construction is
*either* (a) provably **not** α-equivalent to reference `AEx_C(Φ)`
(§49.42) — i.e. it is a different operator, not the faithful oracle — *or*
(b) where it *is* provably α-equivalent, it does not avoid the measured
explosion. The two cannot be had at once on `combinator::machine_stars`.
This closes the question as a first-class result: IEx-grounded +
theorem-calibrated is the only sound path, exactly as docs/16 §7 already
recorded by measurement.

---

## 1. What "faithful AEx" is pinned to (no wiggle room)

`AEx_C(Φ) := ⇓ CSatDiags_C(Φ) = { ⇓δ | δ ∈ CSatDiags_C(Φ) }`
(EngExegesis/doc.md:4125, §49.42). Three load-bearing facts about this
definition:

- **It has no query parameter.** The only argument other than `Φ` is the
  colour set `C ⊆ F⁺⊎F⁻` (§49.42, "We write AEx(Φ) when all colours in Φ
  participate"). The result is the set of actualisations of *every*
  correct saturated diagram of Φ. There is no distinguished "goal star."
- **"Saturated" is a query-independent maximality.** §49.23
  (doc.md:3982): `δ` is saturated iff it is maximal w.r.t. the subgraph
  preorder `⊑` — it cannot be extended *at all*, by *any* matchable ray
  anywhere in the diagram. Saturation is a property of the diagram and
  Φ's dependency graph `𝔇[Φ;C]`, not of any seed.
- **`CEx` (the executable form) iterates over all seeds and is proven
  equal to AEx.** §50.5 stellar construction (doc.md:4258) seeds the
  construction space with *every* star `1 ≤ i ≤ n` (§50.6 clause 1,
  doc.md:4280); §50.7 (doc.md:4283) `AEx_C(Φ) = CEx_C(Φ)` by induction
  on edge count, where ∆ at step `n` is *all* diagrams with `n` edges.
  This is exactly what `execution.rs::saturated_diagrams_with_strategy`
  implements: `for seed in (0..phi.len())` (execution.rs:170), all-rays
  fan-out (execution.rs:183–245), Blind = the §50.7 oracle
  (execution.rs:311–312, 318–321).

So "the faithful AEx oracle" = ⇓ of the actualisation of *the entire set*
of correct saturated diagrams of Φ, computed without reference to any
query. The faithfulness gate `faithfulness::psi_compatible` checks an
engine's output against *this* set (α-equivalence of result-star
multisets; cf. `result_sets_alpha_equiv`, execution.rs:515–528, and the
`oracle_faithfulness_*` / `oracle_gate_*` tests, execution.rs:566–924).

## 2. Where the explosion lives, precisely

`machine_stars()` (combinator.rs:147–151+) is 7 stars. Push is
`[−P(a(M,N)⋆π), +P(M⋆N·π)]`. Its **positive** ray `+P(M⋆N·π)` is
matchable (after the diagram's renaming, §49.27, doc.md:3992–4002) with
its own **negative** ray `−P(a(M,N)⋆π)` (unify `M⋆N·π =? a(M',N')⋆π'`
succeeds: `M ↦ a(M',N')`), with `−P(I⋆X·π)`, `−P(T⋆…)`, `−P(S⋆…)`, etc.
— `M` and `π` are unconstrained variables. The 7 KAM stars are therefore
**mutually matchable as a clique** at the `±P(st(·,·))` head, *before any
reduction of a concrete process term*. Consequence (measured, f96b452 /
docs/16 §7 step 3; aex_combinator_probe.rs):
`machine_stars + [+P(st(x,ε))]` — a single **zero-redex value** seed —
fails to enumerate `CSatDiags` within 45 s under `aex_full`,
`aex_seminaive_full`, and copy-free `aex` alike. The `bare x` blowup is
**entirely Φ-internal**: it is the combinatorial closure of the 7-clique
under "add a matchable occurrence," independent of the seed value. This
is §62.5's "black hole" shape (doc.md:5122–5128): a star whose positive
ray re-feeds its own negative ray ⇒ "it is always possible to add an
occurrence and extend the diagram as we wish" ⇒ diagrams are never
saturated along that axis; the supply is `expand_constellation`-bounded
(execution.rs:340–352, MAX_VERTICES=16, execution.rs:22) so it does not
diverge but the *count* is super-exponential in the copy/vertex budget.

## 3. The candidate: query-directed saturation — and why it splits

A "query-directed" AEx would seed the construction space with *only* the
query star `q = [+P(st(M•,ε))]` and only build diagrams reachable from
`q` (a demand-driven / goal-restricted `saturated_diagrams` whose
worklist is rooted at `q`, never seeding the 7 machine stars as
standalone diagrams). Call this `AEx^q`. Two mutually exclusive cases,
and the dichotomy is forced by §49.42 + §49.23:

### Case (b) — restrict seeds but keep §49.23 saturation: α-equivalent, NOT tractable

Seed only from `q`, but keep the §49.23 saturation condition (a diagram
is emitted only when it admits *no* extension by *any* matchable ray).
Because every machine star is reachable from `q` (Push fires on `q`'s
`+P(st(a(_,_),ε))`, the combinator stars on the unwound head), and
because the 7 stars are a mutually-matchable clique (§2), **every
saturated diagram of Φ that has a correct actualisation is reachable from
`q`** for a closed process seed: the connected component of `𝔇[Φ;C]`
containing `q` *is* the whole machine. Restricting seeds changes nothing
about which diagrams get built — §62.16/§62.3-style component reasoning
(doc.md:5197: `CSatDiags_C(Φ) = ⋃_k CSatDiags_C(Φ_k)` over connected
components `k`; here there is one component once `q` is attached). This
**is** provably α-equivalent to reference `AEx_C` (it computes the same
`CSatDiags` of the same single component, §49.42 + the §50.7 induction
restricted to the reachable component). But it inherits the §2 explosion
*exactly*: the explosion is the 7-clique's internal saturation
combinatorics, which the query does not gate because the clique is
*inside* the component the query is attached to. This is precisely the
measured f96b452 result — `bare x` / `[+P(st(x,ε))]` already explodes,
and that seed *is* a query-only seed. **α-equivalent but not tractable.**

### Case (a) — prune by demand (stop at the query's answer): tractable, NOT α-equivalent

To get tractability one must *prune*: stop extending a diagram once the
query's free ray is "resolved" (e.g. once the focused `+P(st(v,ε))` has
no `−P`-redex), and *not* enumerate the Φ-internal extensions that §49.23
still permits (Push re-matching its own output, idle combinator-star
occurrences attachable to free `π`/`M` slots, etc.). This is exactly
demand-driven / SLD control. But this **changes the result set**, and
provably so, for three independent §-cited reasons:

1. **It violates §49.23 saturation.** A diagram stopped at "query
   resolved" is, in general, *not maximal*: §49.23 demands no extension
   by *any* matchable ray; the pruned diagram still admits the
   clique-internal extensions. So the emitted diagrams are not
   `SatDiags_C(Φ)` — they are a strict subset chosen by a strategy. The
   strategy machinery in `execution.rs`
   (`saturated_diagrams_with_strategy`, lines 158–295) is explicitly
   *reorder-only, never prune* ("all candidates are still explored (no
   pruning), so completeness is preserved", execution.rs:155–157); the
   `SelectionStrategy` faithfulness tests (execution.rs:566–654) hold
   *because* nothing is pruned. A pruning `AEx^q` falls outside that
   completeness invariant by construction.

2. **AEx and a query-stopped walk are *defined* to differ — Eng says so.**
   §51.11–51.12 (doc.md:4348–4382): for the addition program,
   `AEx`/`CEx` over `Φ ⊎ query` builds **infinitely many** saturated
   diagrams but only **one** is correct ("there are infinitely many
   saturated diagrams which can be constructed but only one correct.
   Interactive execution has to compute all diagrams iteratively"). Eng
   then introduces §51.12: "in order to correctly execute programs, we
   need control over the interactive execution … Prolog uses
   SLD-resolution which is a controlled version of Robinson's original
   resolution. In particular, the interactive configuration should only
   have the query in its interaction space." The query-directed,
   stop-when-resolved object **is IEx with the query in Ψ (§51.10,
   doc.md:4347)** — Eng's *other*, deliberately distinct operator. It is
   not a tractable AEx; it is IEx. §62.4 (doc.md:5121) nails the
   semantic gap with a worked witness: `AEx([−c(X),+c(f(X))]) = ∅`
   ("impossible to construct a saturated diagram"), whereas the
   demand-driven concrete walk "would have an infinite loop." AEx's
   answer on a black hole is the *empty set by non-saturation*; any
   query-stopped construction returns something else (a partial diagram's
   actualisation, or nothing, but not "∅ because unsaturable"). The
   operators provably disagree on exactly the `machine_stars` shape (§2 =
   a §62.5 black hole). **Not α-equivalent — by Eng's own definitions and
   his own §62.4 counterexample.**

3. **It would silently drop the AEx-only finite outputs.** §62.1–62.4
   (doc.md:5117–5121): AEx is *visible* normalisation, IEx is *strong*
   normalisation, "strong normalisation subsumes visible normalisation"
   — they are different termination notions with different outputs on
   non-SN constellations. A pruned `AEx^q` computes the IEx answer, which
   is the strictly finer (and on black holes, divergent rather than `∅`)
   object. Re-labelling it "AEx" would be the precise smuggle the
   `psi_compatible` gate exists to catch.

## 4. The dichotomy is exhaustive (the impossibility argument)

Any saturated-diagram construction for `machine_stars` either keeps the
§49.23 maximality condition or relaxes it.

- **Keep it** ⇒ (Case b) you build the full `CSatDiags` of the query's
  connected component, which for the 7-clique machine *is* the whole
  blowup (§2, measured f96b452). α-faithful, intractable.
- **Relax it** (any demand/goal/strategy stopping rule that makes it
  finish) ⇒ (Case a) you no longer compute `SatDiags_C(Φ)`; you compute
  a strategy-selected subset = IEx-with-query-in-Ψ (§51.10/§51.12),
  provably a *different operator* whose disagreement with AEx is
  exhibited by Eng at §62.4 on exactly the black-hole shape
  `machine_stars` has. Tractable, not α-faithful.

There is no third option: tractability on a §62.5 black hole *requires*
not enumerating the unbounded clique-internal extensions, and "not
enumerating extensions §49.23 permits" *is* the negation of saturation.
The query cannot gate the explosion because the explosion is **inside the
query's own connected component** (§2; component-decomposition
doc.md:5197) — it is not query-irrelevant noise that lives in a separable
component; it is the machine itself. (Contrast: if the blowup were in a
component *disconnected* from `q`, §62.16/doc.md:5197's
`AEx = ⨄_k AEx(Φ_k)` would let a reachability filter drop it
α-faithfully. It is not disconnected — Push's self-matchability welds the
clique into `q`'s component the instant `q` attaches.)

### The one conditional, stated and closed

*Conditional:* a pruned `AEx^q` **is** α-equivalent to reference `AEx_C`
*iff* one can prove, for the specific `Φ = machine_stars` and the closed
binder-free query class, that **every clique-internal extension that
§49.23 permits but the pruning drops leads only to incorrect or
α-redundant diagrams** (so dropping them does not change `⇓CSatDiags`).
This is exactly the **§49.55/§49.57 objectivity + idempotence obligation**
on `K★`. It is *undischarged*: docs/16 §7 step 2 measured §49.57 as
"prototype `aex` is idempotent even on the subjective fragment ⇒
non-idempotence lives in `subjective::subjective_stream`, NOT `aex`",
and §49.55 holds only on the *faithful* objective partition that
`star_kind_eng` carves — but `aex(machine_stars())` itself **cannot be
run to fixpoint** to certify the drop is sound (f96b452: it does not
finish). So the conditional's premise is **not establishable by
execution** for the very reason the question asks about: the oracle that
would certify the pruning sound is the intractable oracle. The
conditional collapses into the main verdict: NO tractable faithful AEx,
because the only thing that could make a tractable pruned variant
*provably* faithful is a fixpoint run of the intractable operator.

## 5. Complexity argument vs the measured explosion

Reference: `|CSatDiags_C(Φ)|` for the 7-clique grows as the number of
connected, edge-saturated multigraph homomorphisms into `𝔇[machine_stars]`
bounded by vertex budget (`expand_constellation` copies × `MAX_VERTICES`,
execution.rs:22,340–363). Push's positive↔negative self-edge plus 6
combinator stars each matchable to Push's output ⇒ the per-step candidate
fan-out (execution.rs:183–245) does not shrink as the seed reduces (a
*value* seed has the same Φ-internal fan-out as a redex seed — measured:
`bare x` already does not finish, aex_combinator_probe.rs:30,50). This is
super-exponential in the budget and **independent of query depth** — so
no query-rooted seeding changes the asymptotics (Case b). The only thing
that flattens it is refusing the clique-internal candidates (Case a),
which is a Θ(reduction-length) IEx walk (`iex_fast`, combinator.rs:59,
the engine that *does* finish) — i.e. tractability is recovered exactly
by becoming IEx, confirming the dichotomy is the operator boundary, not
an implementation inefficiency. Per-step levers (docs/11 Fact-2, docs/16
§1) cannot convert a super-exponential count into a finite enumeration.

## 6. Faithfulness gate it would sit behind, and the docs/08 §7 question

Any `AEx^q` tier would have to pass `faithfulness::psi_compatible`
against reference `aex`/`aex_full` (the execution.rs:566–924
oracle-faithfulness / oracle-gate discipline; two-tier + deopt, docs/16
§6). Case (b) passes the gate but never returns (intractable — the gate
cannot even be *evaluated* because the reference side does not finish:
f96b452). Case (a) returns but **fails** the gate on any black-hole input
(§62.4 disagreement) — and where it happens to agree (strongly
normalising inputs), it agrees *because it is IEx and the fragment is
confluent*, which is the **already-known** `iex_fast` result, not a new
AEx. So `AEx^q` adds nothing the gate can certify as AEx.

**Does it reopen docs/08 §7 (IEx-loop-NF = AEx-fixpoint)?** No. docs/08
§7's single open question is whether `eval_forced`'s per-loop `final_ray`
is a faithful `AEx`-layer boundary. That is *empirically* unanswerable
because the AEx side is intractable (docs/16 §7 step 3, explicitly:
"docs/08 §7 (IEx-loop-NF = AEx-fixpoint) is NOT empirically
establishable — closed by measurement, not omission"; docs/08:408–415).
A tractable faithful `AEx^q` would have reopened it (it would supply the
AEx side cheaply). This investigation shows **no such `AEx^q` exists**:
the only tractable query-directed object is IEx itself (Case a), so
"IEx-loop-NF = AEx-fixpoint" cannot be checked by *constructing* the AEx
fixpoint — the construction is either the intractable oracle or a
relabelled IEx. docs/08 §7 stays **closed by measurement**, not reopened.
The sound path is the one already taken: reference `iex`/`eval_forced` as
oracle, `psi_compatible` as gate, §67.10-calibrated `detect_recurrence`
for the recurrence side, and the §49.55/§49.57 metatheory carried as
*theorem-calibrated* (the falsifiable idempotence tests,
execution.rs:977–1102) rather than as an executed AEx fixpoint.

---

## Return summary

**Feasible? — NO.**

No tractable faithful AEx exists for `machine_stars`. Reference AEx
(§49.42, doc.md:4125) is defined as ⇓ of *all* correct saturated diagrams
(§49.23 maximality, doc.md:3982), with no query parameter and proven
equal to all-seed `CEx` (§50.7, doc.md:4283). Query-directed construction
splits exhaustively: (b) keep §49.23 saturation but seed only from the
query — this is provably α-equivalent (the query's connected component is
the whole 7-star clique, doc.md:5197) but inherits the measured explosion
unchanged (the blowup is Φ-internal to that component — f96b452 /
`bare x` already fails); (a) prune to stop at the query's answer to gain
tractability — this violates §49.23 maximality and **is**, by Eng's own
§51.11–51.12 (doc.md:4348–4382) and the §62.4 black-hole counterexample
(doc.md:5121), the *different operator* IEx-with-query-in-Ψ, provably not
α-equivalent to AEx. The explosion cannot be query-gated because it lives
inside the query's own connected component, not in a separable one. The
only conditional under which a pruned variant is provably faithful — that
the dropped clique-internal extensions are all incorrect/redundant — is
exactly the §49.55/§49.57 objectivity obligation on `K★`, which is
*undischargeable by execution* precisely because certifying it requires
running the intractable oracle to fixpoint (f96b452). Verdict closes the
question: **IEx-grounded + theorem-calibrated is the only sound path**,
docs/08 §7 stays closed-by-measurement and is **not** reopened.
