# Thesis audit 01 — the CORE stellar-resolution / transcendental-syntax calculus

READ-ONLY audit. Date 2026-05-17. Auditor: automated pass against sources.

## 0. Scope and source situation

**Mandate:** compare Boris Eng's CORE transcendental-syntax / stellar-resolution
calculus against `crates/stella-core/src/{term,constellation,polarised,unify,
unify_fast,antiunify,interactive}.rs`, plus `docs/05` and `docs/09`.

**Source note (a finding in itself).** The mandate named
`refs/extracted/transcendental_syntax/` and `refs/originals/transcendental_syntax.pdf`
as a source. That PDF is **not Eng** — it is Abrusci & Pistone, *On Transcendental
Syntax: a Kantian Program for Logic?* (27 pp, philosophy only, contains **no
stellar-resolution calculus**: no stars, rays, fusion, or dependency graph). It is
useful background on the *quid iuris* / proofs-vs-counterproofs / internal-completeness
motivation but contributes zero formal definitions. Eng's calculus is carried by:

- `refs/extracted/TranscendentalForLinearLogician/doc.md` — Eng's *gentle
  introduction* (46 pp): §2.2 stars/constellations, §2.3 evaluation
  (fusion / actualisation / saturated / correct / `Ex`).
- `docs/00-thesis-and-semantics.md` §4 — the canonical implementation contract,
  citing `EngExegesis.pdf` §48–§51 and Appendix B verbatim.
- `docs/eng-digest-ch8/10/11/12-13.md` — spec-grade verbatim extractions of the
  thesis (the "PDF-free source for implementation workers").

`EngExegesis.pdf` itself (per `docs/00` §0) is the **sole source of truth**; the
digests are its faithful proxy and are treated as canonical here. Citations below
are Eng §-numbers via the digests / `docs/00` §4, and the gentle-intro by section.

---

## 1. Concept-by-concept status

### 1.1 Rays — first-order terms over a polarised signature

**Status: implemented.** `term.rs` — hash-consed first-order terms. `Var`
(`term.rs:81`: `Named` | `Idx`), `Sym { name, pol }` (`term.rs:156`), `TermData`
= `Var | App(Sym, Arc<[TermId]>)` (`term.rs:210`). `Ray = TermId`
(`polarised.rs:13`). The underlying-term operator `|·|` (§48.7) is
`underlying_term` (`polarised.rs:123`), recursively stripping polarity to
`Neutral`. `op(f)` opposite (§48.3) is `Sym::opposite` (`term.rs:188`).

**Faithfulness divergence (FOUNDATIONAL — see §2.1):** Eng's signature
`P = (V, F, ar, ⊂, |·|)` (§48.2, `docs/00` §4.1) distinguishes a function
symbol's **colour** (its neutral identity / predicate name, e.g. `add`, `c`,
`t`) from its **polarity** (`+ / − / none`). The code collapses "colour" onto
"polarity sign": `ray_colours` (`dep_graph.rs:18`) returns the head's
display-name **iff `pol ≠ Neutral`**, i.e. a ray is "coloured" exactly when it
is polarised. There is no representation of an *uncoloured polarised* ray, nor of
the colour-as-predicate-identity that Eng's objective/subjective distinction
turns on.

### 1.2 Stars

**Status: implemented (with a divergence).** `Star = Vec<Ray>`
(`constellation.rs:12`), a finite indexed family of rays (§48.10). Empty star
`[]` representable. Stars equivalent up to renaming with disjoint variables —
realised by `freshen` / `alpha_rename_star` at use sites
(`interactive.rs:96` `freshen_star`; `diagram.rs:95` per-vertex renaming);
α-canonical form `canonical` (`antiunify.rs:52`).

**Faithfulness divergence (objective/subjective/animist):** `StarKind` and
`star_kind` (`constellation.rs:16,26`) classify by **polarity census**:
all-pos-or-neutral ⇒ `Objective`; all-neg-or-neutral ⇒ `Subjective`; mixed ⇒
`Animist`. Eng's definition (§48.7/§48.10, `docs/00` §4.1) is on **colour
dependency**: a ray is *objective* if uncoloured **or a colour over uncoloured
arguments**; *subjective* if a coloured ray with **≥1 coloured argument**; a star
is animist if it mixes objective and subjective rays. Eng's split is about
*colours nested inside arguments*, not the +/− sign of the head. The code's
notion is a polarity heuristic with the same names; it will misclassify e.g.
`+c(+d(X))` (Eng: subjective, nested colour) and `[+a(X), −a(Y)]` (Eng: depends
on colour-arg nesting, not sign mixing). Confirmed by the `engine_tests.rs:50`
`star_kind_animist` test, which asserts animism from sign-mixing alone.

### 1.3 Constellations

**Status: implemented.** `Constellation = Vec<Star>` (`constellation.rs:42`),
finite indexed family of stars (§48.14). `IdRays`, `±IdRays`, `get_ray`
(`constellation.rs:48–74`). Eng allows *countably infinite* constellations
(gentle-intro §2.2; "finite is sufficient for logic"); the type is finite, but
the **non-linear reference Φ** (infinite supply) is modelled operationally by
fresh-renaming on demand in `interactive.rs` (§51.3/§51.13) — faithful for the
intended use. `docs/00` §5.x flags the AEx copy-cap as a known prototype
deviation; the subjective stream (`subjective.rs`) is unbounded.

### 1.4 Fusion (MGU + substitute)

**Status: implemented.** Martelli–Montanari unifier `unify_with<C: Compatible>`
(`unify.rs:62`) with the four rules **Clear** (`unify.rs:72`), **Orient**
(`unify.rs:78`), **Replace** + occur-check (`unify.rs:85–111`), **Open**
(`unify.rs:114`), solved-form check (`unify.rs:140–157`) — verbatim against
`docs/00` §4.2 / §B.2.1. Fusion `∇` and self-interaction `▷` are in
`interactive.rs` (doc §49.30 / §51.7; `θ` solved over `underlying_term`,
§49.27). Diagram-level actualisation `↓δ` via the big unification problem:
`underlying_problem` / `is_correct` / `actualise` (`diagram.rs:128,150,156`),
matching the gentle-intro §2.3 "Actualisation: the set of all edges defines a
big unification problem; θ applied to free rays". A fast substitution-free
matchability oracle `matchable_fast` (`polarised.rs:265`) is differentially
gated against `matchable` (`polarised.rs:319` fuzz). `unify_fast.rs` is the
performance analogue.

**Faithfulness:** the algorithm is faithful. The compatibility relation it runs
under for *fusion/actualisation* is `StdCompat` (`unify.rs:48`, `f ⊂ g ⟺ f=g`)
on polarity-stripped terms — correct per §49.27. Matchability `⋈`
(`polarised.rs:173`) runs `PolarisedCompat` (`polarised.rs:97`):
`c ⊂ d ⟺ |c|=|d| ∧ (opposite polarities ∨ both neutral)`. This is faithful to
§48.2's *polarity* condition, but see §2.1: it conflates Eng's separate **colour
compatibility** with polarity duality.

### 1.5 Colours / dependency

**Status: partial / divergent.** `ray_colours` (`dep_graph.rs:18`),
`all_colours` (`dep_graph.rs:34`), the dependency graph `D[Φ;C]`
(`dep_graph.rs:70`, `build_scan` O(n²) oracle at `:91`, indexed build via
`index.rs`), `mat_Φ^C` (`interactive.rs:196`+) all exist and the `⊆ C`
colour-filter is wired through. **But** `colours(r)` = "{display-name} iff
polarised" (§1.1 divergence), and in every execution path `C` is set to
`all_colours(Φ) ∪ all_colours(Ψ)` (`interactive.rs:209,214`), which the code's
own comments (`interactive.rs:320–323`) certify makes the `crj ⊆ c_set` filter
**always true** — i.e. colour-restricted execution `Ex_C` for a *proper subset*
`C` is structurally a no-op and never exercised. Eng uses proper-subset `C`
substantively (e.g. `⊥^1_C`, `⊥^R_C` orthogonality §69.4; tests vs vehicle by
colour; the GoI computational/logical split). **The colour dimension exists
syntactically but is not semantically live.**

### 1.6 Polarity (objective / subjective)

**Status: implemented as polarity; divergent as Eng's objective/subjective.**
`Polarity::{Pos,Neg,Neutral}` (`term.rs:48`), prefix-parsed once
(`term.rs:168`). Faithful as the *sign* attribute. As Eng's
**objective/subjective** ray/star *kinds* (§48.7/§48.10), see §1.2 / §2.1: the
implemented kind is a polarity census, not the colour-dependency definition.
Consequence for the load-bearing thesis result (`docs/00` §4.4): Eng proves AEx
idempotent for **objective** constellations (§49.55) and idempotence *lost* with
**subjective** rays (§49.57), where subjective rays *create new polarised rays
during execution* and need semaphore-like sync (§49.50). The
new-ray/§49.50 dynamics are implemented separately in `subjective.rs`
(`subjective_stream`, black-hole recognition §74.7/§75.8) — but they are keyed
off the polarity-based `StarKind`, not Eng's colour-nesting definition, so the
formal "objective ⇒ dead/idempotent" baseline is **not certified against Eng's
actual partition**.

### 1.7 Interaction / execution relation

**Status: implemented (three modes).**

- **AEx** (abstract execution, §49.42): `execution.rs` —
  `saturated_diagrams_with_strategy` (`:158`), `aex` (`:319`),
  `aex_seminaive` (`:396`), `aex_full` oracle (`:361`). Enumerates correct
  saturated diagrams and actualises (`diagram.rs`). `expand_constellation`
  (`execution.rs:340`) implements the finite k-copy supply (the `docs/00`
  §5.x acknowledged prototype bound).
- **CEx** (concrete execution, §50): `concrete.rs` (construction-space /
  internal-external extension; `conceal` ɟ at `:155`).
- **IEx** (interactive execution, §51): `interactive.rs` —
  stellar-interaction step (§51.9), self-interaction (§51.7), `mat_Φ^C`
  (§51.6), `iex_fast_concealed`. The §4.5 Horn-addition milestone runs here.

The "Connected / Saturated / Correct" diagram side-conditions (gentle-intro
§2.3) are present: connectedness in diagram construction, saturation in
`saturated_diagrams_*`, correctness as `is_correct` (`diagram.rs:150`).

### 1.8 Normal forms

**Status: implemented.** `Ex(Φ)` = actualise all correct saturated diagrams →
new constellation (gentle-intro §2.3). Strong normalisation = finite correct
saturated-diagram set: realised via fuel bounds (`interactive.rs` doc §51.10)
and the k-copy AEx cutoff. The §4.5 milestone
`IEx(Φ⁺_N, [−add(2̄,2̄,R),R]) ↝ [4̄]` is implemented and **passing**:
`arith.rs:97` `add_stars` (verbatim `[+add(z,Y,Y)] + [−add(X,Y,Z),
+add(s(X),Y,s(Z))]`), test `add_2_plus_2_is_4` (`arith.rs:207`).
Faithfulness compare harness: `faithfulness.rs` (ɟ-conceal then star-set
compare; `docs/09` §A documents `psi_compatible`).

### 1.9 Idempotence metatheorem (the load-bearing result)

**Status: design-doc-only as a *certified* property.** `docs/00` §4.4 fixes the
target: AEx idempotent for objective constellations (Eng §49.55);
non-idempotent with subjective rays (§49.57). The engine *can run* both
fragments, and `subjective.rs:419`+ distinguishes "subjective/charged" vs
"objective/dead", but there is **no test or property check that asserts
`AEx(AEx(Φ)) = AEx(Φ)` on objective Φ and its failure on subjective Φ** — and
because the objective/subjective split in code is the polarity heuristic (§2.1),
even such a test would not certify Eng's theorem as stated. This is the single
biggest gap between "implemented" and "Eng-faithful" in the core.

---

## 2. Faithfulness divergences (consolidated)

### 2.1 ★ The colour/polarity conflation (root divergence)

Eng's polarised signature has **two independent attributes** per function
symbol: a *colour* (neutral identity / predicate name; the compatibility
relation `⊂` is over colours) and a *polarity* (`+/−/none`). The codebase has
**one**: `Sym = (name, pol)`, and `ray_colours` *defines* "coloured" as
"`pol ≠ Neutral`". Downstream consequences, all confirmed:

1. **objective/subjective/animist** (`constellation.rs:26`) is a polarity census,
   not Eng's colour-argument-nesting definition (§48.7/§48.10). The named
   fragment where the project's whole "charge / dead" distinction lives
   (`docs/00` §4.4) is therefore **not the fragment Eng named**.
2. **`Ex_C` for proper subset `C`** is dead code in practice
   (`interactive.rs:320–323`): colour-restricted execution, orthogonality
   `⊥_C` (§69.4), and the GoI logical/computational separation cannot be
   exercised because `C` is always the full colour set.
3. **Matchability** uses polarity-duality for `⊂`; faithful to §48.2's polarity
   clause, but cannot express colour-only compatibility (`f ⊂ g` with `|f|≠|g|`,
   used by adapters §69.19 and the `⊂` "subtyping" generality of §B.1.2).

This is *internally consistent and sufficient for the encodings done so far*
(Horn programs, NFA/PDA/TM, MLL where colours and polarity happen to coincide in
the chosen encodings), which is why the milestone passes. It is **not** Eng's
signature, and it caps the project at exactly the place its thesis needs most
(the subjective/animist fragment, `docs/00` §2, §4.4).

### 2.2 Star/constellation as `Vec`, not multiset

Eng: star = finite **multiset** of rays; constellation = **multiset** of stars
(gentle-intro §2.2; §48.10/§48.14). Code uses `Vec` with positional `RayId`.
Multiset semantics (Φ + Φ duplication, `⊎`) is handled ad hoc at call sites.
Low-risk for current encodings but a latent divergence for any result that
quantifies over multiset equality / star multiplicity (e.g. weight ω,
`docs/eng-digest-ch12-13` §79.8).

### 2.3 Termination / strong normalisation is fuel-bounded, not analysed

Eng's "strongly normalising ⟺ finite correct-saturated-diagram set" is
approximated by fuel/copy caps. `docs/eng-digest-ch12-13` notes Eng himself
*omitted* a dependency-graph termination analysis ("tried but omitted"), so this
is a faithful *gap-for-gap* match, not a divergence — but it means the engine
cannot positively certify SN; it can only fail to diverge within budget. Death
is positively certified only via the Eng-named black-hole recognition
(`subjective.rs:985`+, §62.5 scope caveat), not generically.

### 2.4 Minor / non-divergences

- `antiunify.rs` (lgg / α-canonical) is an **engine extension** (KA0 recurrence
  detector, `docs/05` §9), **not** part of Eng's core calculus — correctly
  outside scope; faithful by construction (pure, observational).
- The Abrusci–Pistone "internal completeness / proofs-vs-counterproofs / tests"
  story is realised in `mll.rs` / `mll2i.rs` (Danos–Regnier as constellations,
  gentle-intro §5.2, digest ch10 §68); not in the seven core files but the
  conceptual through-line is present and faithful at the MLL layer.

---

## 3. Encodable experiments + infrastructure we lack

### 3.1 ★★★ Highest value: the idempotence metatheorem as a falsifiable engine property

**Experiment.** Pick a battery of *objective* constellations (Horn-add, NFA
encodings — already in `arith.rs`/`automata.rs`) and assert
`AEx(AEx(Φ)) =α AEx(Φ)` (Eng §49.55). Then a battery of *subjective* ones
(`subjective.rs` corpus, §49.50 new-ray example) and assert idempotence
**fails** (§49.57). This directly tests `docs/00` §4.4 — the project's load-
bearing "dead vs charged" claim — and §6's fourth pre-registered null
("subjective fragment provably as idempotent as objective ⇒ no charge").

**Infrastructure we lack:**
- An `aex_idempotent(Φ) -> bool` checker (compose `aex` with itself, compare
  under α via `antiunify::canonical` + multiset-equality of stars). ~30 LOC,
  no engine change.
- **Prerequisite:** a *correct* objective/subjective classifier (Eng's
  colour-nesting definition), distinct from the polarity-census `star_kind`.
  This is the §2.1 fix and is the gating dependency for the experiment to mean
  what Eng's theorem says.

### 3.2 Make `Ex_C` semantically live (proper-subset colour execution)

**Experiment.** Reproduce Eng's GoI computational/logical separation
(gentle-intro §5, digest ch10 §68): execute a vehicle against a *test* under a
**proper** colour subset `C` (e.g. only `t`-coloured typing rays, or only
`c`-coloured computation rays) and show the two halves separate. Requires `C`
to be a genuine parameter, not `all_colours`. **Infra lacking:** a real
distinction between colour and polarity in `Sym` (or a colour-set parameter
threaded into `iex`/`aex` that is not auto-widened); orthogonality predicates
`⊥^1_C`, `⊥^R_C` (§69.4) as functions.

### 3.3 Objective/subjective/animist classifier conformance suite

**Experiment.** Encode Eng's worked classification examples (`+c(+d(X))`
subjective; colour-over-uncoloured objective; mixed animist) and pin
expected `StarKind` against the *colour-nesting* definition. This is the unit
test that would have caught §2.1. **Infra lacking:** the corrected classifier
itself; a small table of Eng-cited examples with expected kinds.

### 3.4 Confluence / termination of diagram contraction on correct diagrams

Eng §49.35–49.36: contraction terminates and is confluent on correct diagrams.
**Experiment:** randomised diagram generation + check all contraction orders
reach the same actualisation. **Infra lacking:** a contraction-order-permuting
harness over `diagram.rs`; currently only one actualisation path
(`underlying_problem` → single `unify`) is exercised, so confluence is
*assumed*, not *observed*.

### 3.5 Multiset semantics for stars/constellations

Lower priority; needed before any ω-weight (`docs/eng-digest-ch12-13` §79.8) or
star-multiplicity result. **Infra lacking:** a multiset wrapper or canonical
multiset key for constellations (the `Vec`→multiset bridge).

---

## 4. Summary table

| Concept | Status | Cite | Divergence |
|---|---|---|---|
| Rays (FO terms) | implemented | `term.rs:210`, `polarised.rs:13` | colour⊂polarity (§2.1) |
| `\|·\|` underlying | implemented | `polarised.rs:123` | — |
| `op(f)` opposite | implemented | `term.rs:188` | — |
| Stars | implemented | `constellation.rs:12` | Vec≠multiset (§2.2) |
| Constellations | implemented | `constellation.rs:42` | finite type; ∞ via freshening |
| Fusion / MGU | implemented | `unify.rs:62`, `diagram.rs:156` | faithful |
| Martelli–Montanari rules | implemented | `unify.rs:72–157` | verbatim |
| Matchability `⋈` | implemented | `polarised.rs:173` | polarity-only `⊂` (§2.1) |
| Colours `colours(r)` | partial/divergent | `dep_graph.rs:18` | = polarity sign (§2.1) |
| Dependency graph `D[Φ;C]` | implemented | `dep_graph.rs:70` | `C` always full set |
| Objective/subjective/animist | divergent | `constellation.rs:26` | polarity census ≠ Eng colour-nesting (§2.1) |
| AEx | implemented | `execution.rs:319` | k-copy cap (acknowledged) |
| CEx | implemented | `concrete.rs` | — |
| IEx | implemented | `interactive.rs` | — |
| Saturated/Correct/Connected | implemented | `diagram.rs:150`, `execution.rs:158` | — |
| Normal form `Ex` | implemented | `execution.rs`, `arith.rs:207` | fuel-bounded SN |
| §4.5 Horn-add milestone | implemented (passing) | `arith.rs:97,207` | — |
| Idempotence metatheorem (§49.55/57) | design-doc-only | `docs/00` §4.4 | not certified; would need §2.1 fix |
| `Ex_C` proper-subset colour | absent (no-op) | `interactive.rs:320` | structurally dead |
| Anti-unification (lgg) | implemented (extension) | `antiunify.rs:52` | out of core scope; faithful |
