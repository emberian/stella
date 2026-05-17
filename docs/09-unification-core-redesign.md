# 09 — Unification-Core Redesign (near-linear unifier + first-class faithfulness instrument)

Status of tags: **[Built]** = exists in tree now; **[Spec]** = to be implemented
to this design; **[Proto]** = prototype-is-spec (beyond Eng, marked).

This document is a read-only design. No code was changed. It is written to let
implementation start cold.

---

## 0. Problem statement and measured facts (cite)

`STELLA_KS_PROF=1` on the galaxy Φ=405 reduction (`interactive.rs:849-868`,
`ks_report` at `interactive.rs:1109-1127`):

- `fuse ≈ 82%` of wall, of which **`unify ≈ 53%` of total**, `subst ≈ 5%`,
  `find ≈ 15%`, `freshen ≈ 3%`. [Built measurement]
- `unify` is timed at `interactive.rs:465-467` (`T_UNIFY` around the single
  `unify(vec![Equation::new(r1,r2)])` call in `fuse_theta`).

Root cause is `unify_with` in `crates/stella-core/src/unify.rs:62-168`,
textbook Robinson driven as Martelli–Montanari:

- On every variable binding (Replace, `unify.rs:84-111`) it eagerly
  `binding.apply`s across the **entire remaining worklist** (`unify.rs:100-107`).
  O(n²) in worklist length, allocation-heavy: `Substitution::apply`
  (`subst.rs:47-67`) rebuilds spines.
- It calls **uncached `t.vars()`** (full term walk, `term.rs:369-383`) 3–4×
  per equation: occurs-check `t.vars()` (`unify.rs:87`), the
  `x_in_p` scan calling `e.lhs.vars()`/`e.rhs.vars()` for every other equation
  (`unify.rs:95-98`), and the solved-form `rhs_vars` pass (`unify.rs:151`).
- Galaxy's δ-bodies are large terms; both factors compound.

The `ground:bool` per-node cache + `term::is_ground` short-circuit in
`Substitution::apply` (`subst.rs:48-54`, `term.rs:250/267-274/313-315`,
commit 7138e3f) already landed and is kept. It cut `subst` to 5%; subst is
**not** the lever. The lever is the unifier.

The unifier is generic over `Compatible` (`unify.rs:42-54`,
`unify_with<C: Compatible>` at `unify.rs:62`). The hot path passes
`StdCompat` via `unify` (`unify.rs:171-173`) on the **underlying terms**
(`fuse_theta` calls `underlying_term` at `interactive.rs:463-464`, which
strips polarity to `Polarity::Neutral`, `polarised.rs:117-132`). `matchable`
(`polarised.rs:173-183`) uses `PolarisedCompat` (`polarised.rs:95-111`) via
`alpha_unify_with` for the *decision* in `find`; that decision path already
has a near-linear substitution-free analogue `matchable_fast`
(`polarised.rs:186-276`) gated by `matchable_fast_equiv_matchable_fuzz`
(`polarised.rs:319-334`). **This redesign is the `matchable_fast` move done
for the substitution-producing `fuse` path.**

### Invariant (state once, hold throughout)

The term store is hash-consed + immutable behind `RwLock<TermStore>`
(`term.rs:241-308`, append-only `vec`/`map`/`ground`). The new unifier
**must not** mutate interned nodes. All union-find / triangular state lives
in a **separate mutable substitution layer keyed by `Var`**; interned
`TermId`s are read-only inputs and the produced `Substitution`
(`subst.rs:22-23`, `FxHashMap<Var,TermId>`) is the only mutable output. UF
parent links are `Var → (Var | TermId)`, never a rewrite of a `TermData`.

---

## A. The faithfulness instrument (the linchpin — designed first)

A **separate result-compatibility validator**, not part of the unifier and
not invoked by it. The unifier could be arbitrarily wrong; the validator's
job is to *catch* that against the reference oracle.

### A.1 Decision-only predicate

```
psi_compatible(ref: &[Star], fast: &[Star]) -> bool          // constellation level
star_set_compatible(ref: &[Star], fast: &[Star]) -> bool     // (alias / same thing)
stars_alpha_equiv(s1: &Star, s2: &Star) -> bool              // [Built] execution.rs:948
```

`psi_compatible` returns **yes/no only**. No equivalence witness (no MGU, no
renaming map, no diff) is constructed or retained. This matters: a witness
would be (a) expensive, (b) a second thing to keep faithful. The whole point
is a cheap proven *decision*.

### A.2 Mechanism — a normalization pass

`psi_compatible(ref, fast)`:

1. `rv = conceal_and_filter(ref)`, `fv = conceal_and_filter(fast)`
   — the ɟ-concealed *visible answer set*: drop every star with any coloured
   ray, then drop empty stars. **[Built]** `concrete.rs:155-179`
   (`conceal` §49.44 / `noise_filter` §49.46), re-exported
   `interactive.rs:1173`. This is exactly what `iex_tabled_result_eq_iex`
   (`interactive.rs:1509-1518`) and `evaluate.rs:183-184` already do.
2. α-canonicalize each visible star. The existing differential gates use
   `stars_alpha_equiv` (`execution.rs:948-…`, an O(n!)-permutation α-match
   over ray order). For the validator we **strengthen the per-star key** to
   `antiunify::canonical` of the star reified as one term:
   `canonical(mk_app_str("⋆star", star.clone()))` — exactly the existing
   `star_key` at `interactive.rs:1019-1021`. `canonical`
   (`antiunify.rs:31-56`) renumbers every variable to `Var::Idx(0,1,2,…)` in
   first-occurrence pre-order; α-equivalent terms ⇒ **identical hash-consed
   `TermId`** ⇒ O(1) compare thereafter (`antiunify.rs:48-56`).
3. Structural **mutual-set** compare: build multisets
   `Rk = { canonical(⋆star sᵢ) | sᵢ ∈ rv }`, `Fk` likewise for `fv`; return
   `Rk == Fk` as **multisets** (sorted `Vec<TermId>` equality, or
   `Counter<TermId>` equality).

### A.3 Definition of "compatible" and what it ignores

`ref` and `fast` are **ψ-compatible** iff their ɟ-concealed visible answer
sets are equal as multisets of α-canonical stars.

Deliberately ignored (by construction, argued):

- **Variable names / identities**: `canonical` collapses all α-variants to
  one `TermId` (`antiunify.rs:48-61`, `alpha_eq` test
  `antiunify.rs:441-453`). Result-equivalence under the SAME compatibility
  predicate permits MGUs that differ only by renaming.
- **ɟ-concealed scaffolding**: `conceal` removes every star with a coloured
  ray (`concrete.rs:155-164`); intermediate machine/colour stars never enter
  the comparison — only logician-visible answers.
- **Star / answer order**: multiset compare; constellation order and ray
  order within a star do not matter (ray order is folded into the per-star
  `canonical` because `⋆star` wraps the ray list — note ray order *is*
  significant inside one star key; see Risk G.3).

### A.4 Soundness argument

Claim: `psi_compatible` has **no false "compatible"** — if the reference and
the fast result denote different visible answer sets, it returns `false`.

- `conceal_and_filter` is a deterministic pure function applied identically
  to both sides (`concrete.rs:177-179`); it cannot mask a divergence that is
  in the visible (uncoloured) fragment, and divergences in the *concealed*
  fragment are by definition not observable answers (§49.44 — concealing is
  the spec-level answer-extraction operator; the engine's own correctness
  contract is stated over `↨♭ IEx`, `interactive.rs:1183-1206`).
- `canonical` is a *complete and sound* α-invariant: `canonical(s)==canonical(t)`
  **iff** `s,t` are α-equivalent (`antiunify.rs:48-61`; tested
  `antiunify.rs:441-453` including the negative `f(X,Y) ≠ f(X,X)` sharing
  case). So two stars compare equal **iff** they are genuinely α-equal — no
  conflation of structurally different stars (this is also why `star_key`
  was already chosen sound for tabling, `interactive.rs:1015-1021`).
- Multiset equality catches *count* divergence (a missing or duplicated
  answer), not only *set* divergence — strictly stronger than the
  `subset ∧ subset` test in `iex_tabled_result_eq_iex`
  (`interactive.rs:1513-1517`) and `evaluate.rs:185-189`, which cannot see a
  duplicated answer. (Adopting multiset compare is a deliberate
  strengthening; see D and Risk G.5.)

The validator can still return `false` on a result that is "morally fine but
differently shaped" only if the shape difference survives conceal+canonical —
i.e. a genuine difference in the visible answer multiset. That is exactly the
contract: it is conservative toward **catching**, never toward **passing**.

### A.5 Standing differential corpus harness

Pure ⇒ `#[test]`-driven. The standing gate that **replaces byte-identical
`iex_eq_iex_fast`** (`interactive.rs:1456-1499`) for the accelerated tier:

```
#[test] fn iex_fast_result_eq_iex()         // per corpus: psi_compatible(iex, iex_fast)
```

Corpora (reuse the exact ones already in tree so the new gate is a drop-in):

- **Horn add** — `add_prog()` + `add(3,2)` query (`interactive.rs:1462-1473`,
  `evaluate.rs:328-342`).
- **Combinator SKK = I** — `combinator::machine_stars()` + STTx
  (`interactive.rs:1475-1487`, `evaluate.rs:345-355`).
- **binarith add(5,6)** — `binarith::binarith_module()`
  (`interactive.rs:1489-1498`, `evaluate.rs:358-368`).
- **galaxy entry** — one representative galaxy Φ reduction (the Φ=405 run, or
  a smaller deterministic galaxy query if the full run is too slow for a unit
  test; gate the full run behind `#[ignore]` + a `cargo test -- --ignored`
  perf lane). This corpus is new to the gate and is the one that actually
  exercises the large-term regime the redesign targets.

Property / fuzz layer (mirror `matchable_fast_equiv_matchable_fuzz`,
`polarised.rs:319-334`, including the deterministic dependency-free LCG
`polarised.rs:284-293`):

```
#[test] fn unify_fast_equiv_unify_fuzz()
```

For 20_000 random equation pairs over a small signature with deliberately
**shared variable names across the two sides** (stress α-disjointness exactly
as `polarised.rs:295-314` does): assert
`unify_fast(eqs).is_some() == unify(eqs).is_some()` and, when both succeed,
that applying each resulting θ to a probe term yields α-equal terms
(`alpha_eq`, `antiunify.rs:59-61`). This tests the unifier *directly*, below
the iex level, so a unifier bug is localized without an iex run.

Runtime reuse: `evaluate.rs` `differential_check` (`evaluate.rs:145-200`)
currently inlines the `conceal_and_filter` + `subset∧subset` criterion for
`Tier::Tabled` (`evaluate.rs:176-198`). It MUST be refactored to call the
**same** `psi_compatible` so the live sampled oracle
(`OracleMode`/`OracleStatus`, `evaluate.rs:62-104`,
`evaluate_with_accel:234-276`) and the unit gate use one definition. No new
oracle plumbing — `Tier::Fast`'s byte-identity leg (`evaluate.rs:155-175`)
is replaced by `psi_compatible` once the fast tier is the new unifier (see C).

### A.6 Bootstrap — Stage 0: validate the validator *before* the new unifier

Today `iex` and `iex_fast` are **byte-identical** (`iex_eq_iex_fast`,
`interactive.rs:1460-1499`; `iex_fast` is documented byte-identical
`interactive.rs:939-955`). So before any new unifier exists we can pin the
validator against ground truth:

**Bootstrap test B0a — must PASS (true ⇒ compatible).**
For each corpus: `assert!(psi_compatible(&iex(...).psi, &iex_fast(...).psi))`.
Because the two are byte-identical here, conceal+canonical+multiset MUST
return true. If it returns false, the validator is broken (over-strict) and
must be fixed before proceeding.

**Bootstrap test B0b — must catch a perturbation (Goodhart guard).**
Reuse the KG7 Goodhart-perturbation pattern verbatim
(`evaluate.rs:408-477`, `goodhart_guard_oracle_catches_unfaithful_fast_path`):
take a real faithful `iex` result, then forge a wrong-but-plausible result:

- push an extra **all-neutral** star (survives conceal+filter as a spurious
  visible answer): `forged.push(vec![app("BOGUS", vec![cst("0")])])` —
  exactly `evaluate.rs:422-423`. Assert `!psi_compatible(&real, &forged)`.
- drop a visible answer star from `fast`: assert `!psi_compatible`.
- duplicate a visible answer star in `fast` (the multiset-specific case the
  old subset∧subset test would have *missed*): assert `!psi_compatible` —
  this is the test that justifies the multiset strengthening (A.4, D).
- α-rename a visible answer (must still be **compatible** — proves the
  validator ignores variable names): assert `psi_compatible` true.
- structurally perturb one visible answer (`s(0)` → `s(s(0))`): assert
  `!psi_compatible`.

Only after B0a and B0b are green do we have a *proven* checker. Every later
stage's correctness falsifier is "B0a-style: validator still passes on the
corpus" + "B0b-style: a deliberately-wrong unifier is caught".

---

## B. The new unifier `[Spec]`

`crates/stella-core/src/unify_fast.rs` (new module; `unify.rs` untouched —
it stays the spec oracle, `unify.rs:62-173`).

### B.1 Signature (Compatible-generic, like the reference)

```rust
pub fn unify_fast_with<C: Compatible>(
    equations: Vec<Equation>, compat: &C,
) -> Option<Substitution>;
pub fn unify_fast(equations: Vec<Equation>) -> Option<Substitution>
    { unify_fast_with(equations, &StdCompat) }
```

Same shape as `unify_with`/`unify` (`unify.rs:62,171`). It MUST preserve the
exact `Compatible` semantics: `App` nodes unify their heads via
`compat.compatible(f,g)` (NOT `f==g`) and require equal arity — identical to
the reference Open rule (`unify.rs:113-131`) and to `matchable_fast`'s App
case (`polarised.rs:252-259`). For the hot `fuse` path `compat = StdCompat`
on `underlying_term`s; the polarised-α semantics live where `PolarisedCompat`
is passed (the `find` path already has `matchable_fast`), but keeping the
generic means the new unifier is a strict superset and the differential fuzz
can exercise both `StdCompat` and `PolarisedCompat`.

### B.2 Data structures (UF over `Var`, triangular substitution)

A single mutable `Solver` (dropped when `unify_fast_with` returns):

```rust
enum Bound { Var(Var), Term(TermId) }      // UF parent: a Var or a non-var term
struct Solver {
    parent: FxHashMap<Var, Bound>,         // triangular store + UF links
    // optional: rank/size for union-by-rank
}
```

- **`resolve(t: TermId) -> TermId`**: if `t` is `App` return `t` as-is
  (structure is read from the immutable store, never copied for resolution).
  If `t` is `Var(v)`, walk `parent` with **path compression**: follow
  `Bound::Var` chains, compressing each hop to point at the representative;
  stop at an unbound var (return `mk_var_interned(rep)`) or a `Bound::Term`
  (return that `TermId`, *not* recursively substituted — triangular: bindings
  are shallow). This is the `mf_walk` shape (`polarised.rs:212-223`) extended
  with compression and a term sink.
- **`bind(v, b)`**: `parent.insert(v, b)`. Union for var=var picks a
  representative (union-by-rank optional; correctness does not need it,
  near-linearity wants it — see B.5).

This is **triangular** substitution: bindings are not eagerly applied to each
other (no `Substitution::compose`, no worklist re-application — the O(n²)
killer `unify.rs:100-108` is *gone*). Resolution is lazy via UF walk.

### B.3 Algorithm (one explicit recursive `unify1`)

```
unify1(a, b):
  a = resolve(a); b = resolve(b)
  if a == b: return Ok            // Clear, O(1) hash-cons id compare
  match (get(a), get(b)):
    (Var x, Var y):  union(x, y); Ok          // bind one rep to the other
    (Var x, _):      occurs_guarded_bind(x, b)
    (_, Var y):      occurs_guarded_bind(y, a) // Orient folded in
    (App f fa, App g ga):                       // Open
        if !compat.compatible(f, g): return Err
        if fa.len() != ga.len():     return Err
        for (fi, gi) in fa.zip(ga): unify1(fi, gi)?   // structural recursion
    _: Err
```

Driven over the input equations: `for eq in equations { unify1(eq.lhs, eq.rhs)? }`.
Note inputs are at most a single equation in the hot path
(`fuse_theta`/`self_interact_theta` build `vec![Equation::new(r1,r2)]`,
`interactive.rs:466,507`), but the API stays vector-general for the fuzz and
for `alpha_unify_with` reuse (`alpha.rs:11-22`).

Recursion depth = term depth. Galaxy terms are deep; convert to an explicit
work stack `Vec<(TermId,TermId)>` to avoid native stack overflow (the
reference recurses through `vars()`/`apply` anyway, but the new path should
be iterative for the large-term regime — this is the same shape as
`mf_unify` made iterative).

### B.4 The occurs-check decision (the key design choice — argued)

Three candidates:

1. **Incremental occurs-check at bind time** (what the reference does,
   `unify.rs:87-92`; what `matchable_fast` does, `mf_occurs`
   `polarised.rs:225-231`): before `bind(x, t)`, walk `resolve`d `t` looking
   for `x`. Cost: O(size of resolved t) per bind. Under triangular bindings
   the resolved term can re-expand previously-bound subterms ⇒ worst-case
   reintroduces super-linear blow-up on pathological sharing
   (the classic exponential-occurs term).
2. **Stamped-DFS occurs-check**: per-bind DFS but memoize "this `TermId`
   subtree is `x`-free" with an epoch stamp so shared subterms are visited
   once. With hash-consed `TermId`s a visited-set keyed by `TermId` is
   natural and the store is immutable so a subtree's variable content is
   stable. Cost: O(distinct subterms seen) per bind, amortized by the
   `varsig` skip from E.
3. **Deferred / post-pass occurs-check** (Martelli–Montanari "solved-form
   acyclicity check"): never occurs-check at bind time; allow the triangular
   store to become cyclic; after all equations are processed, run **one**
   pass that detects a cycle in the `Var → term` graph (a DFS with a
   greyset / Tarjan-style), failing the unification iff a variable reaches
   itself. This is the standard near-linear approach (Paterson–Wegman /
   Martelli–Montanari almost-linear): bind is O(1), the single acyclicity
   pass is O(total term size of the triangular store) once.

**Decision: (3) deferred post-pass occurs-check, with (2)'s stamping reused
as the post-pass's own visited-memo.**

Rationale:

- The measured pathology is **eager work per binding** (`unify.rs:100-108`
  re-apply; `unify.rs:95-98` `x_in_p` scan). (1) keeps a per-bind walk; even
  if each walk is cheap, galaxy does many binds against large terms ⇒ it is
  the same shape of cost we are removing. Choosing (1) would leave a residual
  super-linear term on adversarial sharing.
- (3) makes `bind` strictly O(1) (the property that makes the whole unifier
  near-linear) and pays occurs **once** over the final store, where the
  `varsig`/`size` metadata from E lets the DFS skip whole subtrees that
  contain none of the bound variables — so the post-pass is ~O(store size
  touched), not O(store size).
- Soundness: a cyclic triangular store ⇔ a non-unifiable occurs-failure
  (`X = f(X)` ⇒ `X`'s rep reaches itself). The post-pass detects exactly
  this. It is the reference's occur-check `unify.rs:90-92` + solved-form
  acyclicity check `unify.rs:139-157` collapsed into one acyclicity pass —
  **same accept/reject set**, proven equivalent by the differential fuzz
  (A.5) and the `unify` oracle.
- Risk of (3): an *intermediate* cyclic store could, if the recursion
  dereferenced through a cycle before the post-pass, loop forever. Mitigation
  (mandatory): `resolve` is iterative with path compression and **never
  dereferences a `Bound::Term`'s internal structure** (triangular: it returns
  the bound `TermId` shallowly). `unify1` only recurses into `App` args of
  *resolved* terms; a var→var cycle is collapsed by union (a representative
  has no self-parent by union-find invariant); a var→term cycle
  (`X↦f(X)`) cannot cause non-termination because `unify1` recurses on the
  *term's* args, and re-encountering `X` just `resolve`s to `f(X)` again and
  recurses one structural level — bounded by the **finite** set of distinct
  hash-consed subterms, so it terminates and the cycle is then reported by
  the post-pass. (If we want a belt-and-suspenders guarantee, keep a small
  per-call recursion-budget = total input term size × 2; exceeding it ⇒ treat
  as occurs-fail. The differential oracle would catch any wrong rejection.)

### B.5 Complexity

- `resolve` with path compression + union-by-rank: amortized near-O(α(n))
  per call (inverse Ackermann), n = number of distinct vars.
- `unify1` over structure: each pair of hash-consed subterms is visited O(1)
  times; with a `(TermId,TermId)`-keyed visited memo (the canonical "unify
  DAGs in near-linear time" trick — same store immutability that makes
  `canonical`/`star_key` O(1) afterwards) the structural traversal is
  ~O(#distinct subterm pairs), not O(tree size).
- Occurs post-pass: one DFS over the triangular store, `varsig`-pruned (E).
- Net: **near-linear** in total input term size, vs the reference's O(n²)+
  worklist re-application. This is the same algorithmic move `matchable_fast`
  made for the decision-only `find` path (`polarised.rs:186-201` header), now
  for the substitution-producing `fuse` path.

### B.6 Producing a `Substitution` the existing consumers accept

The consumers are `fuse_theta`/`self_interact_theta`
(`interactive.rs:457-516`): they take `theta: Substitution` and call
`theta.apply(r)` (`subst.rs:47-67`) on each remaining ray. They need a
**fully-resolved (idempotent) `Substitution`**, because the reference returns
the composed solved-form substitution (`unify.rs:159-167`) and `apply` does a
single non-recursive pass over the map (`subst.rs:55-66` — it does *not*
chase chains; it relies on θ being idempotent).

So after a successful solve, **materialize** the triangular store into a flat
idempotent `Substitution`:

```
for v in parent.keys():
    let r = deep_resolve(v)   // resolve v, then recursively resolve every
                              // var inside the result until fixpoint
    if r != mk_var_interned(v): out.insert(v, r)
```

`deep_resolve` is the only place chains are fully expanded — once, at the
end, over the (now acyclic, post-pass-verified) store. This is the moral
equivalent of the reference's final
`Substitution::compose(&solved_subst,&sigma)` (`unify.rs:159-167`) but
computed once from the UF store instead of incrementally. Cost is bounded by
the materialized substitution size; `is_ground`/`varsig` skips ground
subtrees (E). The resulting `Substitution` is `subst.rs:22-23`'s exact type
⇒ `fuse_theta`'s `theta.apply` (`interactive.rs:475-483`) is unchanged.

Equivalence to the reference is **result-equivalence under the same
`Compatible`**: `unify_fast(E)` succeeds iff `unify(E)` succeeds, and on
success `unify_fast(E)(t) =α unify(E)(t)` for all `t` (both are MGUs of `E`;
MGU is unique up to α, §B.2.6, `unify.rs:14-16`). The α-slack is *exactly*
what `psi_compatible` (A) is built to tolerate and what byte-identity could
not. `unify` (`unify.rs:171`) is the differential oracle for `unify_fast`.

---

## C. The integration crux (resolved explicitly)

`fuse_theta` (`interactive.rs:457-488`) and `self_interact_theta`
(`interactive.rs:504-516`) both call `unify(...)`
(`interactive.rs:466,507`). They are **shared** by the reference `iex`
(via `fuse`/`self_interact` → `interaction_step`, `interactive.rs:451-453,
499-501, 568-580`) and by the accelerated `iex_fast`/`iex_tabled`
(via `produce_stars_fast`, `interactive.rs:905,913`,
`is_normal_form_accel` → `iex_fast_inner`). If we simply swap `unify` →
`unify_fast` inside `fuse_theta`, the **reference path would also use the
fast unifier**, destroying the oracle. Must not happen.

### Call-site inventory

| caller | line | tier | unifier today |
|---|---|---|---|
| `fuse_theta` → `fuse` → `interaction_step` (1568) | 466 | reference `iex` | `unify` |
| `self_interact_theta` → `self_interact` → `interaction_step` (1577) | 507 | reference `iex` | `unify` |
| `fuse` (1568) and `self_interact` (1577) **also reached from** `step_at` (1156) | — | UI driver | `unify` |
| `produce_stars_fast` → `fuse` (905) | 466 (via fuse) | `iex_fast`/`iex_tabled` | `unify` |
| `produce_stars_fast` → `self_interact` (913) | 507 | `iex_fast`/`iex_tabled` | `unify` |
| `alpha_unify_with` → `unify_with` (`alpha.rs:21`) | — | `matchable` (find) | reference; **leave as-is** (decision path has `matchable_fast`) |

### Minimal seam: thread a unifier strategy through the fast pipeline only

Introduce a zero-cost strategy enum used **only** by the fast produce path:

```rust
#[derive(Clone, Copy)]
enum Unifier { Ref, Fast }

fn fuse_theta_u(phi1, j, phi2_renamed, j_prime, u: Unifier) -> Option<(Star, Substitution)> {
    // identical to today, except:
    let theta = match u {
        Unifier::Ref  => unify(vec![Equation::new(r1, r2)]),
        Unifier::Fast => unify_fast(vec![Equation::new(r1, r2)]),
    };
    // ... unchanged subst/apply tail ...
}
fn self_interact_theta_u(star, j, j_prime, u: Unifier) -> Option<(Star, Substitution)> { /* same */ }
```

- `fuse_theta` / `self_interact_theta` keep their current signatures and call
  `*_u(.., Unifier::Ref)` — so **every reference-`iex` path and `step_at` are
  byte-for-byte unchanged** and keep using `unify` (`unify.rs:171`).
- `produce_stars_fast` (`interactive.rs:882-919`) is changed to call
  `fuse_theta_u(.., Unifier::Fast)` / `self_interact_theta_u(.., Unifier::Fast)`
  directly (it currently calls `fuse`/`self_interact` at
  `interactive.rs:905,913`; route those two call sites — and *only* those —
  through the `Fast` variant). Equivalently: add `fuse_fast`/`self_interact_fast`
  wrappers that pin `Unifier::Fast` and have `produce_stars_fast` call them.

The reference `unify` (`unify.rs:62-173`) is **never** reachable from the
`Fast` variant and `unify_fast` is **never** reachable from `iex`. The seam
is exactly two call sites in `produce_stars_fast`; no other code path
changes. `evaluate.rs`'s `iex_fast_with_accel`/`iex_tabled_with_accel`
(`evaluate.rs:44,246-247`) inherit `Fast` automatically because they go
through `iex_fast_inner`/`produce_stars_fast`.

(Alternative considered and rejected: a thread-local "use fast unifier" flag.
Rejected — it would couple to reference `iex` if `evaluate.rs` runs the
oracle on the same thread between the fast and reference runs
(`evaluate.rs:246,252`), reintroducing exactly the contamination we must
forbid. The strategy parameter is statically un-contaminable.)

---

## D. What existing gates / scaffolding change

### D.1 `iex_eq_iex_fast` → result-equivalence gate

`iex_eq_iex_fast` (`interactive.rs:1460-1499`) currently asserts
`a.psi == b.psi`, `a.is_normal_form == b.is_normal_form`, `a.steps == b.steps`
(byte-identity) across Horn / combinator / binarith. Under the new unifier,
`iex_fast`'s θ is α-equivalent but **not** byte-identical to reference
(different fresh `Var` choices in the materialized substitution), so
`a.psi == b.psi` will legitimately fail.

It becomes `iex_fast_result_eq_iex` (A.5): for each corpus
`assert!(psi_compatible(&iex(...).psi, &iex_fast(...).psi))`, plus a true-NF
assertion (`iex_fast` must still reach a genuine normal form, like
`iex_tabled_result_eq_iex` asserts `t.is_normal_form`,
`interactive.rs:1525,1539`). `steps` is **no longer asserted equal** (the new
unifier does not change *which* redex is selected — `find`/`mat` are
untouched — so step count will in practice still match, but the gate must not
*require* it, mirroring `iex_tabled`'s contract `interactive.rs:1501-1509`).

### D.2 Byte-identity-only scaffolding that can be REMOVED/simplified

These exist **solely** to keep `iex_fast` byte-identical to reference `iex`;
under result-equivalence they are dead weight and their removal is a net
simplification (and a small perf win):

1. **The per-fusion `*counter += 1` parity hack** in `produce_stars_fast`,
   `interactive.rs:895-902`:
   ```
   // Reference parity: the old scheme consumed one `counter` slot for
   // the (now-unused) per-fusion prefix before the per-var slots.
   // Keep it so the fast path's `Var::Idx` numbering is byte-identical
   *counter += 1;
   alpha_rename_star_fast(&phi[ik], counter)
   ```
   The `*counter += 1` (`interactive.rs:900`) only exists to reproduce the
   reference's `format!("ext{ik}_{counter}"); *counter += 1`
   (`interactive.rs:562-564`) slot consumption so `Var::Idx` numbers line up
   byte-for-byte. Under `psi_compatible` (α-insensitive) the absolute
   `Var::Idx` values are irrelevant ⇒ **delete the `*counter += 1`**; freshen
   only needs to keep stars variable-disjoint, which `alpha_rename_star_fast`
   (`interactive.rs:181-187`) already guarantees by monotone `counter`.
2. **`alpha_rename_star` vs `alpha_rename_star_fast` duplication**
   (`interactive.rs:165-187`): `alpha_rename_star_fast` exists as the
   "same `Var::Idx` assignment … byte-identical residual stars (N-KS gate)"
   hot path that drops the `Substitution`. Once byte-identity is not required,
   the only remaining reason to keep both is that the cold
   `step_detail`/`render_theta` path wants the `Substitution`
   (`interactive.rs:163-164`, `render_theta` `interactive.rs:595-…`). That
   reason still holds, so **keep both** but drop any comment/contract language
   asserting byte-identical numbering vs reference (it is no longer a
   guarantee we owe). [Net: documentation simplification, not deletion.]
3. The `freshen_star` string-prefix path (`interactive.rs:95-102`,
   `format!("f{}", *counter)`, `*counter += *counter/10 + 1`) is only used by
   reference-side renaming; it is **not** byte-identity scaffolding vs the
   fast path and is **not** removed here (it belongs to the reference oracle
   which stays untouched). Listed for completeness so it is not mistaken for
   parity scaffolding.

Concretely the only **deletion** is item 1 (`interactive.rs:900`, one line +
its 4-line parity comment `interactive.rs:896-899`). Small, but it removes a
correctness-coupling between the two tiers, which is the real win.

### D.3 Status of the other gates

- **`mat_accel_eq_mat_ref`** (`interactive.rs:1440-1454`): unaffected. It
  gates `mat_phi_c_accel == mat_phi_c` — the *find* path, which this redesign
  does not touch. **Keep as byte-identical.**
- **`iex_tabled_result_eq_iex`** (`interactive.rs:1508-1544`): already
  result-equivalence-based; it should be refactored to call `psi_compatible`
  (its inline `conceal_and_filter` + `subset∧subset`,
  `interactive.rs:1510-1518`, is the *weaker* set-only criterion). After
  refactor it strengthens to multiset compare for free. **Keep, retarget onto
  `psi_compatible`.**
- **`iex_fast_with_accel_eq_iex_fast`** (`interactive.rs:1550-…`): asserts
  `iex_fast_with_accel` byte-identical to per-call `iex_fast`. This is a
  *fast-vs-fast* reuse contract (`IexAccel` is a pure function of Φ), **not**
  fast-vs-reference. Both sides use the same (new) unifier with the same
  determinism ⇒ they remain byte-identical to each other. **Keep
  byte-identical** (it is not coupled to the reference).
- **`matchable_fast_equiv_matchable_fuzz`** (`polarised.rs:319-334`):
  untouched (different subsystem; the decision-path analogue).

---

## E. Cached node metadata `[Spec]` (extends the [Built] `ground` cache)

`TermStore` already carries `ground: Vec<bool>` computed O(1) bottom-up at
intern (`term.rs:250,267-274`). Add two more parallel `Vec`s, same pattern,
same `intern` site (`term.rs:262-277`):

- **`size: Vec<u32>`** — `Var ⇒ 1`; `App(_, args) ⇒ 1 + Σ size[arg]`
  (saturating). O(1) at intern because args are interned first
  (`term.rs:269-271` already relies on this ordering for `ground`).
- **`varsig: Vec<u64>`** — a Bloom-filter bitmask of the `Var` keys in the
  subtree. `Var ⇒ 1u64 << (hash(var) & 63)`; `App ⇒ OR of args' varsig`
  (`Var::Idx(n)`/`Var::Named(spur)` both hash cheaply). O(1) at intern.
  `varsig == 0` ⇔ `ground` (consistency check / debug-assert).

Public accessors mirroring `is_ground` (`term.rs:313-315`):
`pub fn term_size(id) -> u32`, `pub fn term_varsig(id) -> u64`.

Uses:

- **`unify_fast` occurs post-pass (B.4)**: the DFS over the triangular store
  computes a `u64` mask of the bound-variable domain; any subtree whose
  `varsig & domain_mask == 0` is provably free of every bound variable ⇒
  **skip it whole** (no false negative: Bloom is conservative *toward
  visiting*, never toward skipping a present var — a present var always sets
  its bit). Turns the occurs pass from O(store) to O(store touched).
- **`Substitution::apply` (`subst.rs:47-67`)**: the existing `is_ground`
  short-circuit (`subst.rs:52`) generalizes: if
  `term_varsig(id) & subst_domain_mask == 0`, θ cannot touch this subtree ⇒
  return `id` (O(1)), even when `id` is non-ground. This further shrinks the
  5% `subst` slice. The caller (`fuse_theta`, `interactive.rs:475-483`) would
  precompute `subst_domain_mask` once from `theta.0.keys()`. (Optional —
  subst is not the lever; include only if cheap.)
- **`canonical`/`star_key`** could use `size` to short-circuit, but they are
  not hot here; out of scope.

### E.1 The `RwLock<TermStore>` per-node get+clone constant factor — assess

`get` (`term.rs:306-308`) takes a shared read lock and clones the
`TermData` (`Arc` bump for App args, `term.rs:218-220` — O(1), no heap copy).
docs/07 §D names this "deepest residual constant factor (per-node RwLock),
pure-perf, pervasive" (`docs/07:283-284`) and `lock-free get / append-only
stable store (B3)`.

**Decision: defer it; do not address in this rework.** Rationale:

- It is a *constant factor on every node visit*, orthogonal to the O(n²) →
  near-linear algorithmic win that is the measured 53% lever. Folding a
  pervasive store-representation change (lock-free append-only, B3) into the
  unifier rework would (a) widen the blast radius across every module that
  calls `get`, (b) make the Stage-1 perf delta un-attributable (cannot tell
  if the win is the algorithm or the lock removal), violating the
  staged-falsifier discipline (F).
- The new unifier *reduces* the number of `get` calls super-linearly (no
  worklist re-application, no repeated `vars()` walks), so it independently
  shrinks the aggregate cost of this constant factor without touching it.
- B3 stays a separate parked item (docs/07 §D) with its own before/after.

---

## F. Staged plan (each stage: measurable falsifier + differential gate)

All perf measured with `STELLA_KS_PROF=1` on the **galaxy Φ=405** reduction
(`ks_report`, `interactive.rs:1109-1127`); the headline metric is the
**`unify` % of total** (today ≈53%).

### Stage 0 — the validator + its bootstrap (NO unifier yet)

- Build `psi_compatible` (A.1–A.3). Refactor `evaluate.rs:differential_check`
  (`evaluate.rs:145-200`) and `iex_tabled_result_eq_iex`
  (`interactive.rs:1508-1544`) to call it (behavior-preserving:
  set→multiset is a strengthening; the byte-identical corpora still pass).
- Land bootstrap tests B0a (must pass on byte-identical iex/iex_fast) and B0b
  (Goodhart-pattern, `evaluate.rs:408-477` style: missing / extra /
  **duplicated** / structurally-perturbed answer ⇒ `false`; α-rename ⇒
  `true`).
- **Falsifier**: B0a false on any corpus ⇒ validator over-strict, fix before
  proceeding. B0b: any perturbation that passes ⇒ validator unsound, blocker.
- **Gate**: full existing test suite still green (no behavior change yet).
- Perf: none expected (no hot-path change).

### Stage 1 — new unifier behind the fast tier, validator-gated

- Land `unify_fast` (B). Add the `Unifier::{Ref,Fast}` seam (C); route only
  `produce_stars_fast`'s two call sites to `Fast`.
- Replace `iex_eq_iex_fast` with `iex_fast_result_eq_iex` (D.1) over Horn /
  combinator / binarith / **galaxy entry**; add `unify_fast_equiv_unify_fuzz`
  (A.5, 20_000 cases, shared-var stress, both `StdCompat` and
  `PolarisedCompat`).
- **Correctness falsifier**: (i) `psi_compatible` must hold on every corpus
  vs reference `iex`; (ii) inject a deliberately-wrong `unify_fast` (e.g.
  skip the occurs post-pass, or `compat` → `f==g` instead of
  `compat.compatible`) and assert the gate **fails** (the validator catches
  it — this is the B0b contract applied to the real unifier).
- **Perf falsifier**: `STELLA_KS_PROF` on galaxy Φ=405 — `unify` % **must
  drop materially** (target: from ≈53% to a small fraction; minimal
  acceptance: `unify` no longer the single largest slice). If `unify` % does
  not drop, the algorithm did not deliver — revert, reassess.
- Live oracle: `evaluate.rs` with `OracleMode::Always` on all corpora, both
  tiers, reports `Faithful` (the `evaluate_always_faithful_*` test
  `evaluate.rs:382-401` retargeted onto `psi_compatible`).

### Stage 2 — remove byte-identity scaffolding

- Delete the `*counter += 1` parity hack + its comment (`interactive.rs:896-902`,
  D.2 item 1). Drop byte-identity language from `alpha_rename_star_fast`
  docs (D.2 item 2).
- **Falsifier**: `iex_fast_result_eq_iex` + `unify_fast_equiv_unify_fuzz`
  still green (removal changed only absolute `Var::Idx` numbering, which
  `psi_compatible` ignores by construction, A.3). If any gate flips, the
  removed scaffolding was load-bearing for something other than byte-identity
  — investigate before deleting.
- Perf: marginal (one fewer counter bump per fusion); not the point — the
  point is removing tier-coupling.

### Stage 3 — metadata / varsig

- Add `size`/`varsig` to `TermStore::intern` (E). Wire `varsig` pruning into
  the occurs post-pass; optionally into `Substitution::apply`.
- **Correctness falsifier**: all gates from Stage 1 still green (metadata is
  observationally inert — a conservative Bloom that only ever *adds*
  permission to skip a provably-irrelevant subtree; a debug-assert
  `varsig==0 ⇔ ground` guards the intern computation).
- **Perf falsifier**: `STELLA_KS_PROF` galaxy Φ=405 — the occurs post-pass /
  apply slices shrink further; net `fuse` % drops vs Stage 1. If no
  measurable improvement, the metadata is not earning its intern-time cost —
  keep only if neutral-or-better.

Each stage is independently revertable; each has a single dominant
falsifier (a gate test for correctness, a `KS-PROF` delta for perf).

---

## G. Honest risks / open questions

1. **UF vs immutable hash-cons interaction.** The UF/triangular store is a
   *side* map keyed by `Var` (B.2); it never mutates interned nodes, so the
   hash-cons invariant (`term.rs:241-308`) is preserved. The real subtlety is
   B.4's intermediate-cycle termination argument: it rests on "finitely many
   distinct hash-consed subterms ⇒ `unify1` revisiting a cycle terminates".
   This is believed correct (it is the standard DAG-unification argument) but
   is the part most worth a dedicated adversarial fuzz (deeply self-referential
   inputs: `X =? f(X)`, `X =? f(Y), Y =? f(X)`, and the exponential-occurs
   chain `Xₙ = f(Xₙ₋₁,Xₙ₋₁)`). The recursion-budget belt-and-suspenders
   (B.4) is the fallback; it must be sized so no *legitimate* galaxy term
   trips it (open: measure max legitimate `term_size` on galaxy and set
   budget well above it, e.g. 4×).

2. **Exact α / polarised-compat equivalence definition.** "Result-equivalent"
   is defined operationally as `psi_compatible` (A.3): equal ɟ-concealed
   visible answer multisets up to α. This is *narrower* than "the two MGUs
   are α-equal as substitutions" — we only compare *visible answers*, not
   intermediate θ. That is intentional (the spec contract is over `↨♭ IEx`,
   `interactive.rs:1183`) but it means a unifier that produced a *different
   but still-MGU* θ that happened to change a *concealed* (coloured)
   intermediate would pass — which is correct per spec, but is a weaker
   guarantee than byte-identity gave for the Eng-faithfulness story (see 4).
   The `unify_fast_equiv_unify_fuzz` direct-θ fuzz (A.5) mitigates by also
   checking θ α-equivalence *at the unifier level*, independent of conceal.

3. **Ray order inside a star.** `star_key`/`canonical` wraps the ray list in
   `⋆star(...)` (`interactive.rs:1019-1021`), so it is **ray-order-sensitive**
   within a star, while `stars_alpha_equiv` (`execution.rs:948-…`) tries all
   ray permutations. The new unifier does not reorder rays
   (`fuse_theta` preserves ray order, `interactive.rs:471-485`), so in
   practice keys still match — but if any future change reorders rays,
   `psi_compatible` would report a false divergence. Documented bound: the
   validator is sound (never false-passes) but *not maximally permissive* on
   ray permutation. If this bites, swap the per-star key to a
   permutation-canonical form (sorted multiset of per-ray `canonical`s) — a
   contained change isolated to A.2.

4. **Does dropping byte-identity lose something we want for the Eng
   faithfulness story?** Byte-identity was a very strong, very legible claim
   ("the jet is the interpreter, literally"). Result-equivalence is the
   honest claim for a *different* algorithm (you cannot get byte-identity from
   a different unifier; the fresh-var numbering alone differs). The
   verified-speculative-runtime framing (docs/07 §H, `docs/07:336-375`)
   already embraces this for `iex_tabled` (KA1 is explicitly
   result-equivalent, not byte-identical, `interactive.rs:1001-1010`). The
   redesign makes `iex_fast` join `iex_tabled` on the result-equivalence
   side of the line. The mitigation that preserves the story: the validator
   is *first-class, proven (Stage 0), multiset-strict, and run live*
   (`evaluate.rs` oracle) — "we don't just hope, we check every sampled run
   against the spec interpreter" is a defensible and arguably *stronger*
   faithfulness claim than "the bytes happened to match". This is a framing
   call the user should confirm (it is consistent with docs/07 §H but worth
   an explicit nod).

5. **Multiset strengthening vs the existing set-only criterion.** Adopting
   multiset compare (A.2/A.4) makes the new gate strictly stronger than the
   in-tree `subset∧subset` (`interactive.rs:1513-1517`,
   `evaluate.rs:185-189`). Risk: a *currently-passing* result that happens to
   produce a duplicated visible answer under reference `iex` but a deduped
   one under `iex_tabled` (KA1 *deliberately* drops α-variants,
   `interactive.rs:999-1010`) would now **fail** `psi_compatible` where it
   passed before. Open question: is reference `iex`'s visible answer set ever
   a genuine multiset with duplicates on the corpora? If yes, `Tier::Tabled`
   needs set-compare while `Tier::Fast`(new unifier) uses multiset-compare —
   i.e. the strengthening may not be uniformly applicable across tiers.
   **Resolution path**: in Stage 0, before refactoring `iex_tabled`'s gate,
   empirically check `conceal_and_filter(iex(...).psi)` for duplicate
   canonical stars on all corpora. If duplicates never occur, multiset == set
   there and the strengthening is free for both tiers. If they do, keep
   `psi_compatible` multiset for the new-unifier `Fast` tier and a
   `psi_compatible_setwise` variant for `Tabled`. This is the single most
   important thing to settle empirically in Stage 0.

6. **Perf of the validator itself, run live.** `psi_compatible` is
   `conceal_and_filter` (linear) + one `canonical` per visible star
   (`antiunify.rs:31-56`, linear in star size, hash-consed) + a sort/compare
   of `TermId`s (n log n in #visible stars). Cheap relative to a full `iex`
   re-run — but the live oracle *also* re-runs reference `iex`
   (`evaluate.rs:252`), which dominates. The validator cost is negligible
   next to that; sampling (`OracleMode::Sample(N)`, `evaluate.rs:64-73,
   203-215`) already bounds the re-run cost. No new perf concern from the
   validator; the concern (already known) is the oracle's `iex` re-run, which
   sampling addresses and which is out of scope here.

---

## Appendix — file:line index of every cited anchor

- Reference unifier (oracle, untouched): `unify.rs:62-173` (`unify_with`,
  Replace `84-111`, eager re-apply `100-108`, `x_in_p` `95-98`, occurs `87-92`,
  Open `113-131`, solved-form `139-157`, compose `159-167`, `unify` `171-173`).
- `Compatible`/`StdCompat`: `unify.rs:42-54`. `PolarisedCompat`:
  `polarised.rs:95-111`. `underlying_term`: `polarised.rs:117-132`.
- Decision-path near-linear precedent: `matchable_fast`
  `polarised.rs:186-276`; fuzz `polarised.rs:319-334`; LCG `284-293`;
  shared-var stress `295-314,336-345`.
- α-canonical: `antiunify.rs:31-61`; `alpha_eq` test `441-453`. `star_key`:
  `interactive.rs:1019-1021`.
- conceal/filter: `concrete.rs:155-179`; re-export `interactive.rs:1173`;
  iex*_concealed `interactive.rs:1183-1206`.
- `stars_alpha_equiv`: `execution.rs:948-…`.
- `Substitution`/`apply`/`compose`: `subst.rs:22-98` (apply `47-67`,
  is_ground short-circuit `48-54`). `freshen`: `subst.rs:200-209`.
- term store + metadata: `term.rs:241-308` (intern `262-277`, ground
  `250/267-274`, get `306-308`, `is_ground` `313-315`, Arc args `218-220`).
- fuse/self-interact: `interactive.rs:451-516` (`unify` calls `466,507`).
  produce_stars_fast `882-919` (parity hack `895-902`, fuse/self calls
  `905,913`). alpha_rename_star(_fast) `165-187`. freshen_star `95-102`.
  iex `801-842`; iex_fast `939-955`; iex_fast_inner `1023-1107`; ks_report
  `1109-1127`.
- gates: `iex_eq_iex_fast` `interactive.rs:1460-1499`;
  `iex_tabled_result_eq_iex` `1508-1544`; `mat_accel_eq_mat_ref` `1440-1454`;
  `iex_fast_with_accel_eq_iex_fast` `1550-…`.
- live oracle: `evaluate.rs` (`OracleMode/Status` `54-104`,
  `differential_check` `145-200`, `oracle_fires` `203-215`,
  `evaluate_with_accel` `234-276`, Goodhart guard `408-477`,
  faithful-all-corpora `382-401`).
- strategic frame: `docs/07:275-296` (§D parked items incl.
  triangular/union-find + B3), `docs/07:336-375` (§H verified speculative
  runtime).
