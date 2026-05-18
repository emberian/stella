# χ-existence theory — does any faithful constellation sustain non-idempotent subjective dynamics?

READ-ONLY deep-theory deliverable. Scope: derive (not guess) the structural
conditions under which Eng's §49.50 subjective-ray dynamics *sustain*
non-idempotence (the docs/08 "charge" χ), from §49.50–§49.61 mechanics and the
codebase's `subjective_stream`. Reference engine is the oracle; the answer is
honest even when it is "χ likely cannot exist faithfully."

Sources read: `refs/extracted/EngExegesis/doc.md` §49.45–§49.61, §62.5–§62.7;
`crates/stella-core/src/subjective.rs` (fuse_stars:180, mat_phi_full:229,
is_nf:274, find_gen_step:332, SubjectiveStream::next:727, gate_a test:1272);
`crates/stella-core/src/constellation.rs:81` (`ray_is_subjective`),
`:99` (`star_kind_eng`); `crates/stella-core/examples/chi_stage01_subjective.rs`;
docs/00 §4.4, docs/08 §4.5–§4.8, docs/16 §7.

---

## 1. Why the canonical §49.50 example is idempotent-fast

Eng's §49.50 worked example (`subjective.rs:1272`, fixture F1 in
`chi_stage01_subjective.rs:167`):

```
Φ  = { [X, +f(X)] }              objective supply star (star_kind_eng = Objective:
                                  X is a Var ⇒ ray_is_subjective(X)=false;
                                  +f(X) has no nested colour ⇒ objective, §48.9)
Ψ₀ = { [−f(+g(Z))] }             one star, one ray: −f with +g nested in its
                                  argument ⇒ ray_is_subjective = true (§48.7)
```

The single interaction along `−f(+g(Z)) ⋈ +f(X)` is, under PolarisedCompat
(`fuse_stars`, subjective.rs:180–201), `θ = {X ↦ +g(Z)}`, fusing
`[X,+f(X)]\{+f(X)}` ⊎ `[−f(+g(Z))]\{−f}` = `[+g(Z)]`. Measured:
`chi_stage01` F1 reaches NF at index 1, round 1; trajectory length 400 but
**distinct = 2**; the only whistle is span-1 (degenerate, not a χ-signal).

The structural reason it is transient — three independent properties, each
necessary, jointly sufficient for "idempotent-fast":

1. **The new ray is strictly less subjective than the redex (colour-depth
   decreases).** `ray_is_subjective` (constellation.rs:81–92) is true iff a
   coloured head has a colour *nested in an argument*. The §49.50 transform is
   `−f(+g(Z)) → +g(Z)`: it *peels one colour layer*. The seed ray has nesting
   depth 2 (`f` over `+g`); the product `+g(Z)` has the colour at the head and
   a **bare variable `Z`** as argument ⇒ `term_contains_colour(Z)=false` ⇒
   `ray_is_subjective(+g(Z)) = false`. The product is **objective**. §49.50's
   "new polarised ray" is born, but it is born *objective*. By §49.54/§49.55
   (Objective full evaluation ⇒ idempotence), an objective residue cannot
   generate a fresh matchable pair. χ requires the new ray to *re-enter* the
   subjective fragment; here it exits it on creation.

2. **The supply star is objective and linear-in-effect.** `Φ = {[X,+f(X)]}`:
   `+f(X)` matches `−f(...)` exactly once per round; consuming `[−f(...)]`
   leaves only `[+g(Z)]`, whose head colour `g` has *no `−g` anywhere* (Φ has
   no `g`-ray; `mat_phi_full`, subjective.rs:229–256, finds zero matches; and
   `mat_self_local`:218 finds none — single ray). `is_nf` (subjective.rs:274)
   returns true at the next step. There is no star in the configuration that
   can *consume* `+g(Z)` to mint another subjective ray. The dynamics has no
   feedback edge.

3. **No colour reused across the cut to re-nest.** Sustained χ needs the
   product to be re-substituted *into another ray's argument position* so a
   colour gets re-nested (re-subjectivised). Here the only colour minted is
   `g`, and Φ contains no consumer of `g`, so the §49.52 round-2 supply set
   `Ψ'` (subjective.rs comment 291–294: stars of Φ matchable with `AEx^n`) is
   **empty**. `AEx^1 = AEx^∞`; the §49.56 idempotence barrier closes at k=1.

This is exactly §49.55's mechanism running in reverse of χ: the §49.50
new-ray *is* created (Stage-0 PASS — the grounding is not falsified), but it
is created **into the objective fragment**, so §49.54 immediately reasserts
idempotence. The canonical example is a *one-shot* semaphore unlock, not a
*self-rearming* one.

## 2. Exact conditions for sustained non-idempotence (derived from §49.50/§49.57/§49.61)

§49.57 (verbatim): idempotence "can be lost in presence of subjective rays …
If there is a point in repeated execution where we reach idempotence then
hyperexecution is idempotent." §49.59 is the open question; **§49.60 answers
it in the negative** ("Hyper execution is not necessarily defined. It is
possible that after abstract execution, there are always pairs of matchable
rays, making it impossible to ever reach a normal form"); **§49.61 exhibits an
explicit witness.** So sustained non-idempotence is not merely consistent with
Eng's metatheory — Eng *constructs* it. The structural conditions, read off
§49.61 and the §49.50 new-ray rule:

A faithful constellation `Φ` (Ψ-as-Φ-fragment, the `subjective_stream`
convention) sustains non-idempotence iff there is a **self-reproducing
subjective cycle**: a closed chain of stars such that

- **(C1) Re-subjectivising substitution.** Some fusion's unifier `θ` binds a
  variable that occurs *inside another ray's argument*, so applying `θ`
  produces a ray with a colour nested in an argument — `ray_is_subjective`
  true (constellation.rs:89). This is §49.50 char.(1) running *into*, not out
  of, the subjective fragment (contrast §1.1: there `θ={X↦+g(Z)}`, `Z` bare).
  Concretely: the demand ray must carry a *colour nested over a variable that
  the supply will fill with another colour* — e.g. `−f(−g(X))` (§49.61), so
  `θ` plants a colour where `−g`'s argument was.

- **(C2) A non-linear consumer that duplicates the cycle.** §49.61's third
  star `[+g(X),+g(X),a]` has the *same colour twice*. Its two `+g` rays each
  demand a `−g` supplier, so one round **duplicates** the
  `[X,+f(X)]+[−f(−g(X)),−g(X)]` sub-constellation (Eng: "duplicated in order
  to satisfy the rays"). Duplication is what makes the residue *grow* rather
  than shrink — the well-founded measure of §62.6 (consumed structure) is
  *not* decreasing, because the consumer manufactures two demands per supply.
  Without (C2) the cycle is at best a fixed-size loop that idempotence-barriers
  out (§49.56) or a productive §62.7 loop that a ground base case terminates.

- **(C3) No ground base case (anti-§62.7).** §62.7's productive loop
  `[−a(0·W),+a(W)]` is non-idempotent-looking but *terminates* via the ground
  terminator `[+a(0·0·0·ε)]` ("the constant ε forbids any possible additional
  looping"). For χ to be *sustained* (not merely productive-then-dead) the
  cycle must have **no ground-argument star** that can cancel its negative
  rays. §49.61 has none: every star's arguments are variables or single
  colours over variables; there is no `ε`-style closed terminator. The
  `productivity_measure` instrument (subjective.rs:1117) is precisely the
  detector for "has a ground base case"; sustained χ ⇒ that measure is `None`
  or never reaches 0-via-consumption.

- **(C4) Colour conservation across the cut.** The colour minted by the
  re-subjectivising fusion (C1) must be one that a star in `Φ` *consumes with
  opposite polarity*, so §49.52's `Ψ'` (next-round supply, the stars of Φ
  matchable with `AEx^n`) is **non-empty every round**. In §49.61 the minted
  `−g(X)` rays are consumed by `[+g(X),+g(X),a]`, which re-emits demands that
  re-trigger `[X,+f(X)]+[−f(−g(X)),−g(X)]`. The colour `g` is *conserved* —
  produced and consumed each round, never escaping to a variable (the §1.1
  failure mode).

Necessity argument (from §49.55): if any of C1–C4 fails, the residue is, after
one round, an *objective* or *base-cased* constellation, and §49.54+§49.55
force `AEx∘AEx = AEx` — idempotence. C1 fails ⇒ §1.1 (new ray objective). C2
fails ⇒ residue size bounded ⇒ §49.56 barrier closes at finite k. C3 fails ⇒
§62.7-productive, terminates. C4 fails ⇒ `Ψ'=∅`, `AEx^1=AEx^∞`. So C1–C4 are
*jointly necessary*; §49.61's existence shows they are *satisfiable*, hence
sufficient as a class (the construction is the proof). χ-existence is a
**theorem of Eng's metatheory (§49.60), witnessed by §49.61** — not an open
guess.

## 3. Candidate faithful constellations predicted to sustain χ

All in the codebase's `pos_ray`/`neg_ray`/`mk_var` vocabulary
(`crates/stella-core/src/polarised.rs`, `term::mk_var`), drivable by
`subjective_stream(phi, psi0)` and measurable by `chi_stage01_subjective`.

### Candidate A — Eng §49.61 verbatim (the canonical witness) — STRONGEST

```rust
let x = mk_var("X");
// Φ = [X,+f(X)] + [−f(−g(X)),−g(X)] + [+g(X),+g(X),a]
let phi: Constellation = vec![
    vec![x, pos_ray("f", vec![x])],
    vec![neg_ray("f", vec![neg_ray("g", vec![x])]), neg_ray("g", vec![x])],
    vec![pos_ray("g", vec![x]), pos_ray("g", vec![x]), mk_app_str("a", vec![])],
];
let psi0 = phi.clone();   // hyper-execution of Φ itself (§49.52 AEx^∞(Φ))
```

Predicted mechanism (Eng §49.61, verbatim trace): connect
`[X,+f(X)]`–`[−f(−g(X)),−g(X)]` along `±f`. The §49.50 unifier from
`+f(X) ⋈ −f(−g(X))` is `θ = {X ↦ −g(X)}` — **C1 fires**: the bare `X` of
`[X,+f(X)]` becomes the *coloured* `−g(X)` (`ray_is_subjective` of the f-ray's
context flips a variable to a colour). Residue stars carry `−g(X)`. The
non-linear `[+g(X),+g(X),a]` (C2: colour `g` doubled) consumes them but
**duplicates** the supply pair to satisfy *both* `+g`; Eng states the round
output is `[−g(X),−g(X),a]+[−g(X),−g(X),a]` — two copies, each itself a fresh
`+g`/`−g` demand site reconnectable to `[X,+f(X)]+[−f(−g(X)),−g(X)]` from Φ
(C4: `g` conserved). "Applying abstract execution again will create more
occurrences of `[−g(X),−g(X),a]`." No ground terminator anywhere (C3). The
configuration *grows without an objective fixpoint* — exactly χ.

How `chi_stage01` measures it: Stage-0 must PASS (the `−f(−g(X))` and `−g(X)`
rays are subjective by §48.7 — colour nested in argument). Stage-1 prediction
that *distinguishes χ from the F1/F2 nulls*: `distinct` count **grows
unboundedly** with the cap (F1/F2 plateau at distinct = 2/3 by step 2 — see
measured `chi_stage01` run); `psi_size` strictly increasing across rounds
(duplication); `max subjective rays in any Ψ_k` **> 1 and increasing** (F1/F2
are pinned at 1); and `detect_recurrence` should produce a **span ≥ 2, sound,
non-trivial, recurrence=Some** whistle (the §62.6-style growing-but-self-
similar trajectory the §67.10 calibration was built to catch) — versus the
span-1 degenerate whistle both nulls produce. This is the single decisive
discriminator.

### Candidate B — minimal self-rearming semaphore (C1+C2 stripped to essentials)

```rust
// Φ = [X,+f(X)] + [−f(−g(X)),+g(X)]      (no `a`, no explicit doubler;
//                                          self-feeding via the same colour g)
let phi = vec![
    vec![x, pos_ray("f", vec![x])],
    vec![neg_ray("f", vec![neg_ray("g", vec![x])]), pos_ray("g", vec![x])],
];
let psi0 = phi.clone();
```

Predicted mechanism: `±f` fusion gives `θ={X↦−g(X)}` (C1). The second star now
also emits `+g(X)`; `+g ⋈ −g` is available *within the residue* (C4, colour
`g` self-conserved without an external doubler). Predicted weaker than A:
likely a *fixed-size* non-idempotent loop (size bounded ⇒ may hit the §49.56
barrier — C2 absent means no growth). Value: it isolates whether **growth (C2)
is strictly required**, or whether bare re-subjectivisation+conservation
(C1+C4) already defeats the §49.56 barrier. Measured prediction: distinct
count plateaus but at a value > 3 *and* `max subjective rays` stays ≥ 1 every
round indefinitely (NF never reached) — a "non-terminating but bounded"
signature, distinct from both the F1 null and Candidate A.

### Candidate C — §49.53/§49.61 hybrid control (must STAY idempotent)

```rust
// Eng §49.53 (terminating): [−f(+g(X))] + [X,+f(X)] + [−g(X),+f(X),a]
let phi = vec![
    vec![neg_ray("f", vec![pos_ray("g", vec![x])])],
    vec![x, pos_ray("f", vec![x])],
    vec![neg_ray("g", vec![x]), pos_ray("f", vec![x]), mk_app_str("a", vec![])],
];
let psi0 = phi.clone();
```

Predicted mechanism: Eng proves (§49.53) `AEx^∞ = AEx^2 = [a]+[a]` — it
**terminates**. C1 fires (`+g(X)` born) but C3/C2 fail: the `−g` consumer is
*linear* (single `+f`, single `−g`, no doubled colour) and the chain
collapses to ground `[a]+[a]`. This is the **idempotent positive control**:
`chi_stage01` must show distinct → small, NF reached, *no* sustained whistle.
If A and C are run side-by-side and only A whistles soundly with growing
distinct, the discriminator is validated (specificity, per the §67.10
calibration philosophy in `chi_stage01_subjective.rs:183`).

(A fourth, Candidate B-with-a-doubler, is just Candidate A; not separately
listed — A is the canonical and strongest, B and C bracket it.)

## 4. Does §49.59–60 foreclose χ-existence? — honest verdict

**It does the opposite: §49.60 + §49.61 *establish* χ-existence as a theorem
of Eng's own metatheory.** §49.59 poses the open question (is `AEx^∞` always
defined?); §49.60 answers it explicitly — "Hyper execution is not necessarily
defined … it is possible that after abstract execution, there are always pairs
of matchable rays, making it impossible to ever reach a normal form"; and
§49.61 *constructs* the witness `Φ = [X,+f(X)]+[−f(−g(X)),−g(X)]+
[+g(X),+g(X),a]` with Eng's own trace showing "applying abstract execution
again will create more occurrences." So "χ = 0 always for faithful
constellations" is **refuted by Eng**, not a theorem. The honest qualification:
what §49.59 leaves open is *universality* (whether *every* Φ has a defined
`AEx^∞`), not *existence* (whether *some* Φ sustains non-idempotence) — the
latter is settled affirmative by §49.61. The prior measured nulls
(`chi_stage01` F1/F2: NF by round 1–2, distinct ≤ 3, span-1 whistles) are
therefore correctly diagnosed not as "χ cannot exist" but as "F1/F2 violate
C1/C2/C4" — F1's new ray is born objective (§1, `Z` bare), F2's re-injector
`+h(+g(X))` mints a colour Φ never consumes back (C4 fails). χ is **not yet
exhibited by this codebase** purely because the §49.61-class fixture has not
been run through `subjective_stream`; the apparatus and theory both predict it
will exhibit, and the measure-don't-guess close is to run Candidate A.

---

### RETURN (the two requested items)

**§49.59–60 verdict.** §49.59–60 does *not* foreclose χ-existence — it
*establishes* it. §49.59 flags universality as open; §49.60 explicitly states
hyperexecution "is not necessarily defined" (matchable pairs can persist
forever); and §49.61 gives an explicit faithful witness constellation whose
own Eng-supplied trace grows without an objective fixpoint. Hence "χ = 0
always for faithful constellations" is *false by Eng's metatheory*; the real
theorem is the conditional §49.55 (objective ⇒ idempotent) plus the §49.60/61
existence of subjective Φ that sustain non-idempotence. The codebase's prior
nulls (F1/F2 idempotent-fast) are explained — they fail conditions C1/C2/C4 of
§2 — not evidence against χ; χ is *not-yet-exhibited*, not *refuted*.

**Single most-promising candidate (Candidate A — §49.61 verbatim).**

```rust
let x = mk_var("X");
let phi: Constellation = vec![
    vec![x, pos_ray("f", vec![x])],
    vec![neg_ray("f", vec![neg_ray("g", vec![x])]), neg_ray("g", vec![x])],
    vec![pos_ray("g", vec![x]), pos_ray("g", vec![x]), mk_app_str("a", vec![])],
];
let psi0 = phi.clone();   // AEx^∞(Φ): subjective_stream(&phi, psi0)
```

Mechanism: `±f` fusion mints `θ={X↦−g(X)}` (re-subjectivising, C1); the
doubled-colour non-linear star `[+g(X),+g(X),a]` duplicates the supply pair
each round (C2); colour `g` is produced and consumed every round so §49.52's
`Ψ'` is never empty (C4); no ground ε-terminator exists (C3, anti-§62.7).
Predicted `chi_stage01` signature distinguishing it from the F1/F2 nulls:
`distinct` and `psi_size` grow unboundedly with the step cap (nulls plateau at
distinct ≤ 3 by step 2), `max subjective rays in any Ψ_k` exceeds 1 and
increases (nulls pinned at 1), NF is never reached, and `detect_recurrence`
yields a span ≥ 2 sound non-trivial recurrence whistle (versus the nulls'
degenerate span-1). Run alongside Candidate C (§49.53, must terminate) as the
idempotent control to validate detector specificity.
