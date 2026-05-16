# Eng Exegesis — Digest: Chapters 12–13 & Conclusion
## Boris Eng, *Stellar Resolution and Transcendental Syntax* (thesis)
### Chapters 12–13 (pp. 358–380) + Conclusion §86–88 (pp. 381–389)

**Scope.** These are Eng's own *speculative/frontier* chapters — his interpretation of
Girard's as-yet-unformalized apodictic and epidictic fragments, plus the thesis
conclusion. Eng flags repeatedly: "everything in this chapter is experimental since no
thorough and complete development of these ideas has been proposed yet" (p. 358).
Status markers used below: **DEFINED** = formal definition given; **SKETCHED** = idea
described with partial construction; **OPEN** = explicitly unresolved.

---

## Chapter 12 — Apodictic Experiments (pp. 358–371)

**Frame.** The *apodictic* fragment is linear logic "with no external constraints" /
"without system" — no logical atomic variable, no primitive connectives; connectives
are freely designed via constellations and tests. Eng distinguishes this from simply
"linear logic" (which is itself a system). Throughout, atoms are not substitutable
variables but *individual* objects handled as they are. (p. 358)

---

### §77 — Logical Constants (pp. 358–363) — DEFINED

**Motivation.** In the stellar interpretation, atoms are rays with nothing special about
them. Girard's *morphologism* (Gir18a §1.1.2) uses atomic formulas/behaviours to
specify the *shape* of proof-structures. Two natural constants arise from polarity:

**DEFINED — Objective constant (Fu)** (p. 360/§77.13):

> **ℱ** := { {[r, r₁, …, rₖ]} | ord(r) = 0, r is polarised and **objective**, and all rᵢ are uncoloured }

**DEFINED — Subjective constant (Wo)** (p. 361/§77.16):

> **ꟓ** := { {[r, r₁, …, rₖ]} | ord(r) = 0, r is polarised and **subjective**, and all rᵢ are uncoloured }

**DEFINED — Ray order** (p. 360/§77.6): ord(r) := |vars(r)|, the number of distinct
variables in a polarised ray. Order 0 = no variables (e.g. +1); order 1 = e.g. +1(X);
order 2 = +1(X•Y).

**DEFINED — Regular adapter** (p. 360/§77.10): [r,s] is *regular* if (i) non-animist (r
and s both subjective or both objective) and (ii) ord(r) = ord(s).

**DEFINED — Structural orthogonality** (p. 360/§77.11): Φ ⊥ˢ Φ′ when Φ ⊥ᴿ Φ′ ⊎ Φ_μ
where Φ_μ is a constellation of regular adapters linking rays of Φ to rays of Φ′, and
|± IdRays Φ| = |± IdRays Φ′|.

**Propositions** (p. 361/§77.14, §77.17): Both ℱ and ꟓ are *self-dual behaviours*,
i.e. ℱ = ℱ⊥ = ℱ⊥⊥ and ꟓ = ꟓ⊥ = ꟓ⊥⊥. (Proved via non-animism constraint.)

**Shape specification.** Behaviours using ℱ and ꟓ as atoms characterise the shape of
proof-structures. Key shapes (p. 362/§77.25):
- Atom of proof-structure: [+1] ∈ ℱ
- Axiom: [+1, +2] ∈ (ℱ ⊗ ℱ)⊥ = ℱ ⅋ ℱ
- Test for axiom: [−1,1] + [−2,2] ∈ ℱ ⊗ ℱ
- Tensor proof-structure: [+1] + [+2] ∈ ℱ ⊗ ℱ

**DEFINED — Full tensor** (p. 362/§77.22): For behaviours A and B (not necessarily
disjoint):

> **A ⊗ B** := {Φ_A ⊎ Φ_B | Φ_A ∈ A, Φ_B ∈ B, Φ_A ⋈ Φ_B}⊥⊥

where Φ_A ⋈ Φ_B means all rays of Φ_A and Φ_B are pairwise non-unifiable. A big
problem: the ordinary ⊗ does not work on ℱ and ꟓ because they are not disjoint with
themselves. (p. 362/§77.21)

**DEFINED — Order 0 MLL test** (p. 363/§77.29): Tests defined directly on switched
formulas, independently of proof-structures:
- (A ⊗ B)★ = [−A, −B; +(A ⊗ B)]
- (A ⅋_L B)★ = [−A; +(A ⅋ B)] + [−B]
- (A ⅋_R B)★ = [−A] + [−B; +(A ⅋ B)]
- Extended to sequents: (⊢ A₁,…,Aₙ)★ := Σᵢ (Aᵢ★ + [−Aᵢ; Aᵢ])

**OPEN — Right definition of apodictic fragment.** Eng tried several definitions of
adapters to classify rays; none were fully satisfactory. "The right definition of an
apodictic fragment of linear logic is still open." (p. 360)

---

### §78 — Expansional Connectives (pp. 363–365) — SKETCHED

**Frame** (Gir18a "La logique 2.0"): Alternative exponentials called *expansionals*,
designed system-free by characterizing duplication mechanisms. These handle duplication
for order-1 atoms only (unlike standard exponentials which treat order ≥ 2); no nested
boxes. (p. 363/§78.2)

**SKETCHED — Expansionals** (p. 364/§78.3): Dual unary connectives ↓A and ↑A:
- Node replication: ↓A ⊗ B
- Node co-replication: ↑A ⅋ B
- *Insinuation*: A ↪ B := ↓A −∘ B = ↑A⊥ ⅋ B

**DEFINED — Expansional switching** (p. 364/§78.4):
- φ(↑) ∈ {↑_L, ↑_R}
- φ(↓) ∈ {↓_f, ↓_g}

**DEFINED — Expansional test** (p. 364/§78.5):
- (↓A ⊗ B)★ = [−A(X), −B; +(↓A ⊗ B)]
- (↑_L A ⅋ B)★ = [−A(X); +(↑A ⅋ B)] + [−B, −∞(X); +∞(X)]
- (↑_R A ⅋ B)★ = [−A(X)] + [−B; +(↑A ⅋ B)]

**OPEN — Match with Girard.** Eng distinguishes several orders of rays; his tests
differ from Girard's (Gir18a §2.1.3). "It is possible that my definition of expansional
does not match Girard's, but I will not provide a further exploration of the subject."
(p. 364/§78.6)

---

### §79 — Visibility and Non-Classical Truth (pp. 365–369) — DEFINED

**Frame** (Gir20a, TS paper 4): *Visibility* is Girard's non-classical truth notion,
based on the Euler-Poincaré invariant. Two conditions for truth: (i) special behaviour
**0** is not true; (ii) preserved by cut-elimination. (p. 365/§79.1)

**DEFINED — Weight of a star** (p. 366/§79.8): For star φ with objective rays oᵢ and
subjective rays sⱼ:
- ω([o₁,…,oₙ]) := 2 − n (fully objective)
- ω([o₁,…,oₙ, s₁,…,sₘ]) := −n (mixed/subjective)

**DEFINED — Weight of a constellation** (p. 366/§79.9): ω(φ₁ + … + φₙ) := Σᵢ ω(φᵢ)

**DEFINED — Weight of a behaviour** (p. 367/§79.11): ω(A) := max{ω(Φ) | Φ ∈ A}

Weight table for behaviours (Figure 79.1, p. 367):
- ω(ℱ) = 1; ω(ꟓ) = 0
- ω(A⊥) = 2 − ω(A); ω(A ⊗ B) = ω(A) + ω(B); ω(A −∘ B) = ω(B) − ω(A)
- ω(A ⅋ B) = ω(A) + ω(B) if both contain ꟓ; = ω(A) + ω(B) − 2 otherwise
- ω(A × B) = ω(A ⅋ B); ω(A ⊕ B) = ω(A ⊗ B)

**DEFINED — Zero** (p. 367/§79.13): **0** := (ℱ ⅋ ꟓ) ⊕ ꟓ
(Note: ω(**0**) = −1 < 0, so **0** is invisible/false.)

**DEFINED — Top** (p. 368/§79.19): ⊤ := **0**⊥ = (ℱ ⊗ ꟓ) ⋊ ꟓ
(ω(⊤) = 1 ≥ 0, so ⊤ is visible/true.)

**DEFINED — Visibility** (p. 367/§79.15): A constellation Φ is *visible* (true) when
ω(Φ) ≥ 0. A behaviour A is visible when ω(A) ≥ 0.

**Proposition** (p. 368/§79.17): Visibility defines a truth notion: **0** is invisible
and visibility is closed under cut-elimination for proof-structures.

**Non-classical features** (pp. 368–369/§79.25): The truth table has odd cases — e.g.
ω(ℱ ⊗ ℱ) = 2 (visible) but ω(ℱ ⅋ ꟓ) = −2 (invisible); orthogonality does not
exchange visibility. Visibility is the presence of animist stars that makes **0**
invisible.

**DEFINED — Fu/Wo sequences** (p. 368/§79.23–24):
- ℱₙ: ℱ when n=1; ℱ ⊗ ℱₙ₋₁ when n>1; ℱ ⅋ ℱₙ₊₁ when n<1
- ꟓₙ: ꟓ when n=0; ℱₙ ⊗ ꟓ otherwise

---

### §80 — System-Free Arithmetic on Relative Numbers (pp. 369–370) — DEFINED

**Core claim** (p. 369/§80.1): Relative numbers (integers) can be defined as
behaviours using the logical constants ℱ and ꟓ.

**DEFINED — Encoding of relative numbers** (p. 369/§80.2): Given p ∈ Z, define
encoding [[p]] as a behaviour:
- [[0]] := ꟓ
- [[p]] := ℱₚ ⊗ ꟓ when p > 0
- [[p]] := ℱₚ₊₂ ⅋ ꟓ when p < 0

Example (p. 369/§80.3): [[−1]] := ℱ ⅋ ꟓ; ⊤ = [[−1]] ⇒ [[0]]; **0** = ⊤⊥ = [[−1]] ⊕ [[0]];
[[−n]] = [[n]]⊥.

**DEFINED — Arithmetic operations** (p. 370/§80.6):
- ℱ corresponds to [[1]]
- [[n+1]] ≡ ℱ ⊗ [[n]] (successor)
- [[n−1]] ≡ ℱ −∘ [[n]] (predecessor)
- [[n+m]] ≡ [[n]] ⊗ [[m]] (addition)
- [[n−m]] ≡ [[n]]⊥ ⅋ [[m]] = [[n]] −∘ [[m]] (subtraction)

**Proposition** (p. 370/§80.5, stated from Gir20a §4):
1. A ≡ ℱ_{ω(A)} (encoded number reflected in weight of encoding; ω([[p]]) = p)
2. ℱₘ ⊗ ꟓₙ ≡ ꟓₘ₊ₙ with m,n > 0
3. ℱₙ₊₂ ⅋ ꟓ ≡ ꟓₙ with n < 0
4. ℱₘ ⊗ ℱₙ ≡ ℱₘ₊ₙ; ℱₘ ⅋ ℱₙ ≡ ℱₘ₊ₙ₋₂; ℱₙ⊥ ≡ ℱ₂₋ₙ (combinations of ℱ contractible)
5. ꟓₘ ⊗ ꟓₙ ≡ ꟓₘ ⅋ ꟓₙ ≡ ꟓₘ₊ₙ; ꟓₙ⊥ ≡ ꟓ₋ₙ (combinations of ꟓ contractible)
6. ℱₙ and ꟓₙ are invisible for n < 0

Example (p. 370/§80.7): [[2+3]] = [[2]] ⊗ [[3]] = (ℱ ⊗ ℱ ⊗ ꟓ) ⊗ (ℱ ⊗ ℱ ⊗ ℱ ⊗ ꟓ) ≡ ꟓ₂ ⊗ ꟓ₃ ≡ ꟓ₅ ≡ [[5]].

**Significance.** This is axiom-free, system-free arithmetic: integers are encoded
directly as behaviours, with arithmetic operations as linear logic connectives. No
Peano axioms, no induction principle — only the interaction structure of stellar
resolution. Eng notes: "no clear purpose for [this] and there is no technical use case
for an 'axiom-free' Peano arithmetic. It is mostly interesting for philosophical
purposes." (p. 384/§87.2)

---

### §81 — Discussion: Anarchy (pp. 370–371) — SKETCHED / OPEN

**Core claim** (p. 370/§81.1): "Apodiotics is a state where computational objects
express logic without the need for external regulation or control."

**Decentralisation model** (p. 370–371): Apodictic/system-free logic corresponds to
*decentralised* systems (cf. Figure 81.1b: External control (epidictics) → Meaning
layer (synthetics) → Freely interacting objects). Standard logical systems correspond
to the centralised model (Regulator → Object / Certified object). Apodictic transcendental
syntax is "necessarily more flexible than system-bounded formalisms." (p. 371)

**OPEN — Is apodiotics sufficient?** (p. 371/§81.2): "Apodiotics is about decentralised
logic. Constellations live their life and the synthetics describes their behaviour with
formulas or labels them with tests. But is it sufficient to speak about logic? I do not
have an answer. I believe that it may be sufficient but not satisfying." External
control may be needed for efficiency (algorithmic optimisation) and human readability.

**Key structural claim** (p. 371/§81.3): "Epidictics is exactly what apodiotics lacks
in order to express natural deduction. But adding epidictics is not exactly a 'return
to the outdated traditions'. Instead, it is a layer *over* a space of freely interacting
computational objects, with freedom at the bottom and authority at the top."

---

## Chapter 13 — Epidictic Experiments (pp. 372–380)

**Frame.** Epidictics (§44) is the part of logic which is generic/substitutable —
proof-structures with atoms as universally quantified variables. "There is currently no
true theory of epidictics in the context of transcendental syntax." (p. 372)

---

### §82 — Genericity of Proof-Structures (pp. 372–374) — SKETCHED

**Variables vs. apodictic atoms** (p. 372/§82.1): Proof-structures in stellar
resolution are apodictic (self-sufficient, formula leaves = order-0 rays). Standard
proof-nets require substitutable atoms = universally quantified variables. To handle
usual proofs, must interpret quantifiers.

**SKETCHED — Universal quantification** (p. 373/§82.3): A variable α is generic; it
must fit for any shape. Girard (Gir18b §5.3) proposes three switchings for a variable:
∀_{id}, ∀_⊗, ∀_⅋ for all shapes α can take (irreducible atom, par, tensor). "By
imposing dual atoms, we say that cuts cannot connect any atoms but that we want *some
specific* connections."

**SKETCHED — Existential quantifiers** (p. 373/§82.4): A proof of ∃α.A decomposes
into three parts: specification (⊢ Γ, ∃α.A), computational entity (the proof), and
existential witness σ. These translate to: set of tests (specification), vehicle
(computational content of σ), and tests for σ (materialisation of tests for existential
witnesses = *mould*). Moulds are "pre-integrated" tests checking that the existential
witness has the right shape.

**SKETCHED — Encoding of terms** (p. 373/§82.6): Terms for existential witnesses are
encoded by multiplicative combinations of ℱ; equality between terms = linear
equivalence ≡. Application f(a) is encoded as pair (f,a). Encoding must be injective
(f(t) = f(u) implies t = u). Multiple solutions exist; choice is a matter of
representation.

---

### §83 — Usage Interpretation of Second-Order Linear Logic (pp. 374–375) — DEFINED

**Frame** (p. 374/§83.1): In the Usage interpretation, quantifiers are handled by
infinite unions and intersections. A behaviour is *valid* only when it contains no
variables; substituting behaviour variable X with behaviour T is permitted.

**DEFINED — Epidictic architecture** (p. 374/§83.2): An *epidictic architecture* is a
countable set of behaviours E closed by connectives C, adjunction and composition:
- For all * ∈ C of arity n and A₁,…,Aₙ ∈ E: *(A₁,…,Aₙ) ∈ E
- For all F, A, B ∈ E: F ⊥ A ⊗ B = F(A) ⊥ B, where F(A) = {Ex(Φ_F ⊎ Φ_A) | Φ_F ∈ F, Φ_A ∈ A}
- If A −∘ B ∈ E and A ∈ E, then B ∈ E

**DEFINED — Universal quantification** (p. 374/§83.4): Let E be an epidictic architecture:

> ∀X.A := ∩_{T∈E} {X := T}A

**DEFINED — Existential quantification** (p. 374/§83.5):

> ∃X.A := (∪_{T∈E} {X := T}A)⊥⊥

**DEFINED — Additive connectives via second-order** (p. 375/§83.8):
- A ⊕ B := ∀C. (A −∘ C) ⇒ (B −∘ C) ⇒ C
- A & B := (A⊥ ⊕ B⊥)⊥

**DEFINED — Additive neutrals** (p. 375/§83.9): **0** := ∀X.X; ⊤ := ∃X.X

**DEFINED — Full exponentials via second-order** (p. 375/§83.10):
- !A := ∀X. (A ⇒ X) −∘ X
- ?A := (!A)⊥

**DEFINED — Multiplicative neutrals** (p. 375/§83.11): **1** := !⊤; ⊥ := ?**0**

---

### §84 — Usine in the Case of Predicate Calculus: A Sketch (pp. 376–379) — SKETCHED

**Frame** (p. 376/§84.1): No serious development of the Usine interpretation for
second-order logic has been given. Predicate calculus is treated as a restriction of
second-order logic (Gir18b §5).

**SKETCHED — Dissolution of individuals** (p. 376/§84.2–3): First-order individuals
(natural numbers, persons, programs) "purely come from our intuitive perception of
logic." Since behaviours express what kind of individual something is, and constellations
materialise instances, "an individual f(a) would be a specification saying 'I am f(a)'"
and "instead of a property P(f(a)) saying 'the individual f(a) has the property P', we
would have a statement saying 'I'm an individual satisfying property P'. 'To have'
becomes 'to be'." Predicates = artificial way to manage allowed/forbidden interactions.
(p. 376/§84.3)

**DEFINED (partial) — Encoding of terms** (p. 377/§84.5): A constant is of type ℱ.
For function symbol f, the term f(a) corresponds to encoding (f,a):

> < T, U >★ := (T ⅋ U) ⊗ (T ⅋ T ⅋ U)

(Girard, Gir18b §2.4, inspired by set-theoretic pair representation.)

**DEFINED (partial) — Encoding of variables** (p. 377/§84.6): Variable α treated with
ray α(X). Three sorts of addresses for α in ∀α.A:
- α(x) := (∀α.A)(1·X) — positive occurrences of α in ∀α.A
- α⊥(x) := (∀α.A)(r·X) — negative occurrences of α
- (∀α.A)(c·X) — the formula ∀α.A itself

**SKETCHED — Equality** (p. 377/§84.7): Equality between individuals = linear
equivalence ≡. Girard's criticism (Gir18b §2): equality x=x in second-order form
presupposes a specific space of properties, i.e. an implicit epidictic architecture.
In transcendental syntax, no epidictic architecture is assumed; one must be made explicit.

**SKETCHED — The mould** (p. 378/§84.8): A mould is a constellation-test specifying
existential witnesses. The mould for a formula B associated with σ consists of
Tests(B) and Tests(B⊥). Positive occurrences α link to Tests(B); negative α⊥ link to
Tests(B⊥). The object being tested is a mix of vehicle + mould; requires *épure*
(clear separation between objective vehicle and subjective mould) and the two mould
parts to be negations of each other. (p. 378–379/§84.8–9)

**OPEN — Cut-elimination for moulds.** "A natural way to ensure that the two parts of
the mould are the negation of each other is to try to connect them with cuts and show a
cut-elimination theorem. Although it should work in some cases with the right epidictic
architecture, it is known that it is unprovable in general." (p. 379)

---

### §85 — Discussion: The Theory of Epidictic Architectures (pp. 379–380) — OPEN

**OPEN — No true theory** (p. 379/§85.1): "We still have no true theory of epidictics.
It is not even clear what such a theory should be. But it should at least provide a way
to characterise what a generic proof-structure is." In a free space of construction, it
can be useful to *limit* the space to those proof-structures so as to make generic
reasoning possible: "since the world is limited, I can know what the possible shapes of
the unknown are."

**SKETCHED — Meta-language level** (p. 379/§85.2): If analytics = matter (programs),
synthetics = meaning (formulas), then epidictics (formatting synthetics) = space where
we construct logical languages or logical systems. It is a sort of *meta-language*
"except that unlike previous meta-languages for logic, its purpose is not to justify
but to limit the potential for efficiency." Transcendental syntax works with only 3
layers (analytics, synthetics, epidictics) without the need for an infinite hierarchy
of semantics. Apodiotics = absence of the third layer.

**SKETCHED — Ethics model** (p. 380/§85.4): "Epidictics is a 'guide' for computational
objects and not a system of constraints. Moreover, we can also change epidictics (or
even remove it) without changing objects, just as we can change a political regime."
The behaviour imposed on objects is "only the behaviour we wish for because of some
purpose in some system. It is a sort of *ethics*."

**SKETCHED — Design plans** (p. 380/§85.5): A potential epidictic language should be
able to design "representative objects" from which constellations of a system are
instantiated (via homomorphism). Only some specific constellations can be created,
inducing a limitation of synthetics — "only some behaviours can be considered, thus
forming a logic." Example: an epidictic architecture allowing only typed polymorphic
λ-terms to be created could express natural deduction.

**SKETCHED — MLTT connection** (p. 380/§85.6): Epidictics implicitly appear in
Martin-Löf type theory. MLTT statements about types (0:N, s(n):N, A:Type ∧ B:Type ⇒
A∧B:Type) look like a structuration of epidictics. "One possible task for transcendental
syntax is to give a clearer status for those type assertions in the light of the
Usine/Usage interpretation."

**Girard's terminus** (p. 380/§85.7): "At the present moment, epidictics is but a name
on a blank area of the logical charts; hence a sort of new frontier for logic." (Gir18b
§6.2)

---

## Conclusion — §86–88 (pp. 381–389)

### §86 — Summary and Contributions (pp. 381–382)

Main contributions of the thesis:
1. **Contextualisation**: TS placed as natural successor of geometry of interaction;
   connected to classical realisability, program testing; philosophical connection to
   justification of logical rules (§86.2/p. 381).
2. **Illustration**: Stellar resolution model illustrated with automata, logic programs,
   tile systems, circuits (Chapter 8/§86.3).
3. **Formalisation** (§86.4): First formalisation of transcendental syntax:
   - Stellar resolution formalised (Ch. 7); confluence proven (Ch. 9)
   - Multiple execution modes defined (§§49–51)
   - MLL model given (Ch. 10)
   - Simulation of cut-elimination and Danos-Regnier correctness proven (§68)
   - Completeness and soundness of several MLL models stated (§70)
4. **Extensions** (§86.5): Apodictic (Ch. 12) and epidictic (Ch. 13) fragments
   sketched; formal basis for exponentials given (Ch. 11); alternative exponentials
   (Girard's expansionals, §78) made possible.

---

### §87 — Horizons (pp. 382–388) — OPEN throughout

**§87.2 — Remaining unsolved technical problems** (p. 382):
- No proper treatment of subjective rays (formal definition and examples needed)
- Interactive execution: exact number of duplicates uncharacterised (non-trivial graph problem)
- Links with logic programming not properly defined; formal connections to Bibel's
  "connection method" and constraint programming unestablished
- No alternative definition of λ-calculus with stellar resolution (untyped λ-calculus
  directly via term graphs + stellar resolution mechanisms sketched but not proven faithful)
- No computationally faithful definition of circuits in stellar resolution (synchronised
  flow of computation not naturally specifiable in constellations)
- No complexity analysis for constellations (shape of terms has direct influence on
  complexity; formal links between classes of shapes and complexity classes open)
- No termination analysis for constellations (dependency graph approach tried but omitted)
- Axiom-free Peano arithmetic (§80): "no clear purpose" and "no technical use case";
  philosophically interesting but practically undeveloped
- Predicate calculus interpretation (§84): "still a lot of work to do in order to achieve
  a full formalisation of it"

**§87.3 — Extensions of stellar resolution** (p. 384): Two compatible extensions
discussed with Seiller:
- Putting coefficients on stars → monoid-weighted stars and constellations (generalises
  Seiller's interaction graph weights)
- Putting coefficients on edges of dependency graphs (probability of ray connecting to
  specific other ray; reminiscent of chemical reactions)

**§87.4 — New version of proof-nets** (p. 384): Seiller's idea to use TS to correct
proof-nets. Eng personally does not support this direction: "constellations are the next
form of proof-nets and they *are* what proof-nets should be."

**§87.5 — Parallel and concurrent computation** (p. 385): Stellar resolution as
asynchronous parallel computation model. Two unrealised ideas: encoding Lafont's
interaction nets/combinators (with Marquet); encoding π-calculus (with Castro;
"less trivial than expected because of name handling"). Subjective rays believed
connected to synchronisation and concurrent programming. OPEN.

**§87.6 — Generalised token machine** (p. 385): Transcendental syntax extends
geometry of interaction → natural to seek a generalised token machine. Existing
generalised machines in literature [CC23, DLTY17, CVV21] but no links established.
Idea of "stellar machine" (dependency graph as automaton with tokens = families
representing diagrams being constructed; unification at each step). OPEN.

**§87.7 — Verified computation** (p. 385–386): TS connects logic with program testing.
Automata encoded as constellations + tests asserting membership in automata classes.
"Constellations which can be typed in predicate calculus and second-order logic (and
thus have a specific shape) would theoretically correspond to programs of complexity
classes P and NP." OPEN.

**§87.8 — Discrete complex systems and dynamical systems** (p. 386): Stellar resolution
as tile system (remarked independently by Eng and Seiller). Attempt to generalise with
discrete dynamical systems / complex system theory; "I did not have the mathematical
background to seriously consider this direction." OPEN.

**§87.9 — Ludics** (p. 386): Ludics as abstraction of sequent calculus (whereas GoI
abstracts proof-nets). Encoding ludics with stellar resolution so TS subsumes both.
Idea: order on constellations to internalise sequentialisation. Olarte noted epidictic
control may be related to focalisation. OPEN.

**§87.10 — Deep inference** (p. 386): Alternative culture of logic, distinct from
ludics and GoI. "There is currently no research about how deep inference is different
from or close to transcendental syntax." Impression from discussions: sequent calculi
could be seen as "recipes for the construction/generation of constellations/programs."
OPEN.

**§87.11 — Descriptive complexity** (p. 386): Connections between TS and ICC. Types
(Usine/Usage) have a *descriptive function* — can we characterise complexity classes
by tests/behaviours? Constellations typed in predicate/second-order logic would
correspond to P and NP programs [Imm12, Imm86]. OPEN.

**§87.12 — Nature of programs and algorithms** (p. 387): "There is currently no
satisfying formal definition of algorithm or even of a program." Algorithms as
specifications in Usine interpretation; sequential algorithms would satisfy "sequential
formulas". Proposes extending *shapes* of constellations rather than extending
tests/constellations with external constructions. OPEN.

**§87.13 — Open proof assistant** (p. 387): Proof assistant based on stellar resolution.
Core = unification algorithm; everything else constructed within the language. Typing
given by tests; several logics can coexist as libraries/modules. "Logical systems become
a sort of libraries/modules as in programming." Proving not bound to intuitionistic
logic. Whether functional systems are sufficient remains open. OPEN/SPECULATIVE.

**§87.14 — Epidictic language as a script language for macros** (p. 387–388): The
epidictic as a macro system for stellar resolution. "The primitive system is stellar
resolution which is very flexible and everything else is just syntactic sugar with
complex macros." Formulas as syntactic labels; macros inductively associate formulas
with test constellations. SKETCHED.

**§87.15 — A realist thesis** (p. 388): Philosophical speculation. TS adds a Usine
interpretation showing "the primitive shapes of things matter" — it is possible to
anticipate the behaviour of individuals from their shape. "The shape (of computational
objects) becomes a *primitive essence*." However, behaviours cannot always be fully
characterised by finite tests, limiting this anticipation. Computational monist testing
is "reality-discovery" — "syntactic interactions occurring in mathematics say things
about how reality is structured." OPEN/SPECULATIVE.

---

### §88 — Limits of the Current Presentation of Transcendental Syntax (pp. 388–389)

**§88.1 — A too open theory** (p. 388): "Transcendental syntax is like a computational
sandbox for logic... Because it is so free, it also lacks direction... Transcendental
syntax is still a very speculative and experimental subject for the moment."

**§88.2 — Complexity issues** (p. 388–389): Concrete execution requires graph
isomorphism (known hard). Only interactive execution is feasible for real-world
applications. Danos-Regnier correctness criterion has exponential complexity (2ⁿ tests
for n par hyperedges). "It is currently not known if other more efficient correctness
criteria can be easily and efficiently implemented in stellar resolution." Adding an
epidictic layer *may* make computation more efficient by treating external opaque
interactions without considering the underlying micro-computational mechanisms.

**§88.3 — Limitation to classical computation** (p. 389): The thesis is limited to
classical computation. Not an absolute limit: constellations could be extended with
coefficients to interpret probabilistic or quantum computation (Chardonnet uses token
machine with complex coefficients). "However, it is unclear whether doing so would
provide an interesting non-classical model of computation."

**§88.4 — Another blind spot** (p. 389): TS "still cannot give a 'transcendental'
status to type judgements appearing in (Martin-Löf) type theory." Also: Homotopic Type
Theory (HTT) with new treatment of equality; deep inference — all look distinct from
TS. "Transcendental syntax is not able to provide comments, analysis, or comparisons"
to these theories.

**§88.5 — A materialist conception of logic** (p. 389): TS is "after all, a
computational point of view on logic, hence a logical paradigm among other ones." It
does not take into account the social nature of logical activity. "There is a strong
belief that computation explains the whole logical activity. Whether it is right or
wrong, this is out of my field of expertise." Eng's current belief: "the natural and
social aspects of logic may not be incompatible. There is the natural layer of stellar
resolution, on which logical constructions can be made, and then the social/cultural
layer corresponds to the epidictic which corresponds to systems built on top of stellar
resolution."

---

## Cross-Cutting Notes for stella / Post-Eng Subjective/Animist Frontier

**Animism as falsity engine.** The weight function treats animist stars (mixed
objective/subjective) as weight-lowering: each additional objective ray in a mixed star
reduces weight by 1. Animist constellations are the mechanism that makes **0** false.
This is the formal hook for the subjective/animist distinction as a truth-differentiator.

**The three-layer stack.** Analytics (freely interacting objects) → Synthetics (meaning
layer, formulas/behaviours) → Epidictics (external control, logical systems). Apodiotics
= absence of epidictics. The subjective/animist frontier lives at the boundary between
analytics and synthetics: subjective rays are what give things their internal colour and
are what the epidictic controls/synchronises.

**System-free arithmetic as number-as-shape.** [[p]] encodes integers purely as shapes
of constellations (combinations of ℱ and ꟓ), with arithmetic as linear logic operations.
No axioms, no induction. Weight = integer value. This is a worked-out instance of the
"primitive essence as shape" thesis from §87.15.

**Epidictic = social/political layer.** §85.4's ethics model and §88.5's materialist
conception directly identify the epidictic with the social/cultural layer over the
natural computational substrate. Epidictics is not a constraint system but a *guide* —
changeable like a political regime without changing the underlying objects.

**Open core for stella.** The theory of epidictic architectures (§85) is genuinely
blank. Girard's own terminus is "a name on a blank area." This is where novel
theoretical work is possible: what characterises a generic proof-structure? how does
the epidictic limit the synthetics to form a logic? how do subjective rays encode
synchronisation/social authority?
