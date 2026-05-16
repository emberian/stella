# Eng Ch.10 Digest: Stellar Interpretation of Multiplicative Linear Logic

Boris Eng, *An Exegesis of Transcendental Syntax* (2023), Chapter 10, pp. 305–342.
This document is a spec-grade implementation contract. All definitions are verbatim or near-verbatim from the source.

---

## Background conventions (needed throughout)

**Basis of representation** (§66.2). Fix a polarised signature B := (V, F, ar, ○, |·|) with:
- Variables X ∈ V (typically V = N)
- Function symbols F := F₀ ⊎ F₊ ⊎ F₋ with F := {1, r, ·} ∪ ⋃_{u∈U}{u}, F₊ := ⋃_{u∈U}{+u}, F₋ := ⋃_{u∈U}{-u}, for U a set of elements representing vertices of proof-structures (U := N).
- ar(u) = 1 for all u ∈ U; ar(·) = 2; ar(1) = ar(r) = 0.
- The symbol · is right-associative: t · u · v := t · (u · v).

**Term grammar for addresses** (§69.27): t ::= X | 1 · t | r · X.

**Stars and constellations**: a star is a finite multiset of rays (signed terms). A constellation is a multiset of stars. Written as [r₁, r₂, ...] for a star, Φ = s₁ + s₂ + ... for a constellation. Notation: Ex(Φ) = abstract execution result (normal form multiset of stars), AEx(Φ) = abstract execution (§69.3: in Ch.10, Ex is written AEx).

---

## §66 Proofs as constellations (pp. 305–307)

### §66.1 Orientation
The representation of MLL proofs follows the GoI interpretation of proofs as permutations, but with terms instead of flows. The key novelty: cuts are represented with a single star that duplicates during execution; this encodes the shape of proof-structures directly into addresses.

### §66.3 Localisation
Constellations are "locative": only physical locations in a proof-structure S are translated. Each atom v ∈ Atoms(S) receives a unique **address** addr_S(v) ∈ Term(B). The address encodes the path from a conclusion to the atom.

### §66.6 Definition (Vertex above) (p.306)
A vertex v is *above* another vertex u in a proof-structure if there is a directed path from v to u going through only ⊗ and ⅋ hyperedges.

### §66.7 Definition (Path address) (p.306)
The *path address* pAddr_S(v) of an atom v in a proof-structure S is defined inductively:
- If S ∈ {Ax_{v,*}, Ax_{*,v}}: pAddr_S(v) = X (a fresh variable).
- If S = S₁ ⊎ S₂ and v ∈ V^{S₁}: pAddr_S(v) = pAddr_{S₁}(v).
- If S ∈ {Par^{v',v}(S'), Tens^{v',v}(S')}: pAddr_S(v) = 1 · pAddr_{S'}(v), where v is a conclusion with v above v'.
- If S ∈ {Par^{*,v'}(S'), Tens^{*,v'}(S')}: pAddr_S(v) = r · pAddr_{S'}(v), where v is a conclusion with v above v'.
- pAddr_S(v) = pAddr_{S'}(v) otherwise.

The path address is uniquely defined w.r.t. a conclusion c ∈ Concl(S') where S' is S without cuts (E^{S'} = E^S \ Cuts(S)).
The **address** is: addr_S(v) := c(pAddr_S(v)).

### §66.10 Definition (Set of addresses) (p.307)
Addr_x(S) is the countable set of all terms of the form c(f₁ · ... · fₙ · X) where c ∈ Concl(S) and fᵢ ∈ {1, r}.

### §66.11 Definition (Translation of the computational content of a proof) (p.307)

The **vehicle** and **cuts** of a proof-structure S are:

$$\Phi_S^{\text{ax}} := \sum_{e \in \text{Ax}(S)} [\mu(\text{addr}_S(\overleftarrow{e})),\ \mu(\text{addr}_S(\overrightarrow{e}))]$$

$$\Phi_S^{\text{cut}} := \sum_{e \in \text{Cuts}(S)} [-\overleftarrow{e}(X),\ -\overrightarrow{e}(X)]$$

where μ(c(t)) = +c(t) when c = \overleftarrow{e} or c = \overrightarrow{e} for some e ∈ Cuts(S) (related to a cut), and μ(x) = x otherwise.

The **computational content** of S is: Φ_S^{comp} := Φ_S^{ax} ⊎ Φ_S^{cut}.

**Key example** (Fig. 66.2, p.308): The proof-structure with three axioms (nodes 1–6), one ⅋ (node 7), one ⊗ (node 8), one cut (7–8) translates to:
```
[+7(1·X), +7(r·X)] + [3(X), +8(1·X)] + [+8(r·X), 6(X)] + [-7(X), -8(X)]
```

---

## §67 Simulation of cut-elimination (pp. 308–314)

### §67.1 Mechanism
Cut-elimination in stellar resolution = making the vehicle interact with cuts via execution. The shape of proof-structures is embedded in the addresses of atoms of the vehicle, so cut-elimination is contraction/transfer of information by resolution of addresses/conflicts. The ax/cut case of cut-elimination is the only "true" case; the multiplicative ⊗/⅋ case is purely determined by the shape of objects (logical nature in the sense of transcendental syntax).

### §67.2 Execution mode
Cut-elimination uses **AEx** (abstract execution). The idea: execute Φ_S^{comp}; diagrams correspond to maximal paths from the two ends of a proof-structure, alternating between vehicle and cuts.

### §67.7 Definition (Structural equivalence) (p.310)
Two constellations Φ and Φ' are *structurally equivalent* w.r.t. two sets of colours C and D, written Φ ≃_S^{C,D} Φ', when there is a bijection φ : I_Φ → I_{Φ'} such that |Φ[i]| = |Φ'_{φ(Φ[i])}| for all i ∈ I_Φ, extended to rays: Φ[i][j] ⋈ Φ[i'][j'] iff φ(Φ[i][j]) ⋈ φ(Φ'[i'][j']) for all i ∈ I_Φ and j ∈ I_{Φ[i]}.

### §67.9 Lemma (Simulation of cut-elimination) (p.312)
Let R := (V, E, in, out, ℓ_E) be a proof-structure. If R ~~> S by eliminating e_{cut}, then:
$$\text{AEx}(\Phi_R^{\text{comp}}) \simeq_S \text{AEx}(\Phi_S^{\text{comp}})$$

*Proof sketch (cases)*:
- **Ax/cut case**: e_{cut} is an ax/cut cut with ℓ_E(e₁) = ax. Two sub-cases depending on whether v₀ is related to another cut. In both cases, diagram contraction in Φ_R^{comp} produces exactly the same diagrams as in Φ_S^{comp}.
- **Par/tensor case**: e_{cut} is a ⅋/⊗ cut with ℓ_E(e₁) = ⅋ and ℓ_E(e₂) = ⊗, with in(e₁) = (\overleftarrow{v₁}, \overrightarrow{v₁}) and in(e₂) = (\overleftarrow{v₂}, \overrightarrow{v₂}). The cut is duplicated; diagrams of Φ_R^{comp} and Φ_S^{comp} are equal up to change of function symbols (structural equivalence ≃_S).

### §67.10 Theorem (Simulation of reduction for proof-nets) (p.314)
For an MLL+MIX proof-net R such that R ~~>* S with S in normal form:
$$\text{AEx}(\Phi_R^{\text{comp}}) \simeq_S \Phi_S^{\text{ax}}$$

*Proof*: Induction on the number n of steps of cut-elimination.
- Base case n = 0: R already in normal form, Φ_R^{comp} = Φ_R^{ax}, so AEx(Φ_R^{comp}) = AEx(Φ_R^{ax}) = Φ_R^{ax}.
- Induction step n = n'+1: By hypothesis, if R ~~>^{n'} S then AEx(Φ_R^{comp}) = Φ_S^{ax}. If R₀ ~~> R ~~>^{n'} S, by Lemma 67.9 and R₀ ~~> R: AEx(Φ_{R₀}^{comp}) ≃_S AEx(Φ_R^{comp}). By R ~~>^{n'} S and induction hypothesis, AEx(Φ_R^{comp}) = Φ_S^{ax}. By transitivity of ≃_S: AEx(Φ_{R₀}^{comp}) ≃_S Φ_S^{ax}. □

---

## §68 Simulation of Danos-Regnier correctness test (pp. 315–322)

### §68.1 Strategy
Danos-Regnier tests = correctness hypergraphs without axioms. They are translated by a constellation that reproduces the hypergraph structure of the test. No dynamics: a 3-ary tensor link relating inputs u, v to output w becomes the 3-ary star [-u(X), -v(X), +w(X)]. Conclusions of the whole proof-structure become uncoloured rays.

### §68.3 Definition (MLL test) (p.315)
Let S be a proof-structure and φ one of its switchings. The *test* associated with S^φ is the constellation:
$$\Phi_S^\varphi := \Phi_S^{\text{cut}} \uplus \sum_{v \in V^{S^\varphi}} v^\star$$

where the translation v^★ of a vertex v conclusion of a hyperedge e is:
- ℓ_E(e) = ax: $v^\star = \begin{bmatrix} -\text{addr}_S(v) \\ +v(X) \end{bmatrix}$
- ℓ_E(e) = ⅋_L and in(e) = (u, w): $v^\star = \begin{bmatrix} -u(X) \\ +v(X) \end{bmatrix} + \begin{bmatrix} -w(X) \\ \end{bmatrix}$ — more precisely: $\begin{bmatrix} -u(X) \\ +v(X) \end{bmatrix} + \begin{bmatrix} -w(X) \\ \end{bmatrix}$

  Actually (verbatim from §68.3):
  - ℓ_E(e) = ⅋_L, in(e) = (u,w): $v^\star = \begin{bmatrix} -u(X) \\ +v(X) \end{bmatrix} + \begin{bmatrix} -w(X) \end{bmatrix}$ — note the second star is unary
  - ℓ_E(e) = ⅋_R, in(e) = (u,w): $v^\star = \begin{bmatrix} -u(X) \\ -w(X) \end{bmatrix} + \begin{bmatrix} +v(X) \end{bmatrix}$ — wait, verbatim:

**Verbatim from §68.3** (exact):
- if ℓ_E(e) = ax then $v^\star = \begin{bmatrix} -\text{addr}_S(v) \\ +v(X) \end{bmatrix}$
- if ℓ_E(e) = ⅋_L and in(e) = (u,w) then $v^\star = \begin{bmatrix} -u(X) \\ +v(X) \end{bmatrix} + \begin{bmatrix} -w(X) \end{bmatrix}$ (two-star sum; second is unary)
- if ℓ_E(e) = ⅋_R and in(e) = (u,w) then $v^\star = \begin{bmatrix} -u(X) \\ -w(X) \end{bmatrix} + \begin{bmatrix} +v(X) \end{bmatrix}$ (second unary)
- if ℓ_E(e) = ⊗ and in(e) = (u,w) then $v^\star = \begin{bmatrix} -u(X),\ -w(X) \\ +v(X) \end{bmatrix}$ (3-ray star)
- if v ∈ Concl(S) then $v^\star = \begin{bmatrix} -v(X) \\ v(X) \end{bmatrix}$

The last case (v ∈ Concl(S)) has uncoloured rays representing conclusions.

### §68.5 Colour wrapping (p.316)
To prevent test rays from interacting with vehicle rays at the wrong atoms: wrap +u(t) and -u(t) with a colour +v to obtain +(+u(t)) and -v(-u(t)). The pre-executed compact form (used in practice) is stars for each connected component linking inputs to unpolarised conclusion outputs.

### §68.7 Goal of the simulation (p.316)
When making a fully positively polarised vehicle interact with a test, the aim is to obtain [v₁(X), ..., v_n(X)] where Concl(S) = {v₁, ..., v_n}. This corresponds to the correctness hypergraph being connected and acyclic:
- Several connected components → several stars in the normal form.
- Cycles → infinitely many saturated diagrams (divergence).

### §68.14 Proposition (p.318)
If a connected multiplicative correctness hypergraph S^φ has no conclusion then it is cyclic.

### §68.15 Definition (Full head polarisation) (p.319)
Let Φ be a constellation. Its *full head polarisation* is a constellation $\overset{+}{\Phi}$ defined by $I_{\overset{+}{\Phi}} := I_\Phi$, $\overset{+}{\Phi}[i] := \Phi[i]$ and:
- Φ[i][j] = f(r₁,...,r_k) → $\overset{+}{\Phi}[i][j] := +f(r₁,...,r_k)$
- Φ[i][j] = -c(r₁,...,r_k) → $\overset{+}{\Phi}[i][j] := +c(r₁,...,r_k)$
- Φ[i][j] = +c(r₁,...,r_k) → $\overset{+}{\Phi}[i][j] := +c(r₁,...,r_k)$

where F = F₀ ⊎ F₋ ⊎ F₊, {f, c} ⊆ F₀, -c ∈ F₋, +c ∈ F₊.

### §68.17 Lemma (Structural equivalence of correctness hypergraphs) (p.319)
Let S^φ := (V, E, end, ℓ) be a correctness hypergraph for a switching φ. Let
$$\mathfrak{D}[\overset{+}{\Phi}_S^{\text{ax}} \uplus \text{AEx}(\Phi_S^\varphi)] := (V_\mathfrak{D}, E_\mathfrak{D}, \text{end}_\mathfrak{D})$$
be the dependency graph of its translation by Definition 69.15. There is a bijection ρ : V → V_\mathfrak{D} preserving adjacency.

### §68.18 Corollary (p.320)
Let S^φ be a correctness hypergraph for a switching φ. Let $\mathfrak{D}[\Phi_S^\varphi]$ be the dependency graph of its translation by Definition 69.15. We have:
S^φ is connected or acyclic if and only if $\overset{+}{\Phi}_S^{\text{ax}} \uplus \text{AEx}(\Phi_S^\varphi)$ is.

### §68.19 Theorem (Stellar correctness criterion) (p.320)
A proof-structure S such that Concl(S) = {v₁, ..., v_n} is MLL-certifiable (cf. Definition 30.3) if and only if for all switchings φ, we have:
$$\text{AEx}(\overset{+}{\Phi}_S^{\text{ax}} \uplus \text{AEx}(\Phi_S^\varphi)) = [v_1(X), ..., v_n(X)]$$

*Proof*:
- (⇒) S is MLL-certifiable → by DR criterion all switchings give a connected acyclic S^φ → by Corollary 68.18, $\overset{+}{\Phi}_S^{\text{ax}} \uplus \text{AEx}(\Phi_S^\varphi)$ is connected and acyclic → by Definition 69.15 connexions in tests are between identical terms and all rays are deterministic, making them perfect (Definition 62.15) → $\overset{+}{\Phi}_S^{\text{ax}} \uplus \text{AEx}(\Phi_S^\varphi)$ is perfect → unique diagram → apply compression/fusion strategy (Definition 63.2) → only rays left are unpolarised conclusions v₁(X), ..., v_n(X) → normal form [v₁(X), ..., v_n(X)].
- (⇐) AEx(...) = [v₁(X), ..., v_n(X)] → by contradiction: if S^φ has ≥ 2 connected components → normalisation into several stars → contradicts single star output. If S^φ is cyclic → cycle produces infinitely many closed diagrams normalising into [] or infinitely many conclusion-containing stars → contradicts output. Therefore S^φ is connected and acyclic for all φ → S is MLL-certifiable. □

### §68.21 Corollary (p.321)
Let S be a proof-structure and $\Phi := \overset{+}{\Phi}_S^{\text{ax}} \uplus \text{Ex}(\Phi_S^\varphi)$ be the constellation corresponding to the correctness hypergraph S^φ for some switching φ. We have:
- S^φ is acyclic ⟺ D[Φ] is acyclic ⟺ |Ex(Φ)| < ∞
- S^φ is connected and acyclic ⟺ D[Φ] is a deterministic tree ⟺ |Ex(Φ)| = 1
- S^φ is connected and acyclic ⟺ Φ normalises into the star of its uncoloured rays

### §68.22–24 Problem with tests containing cuts (pp. 322–323)
Correctness tests interact correctly only with **cut-free** proof-structures. When a proof-structure has cuts, the test after cut-elimination (a constellation [3(X), 6(X)]) cannot be tested with the original vehicle containing cuts — the test for ⊢ A, A^⊥ would require evaluating the entire term before type-checking. Consistently with the philosophy of transcendental syntax: correctness tests are applied on cut-free proof-structures only (§68.24).

---

## §69 Construction of multiplicative formulas (pp. 323–331)

### §69.1–2 Overview (p.323)
Formulas are sets of constellations w.r.t. an orthogonality relation. §68.21 suggests three orthogonality relations: ⊥^{fin}, ⊥^1, and ⊥^R.

**Convention** (§69.3): In §69, write Ex for AEx.

### §69.4 Definition (Orthogonality) (p.323)
Binary relations of *orthogonality* between two constellations Φ₁ and Φ₂ w.r.t. a set of colours C ⊆ F₊ ⊎ F₋:
- Φ₁ ⊥^{fin}_C Φ₂ when |Ex_C(Φ₁ ⊎ Φ₂)| < ∞
- Φ₁ ⊥^1_C Φ₂ when |AEx_C(Φ₁ ⊎ Φ₂)| = 1
- Φ₁ ⊥^R_C Φ₂ when Ex_C(Φ₁ ⊎ Φ₂) = {Roots(Φ₁ ⊎ Φ₂)} where Roots(Φ) is the star of uncoloured rays in Φ.

The **orthogonal** of a set of constellations A:
$$\mathbf{A}^{\perp_C} := \{\Phi \mid \forall \Phi' \in \mathbf{A},\ \Phi \perp_C \Phi'\}$$

### §69.5 (p.323)
⊥^R is the favourite orthogonality: it forces full connection between vehicle and test, as in the proof-as-partitions approach. ⊥^{fin} and ⊥^1 are more lax.

### §69.7 (p.324)
- ⊥^{fin} defines a fully complete model of MLL+MIX.
- ⊥^1 and ⊥^R define a fully complete model of MLL.

### §69.8 Lemma (Invariance of orthogonality under execution) (p.324)
Let Φ and Φ' be constellations such that ⋂_C(Φ, Φ') = ∅ for a set of colours C ⊆ F₊ ⊎ F₋. We have Φ ⊥_C Φ' if and only if Ex_C(Φ) ⊥_C Φ' for ⊥_C ∈ {⊥^1_C, ⊥^{fin}_C, ⊥^R_C}.

---

### Usine interpretation (pp. 324–327)

#### §69.10 (p.324)
Usine (Factory) = effective verification. Formulas are constructed by generalising logical correctness: tests for a sequent ⊢ Γ are built from the sequent's syntax tree, independently of proof-structures.

#### §69.11 Definition (Type label) (p.324)
A *type label* is an object A associated to a finite set of constellations Tests(A) called its *tests*. A constellation Φ is of type A w.r.t. ⊥ iff Φ ∈ Tests(A)^⊥.

#### §69.15 Definition (Test of a sequent) (p.325)
Let ⊢ Γ be a sequent of MLL where Γ ⊆ F_MLL and all variables are distinct. Define the **syntax tree** ST(A) of an MLL formula A inductively:
- ST(X_i) and ST(X_i^⊥) are vertices labelled by X_i and X_i^⊥ respectively.
- ST(A ⊗ B) is a hyperedge labelled by ⊗ linking the conclusion of ST(A) and ST(B) as sources and having a vertex labelled A ⊗ B as target.
- ST(A ⅋ B) is a hyperedge labelled by ⅋ linking the conclusion of ST(A) and ST(B) as sources and having a vertex labelled A ⅋ B as target.

The **syntax hypergraph** ST(⊢ Γ) is the hypergraph disjoint union of all ST(Aᵢ) for Aᵢ ∈ Γ. A switching φ (cf. Definition 30.16) still applies on ST(⊢ Γ) as for correction hypergraphs. Write ST(⊢ Γ)^φ for the switching φ applied on ST(⊢ Γ).

The **test** associated with sequent ⊢ Γ and switching φ is the constellation Test(⊢ Γ)^φ such that I_{Test(⊢ Γ)^φ} = V^{ST(⊢ Γ)^φ} (indexed by vertices of the syntax tree) and Test(⊢ Γ)^φ[v] := v^★.

The **set of tests**: Tests(⊢ Γ) := {Test(⊢ Γ)^φ | φ is a switching of ST(⊢ Γ)}.

**Example** (§69.16, p.325):
$$\text{Tests}(\vdash A, A^\perp)^\varphi := \begin{bmatrix} -A(X) \\ A(X) \end{bmatrix} + \begin{bmatrix} -A^\perp(X) \\ A^\perp(X) \end{bmatrix}$$

#### §69.19 Definition (Adapter) (p.326)
Let Φ be a constellation. An *adapter* for Φ is a star [r, r'] where op(r) and op(r') are polarised rays of Φ such that op(r) ⋈̸ op(r') (artificially links two rays which could not be linked using a star [r, r']).

#### §69.22 Definition (Typing) (p.327)
We say that a constellation Φ is of type ⊢ Γ, written ⊢ Φ : Γ, when $\Phi \in \text{Ex}(\Phi_{\Gamma}^\varphi \uplus \Phi_\mu)^\perp$ for a set of adapters Φ_μ and all switchings φ of ⊢ Γ.

#### §69.23 Proposition (Reformulation of logical correctness) (p.327)
A cut-free proof-structure S is MLL-certifiable if and only if there exists a sequent ⊢ Γ and a constellation of adapters Φ such that $\vdash \Phi_S^{\text{ax}} : \Gamma$ with ⊥ ∈ {⊥^1, ⊥^R}. The same statement holds for MLL+MIX w.r.t. ⊥^{fin}.

#### §69.27 Definition (Well-formed vehicle) (p.328)
Let Φ be a constellation defined in a coloured signature (V, F, ar, ○, |·|) with F := F₀ ⊎ F₊ ⊎ F₋. It is a *well-formed vehicle* if it is:
1. finite;
2. only made of binary stars [f_i(t_i), f_j(t_j)];
3. all rays are disjoint, i.e. not α-unifiable;
4. for each f_k, we have f_k ∈ F₊ ⊎ F₀;
5. there is at least one f_k such that f_k ∈ F₊;
6. all t_k are stacks of directions: t ::= X | 1 · t | r · X.

---

### Usage interpretation (pp. 328–331)

#### §69.28–29 (p.328)
Usage = Girard's interactive typing. Constellations are grouped into arbitrary sets called **pre-behaviours**, giving rise to a notion of formula; **behaviours** correspond to actual formulas of linear logic.

#### §69.29 Definition (Pre-behaviour) (p.328)
A *pre-behaviour* A is a set of constellations.

#### §69.30 Definition (Behaviour) (p.329)
A pre-behaviour A is a *behaviour* when there exists a pre-behaviour B such that A = B^⊥.

#### §69.31 Lemma (Invariance of typing under execution) (p.329)
Let Φ be a constellation and A a behaviour such that ⋂_C(Φ, Φ') = ∅ for all Φ' ∈ A^⊥. We have Φ ∈ A if and only if Ex_C(Φ) ∈ A.

#### §69.32 Proposition (Bi-orthogonal closure) (p.329)
A pre-behaviour A is a behaviour iff A = A^{⊥⊥}.

#### §69.33 Definition (Disjointness of behaviours) (p.329)
Let A and B be two behaviours and C ⊆ F₊ ⊎ F₋. They are *disjoint* when for all Φ_A ∈ A and Φ_B ∈ B, we have ⋂_C(Φ_A, Φ_B) = ∅.

#### §69.35 Definition (Pre-tensor) (p.329)
Let A and B be disjoint pre-behaviours. Their *pre-tensor*:
$$\mathbf{A} \odot \mathbf{B} = \{\Phi_1 \uplus \Phi_2 \mid \Phi_1 \in \mathbf{A},\ \Phi_2 \in \mathbf{B}\}$$

#### §69.36 Definition (Tensor) (p.329)
Let A and B be disjoint behaviours. Their *tensor*:
$$\mathbf{A} \otimes \mathbf{B} = (\mathbf{A} \odot \mathbf{B})^{\perp\perp}$$

#### §69.39–40 Definition (Par and linear implication) (p.330)
Let A, B be disjoint behaviours. Define:
$$\mathbf{A} \mathbin{⅋} \mathbf{B} = (\mathbf{A}^\perp \otimes \mathbf{B}^\perp)^\perp \qquad \text{and} \qquad \mathbf{A} \multimap \mathbf{B} = \mathbf{A}^\perp \mathbin{⅋} \mathbf{B}$$

**Remark** (§69.41): Commutativity and associativity of ⊗ are preserved for ⅋: A ⅋ B = (A^⊥ ⊗ B^⊥)^⊥ = (B^⊥ ⊗ A^⊥)^⊥ = B ⅋ A. (Exchange rule is implicit.)

#### §69.43 Theorem (Associativity of pairwise execution) (p.330)
Choose C ⊆ F₊ ⊎ F₋. For constellations Φ₁, Φ₂, Φ₃ such that ⋂_C(Φ₁, Φ₂, Φ₃) = ∅:
$$\text{Ex}_C(\Phi_1 \uplus \text{Ex}_C(\Phi_2 \uplus \Phi_3)) = \text{Ex}_C(\text{Ex}_C(\Phi_1 \uplus \Phi_2) \uplus \Phi_3)$$

#### §69.44 Theorem (Trefoil Property) (p.330)
Let C ⊆ F₊ ⊎ F₋. For constellations Φ₁, Φ₂, Φ₃ with i, j, k ∈ {1,2,3} such that ⋂_C(Φ₁, Φ₂, Φ₃) = ∅:
$$\Phi_1 \perp_C \text{Ex}_C(\Phi_2 \uplus \Phi_3) \text{ iff } \text{Ex}_C(\Phi_1 \uplus \Phi_2) \perp_C \Phi_3$$

#### §69.46 Corollary (Adjunction) (p.331)
Choose C ⊆ F₊ ⊎ F₋. For all constellations Φ_f, Φ_a, Φ_b such that ⋂_C(Φ_a, Φ_b) = ∅:
$$\Phi_f \perp_C \Phi_a \uplus \Phi_b \text{ iff } \text{Ex}_C(\Phi_f \uplus \Phi_a) \perp_C \Phi_b$$

#### §69.48 Proposition (Alternative linear implication) (p.332)
Let A, B be two disjoint behaviours. We have:
$$\mathbf{A} \multimap \mathbf{B} = \{\Phi_f \mid \forall \Phi_a \in \mathbf{A},\ \text{Ex}(\Phi_f \uplus \Phi_a) \in \mathbf{B}\}$$

---

## §70 Soundness and completeness (pp. 332–339)

### §70.1 Overview (p.332)
This section formalises:
1. Girard's adequacy between Usine and Usage.
2. Classical soundness and completeness w.r.t. proof-net theory.

---

### Adequacy between Usine and Usage (pp. 332–334)

#### §70.2 (p.332)
The favourite orthogonality for this subsection is ⊥^R, which requires that the normal form is the star of roots (uncoloured rays) from the two interacting constellations.

#### §70.3 (p.332)
In transcendental syntax, execution expresses both cut-elimination and correctness testing. The difference is the shape of interacting objects:
- Cut-elimination: two vehicles interact.
- Correctness testing: a vehicle and a (compact) test interact.

The orthogonality ⊥^R formalises both: "correct" interaction by cut-elimination means the two vehicles Φ and Φ' interacting only leave the star of uncoloured roots (all cut-related rays eliminated), i.e. Φ ⊥^R Φ'.

#### §70.5 Theorem (Multiplicative adequacy) (p.333)
Let Φ and Φ' be two well-formed vehicles. If $\vdash \overset{+}{\Phi} : \Gamma$ and $\vdash \overset{+}{\Phi'} : \Gamma^\perp$, then Φ ⊥^R Φ' ⊎ Ψ where Ψ is a constellation of fully negative adapters (representing cuts).

*Proof*: This is another formulation of Theorem 67.10. □

#### §70.6 (p.333)
Adequacy is a relation between Usine and Usage: Usine tests guarantee the shape of objects (proof-structures). If ⊢ Φ : Γ then Φ ∈ [⊢ Γ], meaning a constellation passing the tests of ⊢ Γ behaves like an object of the idealised type [[⊢ Γ]]. This implies Tests(⊢ Γ)^⊥ ⊆ [[⊢ Γ]].

---

### A complete model of MLL+MIX (pp. 334–338)

#### §70.8 (p.334)
Formula labels are interpreted by behaviours where distinct behaviours are associated with occurrences of variables by a **basis of interpretation**. Following Seiller [Sei12a, Def. 46], the behaviours corresponding to formula labels are *localised* formulas: defined using the same grammar as MLL formulas, except that variables are of the form X_i(t) where t is a term (representing the path address) used to distinguish occurrences of the same atomic formula X_i.

#### §70.9 Definition (Basis of interpretation) (p.334)
A *basis of interpretation* is a function Ω producing a behaviour Ω(A, i, t) when given a formula A ∈ F_MLL, a natural number i (index of occurrence) and a term t ∈ Addr_x(S). A basis of interpretation has to satisfy: Ex(Ω(A, i, t) + [+A(t), +B(u)]) = Ω(B, j, u) when i = j, and otherwise Ω(A, i, t) and Ω(B, j, u) are disjoint, such that A + φ = {Φ + φ | Φ ∈ A} for a behaviour A and a star φ.

#### §70.10 Definition (Interpretation of MLL formulas) (p.334)
Given a basis of interpretation Ω, a formula C representing the conclusion of a sequent, and an MLL formula occurrence A identified by a unique unary function symbol A(X) (cf. Definition 66.7), define the *interpretation* [[A, t]]_Ω along Ω and a term t (encoding the address of A w.r.t. a conclusion C) inductively:
- [[C, X_i, t]]_Ω = Ω(C, i, t)
- [[C, X_i^⊥, t]]_Ω = Ω(C, i, t)^⊥
- [[C, A ⊗ B, t]]_Ω = [[C, A, 1 · t]]_Ω ⊗ [[C, B, r · t]]_Ω
- [[C, A ⅋ B, t]]_Ω = [[C, A, 1 · t]]_Ω ⅋ [[C, B, r · t]]_Ω

Write [[C]] for [[C, C, X]] and extend the interpretation to sequents:
$$[\![\vdash C_1, ..., C_n]\!]_\Omega := [\![C_1]\!]_\Omega \mathbin{⅋} \cdots \mathbin{⅋} [\![C_n]\!]_\Omega$$

**Remark** (§70.11): The interpretation of an axiom under a basis Ω is defined by [[⊢ X₁, X₁^⊥]]_Ω = [[X₁]]_Ω ⅋ [[X₁^⊥]]_Ω = Ω(X₁, 1, X) ⅋ Ω(X₁^⊥, 1, X)^⊥.

#### §70.12–13 Full soundness setup (pp. 334–335)
For MLL+MIX the orthogonality ⊥^{fin} is used exclusively in this subsection. Instead of the usual soundness, a stronger *full soundness* [Sei12a, Theorem 55] is proved, which takes cut-elimination into account. In terms of adequacy: showing ⊢ Φ : Γ implies Φ ∈ [[⊢ Γ]]_Ω for some Ω, except that for ⊢ Φ : Γ only constellations coming from proof-nets are considered.

#### §70.17 Theorem (Full soundness for MLL+MIX) (p.335)
Let ⊢ S : Γ be an MLL+MIX proof-net and Ω a basis of interpretation. We have:
$$\text{Ex}(\Phi_S^{\text{comp}}) \in [\![\vdash \Gamma]\!]_\Omega$$

*Proof*: By induction on the proof-net structure of S.
- ⊢ S : X_i, X_i^⊥: Show $\Phi_S^{\text{ax}} \in [[X_i]]_\Omega \mathbin{⅋} [[X_i^⊥]]_\Omega$. We have $\Phi_S^{\text{ax}} = [+X_i(X), +X_i^⊥(X)]$, so Ex(Φ_S^{ax} ⊎ Φ₂) ∈ Ω(X_i, i, X) which is orthogonal to Φ₁, and by definition of tensor |Ex(Φ₁ ⊎ Ex(Φ₂ ⊎ Φ_S^{ax}))| < ∞.
- ⊢ S : Γ, Δ, A ⊗ B coming from ⊢ S₁ : Γ, A and ⊢ S₂ : Δ, B: By induction hypothesis Φ_S^{ax} ∈ [[⊢ Γ, A]]_Ω and Φ_S^{ax} ∈ [[⊢ Δ, B]]_Ω. By conjugation, obtain Φ_μ ∈ ([[⊢ Γ]]_Ω ⅋ [[A]]_Ω) ⊗ ([[⊢ Δ]]_Ω ⅋ [[B]]_Ω); by Lemma 70.14, ([[⊢ Γ]]_Ω ⅋ [[A]]_Ω) ⊗ ([[⊢ Δ]]_Ω ⅋ [[B]]_Ω) ⊆ [[⊢ Γ]]_Ω ⅋ [[⊢ Δ]]_Ω ⅋ [[A ⊗ B]]_Ω.
- ⊢ S : Γ, A ⅋ B: Follows from induction hypothesis and [[⊢ Γ, A, B]]_Ω = [[⊢ Γ]]_Ω ⅋ [[A]]_Ω ⅋ [[B]]_Ω by definition.
- ⊢ S : Γ, Δ from ⊢ S₁ : Γ and ⊢ S₂ : Δ (MIX rule): By induction hypothesis Φ_{S_1}^{ax} ∈ [[⊢ Γ]]_Ω and Φ_{S_2}^{ax} ∈ [[⊢ Δ]]_Ω. By definition of tensor Φ_S^{ax} = Φ_{S_1}^{ax} ⊎ Φ_{S_2}^{ax} ∈ [[⊢ Γ]]_Ω ⊗ [[⊢ Δ]]_Ω. Then show A ⊗ B ⊆ A ⅋ B in general (using the fact that A ⅋ B = (A^⊥ ⊗ B^⊥)^⊥).
If proof has cuts: by Theorem 67.10, execute its translation so the normal form corresponds to the normal form of the proof (necessarily cut-free). □

#### §70.18 Lemma (p.336)
Let Ω be a basis of interpretation and ⊢ Γ an MLL sequent. Then:
$$\text{Tests}(\vdash \Gamma) \subseteq [\![\vdash \Gamma]\!]_\Omega^{\perp_{\text{fin}}}$$

#### §70.19 Definition (Proof-like constellation) (p.337)
The syntax tree ST(⊢ Γ) of a sequent induces a set of rays ‡Γ by Definition 66.7 by computing the address of each atom in ST(⊢ Γ). A constellation Φ is *proof-like w.r.t.* an MLL sequent ⊢ Γ if it is well-formed and IdRays(Φ) = ‡Γ.

**Example** (§70.20): A constellation proof-like w.r.t. ⊢ X₁^⊥ ⅋ X₂^⊥, X₁ ⊗ X₂ is:
```
[+(X₁^⊥ ⅋ X₂^⊥)(1·X), +(X₁ ⊗ X₂)(1·X)] + [+(X₁^⊥ ⅋ X₂^⊥)(r·X), +(X₁ ⊗ X₂)(r·X)]
```
But also the wrong linking is proof-like.

#### §70.21 Theorem (Completeness for MLL+MIX) (p.338)
If a constellation Φ ∈ [[⊢ Γ]]_Ω is proof-like w.r.t. ⊢ Γ, then there exists an MLL+MIX proof-net ⊢ S : Γ such that Φ = Φ_S^{ax}.

*Proof*: A proof-like Φ ∈ [[⊢ Γ]]_Ω can be considered as the interpretation of a proof-structure with only axioms; construct S by placing axioms on ST(⊢ Γ). Since Φ ∈ [[⊢ Γ]]_Ω, by Lemma 70.18 for all switchings φ of ⊢ Γ, Test(⊢ Γ)^φ = Φ_S^φ ⊥ Φ, excluding "wrong linking". By Corollary 68.21, S is acyclic, satisfying correctness for MLL+MIX. Therefore S is a proof-net of vehicle Φ. □

---

### A complete model of MLL (pp. 338–339)

#### §70.22 (p.338)
The soundness property holds for MLL with the same arguments, whether using ⊥^1 or ⊥^R as orthogonality. In this subsection, ⊥ means ⊥^1 or ⊥^R.

#### §70.23 Theorem (Full soundness for MLL) (p.338)
Let ⊢ S : Γ be an MLL proof-net and Ω a basis of interpretation. We have:
$$\text{Ex}(\Phi_S^{\text{comp}}) \in [\![\vdash \Gamma]\!]_\Omega$$

*Proof*: Exactly as for Theorem 70.17. The only difference is in the axiom case: need to show Ex(Φ₁ ⊎ Φ₂ ⊎ Φ_S^{ax}) = Roots(Φ₁ ⊎ Φ₂ ⊎ Φ_S^{ax}) (respectively, |Ex(...)| = 1). The basis of interpretation properties ensure that Φ₂ ⊎ Φ_S^{ax} will be orthogonal to Φ₁. Hence Ex(Φ₁ ⊎ Φ₂ ⊎ Φ_S^{ax}) = Roots(Φ₁ ⊎ Φ₂ ⊎ Φ_S^{ax}) (resp. |Ex(...)| = 1). □

#### §70.24–25 Completeness for MLL: strict interpretations (pp. 338–339)
The proof of Lemma 70.18 does not hold for MLL because a general sequent ⊢ A₁, ..., A_n for Aᵢ atomic is used for the base case, valid for MLL+MIX (only acyclicity required) but not for MLL (connectedness required). Instead, identify [[⊢ Γ]]_Ω and Tests(⊢ Γ)^⊥ directly and prove Tests(⊢ Γ) ⊆ Tests(⊢ Γ)^{⊥⊥} (always true [JS21, Prop. 7]). This is done via **strict interpretations**.

#### §70.25 Definition (Strict interpretations) (p.339)
Define two strict interpretations for a given basis of interpretation Ω and MLL sequent ⊢ Γ:
$$\langle\!\langle \vdash \Gamma \rangle\!\rangle^1_\Omega = \text{Tests}(\vdash \Gamma)^{\perp^1} \qquad \langle\!\langle \vdash \Gamma \rangle\!\rangle^R_\Omega = \text{Tests}(\vdash \Gamma)^{\perp^R}$$

#### §70.26 Theorem (Completeness for MLL) (p.339)
If a constellation $\Phi \in \langle\!\langle \vdash \Gamma \rangle\!\rangle^R_\Omega$ (respectively $\Phi \in \langle\!\langle \vdash \Gamma \rangle\!\rangle^1_\Omega$) is proof-like w.r.t. a provable sequent ⊢ Γ of MLL, then there exists an MLL proof-net ⊢ S : Γ such that Φ = Φ_S^{ax}.

*Proof*: Begins like the proof of completeness for MLL+MIX (Theorem 70.21) and reaches the construction of a proof-structure with axioms translated into Φ. Now Φ ∈ ⟨⟨⊢ Γ⟩⟩^R_Ω (resp. ⟨⟨⊢ Γ⟩⟩^1_Ω) implies that in particular Φ passes the Danos-Regnier correctness test for MLL (by Corollary 68.21). Therefore the proof-structure we constructed must be correct. □

#### §70.27 (p.339)
If Φ ∈ ⟨⟨⊢ Γ⟩⟩^X_Ω for some Ω, MLL sequent ⊢ Γ, and X ∈ {1, R}, its Danos-Regnier tests Φ₁, ..., Φ_n are constellations of (⟨⟨⊢ Γ⟩⟩^X_Ω)^⊥. This formalises the intuition in proof-nets that tests are proofs of the dual.

---

## §71 The case of multiplicative units (pp. 339–341)

### §71.1–2 (p.339)
Multiplicative units are problematic but some speculative results hold. The aim is to find behaviours corresponding to the neutral elements for ⊗ (which is 1) and ⅋ (which is ⊥) respectively.

Define a pre-behaviour ⊥⊥ (pole) such that Φ ⊥ Φ' iff Ex(Φ ⊎ Φ') ∈ ⊥⊥, and ⊥⊥ must be closed under *anti-evaluation*: if Φ ∈ ⊥⊥ and Ex(Φ') = Φ then Φ' ∈ ⊥⊥. For ⊥^R: ⊥⊥ is the set of all constellations normalising into a single uncoloured star.

### §71.3 (p.340)
The natural choice of behaviour for the neutral element of ⊗ w.r.t. ⊥^R is the pre-behaviour {∅} (only containing the empty constellation) since Φ ⊎ ∅ = Φ for any constellation Φ.

### §71.4 Proposition (p.340)
The pre-behaviour {∅} is a behaviour.

*Proof*: {∅}^⊥ = ⊥⊥. A constellation Φ ∈ ⊥⊥^⊥ must self-normalise into the set of its roots (since ∅ has no effect). Hence {∅}^⊥^⊥ = ⊥⊥^⊥ = {∅}. □

### §71.5 Definition (One) (p.340)
$$\mathbf{1} := \{\emptyset\} = \bot\!\!\!\bot^\perp$$

### §71.6 Proposition (p.340)
A ⊗ 1 = A for any behaviour A.

*Proof*: A ⊗ 1 = {Φ_A ⊎ ∅ | Φ_A ∈ A}^{⊥⊥} = {Φ_A | Φ_A ∈ A}^{⊥⊥} = A^{⊥⊥} = A. □

### §71.7 (p.340)
Bottom is defined as: 1^⊥ = ⊥⊥.

### §71.8 Proposition (p.340)
The pre-behaviour 1^⊥ = {∅}^⊥ = ⊥⊥ is a behaviour.

*Proof*: Since A^⊥ = A^{⊥⊥⊥} for any behaviour A [JS21, Corollary 9], it follows that 1^⊥ (and thus {∅}^⊥) is a behaviour. □

### §71.9 Definition (Bottom) (p.340)
$$\bot := \mathbf{1}^\perp$$

### §71.10 Proposition (p.340)
A ⅋ ⊥ = A for any behaviour A when considering ⊥^R.

*Proof*: A ⅋ ⊥ = (A^⊥ ⊗ ⊥^⊥)^⊥ = (A^⊥ ⊗ {∅}^{⊥⊥})^⊥ = (A^⊥ ⊗ {∅})^⊥ = A^{⊥⊥} = A (since A is a behaviour). □

### §71.11 Proposition (p.341)
A^⊥ = A ⊸ ⊥ for any behaviour A when considering ⊥^R.

*Proof*: A ⊸ ⊥ = A^⊥ ⅋ ⊥. Since ⊥ is a neutral element for ⅋, it follows that A^⊥ ⅋ ⊥ = A^⊥. □

### §71.12–14 Testing units (pp.341)
The interactive types for units correspond to idealised neutral elements (Usage). For Usine:
- To tell if Φ ∈ ⊥ (= {∅}^⊥), use the set of tests {∅}: test Φ against the empty constellation ∅; if Φ ⊥ ∅ then Φ ∈ ⊥.
- For **1**: just need to tell if Φ = ∅.

This provides a notion of correct constellations for multiplicative units. However, they do not exactly correspond to units of proof-nets because (§71.14): in proof-nets, the ⊥ constant is introduced in a context Γ to which it is dependent, becoming disconnected under a switching → breaks connectedness for the Danos-Regnier criterion. The usual hack: consider jumps (§30) between ⊥ nodes and either axioms or 1 nodes. Girard's idea [Gir18a, §2.1.1]: encode multiplicative units in second-order linear logic because of this non-local dependency (cf. §44).

---

## §72 Discussion: what is a multiplicative proof? (pp. 341–342)

### §72.1 (p.341)
Under orthogonality ⊥^R, correctness tests characterise the shape of proofs and testing collapses to a single star of uncoloured rays by edge contraction. The test for ⊗ is a 3-ary star with two inputs and one output: it forces any interacting constellation to be made of two disjoint connected components — the test for ⊗ *reunites* proof-structures. As for ⅋, the two tests ⅋_L and ⅋_R are made of two disjoint parts — they *separate* proof-structures. MLL proofs are about how primitive data are organised in terms of reunion/separation.

### §72.2–4 Further observations (pp. 341–342)
- An axiom [+1(X), +2(X)] (identity function) can be connected with [+3(X)] by cut [-1(X), -3(X)] to obtain [+2(X)], or by cut [-2(X), -3(X)]. This expresses the equality A ⊸ B = B^⊥ ⊸ A^⊥ of linear logic.
- Whether we have a proof of X₁^⊥ ⅋ X₁ or A^⊥ ⅋ A for any multiplicative formula A: the translation is materialised by some binary star [r, r'] where r and r' are as complex (in their internal structure) as A is.
- The difference between X₁^⊥ and X₁ looks rather artificial in stellar resolution: both are translated into two different rays. It does not mean negation does not exist, but that it seems to be an external consideration over constellations.

### §72.3 Real multiplicatives (p.342)
The multiplicative proof-structures obtained are not "real" MLL proof-structures since multiplicative proof-structures are polymorphic (atomic formulas can be replaced by more complex ones). The stellar interpretation gives "first-order" multiplicatives free of external considerations. Actual polymorphism requires adding more structure — that is the role of Girard's epidictics.

### §72.4 Hidden duplication in MLL proof-structures (p.342)
In GoI, MLL proofs are represented by permutations over atoms where cuts are partial injections linking atoms. In proof-net theory, cuts are links between *conclusions* or whole proof-structures, so cuts are duplicated and distributed to atoms. In the stellar interpretation: the complex shape of proof-structures is internalised directly into terms of rays; to have the cut distributed to its two left premises and two right premises, one must use variables. This shows that technically, MLL proof-net theory is not exactly duplication-free: it hides non-linear behaviours in how terms of the translation are designed.

---

## Summary table: key objects

| Object | Definition | Location |
|--------|-----------|----------|
| Basis of representation B | Polarised signature (V, F, ar, ○, \|·\|) with F₀={1,r,·}∪{u}, F₊={+u}, F₋={-u} | §66.2 |
| Path address pAddr_S(v) | Inductive on proof-structure shape; encodes tree path from conclusion to atom | §66.7 |
| Address addr_S(v) | c(pAddr_S(v)) for conclusion c | §66.7 |
| Vehicle Φ_S^{ax} | Sum of binary stars [μ(addr_S(←e)), μ(addr_S(→e))] over axioms e | §66.11 |
| Cut constellation Φ_S^{cut} | Sum of binary stars [-←e(X), -→e(X)] over cuts e | §66.11 |
| Computational content Φ_S^{comp} | Φ_S^{ax} ⊎ Φ_S^{cut} | §66.11 |
| Cut-elimination simulation | AEx(Φ_R^{comp}) ≃_S Φ_S^{ax} for R ~~>* S (Thm 67.10) | §67.10 |
| MLL test Φ_S^φ | Φ_S^{cut} ⊎ Σ_{v∈V^{S^φ}} v^★ | §68.3 |
| Stellar correctness | AEx(+Φ_S^{ax} ⊎ AEx(Φ_S^φ)) = [v₁(X),...,v_n(X)] for all φ iff MLL-certifiable | §68.19 |
| Orthogonality ⊥^{fin} | \|Ex_C(Φ₁ ⊎ Φ₂)\| < ∞ — gives complete model of MLL+MIX | §69.4, §69.7 |
| Orthogonality ⊥^1 | \|AEx_C(Φ₁ ⊎ Φ₂)\| = 1 — gives complete model of MLL | §69.4, §69.7 |
| Orthogonality ⊥^R | Ex_C(Φ₁ ⊎ Φ₂) = {Roots(Φ₁ ⊎ Φ₂)} — gives complete model of MLL | §69.4, §69.7 |
| Pre-behaviour | Any set of constellations | §69.29 |
| Behaviour | Pre-behaviour A with A = B^⊥ for some pre-behaviour B; equivalently A = A^{⊥⊥} | §69.30, §69.32 |
| Tensor A ⊗ B | (A ⊙ B)^{⊥⊥} where A ⊙ B = {Φ₁ ⊎ Φ₂ \| Φ₁ ∈ A, Φ₂ ∈ B} | §69.35–36 |
| Par A ⅋ B | (A^⊥ ⊗ B^⊥)^⊥ | §69.40 |
| Linear implication A ⊸ B | A^⊥ ⅋ B | §69.40 |
| Sequent interpretation [[⊢ Γ]]_Ω | [[C₁]]_Ω ⅋ ... ⅋ [[Cₙ]]_Ω; atomic [[X_i, t]]_Ω = Ω(X_i, t) | §70.10 |
| Full soundness MLL+MIX | Ex(Φ_S^{comp}) ∈ [[⊢ Γ]]_Ω for any proof-net S:Γ (w.r.t. ⊥^{fin}) | §70.17 |
| Full soundness MLL | Ex(Φ_S^{comp}) ∈ [[⊢ Γ]]_Ω for any proof-net S:Γ (w.r.t. ⊥^1 or ⊥^R) | §70.23 |
| Completeness MLL+MIX | Proof-like Φ ∈ [[⊢ Γ]]_Ω → ∃ proof-net S:Γ with Φ = Φ_S^{ax} | §70.21 |
| Completeness MLL | Proof-like Φ ∈ ⟨⟨⊢ Γ⟩⟩^R or ⟨⟨⊢ Γ⟩⟩^1 → ∃ proof-net S:Γ with Φ = Φ_S^{ax} | §70.26 |
| Unit 1 | {∅} = ⊥⊥^⊥; neutral for ⊗ | §71.5 |
| Bottom ⊥ | 1^⊥ = ⊥⊥; neutral for ⅋ (w.r.t. ⊥^R) | §71.9–10 |

---

## Implementation notes for open-hypergraphs SMC-rewriting

1. **Stars as morphisms**: A binary star [+c(t), -c'(t')] encodes one wire (the axiom case). Multi-ray stars encode connectives. The constellation Φ_S^{comp} is the coproduct (disjoint union of stars) encoding the entire proof structure.

2. **Execution as SMC composition**: AEx(Φ) implements cut-elimination by term unification (α-unification between polarised rays). The trefoil property (§69.44) ensures this composition is associative — the prerequisite for an SMC.

3. **Addresses encode the tree structure**: pAddr_S(v) uses 1 (left) and r (right) to encode the binary tree structure of formulas. An open hypergraph rewriting step corresponds to one step of fusion in the dependency graph D[Φ].

4. **The DR correctness criterion targets**: The condition AEx(+Φ_S^{ax} ⊎ AEx(Φ_S^φ)) = [v₁(X),...,v_n(X)] is equivalent to the dependency graph being a deterministic tree (§68.21). In open-hypergraph terms: the graph D[Φ] after execution should be a spanning tree with uncoloured leaves.

5. **Orthogonality as typing for behaviours**: ⊥^R is the target orthogonality for MLL (not MLL+MIX which uses ⊥^{fin}). The distinction MLL vs MLL+MIX is exactly connected vs merely acyclic correctness hypergraphs.

6. **Usine (tests) vs Usage (behaviours)**: Usine tests are computed from sequent syntax trees independently of proofs (§69.15). Usage behaviours are bi-orthogonally closed sets of constellations (§69.30). Adequacy (§70.5) says: passing Usine tests implies belonging to the Usage behaviour.

7. **Units**: 1 = {∅} and ⊥ = ⊥⊥. Their correct stellar representatives exist but do not exactly match proof-net units due to the non-local dependency of ⊥ in correctness hypergraphs (§71.14).
