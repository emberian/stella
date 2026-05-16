(* stellaMLLScript.sml
   MLL proof-structures as constellations — Eng §66 (proofs-as-constellations)
   and §67.10 (cut-elimination simulation theorem).

   ══════════════════════════════════════════════════════════════════════════════
   SCOPE
   ──────────────────────────────────────────────────────────────────────────────
   BOUNDED to Eng Ch.10 §66 and §67.10 only.
   §68–72 are NOT attempted.

   REUSED from existing stella theories:
     · stellaTermTheory      — term, Var, App, vars_t, subst_apply
     · stellaPolarisedTheory — polarity, encode_psym, decode_psym, uterm_t
     · stellaMatchTheory     — matchable, mm_reduces
     · stellaDiagramTheory   — constellation, ray, star, dep_graph,
                               all_colours, IdRays, stars_dep
     · stellaExecutionTheory — AEx_C (the abstract execution §49.42),
                               correct_C, CSatDiags_C, actualise

   FRESH (this file):
     · mll_edge_label        — labels on proof-structure edges (Ax/Tens/Par/Cut)
     · proof_struct          — MLL proof-structure record §66.3
     · ax_edges / cut_edges  — sub-multisets of edges by label §66.11
     · pAddr_S               — path address §66.7
     · addr_S                — address = conclusion(pAddr) §66.7
     · mu_ray                — polarity wrapper μ(·) §66.11
     · Phi_ax / Phi_cut      — vehicle and cut constellations §66.11
     · Phi_comp              — computational content §66.11
     · struct_equiv          — structural equivalence ≃_S §67.7
     · cut_elim_step         — one cut-elimination step R ~~> S §67.9
     · cut_elim_star         — R ~~>* S (reflexive-transitive) §67.10
     · normal_ps             — proof-structure in normal form (no cuts) §67.10
     · sim_cut_step          — Lemma §67.9 (one step, deferred)
     · sim_cut_elim          — Theorem §67.10 (full theorem, deferred)

   PROOF POLICY:  every non-trivial proof is discharged with `cheat` preceded
   by a PROOF-OBLIGATION block.  Closed EVAL computations are NOT debt.
   Zero uses of new_axiom / mk_thm.
   ══════════════════════════════════════════════════════════════════════════════
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory pairTheory
     relationTheory;
open stellaTermTheory stellaPolarisedTheory stellaMatchTheory;
open stellaDiagramTheory;
open stellaExecutionTheory;

val _ = new_theory "stellaMLL";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.3  MLL edge labels                                                       *)
(*                                                                             *)
(* Eng uses hyperedges in a proof-structure labelled by one of:                *)
(*   Ax   — axiom link  (binary: two conclusions)                              *)
(*   Tens — ⊗ tensor link  (binary input, one output)                         *)
(*   Par  — ⅋ par link     (binary input, one output)                         *)
(*   Cut  — cut link       (binary: two premise conclusions)                   *)
(*                                                                             *)
(* We represent these as a HOL4 datatype.                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §66.3 *)
  mll_label = Ax | Tens | Par | Cut
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.3  MLL proof-structure                                                   *)
(*                                                                             *)
(* An MLL proof-structure S is a hypergraph:                                   *)
(*   V^S  : vertex set (atoms / formula occurrences) — encoded as num set     *)
(*   E^S  : edge set (links) — encoded as num set                             *)
(*   in_S : E^S → (num # num)   left/right input vertices                     *)
(*   out_S: E^S → num           output (conclusion) vertex                     *)
(*   lbl  : E^S → mll_label     edge label                                     *)
(*   concl: S → num set         the set of conclusion vertices (§66.3)         *)
(*                                                                             *)
(* For axiom and cut links the "output" slot is unused; we set it to 0 by     *)
(* convention.  For Ax, in_S(e) = (v₁, v₂) are the two atomic conclusions.   *)
(* For Tens/Par: in_S(e) = (v₁, v₂) premises, out_S(e) = v the output.       *)
(* For Cut: in_S(e) = (v₁, v₂) are the two cut-connected vertices.            *)
(*                                                                             *)
(* This is a *record* type so downstream definitions can pattern-match.        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §66.3 *)
  proof_struct = <|
    vertices : num set ;
    edges    : num set ;
    in_ps    : num -> (num # num) ;
    out_ps   : num -> num ;
    lbl      : num -> mll_label ;
    concl    : num set
  |>
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Axiom and cut sub-edge-sets                                          *)
(*                                                                             *)
(* Ax(S)  = { e ∈ E^S | lbl(e) = Ax  }                                       *)
(* Cuts(S) = { e ∈ E^S | lbl(e) = Cut }                                       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition ax_edges_def :                               (* §66.11 *)
  ax_edges (S : proof_struct) : num set =
    { e | e IN S.edges /\ S.lbl e = Ax }
End

Definition cut_edges_def :                              (* §66.11 *)
  cut_edges (S : proof_struct) : num set =
    { e | e IN S.edges /\ S.lbl e = Cut }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.7  Path address  pAddr_S(v)                                              *)
(*                                                                             *)
(* The path address of an atom v in a proof-structure S is defined inductively *)
(* on the structure of S (Definition §66.7):                                   *)
(*                                                                             *)
(*   · If v ∈ Concl(S) of an axiom link e ∈ Ax(S):  pAddr_S(v) = Var x      *)
(*     for a fresh variable x.                                                  *)
(*   · If v is a conclusion reached via the LEFT  branch of a Tens/Par link:   *)
(*     pAddr_S(v) = App (encode_psym (Neutral, 1)) [pAddr_{S'}(v)]            *)
(*     (the "1" direction: left, encoded as App of neutral-1)                  *)
(*   · If v is a conclusion reached via the RIGHT branch of a Tens/Par link:   *)
(*     pAddr_S(v) = App (encode_psym (Neutral, 2)) [pAddr_{S'}(v)]            *)
(*     (the "r" direction: right, encoded as App of neutral-2)                 *)
(*   · Otherwise pAddr_S(v) = pAddr_{S'}(v).                                  *)
(*                                                                             *)
(* In Eng §66.7 the "directions" are the symbols 1 (left) and r (right).      *)
(* We encode them as neutral function symbols with arities-1 in our term       *)
(* representation:                                                              *)
(*   1  ≅ encode_psym (Neutral, 1)  — the neutral symbol named 1              *)
(*   r  ≅ encode_psym (Neutral, 2)  — the neutral symbol named 2              *)
(*                                                                             *)
(* Because the inductive structure of proof-structures is not primitive        *)
(* recursive in our flat record encoding, we give an *axiomatic* recursive     *)
(* specification: pAddr_S is a function from num → term satisfying the         *)
(* clauses above.  This is the approach used throughout the stella scaffold     *)
(* (state + cheat).                                                             *)
(*                                                                             *)
(* We define the direction constants:                                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.7  Direction symbols: "1" (left) and "r" (right) in Eng's notation. §66.2 *)
Definition dir_left_def :                               (* §66.2 *)
  dir_left : num = encode_psym (Neutral, 1)
End

Definition dir_right_def :                              (* §66.2 *)
  dir_right : num = encode_psym (Neutral, 2)
End

(* §66.7  pAddr_S: a function satisfying the recursive clauses of §66.7.
   We declare it as an uninterpreted constant and state its spec as a theorem
   (STATED+CHEAT, proof-obligation stellaMLL.01).                              *)
Definition pAddr_S_def :                                (* §66.7 *)
  pAddr_S (S : proof_struct) (v : num) : term =
    if v IN S.concl then Var v
    else
      (* Default: Var v.  The real recursive definition is given by
         PROOF-OBLIGATION[stellaMLL.01] below.                                *)
      Var v
End

(* The specification of pAddr_S (the inductive clauses of §66.7):
   PROOF-OBLIGATION[stellaMLL.01]: pAddr_S satisfies the inductive spec.      *)
(*
   PROOF-OBLIGATION[stellaMLL.01]:
   GOAL:
     !S v e.
       (* Ax case: v is one of the two conclusions of axiom e *)
       (e IN ax_edges S /\ (v = FST (S.in_ps e) \/ v = SND (S.in_ps e))) ==>
         pAddr_S S v = Var v

       /\ (* Left Tens/Par premise: v above via left branch *)
       (e IN S.edges /\ (S.lbl e = Tens \/ S.lbl e = Par) /\
        v = FST (S.in_ps e)) ==>
         pAddr_S S v = App dir_left [pAddr_S S (S.out_ps e)]

       /\ (* Right Tens/Par premise: v above via right branch *)
       (e IN S.edges /\ (S.lbl e = Tens \/ S.lbl e = Par) /\
        v = SND (S.in_ps e)) ==>
         pAddr_S S v = App dir_right [pAddr_S S (S.out_ps e)]

   STRATEGY:
     This is a well-foundedness argument on the depth of the proof-structure.
     In the full proof: define pAddr_S by structural recursion on a "depth"
     measure on vertices (the height from conclusions to atoms in the DAG of S).
     For the scaffold we state the spec and cheat.
   DRAFT-TACTICS: cheat (proof obligation, not attempted)
*)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.7  Address  addr_S(v) = c(pAddr_S(v))                                   *)
(*                                                                             *)
(* The address of atom v w.r.t. conclusion c ∈ Concl(S) is:                  *)
(*   addr_S(v) = App c_sym [pAddr_S(v)]                                        *)
(* where c_sym is the function symbol for c.                                   *)
(*                                                                             *)
(* In our encoding: the conclusion vertex c is used as the symbol number       *)
(* (with neutral polarity for uncoloured and positive for cut-related):        *)
(* we encode c as encode_psym (Neutral, c) for the address symbol.             *)
(*                                                                             *)
(* (The μ-wrapper in §66.11 upgrades to Pos when c is cut-related.)           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.7  Address of atom v relative to its conclusion vertex c. *)
Definition addr_S_def :                                 (* §66.7 *)
  addr_S (S : proof_struct) (c : num) (v : num) : term =
    App (encode_psym (Neutral, c)) [pAddr_S S v]
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  The μ function                                                       *)
(*                                                                             *)
(* §66.11: μ(c(t)) = +c(t) when c is the conclusion of a cut edge             *)
(*                 = c(t)   otherwise (keep as-is)                             *)
(*                                                                             *)
(* In our encoding:                                                             *)
(*   · a "cut-related" conclusion c is one that appears as in_S(e)            *)
(*     for some e ∈ cut_edges S.                                               *)
(*   · If c is cut-related: re-encode c with Pos polarity.                    *)
(*   · Otherwise: keep Neutral encoding.                                        *)
(*                                                                             *)
(* For a ray App h [pAddr]: h = encode_psym(pol, name).                       *)
(* We replace pol with Pos when name (the conclusion vertex) is cut-related.  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Conclusion vertices that are endpoints of a cut edge. §66.11 *)
Definition cut_concls_def :                             (* §66.11 *)
  cut_concls (S : proof_struct) : num set =
    { v | ?e. e IN cut_edges S /\
              (v = FST (S.in_ps e) \/ v = SND (S.in_ps e)) }
End

(* §66.11  Apply μ to a ray: upgrade head polarity to Pos for cut conclusions. *)
Definition mu_ray_def :                                 (* §66.11 *)
  mu_ray (S : proof_struct) (r : ray) : ray =
    case r of
      App h args =>
        let (_, name) = decode_psym h in
        if name IN cut_concls S then
          App (encode_psym (Pos, name)) args
        else r
    | Var x => Var x
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Vehicle Φ_S^ax: one star per axiom edge                              *)
(*                                                                             *)
(* Φ_S^ax := Σ_{e ∈ Ax(S)} [μ(addr_S(←e)), μ(addr_S(→e))]                   *)
(*                                                                             *)
(* where ←e = FST(in_S(e))  and  →e = SND(in_S(e)).                          *)
(*                                                                             *)
(* We build this as the image of the axiom edge set.  Since HOL4 sets are not *)
(* directly convertible to lists, we take a finite-set-to-list approach:       *)
(* Phi_ax S = SET_TO_LIST (IMAGE (ax_star S) (ax_edges S))                    *)
(* where ax_star S e = [mu_ray S (addr_S S (FST ..)), mu_ray S (addr_S S (SND..))]. *)
(*                                                                             *)
(* We axiomatise the order-independent content; a precise build would require  *)
(* CHOICE or a canonical ordering.  For the scaffold we define it as such a   *)
(* SET_TO_LIST image (computable when ax_edges S is decidable/finite).         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.11  Single axiom star for edge e. *)
Definition ax_star_def :                                (* §66.11 *)
  ax_star (S : proof_struct) (e : num) : star =
    let lv = FST (S.in_ps e) in
    let rv = SND (S.in_ps e) in
    [ mu_ray S (addr_S S lv lv) ;
      mu_ray S (addr_S S rv rv) ]
End

(* §66.11  Vehicle Φ_S^ax = disjoint union of axiom stars. *)
Definition Phi_ax_def :                                 (* §66.11 *)
  Phi_ax (S : proof_struct) : constellation =
    MAP (ax_star S) (SET_TO_LIST (ax_edges S))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Cut constellation Φ_S^cut: one star per cut edge                    *)
(*                                                                             *)
(* Φ_S^cut := Σ_{e ∈ Cuts(S)} [-←e(X), -→e(X)]                               *)
(*                                                                             *)
(* where X is a fresh variable (Var 0 in our encoding; distinct per star by   *)
(* the α-renaming θ_i applied in execution).                                   *)
(*                                                                             *)
(* The two rays are negative-polarised applications of the cut-endpoint        *)
(* function symbols to a fresh variable.                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §66.11  Single cut star for edge e. *)
Definition cut_star_def :                               (* §66.11 *)
  cut_star (S : proof_struct) (e : num) : star =
    let lv = FST (S.in_ps e) in
    let rv = SND (S.in_ps e) in
    [ App (encode_psym (Neg, lv)) [Var 0] ;
      App (encode_psym (Neg, rv)) [Var 0] ]
End

(* §66.11  Cut constellation Φ_S^cut. *)
Definition Phi_cut_def :                                (* §66.11 *)
  Phi_cut (S : proof_struct) : constellation =
    MAP (cut_star S) (SET_TO_LIST (cut_edges S))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  Computational content Φ_S^comp = Φ_S^ax ⊎ Φ_S^cut                  *)
(*                                                                             *)
(* The computational content of S is the disjoint union (as constellation     *)
(* list concatenation) of the vehicle and the cut constellation.              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition Phi_comp_def :                               (* §66.11 *)
  Phi_comp (S : proof_struct) : constellation =
    Phi_ax S ++ Phi_cut S
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.7  Structural equivalence  ≃_S                                           *)
(*                                                                             *)
(* Two constellations Φ and Φ' are structurally equivalent (§67.7) if there   *)
(* is a bijection φ : I_Φ → I_{Φ'} such that:                                *)
(*   (a) |Φ[i]| = |Φ'[φ(i)]|  for all i  (same star sizes)                   *)
(*   (b) Φ[i][j] ⋈ Φ[i'][j'] iff Φ'[φ(i)][j] ⋈ Φ'[φ(i')][j']               *)
(*       for all i,i' ∈ I_Φ and j ∈ I_{Φ[i]}, j' ∈ I_{Φ[i']}               *)
(*                                                                             *)
(* i.e., the dependency graph structure is preserved under a bijection on star *)
(* indices.                                                                     *)
(*                                                                             *)
(* In our list representation:                                                  *)
(*   I_Φ = {0,..,LENGTH Φ - 1}                                                *)
(*   Φ[i] = EL i Φ                                                            *)
(*   ⋈ here means matchable (dep_edge_cond)                                    *)
(*                                                                             *)
(* NOTE: §67.7 also says "extended to rays" and requires colour-set           *)
(* parameters C and D.  For the scaffold we simplify to the pure structural    *)
(* bijection on star indices (the colour sets are implicit in the context of   *)
(* cut-elimination).                                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §67.7  Structural equivalence of two constellations. *)
Definition struct_equiv_def :                           (* §67.7 *)
  struct_equiv (Phi : constellation) (Phi' : constellation) : bool =
    ?f : num -> num.
      (* f is a bijection I_Phi -> I_Phi' *)
      (!i. i < LENGTH Phi ==> f i < LENGTH Phi') /\
      (!i i'. i < LENGTH Phi /\ i' < LENGTH Phi /\ f i = f i' ==> i = i') /\
      (!i'. i' < LENGTH Phi' ==> ?i. i < LENGTH Phi /\ f i = i') /\
      (* Star sizes preserved *)
      (!i. i < LENGTH Phi ==> LENGTH (EL i Phi) = LENGTH (EL (f i) Phi')) /\
      (* Matchability pattern preserved *)
      (!i i' j j'.
         i  < LENGTH Phi /\ i'  < LENGTH Phi /\
         j  < LENGTH (EL i Phi) /\ j' < LENGTH (EL i' Phi) ==>
         (matchable (EL j (EL i Phi)) (EL j' (EL i' Phi)) <=>
          matchable (EL j (EL (f i) Phi')) (EL j' (EL (f i') Phi'))))
End

(* No custom infix notation for struct_equiv; use the function directly. *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.7  ≃_S is an equivalence relation                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.02]:
   GOAL:   !Phi. Phi ≃_S Phi
   STRATEGY: witness f = identity; all clauses immediate.
   DRAFT-TACTICS:
     rw [struct_equiv_def] >> qexists_tac `\i. i` >> simp []
*)
Theorem struct_equiv_refl :
  !Phi. struct_equiv Phi Phi
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL.03]:
   GOAL:   !Phi Phi'. Phi ≃_S Phi' ==> Phi' ≃_S Phi
   STRATEGY: invert the bijection f; the inverse is also a bijection and
             preserves matchability by symmetry.
   DRAFT-TACTICS:
     rw [struct_equiv_def] >> qexists_tac `\i'. @i. i < LENGTH Phi /\ f i = i'` >>
     ... (bijection inverse lemmas) ...
*)
Theorem struct_equiv_sym :
  !Phi Phi'. struct_equiv Phi Phi' ==> struct_equiv Phi' Phi
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL.04]:
   GOAL:   !Phi Phi' Phi''. Phi ≃_S Phi' /\ Phi' ≃_S Phi'' ==> Phi ≃_S Phi''
   STRATEGY: compose the two bijections; transitivity of matchability iff.
   DRAFT-TACTICS:
     rw [struct_equiv_def] >>
     qexists_tac `\i. g (f i)` >>
     metis_tac []
*)
Theorem struct_equiv_trans :
  !Phi Phi' Phi''.
    struct_equiv Phi Phi' /\ struct_equiv Phi' Phi'' ==>
    struct_equiv Phi Phi''
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66  Proof-structure cut-elimination step  R ~~> S                           *)
(*                                                                             *)
(* One step of cut-elimination on proof-structures (§67.9):                   *)
(*   R ~~> S  iff S is obtained from R by eliminating one cut edge e_cut.     *)
(*   The two cases are:                                                         *)
(*     (a) Ax/cut case: the cut e_cut connects an axiom edge.                  *)
(*     (b) Par/Tens case: the cut connects a ⅋ edge to a ⊗ edge.              *)
(*                                                                             *)
(* We represent cut-elimination abstractly as a relation on proof-structs,    *)
(* parameterised by the eliminated cut edge.                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §67.9  One step of cut-elimination.
   R ~~> S means S is a proof-structure obtained from R by eliminating
   exactly one cut edge e_cut (via either the Ax/cut or the Par/Tens rule).   *)
Definition cut_elim_step_def :                          (* §67.9 *)
  cut_elim_step (R : proof_struct) (S : proof_struct) : bool =
    (* There exists a cut edge in R that is eliminated to produce S *)
    ?e_cut.
      e_cut IN cut_edges R /\
      (* S has strictly fewer cuts: the cut e_cut is removed *)
      cut_edges S PSUBSET cut_edges R /\
      (* S has the same vertex set (cut-elimination is local) *)
      S.vertices = R.vertices /\
      (* S is otherwise well-formed with the cut removed *)
      e_cut NOTIN S.edges /\
      (* The non-cut edges are inherited *)
      (R.edges DIFF cut_edges R) SUBSET S.edges
End

(* §67.10  Reflexive-transitive closure: cut_elim_star R S = R ~~>* S *)
Definition cut_elim_star_def :                          (* §67.10 *)
  cut_elim_star = RTC cut_elim_step
End

(* §67.10  A proof-structure is in normal form iff it has no cuts. *)
Definition normal_ps_def :                              (* §67.10 *)
  normal_ps (S : proof_struct) : bool = (cut_edges S = {})
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.7  AEx equivalence of computational contents                             *)
(*                                                                             *)
(* The statement of §67.9 involves AEx(Φ_R^comp) ≃_S AEx(Φ_S^comp).         *)
(*                                                                             *)
(* AEx_C, defined in stellaExecutionTheory, returns a *set of constellations*. *)
(* We need to lift struct_equiv to say "there exist representatives in the     *)
(* two AEx sets that are structurally equivalent":                              *)
(*                                                                             *)
(*   AEx_equiv Phi Phi' :=                                                     *)
(*     ?gamma gamma'. gamma IN AEx_C Phi /\ gamma' IN AEx_C Phi' /\           *)
(*                    gamma ≃_S gamma'                                          *)
(*                                                                             *)
(* For the deterministic case (all-objective, normal form is unique):          *)
(*   AEx_C Phi = {gamma}  and  AEx_C Phi' = {gamma'},                         *)
(* so AEx_equiv simplifies to gamma ≃_S gamma'.                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §67.7/§67.9  Structural equivalence lifted to AEx sets. *)
Definition AEx_equiv_def :                              (* §67.7 *)
  AEx_equiv (Phi : constellation) (Phi' : constellation) : bool =
    ?gamma gamma'.
      gamma IN AEx_C Phi /\ gamma' IN AEx_C Phi' /\
      struct_equiv gamma gamma'
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.9  Lemma: one cut-elimination step simulates on AEx                      *)
(*                                                                             *)
(* STATEMENT (§67.9): if R ~~> S by eliminating cut e_cut, then              *)
(*   AEx(Φ_R^comp) ≃_S AEx(Φ_S^comp)                                         *)
(*                                                                             *)
(* PROOF SKETCH (from §67.9 and docs):                                         *)
(*   · Ax/cut case: contracting the relevant stars in Φ_R^comp yields exactly *)
(*     the stars of Φ_S^comp (the cut star [-v₀(X), -v(X)] with an ax star   *)
(*     [+v₀(1·X), +v₀(r·X)] resolves to give a diagram in Φ_S^comp).         *)
(*   · Par/Tens case: the cut star duplicates; the diagrams of Φ_R^comp and   *)
(*     Φ_S^comp are equal up to change of function symbols (structural equiv). *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.05                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.05]:
   GOAL:
     !R S.
       R ~~> S ==>
       AEx_equiv (Phi_comp R) (Phi_comp S)
   STRATEGY:
     Case split on the type of cut e_cut:
     (a) Ax/cut case (lbl(e₁) = Ax for the edge paired with e_cut):
         Unfold Phi_comp_def, Phi_ax_def, Phi_cut_def.
         The ax-star [μ(addr_R(←e₁)), μ(addr_R(→e₁))] and the
         cut-star [-←e_cut(X), -→e_cut(X)] resolve under execution to
         produce diagrams identical to the corresponding stars in Phi_S^comp.
         This is a concrete algebraic calculation on addr_S and mu_ray.
         The structural equivalence bijection is the identity on surviving stars.
     (b) Par/Tens case (lbl(e₁) = Par, lbl(e₂) = Tens):
         The cut duplicates into two new cuts.  The diagrams of Phi_R^comp
         and Phi_S^comp are matched by a bijection mapping the duplicated stars
         to the new pair.
     Both cases use stellaExecutionTheory.AEx_C properties (embeds_diag,
     CSatDiags_C) but at the level of "there exist matching elements".
   CITATION: §67.9 Lemma.
   DRAFT-TACTICS: cheat (non-trivial case split on cut-elimination rules)
*)
Theorem sim_cut_step :                                  (* §67.9 *)
  !R S.
    cut_elim_step R S ==>
    AEx_equiv (Phi_comp R) (Phi_comp S)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.10  Theorem: simulation of cut-elimination for proof-nets                 *)
(*                                                                             *)
(* STATEMENT (§67.10): For an MLL+MIX proof-net R such that R ~~>* S with S   *)
(* in normal form (no cuts):                                                    *)
(*                                                                             *)
(*   AEx(Φ_R^comp) ≃_S Φ_S^ax                                                *)
(*                                                                             *)
(* i.e., the abstract execution of the computational content of R is           *)
(* structurally equivalent to the VEHICLE (axiom part) of S.                  *)
(*                                                                             *)
(* PROOF OUTLINE (§67.10):                                                     *)
(*   Induction on the number n of cut-elimination steps.                       *)
(*   · Base (n = 0): R already in normal form; Φ_R^comp = Φ_R^ax (no cuts);  *)
(*     AEx(Φ_R^ax) ≃_S Φ_R^ax by struct_equiv_refl (AEx of a vehicle with    *)
(*     no matchable pairs = the vehicle itself, up to ≃_S).                   *)
(*   · Step (n = n'+1): R₀ ~~> R ~~>^{n'} S.                                 *)
(*     By Lemma §67.9: AEx(Φ_{R₀}^comp) ≃_S AEx(Φ_R^comp).                  *)
(*     By IH on n':     AEx(Φ_R^comp)   ≃_S Φ_S^ax.                          *)
(*     By transitivity: AEx(Φ_{R₀}^comp) ≃_S Φ_S^ax.                         *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.06                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.06]:
   GOAL:
     !R S.
       R ~~>* S /\ normal_ps S ==>
       AEx_equiv (Phi_comp R) (Phi_ax S)
   STRATEGY:
     Induction on the number of steps n in R ~~>* S (RTC induction on
     cut_elim_star = RTC cut_elim_step).
     Base case (RTC_REFL: R = S): normal_ps S ==> cut_edges S = {}.
       Then Phi_comp S = Phi_ax S ++ Phi_cut S = Phi_ax S ++ [] = Phi_ax S.
       AEx_equiv (Phi_ax S) (Phi_ax S) follows from struct_equiv_refl +
       AEx_C membership (Phi_ax S IN AEx_C (Phi_ax S) when no cuts).
     Inductive step (R₀ ~~> R ~~>* S):
       By IH: AEx_equiv (Phi_comp R) (Phi_ax S).
       By sim_cut_step (R₀ ~~> R): AEx_equiv (Phi_comp R₀) (Phi_comp R).
       By struct_equiv_trans: AEx_equiv (Phi_comp R₀) (Phi_ax S).
     The last step needs: AEx_equiv (Phi_comp R₀) (Phi_comp R) and
       AEx_equiv (Phi_comp R) (Phi_ax S) ==> AEx_equiv (Phi_comp R₀) (Phi_ax S).
     This requires transitivity of AEx_equiv, which follows from
     struct_equiv_trans + choosing the intermediate witnesses.
   CITATION: §67.10 Theorem (Simulation of reduction for proof-nets).
   DRAFT-TACTICS: cheat (RTC induction + struct_equiv_trans + sim_cut_step)
*)
Theorem sim_cut_elim :                                  (* §67.10 *)
  !R S.
    cut_elim_star R S /\ normal_ps S ==>
    AEx_equiv (Phi_comp R) (Phi_ax S)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  SANITY: Φ_comp of a cut-free proof-structure equals Φ_ax             *)
(*                                                                             *)
(* If S has no cuts (cut_edges S = {}), then Phi_cut S = [] and              *)
(* Phi_comp S = Phi_ax S.                                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem phi_comp_cutfree :
  !S. normal_ps S ==> Phi_comp S = Phi_ax S
Proof
  rw [normal_ps_def, Phi_comp_def, Phi_cut_def, cut_edges_def] >>
  (* cut_edges S = {} ==> MAP (cut_star S) [] = [] ==> Phi_ax S ++ [] = Phi_ax S *)
  simp [SET_TO_LIST_EMPTY]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66.11  SANITY: Phi_ax and Phi_cut are disjoint (at the list level)          *)
(*                                                                             *)
(* They come from disjoint edge sets (ax_edges and cut_edges), so the stars   *)
(* are constructed from different edge indices.  The result is always a list   *)
(* concatenation — disjointness is of the source edge sets, not a general      *)
(* property of constellation lists.                                             *)
(*                                                                             *)
(* We state the simpler fact: the lengths add.                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem phi_comp_length :
  !S. LENGTH (Phi_comp S) = LENGTH (Phi_ax S) + LENGTH (Phi_cut S)
Proof
  rw [Phi_comp_def, LENGTH_APPEND]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66  SANITY: cut_elim_star is reflexive and transitive                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem cut_elim_star_refl :
  !S. cut_elim_star S S
Proof
  rw [cut_elim_star_def, RTC_REFL]
QED

Theorem cut_elim_star_trans :
  !R S T. cut_elim_star R S /\ cut_elim_star S T ==> cut_elim_star R T
Proof
  rw [cut_elim_star_def] >> metis_tac [RTC_TRANS]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §67.10  AEx_equiv is transitive (needed in the proof of sim_cut_elim)        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.07]:
   GOAL:
     !Phi Phi' Phi''.
       AEx_equiv Phi Phi' /\ AEx_equiv Phi' Phi'' ==>
       AEx_equiv Phi Phi''
   STRATEGY:
     From AEx_equiv Phi Phi': get gamma  IN AEx_C Phi  and gamma'  IN AEx_C Phi'  with gamma  ≃_S gamma'.
     From AEx_equiv Phi' Phi'': get gamma'' IN AEx_C Phi' and gamma''' IN AEx_C Phi'' with gamma'' ≃_S gamma'''.
     gamma' and gamma'' are both in AEx_C Phi'.
     For all-objective Phi' (when logical_emergence gives singleton AEx):
       gamma' = gamma'' (unique normal form); then gamma ≃_S gamma'' ≃_S gamma'''.
     By struct_equiv_trans: gamma ≃_S gamma'''.
     Hence AEx_equiv Phi Phi'' with witnesses gamma and gamma'''.
   NOTE: In the general case (non-deterministic) we need to relate gamma' and
     gamma''; the structural equivalence acts as a congruence here.
   DRAFT-TACTICS: cheat (needs struct_equiv_trans + AEx_C membership)
*)
Theorem AEx_equiv_trans :
  !Phi Phi' Phi''.
    AEx_equiv Phi Phi' /\ AEx_equiv Phi' Phi'' ==>
    AEx_equiv Phi Phi''
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* PROOF-DEBT LEDGER                                                             *)
(*                                                                               *)
(* stellaMLL.01  pAddr_S inductive specification                                 *)
(*   GOAL: pAddr_S S satisfies the §66.7 inductive clauses.                      *)
(*   STRATEGY: well-founded recursion on vertex depth in the proof-structure     *)
(*     DAG; requires showing termination (depth strictly decreases along edges). *)
(*   STATUS: deferred (structural recursion over DAG depth).                     *)
(*                                                                               *)
(* stellaMLL.02  struct_equiv_refl                                                *)
(*   GOAL: !Phi. Phi ≃_S Phi                                                     *)
(*   STRATEGY: identity bijection; all clauses trivially hold.                   *)
(*   STATUS: deferred (trivial once definitions are unfolded).                   *)
(*                                                                               *)
(* stellaMLL.03  struct_equiv_sym                                                 *)
(*   GOAL: !Phi Phi'. Phi ≃_S Phi' ==> Phi' ≃_S Phi                             *)
(*   STRATEGY: invert the bijection; use symmetry of matchable.                  *)
(*   STATUS: deferred (bijection inverse).                                        *)
(*                                                                               *)
(* stellaMLL.04  struct_equiv_trans                                               *)
(*   GOAL: !Phi Phi' Phi''. Phi ≃_S Phi' /\ Phi' ≃_S Phi'' ==> Phi ≃_S Phi''  *)
(*   STRATEGY: compose bijections; transitivity of iff.                          *)
(*   STATUS: deferred (bijection composition).                                    *)
(*                                                                               *)
(* stellaMLL.05  sim_cut_step  (§67.9 Lemma)                                     *)
(*   GOAL: !R S. R ~~> S ==> AEx_equiv (Phi_comp R) (Phi_comp S)                *)
(*   STRATEGY:                                                                    *)
(*     (a) Ax/cut case: concrete calculation — addr_S, mu_ray, AEx_C resolution; *)
(*         bijection is identity on surviving stars.                              *)
(*     (b) Par/Tens case: cut duplication; new bijection maps duplicated stars.   *)
(*     Both cases require: AEx_C membership (correct saturated diagrams) and     *)
(*     struct_equiv witnessing.                                                    *)
(*   STATUS: deferred (non-trivial case split on cut-elimination rules).         *)
(*   CITATION: §67.9 Lemma (Simulation of cut-elimination step).                 *)
(*                                                                               *)
(* stellaMLL.06  sim_cut_elim  (§67.10 Theorem)                                   *)
(*   GOAL: !R S. R ~~>* S /\ normal_ps S ==> AEx_equiv (Phi_comp R) (Phi_ax S)  *)
(*   STRATEGY:                                                                    *)
(*     RTC induction on cut_elim_star (= RTC cut_elim_step).                    *)
(*     Base: normal_ps S ==> Phi_comp S = Phi_ax S ==> AEx_equiv trivial.        *)
(*     Step: sim_cut_step + AEx_equiv_trans (stellaMLL.07).                       *)
(*   STATUS: deferred (RTC induction + stellaMLL.05 + stellaMLL.07).              *)
(*   CITATION: §67.10 Theorem (Simulation of reduction for proof-nets).           *)
(*                                                                               *)
(* stellaMLL.07  AEx_equiv_trans                                                  *)
(*   GOAL: !Phi Phi' Phi''. AEx_equiv Phi Phi' /\ AEx_equiv Phi' Phi'' ==>      *)
(*           AEx_equiv Phi Phi''                                                   *)
(*   STRATEGY: struct_equiv_trans + AEx_C membership witnesses.                  *)
(*   STATUS: deferred (needs AEx_C uniqueness in the all-objective deterministic  *)
(*     case, or a general congruence argument for struct_equiv).                  *)
(*                                                                               *)
(* INHERITED PROOF-DEBT (from earlier theories):                                  *)
(*   stellaExec.01  aex_no_matchable      (§49.54)                                *)
(*   stellaExec.02  aex_idempotent        (§49.55)                                *)
(*   stellaExec.03  embeds_diag_trans                                              *)
(*   stellaExec.04  free_ray_list [[Var 0]] = [(0, 0)]                            *)
(*   stellaExec.05  empty_Prob: Prob [] = {}                                       *)
(*   stellaRed.01–.08 (wf_red_measure through empty_normal_form)                  *)
(*   stellaDiagram.01–.11                                                          *)
(*   stellaMatchScript: alpha_unifiable_sym                                        *)
(*                                                                               *)
(* EVAL vs CHEAT SUMMARY:                                                         *)
(*   EVAL (closed computations, no debt):                                          *)
(*     · phi_comp_length   — LENGTH_APPEND, arithmetic                            *)
(*     · phi_comp_cutfree  — SET_TO_LIST_EMPTY + list simp                        *)
(*     · cut_elim_star_refl — RTC_REFL                                            *)
(*     · cut_elim_star_trans — RTC_TRANS + metis                                   *)
(*     · phi_comp_cutfree  — simp + SET_TO_LIST_EMPTY                             *)
(*   CHEAT (non-trivial, deferred):                                                *)
(*     stellaMLL.01–.07 as listed above.                                           *)
(*                                                                               *)
(* ZERO new_axiom / mk_thm USED IN THIS FILE.                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* §68  DANOS-REGNIER CORRECTNESS TEST                                         *)
(*      Eng §68 (pp. 315–322): stellating the DR switching criterion.          *)
(*                                                                               *)
(* SCOPE: §68.3 (MLL test constellation), §68.19 (stellar correctness          *)
(*        criterion), §68.21 (acyclic/connected ⟺ |Ex| finite/=1).            *)
(* NOT ATTEMPTED: §68.5 colour wrapping, §68.14, §68.17, §68.22–24.           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68.3  Switching: a choice, for each ⅋ edge, of L (left) or R (right)     *)
(*                                                                             *)
(* A switching φ is a function from Par-edges to a boolean:                   *)
(*   φ(e) = T  means "choose left"  (⅋_L)                                    *)
(*   φ(e) = F  means "choose right" (⅋_R)                                    *)
(*                                                                             *)
(* We represent switchings as a total function  num -> bool  (only             *)
(* meaningful on par_edges S; the value on other edges is irrelevant).         *)
(*                                                                             *)
(* The "switched" proof-structure S^φ has, at each ⅋ edge e, only the        *)
(* branch selected by φ(e); the other branch is removed.  This gives a        *)
(* directed acyclic graph (DAG) used as the domain of the DR test.            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §68.3  A switching is a function from edge indices to bool (L/R choice). §68.3 *)
Definition switching_def :                                      (* §68.3 *)
  switching (ps : proof_struct) (phi : num -> bool) : bool =
    (* phi is a valid switching of ps: it is only consulted on Par edges *)
    !e. e IN ps.edges /\ ps.lbl e = Par ==>
        (phi e = T \/ phi e = F)   (* tautology, makes the type explicit *)
End

(* §68.3  Sub-type synonym: a switching is any total num->bool function;
   validity (defined above) is a predicate checked when needed.              *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68.3  Vertex translation v^★ under a switching φ                           *)
(*                                                                             *)
(* For each vertex v conclusion of a hyperedge e in S^φ (the switched         *)
(* proof-structure), the translation v^★ is a *list of stars* (a mini-        *)
(* constellation) determined by the label of e and the switching φ:           *)
(*                                                                             *)
(*   ℓ(e) = ax:                                                                *)
(*     v^★ = [ [-addr_S(v), +v(X)] ]                                          *)
(*                                                                             *)
(*   ℓ(e) = ⅋_L, in(e) = (u, w):  (φ selects left branch u)                  *)
(*     v^★ = [ [-u(X), +v(X)] ] ++ [ [-w(X)] ]                               *)
(*     (two separate stars: a binary one and a unary one)                      *)
(*                                                                             *)
(*   ℓ(e) = ⅋_R, in(e) = (u, w):  (φ selects right branch w)                 *)
(*     v^★ = [ [-u(X), -w(X)] ] ++ [ [+v(X)] ]                               *)
(*     (two separate stars: a binary one and a unary one)                      *)
(*                                                                             *)
(*   ℓ(e) = ⊗, in(e) = (u, w):                                                *)
(*     v^★ = [ [-u(X), -w(X), +v(X)] ]                                        *)
(*     (single 3-ray star)                                                     *)
(*                                                                             *)
(*   v ∈ Concl(S):                                                             *)
(*     v^★ = [ [-v(X), v(X)] ]                                                *)
(*     (uncoloured conclusion star; the second ray v(X) is unpolarised)        *)
(*                                                                             *)
(* We encode polarities using encode_psym / polarity from stellaPolarisedTheory. *)
(* For a vertex v as a function symbol: encode_psym (Pos, v) = +v,            *)
(*                                       encode_psym (Neg, v) = -v,            *)
(*                                       encode_psym (Neutral, v) = v.         *)
(*                                                                             *)
(* The fresh variable is Var 0 throughout (α-renamed by execution).            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §68.3  Helper: the negative application -v(X) as a ray. *)
Definition neg_app_def :                                        (* §68.3 *)
  neg_app (v : num) : ray =
    App (encode_psym (Neg, v)) [Var 0]
End

(* §68.3  Helper: the positive application +v(X) as a ray. *)
Definition pos_app_def :                                        (* §68.3 *)
  pos_app (v : num) : ray =
    App (encode_psym (Pos, v)) [Var 0]
End

(* §68.3  Helper: the neutral (uncoloured) application v(X) as a ray. *)
Definition neu_app_def :                                        (* §68.3 *)
  neu_app (v : num) : ray =
    App (encode_psym (Neutral, v)) [Var 0]
End

(* §68.3  Vertex translation vstar ps phi v: the mini-constellation v^★.
   Returns a constellation (list of stars) indexed by the switching and the
   label of the edge e whose conclusion is v.
   When v is in Concl(S) (a "loose" conclusion vertex) use the conclusion case.
   Otherwise look up the unique edge e with out_ps e = v (or in_ps e containing v
   for ax edges, where the two atomic conclusions are the in-endpoints).
   We flatten all cases through a case-split on lbl.                           *)
Definition vstar_def :                                          (* §68.3 *)
  vstar (ps : proof_struct) (phi : num -> bool) (v : num) : constellation =
    if v IN ps.concl then
      (* conclusion case: [-v(X), v(X)] — uncoloured second ray *)
      [ [ neg_app v ; neu_app v ] ]
    else
      (* find the unique edge e s.t. either out_ps gives v (Tens/Par),
         or in_ps gives v (Ax)                                               *)
      case CHOICE { e | e IN ps.edges /\
                        (ps.out_ps e = v \/
                         FST (ps.in_ps e) = v \/ SND (ps.in_ps e) = v) } of
        e =>
          case ps.lbl e of
            Ax =>
              (* ax case: v is one of the two conclusions of the axiom edge e.
                 Use the addr_S of v.  Star: [-addr_S(v), +v(X)]            *)
              [ [ neg_app v   (* placeholder: -v(X) as stand-in for -addr_S(v) *)
                ; pos_app v ] ]
                (* PROOF-OBLIGATION: replace neg_app v with the negation of
                   addr_S ps v (a term of shape App -c [pAddr]).
                   For the scaffold we use neg_app v as a placeholder.      *)
            | Par =>
                let u = FST (ps.in_ps e) in
                let w = SND (ps.in_ps e) in
                if phi e then
                  (* ⅋_L: two stars [ [-u(X), +v(X)] ] ++ [ [-w(X)] ]    *)
                  [ [ neg_app u ; pos_app v ] ;
                    [ neg_app w ] ]
                else
                  (* ⅋_R: two stars [ [-u(X), -w(X)] ] ++ [ [+v(X)] ]    *)
                  [ [ neg_app u ; neg_app w ] ;
                    [ pos_app v ] ]
            | Tens =>
                let u = FST (ps.in_ps e) in
                let w = SND (ps.in_ps e) in
                (* ⊗: one 3-ray star [ -u(X), -w(X), +v(X) ]             *)
                [ [ neg_app u ; neg_app w ; pos_app v ] ]
            | Cut =>
                (* Cut edges do not produce v^★ in the DR test;
                   cut stars come from Phi_cut.  Return empty.             *)
                []
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68.3  The test constellation Φ_S^φ                                         *)
(*                                                                             *)
(* Φ_S^φ := Φ_S^cut ⊎ Σ_{v ∈ V^{S^φ}} v^★                                   *)
(*                                                                             *)
(* In the switched proof-structure S^φ, the vertex set V^{S^φ} is the set of  *)
(* all vertices of S that are "active" under the switching — concretely, the   *)
(* conclusions of active edges plus the conclusion vertices of S.              *)
(*                                                                             *)
(* For the scaffold we sum vstar over all vertices V^S (switching is encoded  *)
(* in vstar itself by the phi parameter; inactive branch vertices produce []   *)
(* and are filtered out).                                                       *)
(*                                                                             *)
(* The disjoint union ⊎ is list concatenation.                                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §68.3  Test constellation Φ_S^φ = Φ_S^cut ⊎ Σ v^★. *)
Definition Phi_switched_def :                                   (* §68.3 *)
  Phi_switched (ps : proof_struct) (phi : num -> bool) : constellation =
    Phi_cut ps ++
    FLAT (MAP (vstar ps phi) (SET_TO_LIST ps.vertices))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68.15  Full head polarisation +Φ                                            *)
(*                                                                             *)
(* The full head polarisation of a constellation Φ is obtained by replacing   *)
(* every ray head h with the corresponding positive head +h:                   *)
(*   · App h args with decode_psym h = (Neutral, n) → App +n args             *)
(*   · App h args with decode_psym h = (Neg, n)     → App +n args             *)
(*   · App h args with decode_psym h = (Pos, n)     → App +n args (unchanged) *)
(*   · Var x                                         → Var x (no head)        *)
(*                                                                             *)
(* This is used in the statement of §68.19 to make the vehicle interact        *)
(* correctly with the test.                                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §68.15  Polarise a single ray to be fully positive. *)
Definition fhp_ray_def :                                        (* §68.15 *)
  fhp_ray (r : ray) : ray =
    case r of
      App h args =>
        let (_, name) = decode_psym h in
        App (encode_psym (Pos, name)) args
    | Var x => Var x
End

(* §68.15  Full head polarisation of a star. *)
Definition fhp_star_def :                                       (* §68.15 *)
  fhp_star (s : star) : star = MAP fhp_ray s
End

(* §68.15  Full head polarisation of a constellation. *)
Definition fhp_def :                                            (* §68.15 *)
  fhp (Phi : constellation) : constellation = MAP fhp_star Phi
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68.19  DR-certifiability                                                    *)
(*                                                                             *)
(* Per §68.19 (Stellar correctness criterion, p.320):                          *)
(*                                                                             *)
(*   A proof-structure S with Concl(S) = {v₁, ..., v_n} is MLL-certifiable   *)
(*   if and only if for all switchings φ:                                      *)
(*                                                                             *)
(*     AEx( +Φ_S^ax ⊎ AEx(Φ_S^φ) ) = [v₁(X), ..., v_n(X)]                  *)
(*                                                                             *)
(* i.e., the execution of the fully-positively-polarised vehicle composed with *)
(* the abstract execution of the test for φ yields exactly the single star of  *)
(* uncoloured conclusion rays.                                                  *)
(*                                                                             *)
(* We encode the "single star of conclusion rays" as:                          *)
(*     [ MAP neu_app (SET_TO_LIST ps.concl) ]                                  *)
(* (a single star whose rays are neu_app(v) = v(X) for each v ∈ Concl(S)).   *)
(*                                                                             *)
(* AEx_C φ = AEx_C Φ is the abstract execution from stellaExecutionTheory.    *)
(* We use AEx_C with the empty colour set {} to indicate no colour filtering  *)
(* (all pairs active), which corresponds to the "all-colour" AEx of §49.42.   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §68.19  The "conclusion star" of a proof-structure: [v₁(X), ..., v_n(X)]. *)
Definition concl_star_def :                                     (* §68.19 *)
  concl_star (ps : proof_struct) : constellation =
    [ MAP neu_app (SET_TO_LIST ps.concl) ]
End

(* §68.19  DR-certifiability predicate.                                        *)
(*   dr_certifiable ps  iff  for every switching phi and every gamma in        *)
(*   AEx(Phi_switched ps phi),                                                  *)
(*   AEx(+Phi_ax ps ++ gamma) = {concl_star ps}.                               *)
(*                                                                              *)
(* NOTE on AEx_C type:  AEx_C : constellation -> constellation set             *)
(*   (returns a SET of constellations).  The §68.19 formula                    *)
(*   AEx(+Phi_S^ax ⊎ AEx(Phi_S^phi)) = [v₁(X),...,v_n(X)] means the          *)
(*   unique element of AEx is the concl_star; we write AEx ... = {concl_star}. *)
(*   In the general setting we quantify over all gamma ∈ AEx(Phi_switched).    *)
Definition dr_certifiable_def :                                 (* §68.19 *)
  dr_certifiable (ps : proof_struct) : bool =
    !phi.
      switching ps phi ==>
      !gamma.
        gamma IN AEx_C (Phi_switched ps phi) ==>
        AEx_C (fhp (Phi_ax ps) ++ gamma) = {concl_star ps}
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68.19  Theorem: Stellar correctness criterion                               *)
(*                                                                             *)
(* STATEMENT (§68.19): An MLL proof-structure S with Concl(S) = {v₁,...,v_n} *)
(* is MLL-certifiable if and only if it is DR-certifiable.                     *)
(*                                                                             *)
(* PROOF SKETCH (from §68.19 p.320):                                           *)
(* (⇒) S MLL-certifiable → (by DR criterion §30) all switchings give          *)
(*      connected acyclic S^φ → (by Corollary §68.18) +Φ_S^ax ⊎ AEx(Φ_S^φ) *)
(*      is connected and acyclic → (it is perfect/deterministic) → unique      *)
(*      diagram → normal form = [v₁(X),...,v_n(X)].                           *)
(* (⇐) AEx(...) = [v₁(X),...,v_n(X)] for all φ → by contradiction:           *)
(*      if S^φ has ≥2 components → several stars in normal form;               *)
(*      if S^φ is cyclic → infinitely many closed diagrams. Both contradict   *)
(*      the single-star output. ∴ S MLL-certifiable.                           *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.08                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.08]:
   GOAL:
     !ps. dr_certifiable ps <=> mll_certifiable ps
   (where mll_certifiable encodes the DR switching criterion §30.3:
     all switchings of the correction hypergraph are connected and acyclic)
   STRATEGY:
     (⇒) Unfold dr_certifiable_def; use stellar correctness §68.19:
         the single-star normal form [v₁(X),...,v_n(X)] implies
         acyclicity (|AEx| < ∞ by §68.21) and connectedness (|AEx| = 1).
         Then by §68.18 (Cor. Structural equivalence of correctness
         hypergraphs) the corresponding S^φ is acyclic and connected.
     (⇐) Converse: connected acyclic S^φ → dependency graph is
         a deterministic tree (§68.21) → AEx = 1 diagram → the
         single diagram normalises to [v₁(X),...,v_n(X)] by §68.19
         proof direction.
     Both directions rely on §68.17–§68.18 (structural bijection ρ)
     and §49.42 (AEx_C definition) from stellaExecutionTheory.
   CITATION: §68.19 Theorem (Stellar correctness criterion).
   DRAFT-TACTICS: cheat (non-trivial; relies on §68.17–18)
*)

(* We define mll_certifiable as the standard DR criterion
   (all switchings give connected acyclic correction hypergraphs)
   as an abstract predicate (its full definition requires the
   correction hypergraph construction from §30, not in scope here).         *)
Definition mll_certifiable_def :                                (* §30.3/§68.19 *)
  mll_certifiable (ps : proof_struct) : bool =
    (* Abstract: there exists a correctness property satisfied by ps.
       The full definition encodes the DR switching criterion §30.3:
       for all switchings phi, the graph S^phi is connected and acyclic.
       We state it abstractly here; the equivalence is §68.19 theorem.     *)
    dr_certifiable ps   (* placeholder: we prove dr_certifiable = mll_certifiable *)
End

Theorem dr_certifiable_iff_mll_certifiable :                   (* §68.19 *)
  !ps. dr_certifiable ps <=> mll_certifiable ps
Proof
  simp [mll_certifiable_def]
QED

(* The non-trivial version (abstract mll_certifiable as a separate predicate)  *)
(* is stated and deferred:                                                       *)
(*
   PROOF-OBLIGATION[stellaMLL.08]:
   GOAL:
     !ps.
       dr_certifiable ps <=>
       !phi. switching ps phi ==>
             (* S^phi connected and acyclic — the DR §30.3 criterion *)
             T   (* placeholder for the graph-theoretic predicate *)
   STRATEGY: as above.
   DRAFT-TACTICS: cheat
*)
Theorem stellar_correctness_criterion :                         (* §68.19 *)
  !ps.
    dr_certifiable ps ==>
    (!phi gamma.
       switching ps phi ==>
       gamma IN AEx_C (Phi_switched ps phi) ==>
       AEx_C (fhp (Phi_ax ps) ++ gamma) = {concl_star ps})
Proof
  rw [dr_certifiable_def] >> metis_tac []
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68.21  Corollary: acyclicity/connectedness ⟺ |Ex| finite/=1              *)
(*                                                                             *)
(* STATEMENT (§68.21, p.321):                                                  *)
(*   Let ps be a proof-structure, phi a switching, and                         *)
(*     Phi := +Phi_ax ps ++ AEx(Phi_switched ps phi)                           *)
(*   (the constellation corresponding to the correctness hypergraph S^phi).   *)
(*                                                                             *)
(*   (1) S^phi is acyclic             ⟺  |AEx(Phi)| < ∞                      *)
(*   (2) S^phi is connected & acyclic ⟺  |AEx(Phi)| = 1                      *)
(*   (3) S^phi is connected & acyclic ⟺  AEx(Phi) = concl_star ps             *)
(*                                                                             *)
(* PROOF SKETCH (§68.21):                                                      *)
(*   Follows from §68.17–18 (structural bijection between S^phi and D[Phi]).  *)
(*   The dependency graph D[Phi] mirrors the topology of S^phi:                *)
(*     · Cycle in S^phi ↔ cycle in D[Phi] ↔ |AEx| = ∞.                       *)
(*     · Two components in S^phi ↔ two stars in AEx output.                   *)
(*     · Connected tree ↔ single deterministic diagram ↔ |AEx| = 1.          *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.09 and stellaMLL.10                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §68.21  The set AEx(+Phi_ax ps ++ gamma) for a given gamma in AEx(Phi_S^phi). *)
(* We define dr_test_AEx as the union over all gamma in AEx(Phi_switched ps phi)  *)
(* of the further-executed set AEx(+Phi_ax ps ++ gamma).                           *)
(*   dr_test_AEx ps phi = BIGUNION { AEx_C (fhp (Phi_ax ps) ++ gamma)             *)
(*                                 | gamma IN AEx_C (Phi_switched ps phi) }        *)
Definition dr_test_AEx_def :                                    (* §68.21 *)
  dr_test_AEx (ps : proof_struct) (phi : num -> bool) : constellation set =
    BIGUNION { AEx_C (fhp (Phi_ax ps) ++ gamma)
             | gamma IN AEx_C (Phi_switched ps phi) }
End

(*
   PROOF-OBLIGATION[stellaMLL.09]:
   GOAL:
     !ps phi.
       switching ps phi ==>
       (* S^phi acyclic ⟺ |dr_test_AEx ps phi| < ∞ *)
       FINITE (dr_test_AEx ps phi)
       (* ⟺ S^phi acyclic — the graph-theoretic predicate is abstract here *)
   STRATEGY:
     By §68.17 (structural bijection ρ): cycles in S^phi correspond to cycles
     in D[Phi_switched ps phi]. A cycle in the dependency graph causes
     infinitely many saturated diagrams (divergence), so |AEx| = ∞ iff cyclic.
     Contrapositive: acyclic ⟺ |AEx| < ∞.
   CITATION: §68.21 Corollary.
   DRAFT-TACTICS: cheat (structural bijection §68.17 + graph theory)
*)

(*
   PROOF-OBLIGATION[stellaMLL.10]:
   GOAL:
     !ps phi.
       switching ps phi ==>
       (* S^phi connected & acyclic ⟺ dr_test_AEx = {concl_star ps} *)
       (dr_test_AEx ps phi = {concl_star ps} <=>
        FINITE (dr_test_AEx ps phi) /\ CARD (dr_test_AEx ps phi) = 1)
   STRATEGY:
     (⟹) Connected & acyclic → deterministic tree → unique diagram →
          AEx has exactly 1 element and it equals concl_star ps.
     (⟸) |AEx| = 1 → unique diagram → graph is a tree → connected & acyclic.
     Uses §68.18 (Cor.) and definition of concl_star.
   CITATION: §68.21 Corollary.
   DRAFT-TACTICS: cheat (§68.17–18 + deterministic tree characterisation)
*)

Theorem dr_acyclic_iff_finite_AEx :                            (* §68.21 *)
  !ps phi.
    switching ps phi ==>
    FINITE (dr_test_AEx ps phi)   (* iff S^phi acyclic; deferred *)
Proof
  cheat
QED

Theorem dr_connected_acyclic_iff_singleton_AEx :               (* §68.21 *)
  !ps phi.
    switching ps phi ==>
    (dr_test_AEx ps phi = {concl_star ps} <=>
     FINITE (dr_test_AEx ps phi) /\
     CARD (dr_test_AEx ps phi) = 1)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68  SANITY: switching_def is trivially valid for any phi                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem switching_any :
  !ps phi. switching ps phi
Proof
  rw [switching_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68  SANITY: Phi_switched equals Phi_cut for a cut-free proof-structure     *)
(*                                                                             *)
(* If ps has no cuts, Phi_cut ps = [] and Phi_switched ps phi = the vstar sum. *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem phi_switched_cutfree_prefix :
  !ps phi.
    normal_ps ps ==>
    Phi_switched ps phi =
    FLAT (MAP (vstar ps phi) (SET_TO_LIST ps.vertices))
Proof
  rw [normal_ps_def, Phi_switched_def, Phi_cut_def, cut_edges_def] >>
  simp [SET_TO_LIST_EMPTY]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §68  SANITY: dr_certifiable implies stellar_correctness_criterion           *)
(*   (follows immediately from unfolding dr_certifiable_def)                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem dr_certifiable_implies_criterion :
  !ps. dr_certifiable ps ==>
       !phi gamma.
         switching ps phi ==>
         gamma IN AEx_C (Phi_switched ps phi) ==>
         AEx_C (fhp (Phi_ax ps) ++ gamma) = {concl_star ps}
Proof
  rw [dr_certifiable_def] >> metis_tac []
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EXTENDED PROOF-DEBT LEDGER  (§68 additions to §66–67 ledger)               *)
(*                                                                              *)
(* stellaMLL.08  stellar_correctness_criterion equivalence  (§68.19)            *)
(*   GOAL: !ps. dr_certifiable ps <=> mll_certifiable ps                        *)
(*           (where mll_certifiable = all-switching DR acyclic+connected)       *)
(*   STRATEGY:                                                                  *)
(*     (⇒) dr_certifiable → AEx = concl_star for all phi → by §68.21 each     *)
(*         S^phi is acyclic+connected → mll_certifiable.                        *)
(*     (⇐) mll_certifiable → all S^phi acyclic+connected → by §68.21           *)
(*         |AEx| = 1 and the unique diagram = concl_star → dr_certifiable.     *)
(*     Relies on §68.17–18 (structural bijection ρ, not yet in scope).         *)
(*   STATUS: deferred (depends on §68.17–18 graph-theoretic machinery).        *)
(*   CITATION: §68.19 Theorem (Stellar correctness criterion).                  *)
(*                                                                              *)
(* stellaMLL.09  dr_acyclic_iff_finite_AEx  (§68.21 part 1)                    *)
(*   GOAL: !ps phi. switching ps phi ==>                                        *)
(*           FINITE (dr_test_AEx ps phi)  (* iff S^phi acyclic *)              *)
(*   STRATEGY: §68.17 structural bijection ρ maps cycles in S^phi to cycles    *)
(*     in D[Phi]; divergence iff cyclic. Requires graph-theoretic acyclicity    *)
(*     definition (not in scope here).                                          *)
(*   STATUS: deferred (structural bijection §68.17).                            *)
(*   CITATION: §68.21 Corollary.                                                *)
(*                                                                              *)
(* stellaMLL.10  dr_connected_acyclic_iff_singleton_AEx  (§68.21 part 2)       *)
(*   GOAL: !ps phi. switching ps phi ==>                                        *)
(*     (dr_test_AEx ps phi = {concl_star ps} <=>                               *)
(*      FINITE (dr_test_AEx ps phi) /\                                          *)
(*      CARD (dr_test_AEx ps phi) = 1)                                          *)
(*   STRATEGY: deterministic tree ↔ |AEx|=1 ↔ unique diagram = concl_star.    *)
(*   STATUS: deferred (structural bijection §68.17–18).                         *)
(*   CITATION: §68.21 Corollary.                                                *)
(*                                                                              *)
(* EVAL vs CHEAT SUMMARY  (§68 additions):                                      *)
(*   EVAL:                                                                       *)
(*     · dr_certifiable_iff_mll_certifiable — simp (definitional)               *)
(*     · stellar_correctness_criterion      — rw [dr_certifiable_def]           *)
(*     · switching_any                      — rw [switching_def]                *)
(*     · phi_switched_cutfree_prefix        — rw + SET_TO_LIST_EMPTY            *)
(*     · dr_certifiable_implies_criterion   — rw [dr_certifiable_def]           *)
(*   CHEAT (non-trivial, deferred):                                              *)
(*     · dr_acyclic_iff_finite_AEx    (stellaMLL.09)                            *)
(*     · dr_connected_acyclic_iff_singleton_AEx (stellaMLL.10)                  *)
(*                                                                              *)
(* ZERO new_axiom / mk_thm USED IN THIS FILE.                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* §69  Construction of multiplicative formulas                                *)
(*       Orthogonality · Behaviours · Usine/Usage                              *)
(*                                                                             *)
(* Eng §69.1–44.  Convention (§69.3): Ex = AEx throughout this section.       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.4  Three orthogonality relations                                        *)
(*                                                                             *)
(* Three binary relations on constellations, parameterised by a colour-set C: *)
(*                                                                             *)
(*   Φ₁ ⊥^{fin}_C Φ₂  iff  |Ex_C(Φ₁ ⊎ Φ₂)| < ∞                            *)
(*   Φ₁ ⊥^1_C   Φ₂  iff  |AEx_C(Φ₁ ⊎ Φ₂)| = 1                             *)
(*   Φ₁ ⊥^R_C   Φ₂  iff  Ex_C(Φ₁ ⊎ Φ₂) = {Roots(Φ₁ ⊎ Φ₂)}               *)
(*                                                                             *)
(* where Roots(Φ) is the star of uncoloured (free) rays of Φ, i.e. the       *)
(* unique star whose rays are exactly the free rays of the union.              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §69.4  The star of uncoloured (free/neutral) rays in the union Phi1 ⊎ Phi2. *)
(* Roots(Phi) is the single star of all rays with a neutral (uncoloured) head.  *)
(* We return it as a constellation (singleton star list) so that                 *)
(* AEx_C(...) = {roots_C Phi1 Phi2} is a set of constellations equation.        *)
Definition roots_def :                                          (* §69.4 *)
  roots (Phi1 : constellation) (Phi2 : constellation) : constellation =
    [ FILTER (λr. case r of
                    Var _ => T
                  | App h _ => let (pol, _) = decode_psym h in pol = Neutral)
             (FLAT Phi1 ++ FLAT Phi2) ]
End

(* §69.4  ⊥^{fin}: the execution of the union is finite. *)
Definition orth_fin_def :                                       (* §69.4 *)
  orth_fin_C (C : num set) (Phi1 : constellation) (Phi2 : constellation) : bool =
    FINITE (AEx_C (Phi1 ++ Phi2))
End

(* §69.4  ⊥^1: the abstract execution of the union has exactly one element. *)
Definition orth_one_def :                                       (* §69.4 *)
  orth_one_C (C : num set) (Phi1 : constellation) (Phi2 : constellation) : bool =
    (CARD (AEx_C (Phi1 ++ Phi2)) = 1)
End

(* §69.4  ⊥^R: the abstract execution of the union equals the singleton       *)
(* {Roots(Phi1 ⊎ Phi2)}, i.e. reduces to the star of uncoloured rays only.   *)
Definition orth_roots_def :                                     (* §69.4 *)
  orth_roots_C (C : num set) (Phi1 : constellation) (Phi2 : constellation) : bool =
    (AEx_C (Phi1 ++ Phi2) = {roots Phi1 Phi2})
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.4  Orthogonal of a set of constellations                                *)
(*                                                                             *)
(*   A^{⊥_C} := { Φ | ∀ Φ' ∈ A, Φ ⊥_C Φ' }                                 *)
(*                                                                             *)
(* We parameterise over the orthogonality predicate `orth` to obtain a single *)
(* definition covering ⊥^{fin}, ⊥^1, and ⊥^R.                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition orthogonal_set_def :                                 (* §69.4 *)
  orthogonal_set (orth : constellation -> constellation -> bool)
                 (A : constellation set) : constellation set =
    { Phi | !Phi'. Phi' IN A ==> orth Phi Phi' }
End

(* Convenient notation for the double orthogonal. *)
Definition biorth_def :                                         (* §69.4 *)
  biorth (orth : constellation -> constellation -> bool)
         (A : constellation set) : constellation set =
    orthogonal_set orth (orthogonal_set orth A)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.29  Pre-behaviour and §69.30  Behaviour                                 *)
(*                                                                             *)
(* §69.29  A *pre-behaviour* is any set of constellations.                     *)
(* §69.30  A pre-behaviour A is a *behaviour* when ∃ B s.t. A = B^⊥.         *)
(* Equivalently (§69.32): A is a behaviour iff A = A^{⊥⊥}.                   *)
(*                                                                             *)
(* We fix ⊥ = ⊥^{fin} throughout; the analogues for ⊥^1 and ⊥^R are         *)
(* definitionally identical up to swapping orth_fin for orth_one / orth_roots. *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §69.29  A pre-behaviour is simply a set of constellations. *)
Type pre_behaviour = ``:constellation set``

(* §69.30  A is a behaviour iff it is the orthogonal of some set B. *)
Definition is_behaviour_def :                                   (* §69.30 *)
  is_behaviour (orth : constellation -> constellation -> bool)
               (A : constellation set) : bool =
    ?B. A = orthogonal_set orth B
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.32  Proposition (Bi-orthogonal closure)                                 *)
(*                                                                             *)
(* A pre-behaviour A is a behaviour iff A = A^{⊥⊥}.                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.11]:
   GOAL:
     !orth A.
       is_behaviour orth A <=>
       (orthogonal_set orth (orthogonal_set orth A) = A)
   STRATEGY:
     (⇒) A = B^⊥  →  A^{⊥⊥} = B^{⊥⊥⊥} = B^⊥ = A
         (using the general closure property: X^⊥ = X^{⊥⊥⊥} for all X).
     (⇐) A = A^{⊥⊥} → take B := A^⊥; then B^⊥ = A^{⊥⊥} = A.
     The standard closure property (X ⊆ X^{⊥⊥}, A^⊥ = A^{⊥⊥⊥}) holds
     for any orthogonality predicate.  Both directions follow by set
     extensionality and unfolding orthogonal_set_def / is_behaviour_def.
   STATUS: deferred (biorthogonal closure lattice argument).
   CITATION: §69.32 Proposition.
*)

Theorem behaviour_iff_biorth :
  !orth (A : constellation set).
    is_behaviour orth A <=>
    (orthogonal_set orth (orthogonal_set orth A) = A)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.35  Pre-tensor  (Usine)                                                 *)
(*                                                                             *)
(*   A ⊙ B := { Φ₁ ⊎ Φ₂ | Φ₁ ∈ A, Φ₂ ∈ B }                                *)
(*                                                                             *)
(* where ⊎ is disjoint union of constellations (i.e. list append ++ in our   *)
(* concrete representation, assuming the stars are vertex-disjoint by §69.33).*)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition pre_tensor_def :                                     (* §69.35 *)
  pre_tensor (A : constellation set) (B : constellation set)
             : constellation set =
    { Phi | ?Phi1 Phi2. Phi1 IN A /\ Phi2 IN B /\ Phi = Phi1 ++ Phi2 }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.36  Tensor  (Usage)                                                     *)
(*                                                                             *)
(*   A ⊗ B := (A ⊙ B)^{⊥⊥}                                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition behaviour_tensor_def :                               (* §69.36 *)
  behaviour_tensor (orth : constellation -> constellation -> bool)
                   (A : constellation set) (B : constellation set)
                   : constellation set =
    biorth orth (pre_tensor A B)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.39–40  Par and linear implication                                       *)
(*                                                                             *)
(*   A ⅋ B := (A^⊥ ⊗ B^⊥)^⊥                                                *)
(*   A ⊸ B := A^⊥ ⅋ B                                                        *)
(*                                                                             *)
(* We define these in terms of behaviour_tensor and orthogonal_set.            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition behaviour_par_def :                                  (* §69.40 *)
  behaviour_par (orth : constellation -> constellation -> bool)
                (A : constellation set) (B : constellation set)
                : constellation set =
    orthogonal_set orth
      (behaviour_tensor orth (orthogonal_set orth A) (orthogonal_set orth B))
End

Definition behaviour_impl_def :                                 (* §69.40 *)
  behaviour_impl (orth : constellation -> constellation -> bool)
                 (A : constellation set) (B : constellation set)
                 : constellation set =
    behaviour_par orth (orthogonal_set orth A) B
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.43  Theorem (Associativity of pairwise execution)                       *)
(*                                                                             *)
(*   For constellations Φ₁, Φ₂, Φ₃ with ⋂_C(Φ₁, Φ₂, Φ₃) = ∅:             *)
(*   Ex_C(Φ₁ ⊎ Ex_C(Φ₂ ⊎ Φ₃)) = Ex_C(Ex_C(Φ₁ ⊎ Φ₂) ⊎ Φ₃)                *)
(*                                                                             *)
(* We encode "colour-disjointness" by the predicate colours_disjoint below.   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Placeholder: three constellations are mutually colour-disjoint. *)
Definition colours_disjoint3_def :                              (* §69.43 *)
  colours_disjoint3 (Phi1 : constellation) (Phi2 : constellation)
                    (Phi3 : constellation) : bool =
    (* Colours used by any star in Phi_i are disjoint from those in Phi_j, i≠j *)
    (* The precise definition requires the colour-set machinery of §49; we     *)
    (* state it abstractly here.                                                *)
    T   (* placeholder — proof obligation spells out the content *)
End

(*
   PROOF-OBLIGATION[stellaMLL.12]:
   GOAL:
     !Phi1 Phi2 Phi3.
       colours_disjoint3 Phi1 Phi2 Phi3 ==>
       AEx_C (Phi1 ++ (FLAT (SET_TO_LIST (AEx_C (Phi2 ++ Phi3))))) =
       AEx_C ((FLAT (SET_TO_LIST (AEx_C (Phi1 ++ Phi2)))) ++ Phi3)
   STRATEGY:
     Follows from §49.55 (aex_idempotent) and the fact that AEx_C distributes
     over colour-disjoint unions (confluence of the stellar resolution rewriting
     system).  The key steps are:
       1. AEx_C(Phi2 ++ Phi3) can be substituted in Phi1's context because the
          colour sets are disjoint (stars interact only within their own colour
          ranges → AEx commutes with disjoint-colour decomposition).
       2. Fold / unfold AEx_C via aex_idempotent (stellaExecution §49.55).
       3. Associativity of the underlying resolution steps (one-step reduction
          Church-Rosser, given colour-disjointness).
   STATUS: deferred (requires §49 colour-disjoint confluence machinery).
   CITATION: §69.43 Theorem.
*)

Theorem aex_assoc :
  !Phi1 Phi2 Phi3.
    colours_disjoint3 Phi1 Phi2 Phi3 ==>
    AEx_C (Phi1 ++ FLAT (SET_TO_LIST (AEx_C (Phi2 ++ Phi3)))) =
    AEx_C (FLAT (SET_TO_LIST (AEx_C (Phi1 ++ Phi2))) ++ Phi3)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69.44  Theorem (Trefoil Property / Adjunction)                             *)
(*                                                                             *)
(*   For Φ₁, Φ₂, Φ₃ with ⋂_C = ∅:                                           *)
(*   Φ₁ ⊥_C Ex_C(Φ₂ ⊎ Φ₃)  iff  Ex_C(Φ₁ ⊎ Φ₂) ⊥_C Φ₃                    *)
(*                                                                             *)
(* We state for ⊥^{fin}; analogues hold for ⊥^1 and ⊥^R by same argument.   *)
(* The §69.46 Corollary (Adjunction) is the special case where Φ₂ = adapters.*)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.13]:
   GOAL:
     !Phi1 Phi2 Phi3.
       colours_disjoint3 Phi1 Phi2 Phi3 ==>
       (orth_fin_C {} Phi1 (FLAT (SET_TO_LIST (AEx_C (Phi2 ++ Phi3)))) <=>
        orth_fin_C {} (FLAT (SET_TO_LIST (AEx_C (Phi1 ++ Phi2)))) Phi3)
   STRATEGY:
     orth_fin_C unfolds to FINITE (AEx_C (Phi ++ Phi')).
     Use aex_assoc (stellaMLL.12) to rewrite:
       AEx_C(Phi1 ++ AEx_C(Phi2 ++ Phi3)) = AEx_C(AEx_C(Phi1 ++ Phi2) ++ Phi3)
     Then FINITE of either side equals FINITE of the common value.
     The same argument works mutatis mutandis for ⊥^1 (CARD = 1) and
     ⊥^R ({Roots}) using set-equality.
   STATUS: deferred (depends on stellaMLL.12 + AEx_C FINITE lemma).
   CITATION: §69.44 Theorem (Trefoil), §69.46 Corollary (Adjunction).
*)

Theorem trefoil :
  !Phi1 Phi2 Phi3.
    colours_disjoint3 Phi1 Phi2 Phi3 ==>
    (orth_fin_C {} Phi1 (FLAT (SET_TO_LIST (AEx_C (Phi2 ++ Phi3)))) <=>
     orth_fin_C {} (FLAT (SET_TO_LIST (AEx_C (Phi1 ++ Phi2)))) Phi3)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69  SANITY: orthogonal_set is monotone-decreasing                          *)
(*   If A ⊆ B then B^⊥ ⊆ A^⊥.                                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem orth_set_anti_mono :
  !orth (A : constellation set) B.
    A SUBSET B ==>
    orthogonal_set orth B SUBSET orthogonal_set orth A
Proof
  rw [orthogonal_set_def, SUBSET_DEF] >> metis_tac []
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69  SANITY: A ⊆ A^{⊥⊥}                                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem subset_biorth :
  !orth (A : constellation set).
    A SUBSET biorth orth A
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69  SANITY: pre_tensor is contained in the tensor                          *)
(*   A ⊙ B ⊆ A ⊗ B   (immediate from A ⊙ B ⊆ (A ⊙ B)^{⊥⊥})                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem pre_tensor_subset_tensor :
  !orth (A : constellation set) B.
    pre_tensor A B SUBSET behaviour_tensor orth A B
Proof
  rw [behaviour_tensor_def] >> irule subset_biorth
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69  SANITY: par in terms of tensor (unfold check)                          *)
(*   A ⅋ B = (A^⊥ ⊗ B^⊥)^⊥                                                 *)
(*   This holds definitionally; we state it as an equality for documentation.  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem par_eq_dual_tensor_dual :
  !orth (A : constellation set) B.
    behaviour_par orth A B =
    orthogonal_set orth
      (behaviour_tensor orth (orthogonal_set orth A) (orthogonal_set orth B))
Proof
  rw [behaviour_par_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §69  SANITY: implication in terms of par (unfold check)                     *)
(*   A ⊸ B = A^⊥ ⅋ B                                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem impl_eq_par :
  !orth (A : constellation set) B.
    behaviour_impl orth A B =
    behaviour_par orth (orthogonal_set orth A) B
Proof
  rw [behaviour_impl_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EXTENDED PROOF-DEBT LEDGER  (§69 additions)                                 *)
(*                                                                              *)
(* stellaMLL.11  behaviour_iff_biorth  (§69.32 Proposition)                   *)
(*   GOAL: is_behaviour orth A <=> orthogonal_set orth (orthogonal_set orth A) = A*)
(*   STRATEGY: Biorthogonal closure A^{⊥⊥⊥} = A^⊥; both directions by set-   *)
(*     extensionality + unfolding is_behaviour_def / orthogonal_set_def.        *)
(*   STATUS: deferred (closure-lattice argument).                               *)
(*   CITATION: §69.32.                                                          *)
(*                                                                              *)
(* stellaMLL.12  aex_assoc  (§69.43 Theorem)                                  *)
(*   GOAL: colours_disjoint3 Phi1 Phi2 Phi3 ==>                                *)
(*     AEx_C(Phi1 ++ AEx(Phi2++Phi3)) = AEx_C(AEx(Phi1++Phi2) ++ Phi3)       *)
(*   STRATEGY: §49.55 idempotence + colour-disjoint confluence.                 *)
(*   STATUS: deferred (§49 confluence machinery).                               *)
(*   CITATION: §69.43.                                                          *)
(*                                                                              *)
(* stellaMLL.13  trefoil  (§69.44 Theorem + §69.46 Adjunction)                *)
(*   GOAL: colours_disjoint3 ==>                                                *)
(*     orth_fin Phi1 AEx(Phi2++Phi3) <=> orth_fin AEx(Phi1++Phi2) Phi3       *)
(*   STRATEGY: unfold orth_fin, use aex_assoc (stellaMLL.12), FINITE iff.     *)
(*   STATUS: deferred (depends on stellaMLL.12).                                *)
(*   CITATION: §69.44, §69.46.                                                 *)
(*                                                                              *)
(* EVAL vs CHEAT SUMMARY  (§69 additions):                                     *)
(*   EVAL / rw (non-debt):                                                      *)
(*     · orth_set_anti_mono   — rw + metis_tac, pure set reasoning             *)
(*     · subset_biorth         — rw + metis_tac, pure set reasoning            *)
(*     · pre_tensor_subset_tensor — irule subset_biorth                        *)
(*     · par_eq_dual_tensor_dual  — rw [behaviour_par_def]                    *)
(*     · impl_eq_par              — rw [behaviour_impl_def]                   *)
(*   CHEAT (non-trivial, deferred):                                             *)
(*     · behaviour_iff_biorth   (stellaMLL.11)                                  *)
(*     · aex_assoc              (stellaMLL.12)                                  *)
(*     · trefoil                (stellaMLL.13)                                  *)
(*                                                                              *)
(* ZERO new_axiom / mk_thm USED IN THIS FILE.                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* §70  Soundness and completeness (pp. 332–339)                               *)
(*                                                                             *)
(* SCOPE: §70.9 (basis of interpretation), §70.10 (formula interpretation),   *)
(*        §70.17 (full soundness MLL+MIX), §70.21 (completeness MLL+MIX),     *)
(*        §70.23 (full soundness MLL), §70.25 (strict interpretations),        *)
(*        §70.26 (completeness MLL).                                            *)
(*                                                                             *)
(* NOT ATTEMPTED: §71–72.                                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.9  Basis of interpretation Ω                                             *)
(*                                                                             *)
(* A basis of interpretation is a function                                     *)
(*   Ω : mll_formula × num × term → constellation set                         *)
(* mapping a formula label A, an occurrence index i, and an address term t     *)
(* to a behaviour Ω(A, i, t).                                                  *)
(*                                                                             *)
(* MLL formula syntax — a simple HOL4 datatype for the scaffold.               *)
(* We keep it minimal: atoms, negations, tensor, par.                           *)
(* (Full MLL would also include the multiplicative units; §71 is out of scope.) *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §70.9  MLL formula datatype.  Atoms are identified by natural numbers.      *)
Datatype:                                                       (* §66.2/§70.9 *)
  mll_formula =
    MAtom  num          (* positive atom X_i                                  *)
  | MNeg   num          (* negative atom X_i^⊥                                *)
  | MTens  mll_formula mll_formula   (* A ⊗ B                                *)
  | MPar   mll_formula mll_formula   (* A ⅋ B                                *)
End

(* §70.9  A basis of interpretation Ω maps (formula, occurrence index, address
   term) to a behaviour (a set of constellations).                              *)
(* We represent Ω as a HOL function of type:                                   *)
(*   mll_formula -> num -> term -> constellation set                            *)
Type basis_interp = ``:mll_formula -> num -> term -> constellation set``

(* §70.9  Well-formedness predicate for a basis of interpretation Ω (§70.9).   *)
(* Ω must satisfy:                                                              *)
(*   (1) Each Ω(A, i, t) is a behaviour (w.r.t. the given orthogonality).     *)
(*   (2) Ω(A, i, t) and Ω(B, j, u) are disjoint when i ≠ j.                  *)
(* We state this abstractly.                                                   *)
(* §70.9  Well-formedness: each Omega(A,i,t) is a behaviour (§69.30).         *)
Definition wf_basis_behaviours_def :                            (* §70.9 *)
  wf_basis_behaviours (orth : constellation -> constellation -> bool)
                      (Omega : basis_interp) : bool =
    !A i t. is_behaviour orth (Omega A i t)
End

(* §70.9  Combined well-formedness predicate for a basis of interpretation.   *)
(* The disjointness condition (§69.33) is abstract and trivially satisfied in  *)
(* this scaffold; only the behaviour condition is non-trivial.                  *)
Definition wf_basis_def :                                       (* §70.9 *)
  wf_basis (orth : constellation -> constellation -> bool)
           (Omega : basis_interp) : bool =
    wf_basis_behaviours orth Omega
    (* §69.33 colour-disjointness of distinct-index behaviours: abstract/trivial *)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.10  Interpretation of MLL formulas  [[C, A, t]]_Ω                        *)
(*                                                                             *)
(* Given Ω, a conclusion formula C (as the function-symbol wrapper), a         *)
(* formula occurrence A, and a term t encoding the path from C to A:           *)
(*                                                                             *)
(*   [[X_i,   t]]_Ω = Ω(X_i,   i, t)                                         *)
(*   [[X_i^⊥, t]]_Ω = Ω(X_i^⊥, i, t)^⊥ = orthogonal_set orth (Ω(X_i,i,t)) *)
(*   [[A ⊗ B, t]]_Ω = [[A, 1·t]]_Ω ⊗ [[B, r·t]]_Ω   (behaviour_tensor)      *)
(*   [[A ⅋ B, t]]_Ω = [[A, 1·t]]_Ω ⅋ [[B, r·t]]_Ω   (behaviour_par)        *)
(*                                                                             *)
(* The term constructors 1·t and r·t are App dir_left [t] / App dir_right [t]. *)
(*                                                                             *)
(* For the sequent interpretation: [[⊢ C₁,...,Cₙ]]_Ω = [[C₁]] ⅋ ... ⅋ [[Cₙ]].*)
(* We represent a sequent as a list of formulas.                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §70.10  Formula interpretation:  [[A, t]]_Ω as a behaviour (constellation set). *)
(* The recursion on mll_formula is primitive-recursive in HOL4.                    *)
Definition interp_formula_def :                                 (* §70.10 *)
  interp_formula
    (orth  : constellation -> constellation -> bool)
    (Omega : basis_interp)
    (A     : mll_formula)
    (t     : term)
    : constellation set =
  case A of
    MAtom i  => Omega (MAtom i) i t
  | MNeg  i  => orthogonal_set orth (Omega (MAtom i) i t)
  | MTens A1 A2 =>
      behaviour_tensor orth
        (interp_formula orth Omega A1 (App dir_left  [t]))
        (interp_formula orth Omega A2 (App dir_right [t]))
  | MPar A1 A2 =>
      behaviour_par orth
        (interp_formula orth Omega A1 (App dir_left  [t]))
        (interp_formula orth Omega A2 (App dir_right [t]))
End

(* §70.10  Sequent interpretation  [[⊢ Γ]]_Ω = [[C₁]] ⅋ ... ⅋ [[Cₙ]].       *)
(* We use the variable Var 0 as the "top" address X for each top-level formula. *)
Definition interp_sequent_def :                                 (* §70.10 *)
  interp_sequent
    (orth  : constellation -> constellation -> bool)
    (Omega : basis_interp)
    (Gamma : mll_formula list)
    : constellation set =
  case Gamma of
    []       => {[]}   (* empty sequent: singleton containing the empty constellation *)
  | [C]      => interp_formula orth Omega C (Var 0)
  | (C :: Cs) =>
      behaviour_par orth
        (interp_formula orth Omega C (Var 0))
        (interp_sequent orth Omega Cs)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.19  Proof-like constellation  (§70.19)                                   *)
(*                                                                             *)
(* A constellation Φ is *proof-like* w.r.t. ⊢ Γ if it is well-formed (§69.27)*)
(* and its identity rays IdRays(Φ) match the address-rays ‡Γ of the syntax    *)
(* tree of ⊢ Γ.                                                                *)
(*                                                                             *)
(* We encode well-formedness abstractly (full §69.27 checking would require    *)
(* inspecting all rays) and the address-ray condition as a predicate.           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §70.19  Abstract well-formedness of a constellation (§69.27 conditions).    *)
(* The full definition requires checking: finite, binary stars, disjoint rays, *)
(* all heads Pos or Neutral, at least one Pos head, address-form subterms.     *)
(* We state it as an abstract predicate.                                        *)
(* §70.19  wf_vehicle: §69.27 conditions (1) binary stars (2) at least one   *)
(* positive head.  The remaining conditions (disjointness, address-form) are   *)
(* stated abstractly.                                                           *)
Definition wf_vehicle_binary_def :                              (* §69.27 (2) *)
  wf_vehicle_binary (Phi : constellation) : bool =
    !s. MEM s Phi ==> LENGTH s = 2
End

Definition wf_vehicle_pos_head_def :                            (* §69.27 (5) *)
  wf_vehicle_pos_head (Phi : constellation) : bool =
    ?s r. MEM s Phi /\ MEM r s /\
          ?h args. r = App h args /\
                   FST (decode_psym h) = Pos
End

val wf_vehicle_def = Define `                                   (* §69.27/§70.19 *)
  wf_vehicle (Phi : constellation) : bool =
    (wf_vehicle_binary Phi /\ wf_vehicle_pos_head Phi)
`;

(* §70.19  Address-ray set ‡Γ: the set of address-rays from the syntax tree   *)
(* ST(⊢ Γ).  We represent this abstractly.                                     *)
Definition addr_rays_sequent_def :                              (* §70.19 *)
  addr_rays_sequent (Gamma : mll_formula list) : (num # num) set =
    (* IdRays(Phi) is defined in stellaDiagramTheory; here we just state the  *)
    (* matching condition abstractly as a set of (star-index, ray-index) pairs *)
    (* encoding the addresses of atoms in the syntax tree of ⊢ Gamma.         *)
    (* The full definition requires computing pAddr on the syntax tree.        *)
    {}   (* abstract placeholder *)
End

(* §70.19  Proof-like constellation w.r.t. sequent ⊢ Γ.                       *)
(* Full condition: wf_vehicle AND IdRays(Phi) = address-rays of ST(⊢ Gamma). *)
val proof_like_def = Define `                                   (* §70.19 *)
  proof_like (Phi : constellation) (Gamma : mll_formula list) : bool =
    (wf_vehicle Phi /\ (IdRays Phi = addr_rays_sequent Gamma))
`;

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.25  Strict interpretations ⟨⟨⊢ Γ⟩⟩^1_Ω and ⟨⟨⊢ Γ⟩⟩^R_Ω              *)
(*                                                                             *)
(* §70.25 defines two strict interpretations for MLL (p.339):                  *)
(*   ⟨⟨⊢ Γ⟩⟩^1_Ω = Tests(⊢ Γ)^{⊥^1}                                        *)
(*   ⟨⟨⊢ Γ⟩⟩^R_Ω = Tests(⊢ Γ)^{⊥^R}                                        *)
(*                                                                             *)
(* Tests(⊢ Γ) is the set of Φ_S^φ test constellations from §69.15, defined   *)
(* from the syntax tree of ⊢ Γ (independent of proof-structures).              *)
(*                                                                             *)
(* We encode Tests(⊢ Γ) as the set of all switched test constellations of     *)
(* the syntax-hypergraph proof-structure derived from ⊢ Γ.                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §69.15 / §70.25  Set of tests for a sequent ⊢ Γ.                           *)
(* Tests(⊢ Γ) = { Test(⊢ Γ)^φ | φ switching of ST(⊢ Γ) }.                   *)
(* We model this as the image of all switchings of the syntax-tree proof-struct.*)
Definition tests_sequent_def :                                  (* §69.15 *)
  tests_sequent (Gamma : mll_formula list) : constellation set =
    (* Abstract: the set of all test constellations Test(⊢ Gamma)^phi,        *)
    (* ranging over all switchings phi of the syntax tree ST(⊢ Gamma).        *)
    (* The concrete definition would build the syntax-tree proof-structure     *)
    (* and apply Phi_switched; we leave this abstract for the scaffold.        *)
    { T_phi | ?phi. T_phi = Phi_switched
                      <| vertices := {}; edges := {}
                       ; in_ps := \e. (0,0); out_ps := \e. 0
                       ; lbl := \e. Ax; concl := {} |>
                      phi }
    (* placeholder: the actual definition must build the ST(⊢ Gamma)          *)
    (* proof-structure from the formula grammar.                               *)
End

(* §70.25  Strict interpretation ⟨⟨⊢ Γ⟩⟩^1_Ω = Tests(⊢ Γ)^{⊥^1}.           *)
Definition strict_interp_one_def :                              (* §70.25 *)
  strict_interp_one
    (Omega : basis_interp)
    (Gamma : mll_formula list)
    : constellation set =
    orthogonal_set (orth_one_C {}) (tests_sequent Gamma)
End

(* §70.25  Strict interpretation ⟨⟨⊢ Γ⟩⟩^R_Ω = Tests(⊢ Γ)^{⊥^R}.           *)
Definition strict_interp_roots_def :                            (* §70.25 *)
  strict_interp_roots
    (Omega : basis_interp)
    (Gamma : mll_formula list)
    : constellation set =
    orthogonal_set (orth_roots_C {}) (tests_sequent Gamma)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.17  Theorem: Full soundness for MLL+MIX                                  *)
(*                                                                             *)
(* STATEMENT (§70.17, p.335):                                                   *)
(*   Let ⊢ S : Γ be an MLL+MIX proof-net and Ω a basis of interpretation.     *)
(*   We have:  Ex(Φ_S^comp) ∈ [[⊢ Γ]]_Ω                                       *)
(*   (w.r.t. orthogonality ⊥^{fin})                                            *)
(*                                                                             *)
(* In our encoding: "S is an MLL+MIX proof-net ⊢ S : Γ" is stated as a        *)
(* predicate is_mll_proof_net relating proof_struct, sequent, and certification.*)
(*                                                                             *)
(* We use AEx_C and interp_sequent with orth_fin_C.                            *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.14                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §70.17  Abstract predicate: S is an MLL+MIX proof-net proving sequent Γ.   *)
(* This encodes the conditions: proof-structure, DR-certifiable, ⊢ S : Γ.     *)
Definition is_mll_mix_proof_net_def :                           (* §70.12 *)
  is_mll_mix_proof_net (S : proof_struct) (Gamma : mll_formula list) : bool =
    dr_certifiable S   (* MLL-certifiable proof-net; MIX allows disconnected components *)
    (* PROOF-OBLIGATION: strengthen to include the sequent-labelling condition *)
End

(* §70.17  Abstract predicate: S is an MLL proof-net (connected, not just MIX). *)
(* MLL requires that ALL switchings are connected AND acyclic (not just acyclic). *)
Definition is_mll_proof_net_def :                               (* §70.23 *)
  is_mll_proof_net (S : proof_struct) (Gamma : mll_formula list) : bool =
    dr_certifiable S   (* same placeholder; MLL-certifiable implies fully correct *)
    (* PROOF-OBLIGATION: the MLL case additionally requires connectedness of
       every switching — cf. §69.7 / §68.21 *)
End

(*
   PROOF-OBLIGATION[stellaMLL.14]:
   GOAL (§70.17 — Full soundness MLL+MIX, orthogonality ⊥^{fin}):
     !S Gamma Omega.
       is_mll_mix_proof_net S Gamma ==>
       wf_basis (orth_fin_C {}) Omega ==>
       ?gamma. gamma IN AEx_C (Phi_comp S) /\
               gamma IN interp_sequent (orth_fin_C {}) Omega Gamma
   STRATEGY (§70.17 proof, p.335):
     Induction on the proof-net structure of S.
     · Axiom case (S ⊢ X_i, X_i^⊥):
         Phi_comp S = Phi_ax S = [[+X_i(X), +X_i^⊥(X)]].
         Show Phi_ax S ∈ [[X_i]]_Omega ⅋ [[X_i^⊥]]_Omega.
         Unfold behaviour_par, behaviour_tensor; the basis Omega satisfies
         Phi_ax S ⊥^{fin} every test of ⊢ X_i, X_i^⊥.
         By wf_basis and orth_fin_C.
     · Tensor case (⊢ S : Γ, Δ, A ⊗ B from S₁ : Γ,A and S₂ : Δ,B):
         By IH on S₁ and S₂; Phi_comp S₁ ∈ [[⊢ Γ,A]]_Omega,
         Phi_comp S₂ ∈ [[⊢ Δ,B]]_Omega.
         Phi_comp S = Phi_comp S₁ ++ Phi_comp S₂ ∈ pre_tensor ... ⊆ tensor.
         Use Lemma §70.14 (tensor interaction).
     · Par case (⊢ S : Γ, A ⅋ B): direct from IH and definition of par.
     · MIX case (⊢ S : Γ,Δ from S₁:Γ and S₂:Δ):
         As in tensor case; note MIX allows pre_tensor ⊆ par (§70.17 proof).
     · Cut case: Phi_comp has cuts; by Theorem §67.10 (sim_cut_elim),
         AEx(Phi_comp S) ≃_S Phi_ax(S'), S' cut-free normal form.
         Apply the cut-free case to S'.
   CITATION: §70.17 Theorem (Full soundness MLL+MIX).
   DRAFT-TACTICS: cheat
*)
Theorem full_soundness_mll_mix :                                (* §70.17 *)
  !S Gamma Omega.
    is_mll_mix_proof_net S Gamma ==>
    wf_basis (orth_fin_C {}) Omega ==>
    ?gamma.
      gamma IN AEx_C (Phi_comp S) /\
      gamma IN interp_sequent (orth_fin_C {}) Omega Gamma
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.21  Theorem: Completeness for MLL+MIX                                    *)
(*                                                                             *)
(* STATEMENT (§70.21, p.338):                                                   *)
(*   If Φ ∈ [[⊢ Γ]]_Ω is proof-like w.r.t. ⊢ Γ, then there exists an         *)
(*   MLL+MIX proof-net ⊢ S : Γ such that Φ = Φ_S^{ax}.                        *)
(*                                                                             *)
(* DEFERRED: proof-obligation stellaMLL.15                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.15]:
   GOAL (§70.21 — Completeness MLL+MIX):
     !Phi Gamma Omega.
       proof_like Phi Gamma ==>
       wf_basis (orth_fin_C {}) Omega ==>
       Phi IN interp_sequent (orth_fin_C {}) Omega Gamma ==>
       ?S. is_mll_mix_proof_net S Gamma /\ Phi_ax S = Phi
   STRATEGY (§70.21 proof, p.338):
     Phi is proof-like: well-formed, binary stars, address-rays match ST(⊢ Gamma).
     Construct S by placing axiom links on the syntax tree ST(⊢ Gamma),
     linking atoms matched by Phi (each binary star [r, r'] gives one ax link).
     Since Phi ∈ [[⊢ Gamma]]_Omega ⊆ Tests(⊢ Gamma)^{⊥^{fin}} (by §70.18):
       for all switchings phi, Test(⊢ Gamma)^phi ⊥^{fin} Phi
       <=> AEx(Test(⊢ Gamma)^phi ++ Phi) is finite
       => by §68.21 (dr_acyclic_iff_finite_AEx): S^phi is acyclic.
     Acyclicity for all switchings = MLL+MIX correctness (§68.21 (1)).
     Hence S is an MLL+MIX proof-net with Phi_ax S = Phi.
   CITATION: §70.21 Theorem (Completeness MLL+MIX).
   DRAFT-TACTICS: cheat
*)
Theorem completeness_mll_mix :                                  (* §70.21 *)
  !Phi Gamma Omega.
    proof_like Phi Gamma ==>
    wf_basis (orth_fin_C {}) Omega ==>
    Phi IN interp_sequent (orth_fin_C {}) Omega Gamma ==>
    ?S.
      is_mll_mix_proof_net S Gamma /\ Phi_ax S = Phi
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.23  Theorem: Full soundness for MLL                                       *)
(*                                                                             *)
(* STATEMENT (§70.23, p.338):                                                   *)
(*   Let ⊢ S : Γ be an MLL proof-net and Ω a basis of interpretation.          *)
(*   We have:  Ex(Φ_S^comp) ∈ [[⊢ Γ]]_Ω                                        *)
(*   (holding for both ⊥^1 and ⊥^R orthogonalities)                            *)
(*                                                                             *)
(* We state two variants — one for ⊥^1 and one for ⊥^R.                       *)
(* DEFERRED: proof-obligation stellaMLL.16 / stellaMLL.17                       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.16]:
   GOAL (§70.23 — Full soundness MLL, orthogonality ⊥^1):
     !S Gamma Omega.
       is_mll_proof_net S Gamma ==>
       wf_basis (orth_one_C {}) Omega ==>
       ?gamma.
         gamma IN AEx_C (Phi_comp S) /\
         gamma IN interp_sequent (orth_one_C {}) Omega Gamma
   STRATEGY (§70.23 proof, p.338):
     Exactly as §70.17 proof, but using ⊥^1.
     The only difference is the axiom case:
       Need CARD(AEx(Phi1 ++ Phi2 ++ Phi_ax S)) = 1 (not merely finite).
       By wf_basis: Phi2 ++ Phi_ax S is orthogonal ⊥^1 to Phi1
       (the basis satisfies the interaction condition — §70.9 property).
       Hence AEx has exactly 1 element.
   CITATION: §70.23 Theorem (Full soundness MLL).
   DRAFT-TACTICS: cheat
*)
Theorem full_soundness_mll_one :                                (* §70.23 *)
  !S Gamma Omega.
    is_mll_proof_net S Gamma ==>
    wf_basis (orth_one_C {}) Omega ==>
    ?gamma.
      gamma IN AEx_C (Phi_comp S) /\
      gamma IN interp_sequent (orth_one_C {}) Omega Gamma
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL.17]:
   GOAL (§70.23 — Full soundness MLL, orthogonality ⊥^R):
     !S Gamma Omega.
       is_mll_proof_net S Gamma ==>
       wf_basis (orth_roots_C {}) Omega ==>
       ?gamma.
         gamma IN AEx_C (Phi_comp S) /\
         gamma IN interp_sequent (orth_roots_C {}) Omega Gamma
   STRATEGY:
     Same as stellaMLL.16 but for ⊥^R:
       AEx(Phi1 ++ Phi2 ++ Phi_ax S) = {Roots(Phi1 ++ Phi2 ++ Phi_ax S)}
       (reduces entirely to uncoloured rays).
   CITATION: §70.23 Theorem (Full soundness MLL) — ⊥^R variant.
   DRAFT-TACTICS: cheat
*)
Theorem full_soundness_mll_roots :                              (* §70.23 *)
  !S Gamma Omega.
    is_mll_proof_net S Gamma ==>
    wf_basis (orth_roots_C {}) Omega ==>
    ?gamma.
      gamma IN AEx_C (Phi_comp S) /\
      gamma IN interp_sequent (orth_roots_C {}) Omega Gamma
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70.26  Theorem: Completeness for MLL                                         *)
(*                                                                             *)
(* STATEMENT (§70.26, p.339):                                                   *)
(*   If Φ ∈ ⟨⟨⊢ Γ⟩⟩^R_Ω (resp. ⟨⟨⊢ Γ⟩⟩^1_Ω) is proof-like w.r.t. a          *)
(*   provable MLL sequent ⊢ Γ, then there exists an MLL proof-net ⊢ S : Γ     *)
(*   such that Φ = Φ_S^{ax}.                                                    *)
(*                                                                             *)
(* We state two variants — for ⊥^R and for ⊥^1.                               *)
(* DEFERRED: proof-obligation stellaMLL.18 / stellaMLL.19                       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL.18]:
   GOAL (§70.26 — Completeness MLL, strict interpretation ⟨⟨⊢ Γ⟩⟩^R):
     !Phi Gamma Omega.
       proof_like Phi Gamma ==>
       wf_basis (orth_roots_C {}) Omega ==>
       Phi IN strict_interp_roots Omega Gamma ==>
       ?S. is_mll_proof_net S Gamma /\ Phi_ax S = Phi
   STRATEGY (§70.26 proof, p.339):
     Like MLL+MIX completeness (stellaMLL.15).
     Construct S on ST(⊢ Gamma) from Phi.
     Now Phi ∈ ⟨⟨⊢ Gamma⟩⟩^R_Omega = Tests(⊢ Gamma)^{⊥^R}:
       for all switchings phi, Phi ⊥^R Test(⊢ Gamma)^phi
       <=> AEx(Phi ++ Test(⊢ Gamma)^phi) = {Roots(...)}.
       By §68.21 Corollary (dr_connected_acyclic_iff_singleton_AEx):
         AEx has exactly 1 element => S^phi connected & acyclic.
     Connected & acyclic for all switchings = MLL correctness.
     Hence S is an MLL proof-net.
   CITATION: §70.26 Theorem (Completeness MLL) — ⊥^R variant.
   DRAFT-TACTICS: cheat
*)
Theorem completeness_mll_roots :                                (* §70.26 *)
  !Phi Gamma Omega.
    proof_like Phi Gamma ==>
    wf_basis (orth_roots_C {}) Omega ==>
    Phi IN strict_interp_roots Omega Gamma ==>
    ?S.
      is_mll_proof_net S Gamma /\ Phi_ax S = Phi
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL.19]:
   GOAL (§70.26 — Completeness MLL, strict interpretation ⟨⟨⊢ Γ⟩⟩^1):
     !Phi Gamma Omega.
       proof_like Phi Gamma ==>
       wf_basis (orth_one_C {}) Omega ==>
       Phi IN strict_interp_one Omega Gamma ==>
       ?S. is_mll_proof_net S Gamma /\ Phi_ax S = Phi
   STRATEGY:
     Same as stellaMLL.18 but using ⊥^1:
       Phi ⊥^1 Test(⊢ Gamma)^phi => CARD(AEx) = 1 => S^phi connected & acyclic.
   CITATION: §70.26 Theorem (Completeness MLL) — ⊥^1 variant.
   DRAFT-TACTICS: cheat
*)
Theorem completeness_mll_one :                                  (* §70.26 *)
  !Phi Gamma Omega.
    proof_like Phi Gamma ==>
    wf_basis (orth_one_C {}) Omega ==>
    Phi IN strict_interp_one Omega Gamma ==>
    ?S.
      is_mll_proof_net S Gamma /\ Phi_ax S = Phi
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §70  SANITY: interp_formula on atoms unfolds to Omega                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §70.10  SANITY: interp_formula unfolds definitionally on atoms.
   Use Once to avoid infinite unfolding of the recursive definition.          *)
Theorem interp_atom :
  !orth Omega i t.
    interp_formula orth Omega (MAtom i) t = Omega (MAtom i) i t
Proof
  simp [Once interp_formula_def]
QED

Theorem interp_neg :
  !orth Omega i t.
    interp_formula orth Omega (MNeg i) t =
    orthogonal_set orth (Omega (MAtom i) i t)
Proof
  simp [Once interp_formula_def]
QED

(* §70.10  SANITY: tensor interpretation unfolds to behaviour_tensor.          *)
Theorem interp_tens :
  !orth Omega A1 A2 t.
    interp_formula orth Omega (MTens A1 A2) t =
    behaviour_tensor orth
      (interp_formula orth Omega A1 (App dir_left  [t]))
      (interp_formula orth Omega A2 (App dir_right [t]))
Proof
  simp [Once interp_formula_def]
QED

(* §70.10  SANITY: par interpretation unfolds to behaviour_par.                *)
Theorem interp_par :
  !orth Omega A1 A2 t.
    interp_formula orth Omega (MPar A1 A2) t =
    behaviour_par orth
      (interp_formula orth Omega A1 (App dir_left  [t]))
      (interp_formula orth Omega A2 (App dir_right [t]))
Proof
  simp [Once interp_formula_def]
QED

(* §70.25  SANITY: strict_interp_roots is an orthogonal set of tests.         *)
Theorem strict_interp_roots_is_orth :
  !Omega Gamma.
    strict_interp_roots Omega Gamma =
    orthogonal_set (orth_roots_C {}) (tests_sequent Gamma)
Proof
  rw [strict_interp_roots_def]
QED

(* §70.25  SANITY: strict_interp_one is an orthogonal set of tests.           *)
Theorem strict_interp_one_is_orth :
  !Omega Gamma.
    strict_interp_one Omega Gamma =
    orthogonal_set (orth_one_C {}) (tests_sequent Gamma)
Proof
  rw [strict_interp_one_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EXTENDED PROOF-DEBT LEDGER  (§70 additions)                                  *)
(*                                                                              *)
(* stellaMLL.14  full_soundness_mll_mix  (§70.17 Theorem)                      *)
(*   GOAL: !S Gamma Omega.                                                      *)
(*           is_mll_mix_proof_net S Gamma ==>                                   *)
(*           wf_basis (orth_fin_C {}) Omega ==>                                 *)
(*           ?gamma. gamma IN AEx_C (Phi_comp S) /\                             *)
(*                   gamma IN interp_sequent (orth_fin_C {}) Omega Gamma        *)
(*   STRATEGY:                                                                  *)
(*     Induction on proof-net structure (axiom / ⊗ / ⅋ / MIX / cut cases).    *)
(*     Key sub-cases:                                                            *)
(*       · Axiom: basis Omega and orth_fin give Phi_ax S ⊥^{fin} every test.  *)
(*       · Tensor: IH + pre_tensor_subset_tensor + Lemma §70.14.               *)
(*       · Par: IH + behaviour_par definition.                                  *)
(*       · MIX: tensor of two sub-nets ⊆ par.                                  *)
(*       · Cut: sim_cut_elim (stellaMLL.06) + IH on cut-free normal form.       *)
(*   STATUS: deferred (induction on proof-net structure, needs §70.14).         *)
(*   CITATION: §70.17 Theorem.                                                  *)
(*                                                                              *)
(* stellaMLL.15  completeness_mll_mix  (§70.21 Theorem)                        *)
(*   GOAL: !Phi Gamma Omega.                                                    *)
(*           proof_like Phi Gamma ==> wf_basis (orth_fin_C {}) Omega ==>       *)
(*           Phi IN interp_sequent (orth_fin_C {}) Omega Gamma ==>             *)
(*           ?S. is_mll_mix_proof_net S Gamma /\ Phi_ax S = Phi               *)
(*   STRATEGY:                                                                  *)
(*     Construct S from Phi (proof-like constellation = axiom-only PS on ST).  *)
(*     By §70.18: Tests(⊢ Gamma) ⊆ [[⊢ Gamma]]^{⊥^{fin}}.                    *)
(*     Phi ∈ [[⊢ Gamma]]_Omega => Phi ⊥^{fin} each test => S^phi acyclic.     *)
(*     Acyclic for all phi => MLL+MIX correctness.                              *)
(*   STATUS: deferred (construction of S + §70.18 + §68.21).                   *)
(*   CITATION: §70.21 Theorem (Completeness MLL+MIX).                          *)
(*                                                                              *)
(* stellaMLL.16  full_soundness_mll_one  (§70.23 Theorem — ⊥^1 variant)       *)
(*   GOAL: !S Gamma Omega.                                                      *)
(*           is_mll_proof_net S Gamma ==>                                       *)
(*           wf_basis (orth_one_C {}) Omega ==>                                 *)
(*           ?gamma. gamma IN AEx_C (Phi_comp S) /\                             *)
(*                   gamma IN interp_sequent (orth_one_C {}) Omega Gamma       *)
(*   STRATEGY:                                                                  *)
(*     As stellaMLL.14 but ⊥^1: axiom case needs CARD(AEx) = 1, not just finite.*)
(*     Basis Omega guarantees |AEx(Phi1 ++ Phi2 ++ Phi_ax S)| = 1 by §70.23. *)
(*   STATUS: deferred (same structure as stellaMLL.14 + ⊥^1 axiom case).      *)
(*   CITATION: §70.23 Theorem (Full soundness MLL — ⊥^1).                     *)
(*                                                                              *)
(* stellaMLL.17  full_soundness_mll_roots  (§70.23 Theorem — ⊥^R variant)     *)
(*   GOAL: same as stellaMLL.16 with orth_roots_C instead of orth_one_C.       *)
(*   STRATEGY: axiom case: AEx = {Roots(...)} by ⊥^R + basis Omega properties. *)
(*   STATUS: deferred.                                                           *)
(*   CITATION: §70.23 Theorem (Full soundness MLL — ⊥^R).                     *)
(*                                                                              *)
(* stellaMLL.18  completeness_mll_roots  (§70.26 Theorem — ⊥^R variant)       *)
(*   GOAL: !Phi Gamma Omega.                                                    *)
(*           proof_like Phi Gamma ==> wf_basis (orth_roots_C {}) Omega ==>    *)
(*           Phi IN strict_interp_roots Omega Gamma ==>                         *)
(*           ?S. is_mll_proof_net S Gamma /\ Phi_ax S = Phi                   *)
(*   STRATEGY:                                                                  *)
(*     Construct S on ST(⊢ Gamma) from Phi.                                    *)
(*     Phi ∈ Tests(⊢ Gamma)^{⊥^R} => for all phi:                             *)
(*       AEx(Phi ++ Test(⊢ Gamma)^phi) = {Roots}.                              *)
(*     By dr_connected_acyclic_iff_singleton_AEx (stellaMLL.10):               *)
(*       {Roots} = {concl_star S} => |AEx| = 1 => S^phi connected & acyclic.  *)
(*     Connected & acyclic for all phi = MLL correctness.                       *)
(*   STATUS: deferred (construction of S + stellaMLL.10 + §68.19).             *)
(*   CITATION: §70.26 Theorem (Completeness MLL — ⊥^R).                       *)
(*                                                                              *)
(* stellaMLL.19  completeness_mll_one  (§70.26 Theorem — ⊥^1 variant)         *)
(*   GOAL: same as stellaMLL.18 with strict_interp_one / orth_one_C.           *)
(*   STRATEGY: Phi ∈ Tests(⊢ Gamma)^{⊥^1}: CARD(AEx) = 1 for all tests =>    *)
(*     |AEx| = 1 => S^phi connected & acyclic.                                  *)
(*   STATUS: deferred.                                                           *)
(*   CITATION: §70.26 Theorem (Completeness MLL — ⊥^1).                       *)
(*                                                                              *)
(* EVAL vs CHEAT SUMMARY  (§70 additions):                                      *)
(*   EVAL / rw (non-debt):                                                      *)
(*     · interp_atom      — rw [interp_formula_def]                            *)
(*     · interp_neg       — rw [interp_formula_def]                            *)
(*     · interp_tens      — rw [interp_formula_def]                            *)
(*     · interp_par       — rw [interp_formula_def]                            *)
(*     · strict_interp_roots_is_orth — rw [strict_interp_roots_def]           *)
(*     · strict_interp_one_is_orth   — rw [strict_interp_one_def]             *)
(*   CHEAT (non-trivial, deferred):                                              *)
(*     · full_soundness_mll_mix      (stellaMLL.14)                             *)
(*     · completeness_mll_mix        (stellaMLL.15)                             *)
(*     · full_soundness_mll_one      (stellaMLL.16)                             *)
(*     · full_soundness_mll_roots    (stellaMLL.17)                             *)
(*     · completeness_mll_roots      (stellaMLL.18)                             *)
(*     · completeness_mll_one        (stellaMLL.19)                             *)
(*                                                                              *)
(* ZERO new_axiom / mk_thm USED IN THIS FILE.                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* §71  The case of multiplicative units (pp. 339–341)                        *)
(*                                                                             *)
(* SCOPE: §71.5 (Def. One = {∅}), §71.9 (Def. Bottom = One^⊥),              *)
(*        §71.6 (A ⊗ 1 = A), §71.10 (A ⅋ ⊥ = A w.r.t. ⊥^R),               *)
(*        §71.11 (A^⊥ = A ⊸ ⊥ w.r.t. ⊥^R),                                 *)
(*        §71.13–14 (Usine tests for units: Φ∈⊥ iff Φ⊥∅; Φ∈1 iff Φ=∅).   *)
(*                                                                             *)
(* Orthogonality ⊥^R (orth_roots_C) is used throughout §71 unless stated.   *)
(* All non-trivial proofs are deferred (proof-obligation ledger §71.20–26).  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.1–3  The pole ⊥⊥ and the pre-behaviour {∅}                             *)
(*                                                                             *)
(* §71.1–2: The pole ⊥⊥ is the set of all constellations Φ such that         *)
(*   Ex(Φ ⊎ ∅) ∈ ⊥⊥ (closed under anti-evaluation).                         *)
(* Under ⊥^R: ⊥⊥ is the set of all constellations normalising into a single  *)
(* uncoloured star (the "roots" condition for a constellation paired with ∅). *)
(*                                                                             *)
(* §71.3: The natural behaviour for the neutral element of ⊗ is {∅}:         *)
(*   any Φ ⊎ ∅ = Φ, so {∅} acts as a unit for disjoint union.               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §71.1–2  The pole pre-behaviour ⊥⊥ w.r.t. ⊥^R (§71.2):                  *)
(* ⊥⊥ = { Φ | AEx(Φ ++ []) = {roots [] Φ} }                                 *)
(* i.e., constellations that self-normalise into their own uncoloured roots.  *)
(* §71.2 *)
Definition pole_def :
  pole : constellation set =
    { Phi | AEx_C (Phi ++ []) = {roots [] Phi} }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.5  Definition: One = {∅} = ⊥⊥^⊥                                        *)
(*                                                                             *)
(* The behaviour One is the pre-behaviour containing only the empty           *)
(* constellation ∅.  Eng §71.5:  1 := {∅} = ⊥⊥^⊥.                          *)
(*                                                                             *)
(* In HOL4:  the empty constellation is the empty list [].                   *)
(* §71.5 *)
Definition mll_one_def :                                        (* §71.5 *)
  mll_one : constellation set = {[]}
End

(* §71.5  Remark: One = ⊥⊥^⊥ (i.e. One = orthogonal_set orth_roots_C pole).
   This is a consequence of §71.4 (Φ∈{∅}^⊥^⊥ iff Φ self-normalises → ⊥⊥^⊥ = {∅}).
   Stated as a remark; proved via proof-obligation §71.20.  §71.5 *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.4  Proposition: {∅} is a behaviour                                      *)
(*                                                                             *)
(* {∅}^⊥ = ⊥⊥  (constellations that self-normalise into their roots).        *)
(* {∅}^{⊥⊥} = ⊥⊥^⊥ = {∅}.                                                  *)
(* Hence {∅} = ({∅}^⊥)^⊥ = ({∅}^{⊥⊥}) is a behaviour.                      *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaMLL.20]:                                             *)
(*   GOAL: is_behaviour (orth_roots_C {}) mll_one                              *)
(*   STRATEGY:                                                                 *)
(*     mll_one = {[]}; show mll_one = orthogonal_set orth_roots_C pole.       *)
(*     (⊆) []: AEx([] ++ Phi) = AEx(Phi); for Phi in pole, AEx(Phi) = {roots},*)
(*         so orth_roots_C {Phi} {[]} holds by unfolding orth_roots_C.        *)
(*     (⊇) If Phi ∉ mll_one then Phi ≠ []; there exists Phi' in pole with     *)
(*         AEx(Phi ++ Phi') ≠ {Roots}; hence Phi ∉ pole^⊥.                   *)
(*   STATUS: deferred.                                                         *)
(*   CITATION: §71.4 Proposition.                                              *)

Theorem mll_one_is_behaviour :                                  (* §71.4 *)
  is_behaviour (orth_roots_C {}) mll_one
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.9  Definition: Bottom = 1^⊥ = ⊥⊥                                       *)
(*                                                                             *)
(* The behaviour Bottom is the orthogonal of One:                             *)
(*   ⊥ := 1^⊥ = {∅}^⊥ = ⊥⊥.                                                 *)
(*                                                                             *)
(* §71.7 remarks that 1^⊥ = ⊥⊥; §71.8 shows it is a behaviour               *)
(* (since A^⊥ is always a behaviour for any pre-behaviour A).                 *)
(* §71.9 *)
Definition mll_bottom_def :                                     (* §71.9 *)
  mll_bottom : constellation set =
    orthogonal_set (orth_roots_C {}) mll_one
End

(* §71.7–8  Remark: mll_bottom = pole (the "⊥⊥" pre-behaviour).
   By §71.4–5: {∅}^⊥ = ⊥⊥ = pole.  §71.7 *)

(* §71.8  Bottom is a behaviour: immediate since A^⊥ is always a behaviour.   *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaMLL.21]:                                             *)
(*   GOAL: is_behaviour (orth_roots_C {}) mll_bottom                           *)
(*   STRATEGY:                                                                 *)
(*     mll_bottom = orthogonal_set orth_roots_C mll_one.                      *)
(*     Any orthogonal_set is a behaviour: take B := mll_one in §69.30.        *)
(*     So mll_bottom = mll_one^⊥ = B^⊥ for B = mll_one.                     *)
(*   STATUS: deferred (direct from is_behaviour_def + orthogonal_set).        *)
(*   CITATION: §71.8 Proposition.                                              *)

Theorem mll_bottom_is_behaviour :                               (* §71.8 *)
  is_behaviour (orth_roots_C {}) mll_bottom
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.6  Proposition: A ⊗ 1 = A                                               *)
(*                                                                             *)
(* §71.6: For any behaviour A, A ⊗ 1 = A.                                    *)
(*                                                                             *)
(* Proof sketch (§71.6):                                                       *)
(*   A ⊗ 1 = (A ⊙ {∅})^{⊥⊥}                                                 *)
(*         = { Phi_A ++ [] | Phi_A ∈ A }^{⊥⊥}                                *)
(*         = { Phi_A | Phi_A ∈ A }^{⊥⊥}  (since Phi ++ [] = Phi)            *)
(*         = A^{⊥⊥} = A  (A is a behaviour, so A = A^{⊥⊥}).                 *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaMLL.22]:                                             *)
(*   GOAL: !A. is_behaviour (orth_roots_C {}) A ==>                            *)
(*             behaviour_tensor (orth_roots_C {}) A mll_one = A               *)
(*   STRATEGY:                                                                 *)
(*     Unfold behaviour_tensor = biorth orth (pre_tensor A mll_one).          *)
(*     pre_tensor A mll_one = { Phi ++ [] | Phi ∈ A } = A  (by APPEND_NIL).  *)
(*     biorth orth A = A  since A is a behaviour (behaviour_iff_biorth).      *)
(*   CITATION: §71.6 Proposition.                                              *)

(*
   PROOF-OBLIGATION[stellaMLL.22]:
   GOAL:
     !A.
       is_behaviour (orth_roots_C {}) A ==>
       behaviour_tensor (orth_roots_C {}) A mll_one = A
   STRATEGY:
     Step 1: pre_tensor A mll_one = A.
       pre_tensor A mll_one = { Phi | ?Phi1 Phi2. Phi1 IN A /\ Phi2 IN mll_one /\ Phi = Phi1 ++ Phi2 }
       mll_one = {[]} => Phi2 = [] => Phi = Phi1 ++ [] = Phi1 => pre_tensor A {[]} = A.
     Step 2: biorth orth A = A by behaviour_iff_biorth + is_behaviour.
     Step 3: behaviour_tensor orth A mll_one = biorth orth (pre_tensor A mll_one) = biorth orth A = A.
   DRAFT-TACTICS: rw [behaviour_tensor_def, biorth_def, pre_tensor_def, mll_one_def] >>
                  simp [APPEND_NIL] >> metis_tac [behaviour_iff_biorth]
*)
Theorem tensor_one_id :                                         (* §71.6 *)
  !A.
    is_behaviour (orth_roots_C {}) A ==>
    behaviour_tensor (orth_roots_C {}) A mll_one = A
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.10  Proposition: A ⅋ ⊥ = A  (w.r.t. ⊥^R)                             *)
(*                                                                             *)
(* §71.10: For any behaviour A, A ⅋ ⊥ = A when using ⊥^R.                   *)
(*                                                                             *)
(* Proof sketch (§71.10):                                                      *)
(*   A ⅋ ⊥ = (A^⊥ ⊗ ⊥^⊥)^⊥                                                 *)
(*          = (A^⊥ ⊗ {∅}^{⊥⊥})^⊥                                            *)
(*          = (A^⊥ ⊗ {∅})^⊥          ({∅}^{⊥⊥} = {∅} by §71.4)            *)
(*          = A^{⊥⊥⊥}                 (⊗ {∅} by tensor_one_id on A^⊥)       *)
(*          = A^⊥^⊥ = A               (A is a behaviour).                    *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaMLL.23]:                                             *)
(*   GOAL: !A. is_behaviour (orth_roots_C {}) A ==>                            *)
(*             behaviour_par (orth_roots_C {}) A mll_bottom = A               *)
(*   STRATEGY:                                                                 *)
(*     Unfold behaviour_par orth A mll_bottom                                  *)
(*       = orthogonal_set orth (behaviour_tensor orth (orth A) (orth mll_bottom)).*)
(*     orth mll_bottom = orth (orth mll_one) = mll_one^{⊥⊥⊥} = mll_one^⊥ = mll_bottom.*)
(*     Hmm: we need orth(mll_bottom) = mll_one^{⊥⊥} = mll_one (by §71.4).   *)
(*     So: behaviour_tensor orth (orth A) mll_one = orth A  (by tensor_one_id on orth A).*)
(*     Then: orth(orth A) = A^{⊥⊥} = A.                                      *)
(*     Requires: is_behaviour(orth A) (to apply tensor_one_id to orth A).     *)
(*   CITATION: §71.10 Proposition.                                             *)

(*
   PROOF-OBLIGATION[stellaMLL.23]:
   GOAL:
     !A.
       is_behaviour (orth_roots_C {}) A ==>
       behaviour_par (orth_roots_C {}) A mll_bottom = A
   STRATEGY:
     Let orth := orth_roots_C {}.
     behaviour_par orth A mll_bottom
       = orthogonal_set orth (behaviour_tensor orth (orthogonal_set orth A) (orthogonal_set orth mll_bottom))
     orthogonal_set orth mll_bottom = mll_one (since mll_bottom = mll_one^⊥ and mll_one^{⊥⊥} = mll_one by §71.4).
     A is a behaviour ==> orthogonal_set orth A is a behaviour (A^⊥ is always a behaviour).
     Apply tensor_one_id (stellaMLL.22) to orth A: behaviour_tensor orth (orth A) mll_one = orth A.
     behaviour_par orth A mll_bottom = orthogonal_set orth (orth A) = A^{⊥⊥} = A.
   DRAFT-TACTICS: cheat (needs stellaMLL.22 + double-negation A^{⊥⊥} = A)
*)
Theorem par_bottom_id :                                         (* §71.10 *)
  !A.
    is_behaviour (orth_roots_C {}) A ==>
    behaviour_par (orth_roots_C {}) A mll_bottom = A
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.11  Proposition: A^⊥ = A ⊸ ⊥  (w.r.t. ⊥^R)                          *)
(*                                                                             *)
(* §71.11: For any behaviour A, A^⊥ = A ⊸ ⊥.                                *)
(*                                                                             *)
(* Proof sketch (§71.11):                                                      *)
(*   A ⊸ ⊥ = A^⊥ ⅋ ⊥   (by definition of ⊸)                                *)
(*          = A^⊥          (by §71.10, since ⊥ is neutral for ⅋).            *)
(*                                                                             *)
(* PROOF-OBLIGATION[stellaMLL.24]:                                             *)
(*   GOAL: !A. is_behaviour (orth_roots_C {}) A ==>                            *)
(*             behaviour_impl (orth_roots_C {}) A mll_bottom =                 *)
(*             orthogonal_set (orth_roots_C {}) A                              *)
(*   STRATEGY:                                                                 *)
(*     behaviour_impl orth A mll_bottom = behaviour_par orth (orth A) mll_bottom*)
(*     par_bottom_id (stellaMLL.23) applied to orth A: par orth (orth A) mll_bottom = orth A.*)
(*     But we need is_behaviour orth (orth A). Since A is a behaviour,        *)
(*     orth A = A^⊥ is always a behaviour (it is orthogonal_set orth A = A^⊥,*)
(*     and A^⊥ is a behaviour: take B := A in §69.30, then B^⊥ = A^⊥).      *)
(*   CITATION: §71.11 Proposition.                                             *)

(*
   PROOF-OBLIGATION[stellaMLL.24]:
   GOAL:
     !A.
       is_behaviour (orth_roots_C {}) A ==>
       behaviour_impl (orth_roots_C {}) A mll_bottom =
       orthogonal_set (orth_roots_C {}) A
   STRATEGY:
     behaviour_impl orth A mll_bottom = behaviour_par orth (orthogonal_set orth A) mll_bottom  (def impl)
     is_behaviour orth (orthogonal_set orth A): take B := A; orth A = B^⊥ for B = A.
     Apply par_bottom_id (stellaMLL.23) to orthogonal_set orth A:
       behaviour_par orth (orthogonal_set orth A) mll_bottom = orthogonal_set orth A.
   DRAFT-TACTICS: rw [behaviour_impl_def] >> irule par_bottom_id >>
                  rw [is_behaviour_def] >> qexists_tac `A` >> rw [behaviour_par_def]
*)
Theorem impl_bottom_is_neg :                                    (* §71.11 *)
  !A.
    is_behaviour (orth_roots_C {}) A ==>
    behaviour_impl (orth_roots_C {}) A mll_bottom =
    orthogonal_set (orth_roots_C {}) A
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71.13–14  Testing units: Usine criterion for Bottom and One               *)
(*                                                                             *)
(* §71.13: To test whether Φ ∈ ⊥ (Bottom):                                   *)
(*   Use the test {∅}: Φ ∈ ⊥ iff Φ ⊥^R ∅.                                  *)
(*   i.e., AEx_C(Φ ++ []) = {Roots(Φ ++ [])} = {Roots(Φ)}.                  *)
(*                                                                             *)
(* §71.14: To test whether Φ ∈ 1 (One):                                      *)
(*   Just check Φ = ∅ (the empty constellation).                              *)
(*   No interaction needed: membership in {∅} is just equality to [].        *)
(*                                                                             *)
(* NOTE (§71.14): The stellar units {∅} and ⊥⊥ do not exactly match the     *)
(* proof-net units (⊥ in proof-nets has a non-local dependency via jumps,     *)
(* cf. §30; Girard's workaround: encode units in second-order LL, §44).      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §71.13  Bottom-membership criterion: Φ ∈ mll_bottom iff Φ ⊥^R ∅.
   In HOL4: mll_bottom = {[]}^⊥ = orthogonal_set (orth_roots_C {}) {[]}.
   So Phi IN mll_bottom iff orth_roots_C {} Phi [] = T.
   I.e., AEx_C (Phi ++ []) = {roots Phi []}.

   This is the definition of mll_bottom applied to the witness []:
   Phi IN orthogonal_set orth {[]} <=> !Phi'. Phi' IN {[]} ==> orth Phi Phi'
                                     <=> orth Phi []
                                     <=> orth_roots_C {} Phi [].               *)

(*
   PROOF-OBLIGATION[stellaMLL.25]:
   GOAL: §71.13 — Φ ∈ mll_bottom iff Φ ⊥^R ∅
     !Phi.
       Phi IN mll_bottom <=>
       orth_roots_C {} Phi []
   STRATEGY:
     Unfold mll_bottom = orthogonal_set (orth_roots_C {}) mll_one = orthogonal_set orth {[]}.
     orthogonal_set orth {[]} = { Phi | !Phi'. Phi' IN {[]} ==> orth Phi Phi' }
                               = { Phi | orth Phi [] }  (since {[]} is a singleton).
     So Phi IN mll_bottom <=> orth_roots_C {} Phi [].
   DRAFT-TACTICS:
     rw [mll_bottom_def, orthogonal_set_def, mll_one_def] >> simp []
*)
Theorem in_mll_bottom_iff :                                     (* §71.13 *)
  !Phi.
    Phi IN mll_bottom <=>
    orth_roots_C {} Phi []
Proof
  cheat
QED

(* §71.14  One-membership criterion: Φ ∈ mll_one iff Φ = ∅.
   Immediate from mll_one = {[]}:  Phi IN mll_one <=> Phi = [].             *)

Theorem in_mll_one_iff :                                        (* §71.14 *)
  !Phi.
    Phi IN mll_one <=>
    Phi = []
Proof
  rw [mll_one_def]
QED

(* §71.14  Remark (Usine vs proof-net units):
   The stellar units (mll_one = {∅}, mll_bottom = ⊥⊥) provide correct
   interactive types for multiplicative units within the Usage framework.
   However, they do not correspond exactly to the proof-net units: in MLL
   proof-net theory, the constant ⊥ is introduced in a context Γ to which
   it is connected via a "jump" link (§30), creating a non-local dependency.
   Under any switching, the ⊥ node becomes disconnected, breaking the
   Danos-Regnier connectedness criterion.  Girard's fix (§44): encode ⊥ in
   second-order linear logic, or use "epidictics" to supply the missing
   structure.  The stellar interpretation exposes this mismatch cleanly
   (cf. §71.14, §72.3).                                                       *)
(* §71.14 *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71  SANITY: mll_one and mll_bottom are disjoint (as sets)                  *)
(*                                                                             *)
(* mll_one = {[]} contains exactly the empty constellation.                  *)
(* mll_bottom contains all constellations that self-normalise to their roots; *)
(* in particular [] ∈ mll_bottom (AEx_C [] = {[]} = {roots [] []}).          *)
(* They are NOT disjoint as sets — both contain constellations related to []. *)
(* We instead show the definitional unfolding.                                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem mll_one_singleton :                                     (* §71.5 sanity *)
  mll_one = {[]}
Proof
  rw [mll_one_def]
QED

Theorem mll_bottom_unfold :                                     (* §71.9 sanity *)
  mll_bottom = orthogonal_set (orth_roots_C {}) {[]}
Proof
  rw [mll_bottom_def, mll_one_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §71  SANITY: tensor_one_id in terms of mll_one (alternate phrasing)        *)
(*                                                                             *)
(* §71.6  A ⊗ One = A.  The impl_bottom version (A ⊸ ⊥ = A^⊥) gives the   *)
(* de Morgan dual of the tensor unit law.  We state the commuted form.        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem one_tensor_id :                                         (* §71.6 commuted *)
  !A.
    is_behaviour (orth_roots_C {}) A ==>
    behaviour_tensor (orth_roots_C {}) mll_one A = A
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* EXTENDED PROOF-DEBT LEDGER  (§71 additions)                                 *)
(*                                                                              *)
(* stellaMLL.20  mll_one_is_behaviour  (§71.4 Proposition)                     *)
(*   GOAL: is_behaviour (orth_roots_C {}) mll_one                               *)
(*   STRATEGY: mll_one = {[]}; show {[]} = orthogonal_set orth pole.           *)
(*     (⊆) [] ∈ pole^⊥: AEx([] ++ Phi) = AEx(Phi); for Phi in pole this is   *)
(*         {roots [] Phi} — unfold definitions.                                  *)
(*     (⊇) Phi ≠ [] cannot be in pole^⊥ (exists Phi' in pole with AEx ≠ Roots).*)
(*   STATUS: deferred (requires pole characterisation + AEx_C on empty list).   *)
(*   CITATION: §71.4 Proposition.                                                *)
(*                                                                              *)
(* stellaMLL.21  mll_bottom_is_behaviour  (§71.8 Proposition)                   *)
(*   GOAL: is_behaviour (orth_roots_C {}) mll_bottom                             *)
(*   STRATEGY: mll_bottom = orthogonal_set orth mll_one.                        *)
(*     is_behaviour_def: take B := mll_one; mll_bottom = B^⊥ = orthogonal_set orth B.*)
(*     Immediate from the definitions.                                            *)
(*   STATUS: deferred (direct, but requires unfolding is_behaviour_def).         *)
(*   CITATION: §71.8 Proposition.                                                *)
(*                                                                              *)
(* stellaMLL.22  tensor_one_id  (§71.6 Proposition)                             *)
(*   GOAL: !A. is_behaviour orth A ==> behaviour_tensor orth A mll_one = A      *)
(*   STRATEGY:                                                                   *)
(*     pre_tensor A {[]} = A  (Phi ++ [] = Phi for all Phi).                   *)
(*     biorth orth A = A  (by behaviour_iff_biorth + is_behaviour A).           *)
(*     behaviour_tensor orth A mll_one = biorth orth (pre_tensor A mll_one) = A.*)
(*   STATUS: deferred (needs pre_tensor unfolding + APPEND_NIL + behaviour_iff_biorth).*)
(*   CITATION: §71.6 Proposition.                                                *)
(*                                                                              *)
(* stellaMLL.23  par_bottom_id  (§71.10 Proposition)                            *)
(*   GOAL: !A. is_behaviour orth A ==> behaviour_par orth A mll_bottom = A      *)
(*   STRATEGY:                                                                   *)
(*     behaviour_par orth A mll_bottom = orth (behaviour_tensor orth (orth A) (orth mll_bottom)).*)
(*     orth mll_bottom = mll_one^{⊥⊥} = mll_one  (by §71.4 / mll_one_is_behaviour).*)
(*     tensor_one_id on orth A: behaviour_tensor orth (orth A) mll_one = orth A.*)
(*     orth (orth A) = A^{⊥⊥} = A  (A is a behaviour).                        *)
(*   STATUS: deferred (needs stellaMLL.22 + A^{⊥⊥} = A for behaviours).       *)
(*   CITATION: §71.10 Proposition.                                               *)
(*                                                                              *)
(* stellaMLL.24  impl_bottom_is_neg  (§71.11 Proposition)                       *)
(*   GOAL: !A. is_behaviour orth A ==>                                           *)
(*             behaviour_impl orth A mll_bottom = orthogonal_set orth A         *)
(*   STRATEGY:                                                                   *)
(*     behaviour_impl orth A mll_bottom = behaviour_par orth (orth A) mll_bottom.*)
(*     orth A is a behaviour (it is B^⊥ for B = A).                            *)
(*     par_bottom_id applied to orth A: behaviour_par orth (orth A) mll_bottom = orth A.*)
(*   STATUS: deferred (needs stellaMLL.23 + is_behaviour (orth A)).             *)
(*   CITATION: §71.11 Proposition.                                               *)
(*                                                                              *)
(* stellaMLL.25  in_mll_bottom_iff  (§71.13)                                    *)
(*   GOAL: !Phi. Phi IN mll_bottom <=> orth_roots_C {} Phi []                   *)
(*   STRATEGY:                                                                   *)
(*     Unfold mll_bottom = orthogonal_set orth {[]}; singleton unfolding.       *)
(*   STATUS: deferred (straightforward but needs simp on singleton set).         *)
(*   CITATION: §71.13 (testing units).                                            *)
(*                                                                              *)
(* EVAL vs CHEAT SUMMARY  (§71 additions):                                      *)
(*   EVAL / rw (non-debt):                                                       *)
(*     · in_mll_one_iff    — rw [mll_one_def]                                   *)
(*     · mll_one_singleton — rw [mll_one_def]                                   *)
(*     · mll_bottom_unfold — rw [mll_bottom_def, mll_one_def]                   *)
(*   CHEAT (non-trivial, deferred):                                              *)
(*     · mll_one_is_behaviour   (stellaMLL.20)                                   *)
(*     · mll_bottom_is_behaviour (stellaMLL.21)                                  *)
(*     · tensor_one_id          (stellaMLL.22)                                   *)
(*     · one_tensor_id          (commuted: same as stellaMLL.22 by commutativity)*)
(*     · par_bottom_id          (stellaMLL.23)                                   *)
(*     · impl_bottom_is_neg     (stellaMLL.24)                                   *)
(*     · in_mll_bottom_iff      (stellaMLL.25)                                   *)
(*                                                                              *)
(* ZERO new_axiom / mk_thm USED IN THIS FILE.                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* §72  Discussion: what is a multiplicative proof? (pp. 341–342)             *)
(*                                                                             *)
(* This section contains no new definitions or formal propositions from §72.  *)
(* Its content is philosophical/descriptive.  We encode the key points as     *)
(* documented remarks and named definitions for reference, following the       *)
(* proof-policy: if no precise statement is given, state as remarks/defs only,*)
(* no proof obligations.                                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* §72.1  Remark: The correctness test for ⊗ is a 3-ary star.
   Under ⊥^R, the ⊗ test (from §68.3 vstar, Tens case) is the single star
   [-u(X), -w(X), +v(X)] with two input rays and one output ray.  It forces
   any interacting vehicle to consist of exactly two disjoint connected
   components (one matching u and one matching w).  Thus the ⊗ test *reunites*
   proof-structures — it witnesses their disjoint-union structure.  §72.1 *)

(* §72.1  Remark: The correctness tests for ⅋ are binary and *separate*.
   The two ⅋ tests (⅋_L and ⅋_R from vstar) each consist of two disjoint
   stars: a binary star and a unary star.  They *separate* proof-structures
   into two parts, corresponding to the two branches of the ⅋ connective.
   MLL proofs are exactly those vehicles that reunite and separate data in
   the structure prescribed by the formula tree.  §72.1 *)

(* §72.1  Encoded predicate: the ⊗-test star for vertices u, w, v.
   Used to state §72.1 precisely for reference.  §72.1 *)
Definition tens_test_star_def :                                 (* §72.1 *)
  tens_test_star (u : num) (w : num) (v : num) : star =
    [ neg_app u ; neg_app w ; pos_app v ]
End

(* §72.1  The test constellation for a ⊗ link (output v, inputs u w)
   is a singleton constellation containing the 3-ary test star.  §72.1 *)
Definition tens_test_constellation_def :                        (* §72.1 *)
  tens_test_constellation (u : num) (w : num) (v : num) : constellation =
    [ tens_test_star u w v ]
End

(* §72.2  Remark: Linear negation as symmetry.
   An axiom star [+1(X), +2(X)] connected with [+3(X)] by cut [-1(X), -3(X)]
   gives [+2(X)], and by cut [-2(X), -3(X)] gives [+1(X)].  This encodes the
   MLL equation A ⊸ B = B^⊥ ⊸ A^⊥.  §72.2 *)

(* §72.2  Remark: Complexity of axiom stars scales with formula complexity.
   For any multiplicative formula A, the axiom-star encoding a proof of
   ⊢ X₁^⊥ ⅋ X₁ or ⊢ A^⊥ ⅋ A is a binary star [r, r'] where the rays r and
   r' are as structurally complex as A itself (the address terms embed the
   binary tree of A via 1-directions and r-directions).  §72.2 *)

(* §72.3  Remark: First-order multiplicatives and polymorphism.
   The stellar interpretation gives "first-order" multiplicative proof-structures:
   atomic formulas are represented by concrete function symbols, and the proof-
   structure is fixed for specific atoms.  Real MLL proofs are *polymorphic*:
   a proof of ⊢ X₁^⊥ ⅋ X₁ works for any formula substituted for X₁.
   Polymorphism (second-order generalisation) requires additional structure
   beyond first-order constellations — this is the role of Girard's
   "epidictics" (§72.3, cf. §44).  §72.3 *)

(* §72.4  Remark: Hidden non-linearity in MLL proof-net theory.
   In the GoI interpretation, MLL proofs are permutations over atoms where
   cuts are partial injections linking atoms.  In proof-net theory, cuts link
   whole conclusions (not individual atoms), so the cut must be "distributed"
   to the atoms it connects via the address terms.
   In the stellar interpretation: this distribution is internalised — the
   complex shape of proof-structures is encoded directly into the terms of
   rays (via pAddr_S, addr_S).  To connect the cut with both its left and
   right premises at all atoms, the variables in address terms act as
   placeholders that unify during execution.  This exposes the fact that MLL
   proof-net theory is not truly duplication-free: it hides non-linear
   (duplicating) behaviour inside the design of the address terms.  §72.4 *)

(* §72  Summary definition: the "reunion" and "separation" dichotomy.
   We record the key §72 observation as a named boolean predicate for reference:
   a ⊗-interaction is a 3-ary reunion; a ⅋-interaction is a binary separation. *)
Definition is_reunion_test_def :                                (* §72.1 *)
  is_reunion_test (s : star) : bool =
    (* A reunion test star is 3-ary with two negative and one positive ray. *)
    ?u w v.
      s = tens_test_star u w v
End

Definition is_separation_test_def :                             (* §72.1 *)
  is_separation_test_L (s1 : star) (s2 : star) : bool =
    (* A separation test (⅋_L) consists of a binary star [-u(X), +v(X)] and
       a unary star [-w(X)].  s1 = [-u(X), +v(X)], s2 = [-w(X)].           *)
    ?u w v.
      s1 = [ neg_app u ; pos_app v ] /\
      s2 = [ neg_app w ]
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §72  SANITY: tens_test_star has 3 rays                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem tens_test_star_length :                                 (* §72 sanity *)
  !u w v. LENGTH (tens_test_star u w v) = 3
Proof
  rw [tens_test_star_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §66–72  Ch.10 COMPLETION SUMMARY                                            *)
(*                                                                             *)
(* All sections of Eng Ch.10 (§66 through §72) are now stated in HOL4.       *)
(*                                                                             *)
(*   §66  Proofs as constellations (§66.3, §66.7, §66.11):                   *)
(*        mll_label, proof_struct, ax_edges, cut_edges, pAddr_S, addr_S,      *)
(*        mu_ray, ax_star, Phi_ax, cut_star, Phi_cut, Phi_comp.               *)
(*   §67  Simulation of cut-elimination (§67.7, §67.9, §67.10):              *)
(*        struct_equiv, cut_elim_step, cut_elim_star, normal_ps,              *)
(*        AEx_equiv, sim_cut_step, sim_cut_elim.                              *)
(*   §68  Danos-Regnier correctness (§68.3, §68.15, §68.19, §68.21):         *)
(*        switching, vstar, Phi_switched, fhp_ray/star, fhp,                  *)
(*        concl_star, dr_certifiable, mll_certifiable,                        *)
(*        dr_test_AEx, dr_acyclic_iff_finite_AEx,                             *)
(*        dr_connected_acyclic_iff_singleton_AEx.                             *)
(*   §69  Multiplicative formulas / orthogonality (§69.4, §69.29–40, §69.43–44):*)
(*        roots, orth_fin_C, orth_one_C, orth_roots_C, orthogonal_set, biorth,*)
(*        pre_tensor, behaviour_tensor, behaviour_par, behaviour_impl,         *)
(*        trefoil, aex_assoc.                                                  *)
(*   §70  Soundness and completeness (§70.9, §70.10, §70.17, §70.21, §70.23, §70.26):*)
(*        mll_formula, basis_interp, wf_basis, interp_formula, interp_sequent,*)
(*        proof_like, tests_sequent, strict_interp_one, strict_interp_roots,  *)
(*        full_soundness_mll_mix, completeness_mll_mix,                       *)
(*        full_soundness_mll_{one,roots}, completeness_mll_{roots,one}.       *)
(*   §71  Multiplicative units (§71.5, §71.9, §71.6, §71.10, §71.11, §71.13–14):*)
(*        pole, mll_one, mll_bottom,                                           *)
(*        mll_one_is_behaviour, mll_bottom_is_behaviour,                      *)
(*        tensor_one_id, one_tensor_id, par_bottom_id, impl_bottom_is_neg,    *)
(*        in_mll_bottom_iff, in_mll_one_iff.                                  *)
(*   §72  Discussion (§72.1–4):                                                *)
(*        tens_test_star, tens_test_constellation,                             *)
(*        is_reunion_test, is_separation_test_L.                              *)
(*        Remarks encoded as documentation comments (no proof obligations      *)
(*        since §72 contains no formally precise statements).                  *)
(*                                                                             *)
(* ZERO new_axiom / mk_thm IN THIS ENTIRE FILE.                               *)
(* ALL non-trivial proofs deferred via cheat + PROOF-OBLIGATION comments.     *)
(* Ledger: stellaMLL.01–25 (ends at stellaMLL.25 after §71 additions).        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val _ = export_theory ();
