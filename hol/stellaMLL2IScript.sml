(* stellaMLL2IScript.sml
   MLL with Intuitionistic Implication (MLL2I) proof-structures and
   cut-elimination simulation — Eng §73–74.

   ══════════════════════════════════════════════════════════════════════════════
   SCOPE
   ──────────────────────────────────────────────────────────────────────────────
   BOUNDED to Eng Ch.11 §73–74 only.
   §75–76 are NOT attempted.

   REUSED from existing stella theories:
     · stellaTermTheory      — term, Var, App, vars_t, subst_apply
     · stellaPolarisedTheory — polarity, encode_psym, decode_psym, uterm_t
     · stellaMatchTheory     — matchable
     · stellaDiagramTheory   — constellation, ray, star, dep_graph,
                               all_colours, IdRays, stars_dep
     · stellaExecutionTheory — AEx_C (abstract execution §49.42)
     · stellaMLLTheory       — struct_equiv, Phi_ax (pattern reuse §66),
                               cut_elim_star, normal_ps

   FRESH (this file):
     · mll2i_pre_formula     — MLL2I pre-formulas §73.3
     · mll2i_formula         — MLL2I formulas (pre + underlined) §73.4
     · mll2i_edge_label      — hyperedge labels {⊗,⅋,ax,cut,⋊,⊛,w,d,c} §73.9
     · mll2i_ps              — MLL2I proof-structure record (V,E,in,out,ℓ_E,dep) §73.9
     · ax_edges_2i / cut_edges_2i  — sub-edge-sets §73.9
     · exp_box               — exponential box function §73.10
     · mll2i_cut_elim_step   — cut-elimination step (3 cases: w/d/c) §73.12
     · mll2i_cut_elim_star   — R ↝* S (reflexive-transitive) §73.12
     · mll2i_normal          — normal form (no cuts) §73.12
     · bullet_sym            — binary function symbol • §74.2
     · wh_sym / d_sym / c_sym — constants w,d,c ∈ F §74.2
     · box_var               — box variables Y_i §74.2
     · pAddr_2I              — path address extended for MLL2I §74.5
     · addr_2I               — independent/dependent address §74.5
     · black_hole_star       — v★ black-hole weakening §74.7
     · weak_set              — Weak(S) §74.8
     · Phi_ax_2I             — vehicle Φ^ax_S §74.9
     · Phi_cut_2I            — cut constellation Φ^cut_S §74.9
     · Phi_comp_2I           — computational content Φ^comp_S §74.9
     · sim_mll2i_cut_elim    — Theorem §74.11 (stated+cheat)

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
open stellaMLLTheory;

val _ = new_theory "stellaMLL2I";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.3  MLL2I pre-formulas                                                    *)
(*                                                                              *)
(* Pre-formulas: C, D ::= X_i | X_i^⊥ | C⊗D | C⅋D | C⊛D | C⋊D  (i ∈ ℕ)   *)
(*                                                                              *)
(* · X_i    — positive atom (index i)                                          *)
(* · NegAt i — dual atom X_i^⊥                                                *)
(* · Tens2I / Par2I — multiplicative tensor and par (same as MLL)             *)
(* · ETens / EPar   — exponential connectives ⊛ (!A ⊗ B) and ⋊ (?A ⅋ B)     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §73.3 *)
  mll2i_pre_formula =
      PosAt2I num          (* X_i  *)
    | NegAt2I num          (* X_i^⊥ *)
    | Tens2I mll2i_pre_formula mll2i_pre_formula   (* C ⊗ D *)
    | Par2I  mll2i_pre_formula mll2i_pre_formula   (* C ⅋ D *)
    | ETens  mll2i_pre_formula mll2i_pre_formula   (* C ⊛ D = !C ⊗ D *)
    | EPar   mll2i_pre_formula mll2i_pre_formula   (* C ⋊ D = ?C ⅋ D *)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.4  MLL2I formulas                                                        *)
(*                                                                              *)
(* A ::= C | C̲  where C̲ (underlined) denotes ?C.                              *)
(* Underlined formulas appear only as top-level sequent conclusions.           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §73.4 *)
  mll2i_formula =
      Plain mll2i_pre_formula    (* C  (a pre-formula, used linearly)         *)
    | Under mll2i_pre_formula    (* C̲ = ?C  (underlined, exponential)         *)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.9  MLL2I hyperedge labels                                                *)
(*                                                                              *)
(* ℓ_E : E → {⊗, ⅋, ax, cut, ⋊, ⊛, w, d, c}                                *)
(*                                                                              *)
(* · Ax2I   — axiom link                                                        *)
(* · Cut2I  — cut link                                                          *)
(* · Tens2IL — ⊗ tensor (multiplicative, same as MLL Tens)                    *)
(* · Par2IL  — ⅋ par (multiplicative, same as MLL Par)                         *)
(* · EPar2I  — ⋊ left-exponential par  (= ?A ⅋ B)                             *)
(* · ETens2I — ⊛ left-exponential tensor (= !A ⊗ B)                           *)
(* · W2I    — weakening (nullary)                                               *)
(* · D2I    — dereliction (unary)                                               *)
(* · C2I    — contraction (binary)                                              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §73.9 *)
  mll2i_label =
      Ax2I                 (* ax  *)
    | Cut2I                (* cut *)
    | Tens2IL              (* ⊗  (multiplicative tensor link) *)
    | Par2IL               (* ⅋  (multiplicative par link) *)
    | EPar2I               (* ⋊  (left-exponential par) *)
    | ETens2I              (* ⊛  (left-exponential tensor) *)
    | W2I                  (* w  (weakening,   nullary) *)
    | D2I                  (* d  (dereliction,  unary) *)
    | C2I                  (* c  (contraction,  binary) *)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.9  MLL2I proof-structure record                                          *)
(*                                                                              *)
(* S = (V, E, in, out, ℓ_E, dep)  where:                                      *)
(*   vertices : num set         — vertex set V^S                               *)
(*   edges    : num set         — hyperedge set E^S                            *)
(*   in_2i    : num → (num#num) — ordered input vertices (left, right)        *)
(*   out_2i   : num → num       — output (conclusion) vertex                   *)
(*   lbl_2i   : num → mll2i_label  — labelling ℓ_E                            *)
(*   dep      : num → num set   — dependency relation dep : V → 𝒫(V)          *)
(*              dep(v) = set of vertices that v (a left premise of ⊛) depends on *)
(*   concl_2i : num set         — set of conclusion vertices                   *)
(*                                                                              *)
(* For W2I (weakening), in_2i(e) = (0, 0) by convention (nullary: no inputs). *)
(* For D2I, only FST(in_2i(e)) is the unique input vertex.                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:                                               (* §73.9 *)
  mll2i_ps = <|
    vertices  : num set ;
    edges     : num set ;
    in_2i     : num -> (num # num) ;
    out_2i    : num -> num ;
    lbl_2i    : num -> mll2i_label ;
    dep       : num -> num set ;
    concl_2i  : num set
  |>
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.9  Sub-edge-sets by label                                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition ax_edges_2i_def :                            (* §73.9 *)
  ax_edges_2i (S : mll2i_ps) : num set =
    { e | e IN S.edges /\ S.lbl_2i e = Ax2I }
End

Definition cut_edges_2i_def :                           (* §73.9 *)
  cut_edges_2i (S : mll2i_ps) : num set =
    { e | e IN S.edges /\ S.lbl_2i e = Cut2I }
End

Definition weak_edges_def :                             (* §73.9 *)
  weak_edges (S : mll2i_ps) : num set =
    { e | e IN S.edges /\ S.lbl_2i e = W2I }
End

Definition derel_edges_def :                            (* §73.9 *)
  derel_edges (S : mll2i_ps) : num set =
    { e | e IN S.edges /\ S.lbl_2i e = D2I }
End

Definition contr_edges_def :                            (* §73.9 *)
  contr_edges (S : mll2i_ps) : num set =
    { e | e IN S.edges /\ S.lbl_2i e = C2I }
End

Definition etens_edges_def :                            (* §73.9 *)
  etens_edges (S : mll2i_ps) : num set =
    { e | e IN S.edges /\ S.lbl_2i e = ETens2I }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.10  Exponential box                                                      *)
(*                                                                              *)
(* For each left premise v of an ⊛ (ETens2I) hyperedge, the box of v is       *)
(* the sub-proof-structure reachable from v and all dep(v):                    *)
(*                                                                              *)
(*   box : V → 𝒫(V) × 𝒫(E)                                                    *)
(*                                                                              *)
(* box(v) = (V_b, E_b) where V_b (resp. E_b) are vertices (resp. edges)       *)
(* reachable from {v} ∪ dep(v) by non-oriented paths in the hypergraph.       *)
(*                                                                              *)
(* We state box as an uninterpreted function satisfying a reachability spec    *)
(* (PROOF-OBLIGATION[stellaMLL2I.01]).                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §73.10  Box of vertex v in MLL2I proof-structure S.
   Returns (V_b, E_b): vertices and edges of the sub-proof-structure for v.  *)
Definition exp_box_def :                                (* §73.10 *)
  exp_box (S : mll2i_ps) (v : num) : (num set # num set) =
    (* Stub: the real definition requires graph reachability.
       PROOF-OBLIGATION[stellaMLL2I.01] below specifies the correct content. *)
    ({v} ∪ S.dep v, {})
End

(*
   PROOF-OBLIGATION[stellaMLL2I.01]:
   GOAL:
     !S v.
       (* v is a left premise of some ETens2I hyperedge *)
       (?e. e IN etens_edges S /\ v = FST (S.in_2i e)) ==>
       let (V_b, E_b) = exp_box S v in
       (* v and all dep(v) are contained in the box vertices *)
       v IN V_b /\ S.dep v SUBSET V_b /\
       (* E_b consists of edges with both input vertices in V_b *)
       (!e. e IN E_b ==> e IN S.edges /\
            FST (S.in_2i e) IN V_b /\ SND (S.in_2i e) IN V_b) /\
       (* V_b is closed under non-oriented paths within S.edges *)
       (!u. u IN V_b ==> u IN S.vertices)
   STRATEGY:
     Define exp_box via BFS/DFS reachability from {v} ∪ dep(v) in the
     undirected version of the hypergraph. The stub above is a placeholder.
     Prove by wellfounded induction on hypergraph structure.
   DRAFT-TACTICS: cheat
*)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.12  MLL2I cut-elimination step  R ↝ S                                   *)
(*                                                                              *)
(* Three cases for a cut between ⋊ (EPar2I) and ⊛ (ETens2I) hyperedges:      *)
(*   · Weakening (W2I):    erase the box                                       *)
(*   · Dereliction (D2I):  remove dependencies, add two new cuts              *)
(*   · Contraction (C2I):  duplicate the box with fresh vertex/edge names     *)
(*                                                                              *)
(* We abstract cut-elimination as a relation, per the stellaMLL pattern.       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §73.12  One step of MLL2I cut-elimination.
   mll2i_cut_elim_step R S means S is obtained from R by eliminating one
   cut edge e_cut (one of the three exponential cases, or multiplicative).    *)
Definition mll2i_cut_elim_step_def :                    (* §73.12 *)
  mll2i_cut_elim_step (R : mll2i_ps) (S : mll2i_ps) : bool =
    (* There exists a cut edge e_cut in R that is eliminated to produce S *)
    ?e_cut.
      e_cut IN cut_edges_2i R /\
      (* S has strictly fewer cuts *)
      cut_edges_2i S PSUBSET cut_edges_2i R /\
      (* S has the same or smaller vertex set (erasing reduces V) *)
      S.vertices SUBSET R.vertices /\
      (* e_cut is removed from S *)
      e_cut NOTIN S.edges /\
      (* Non-cut edges (except those erased) are inherited *)
      (R.edges DIFF cut_edges_2i R) SUBSET S.edges ∪ (R.edges DIFF S.edges)
End

(*
   PROOF-OBLIGATION[stellaMLL2I.02]:
   GOAL:
     !R S e_cut e1 e2 e_epar w1 w2 u1 u2.
       (* e_cut is a cut between EPar2I (e1 via e_epar) and ETens2I (e2) *)
       e_cut IN cut_edges_2i R /\
       S.lbl_2i e1 = EPar2I /\ S.lbl_2i e2 = ETens2I /\
       FST (R.in_2i e1) = u1 /\ SND (R.in_2i e1) = u2 /\
       FST (R.in_2i e2) = w1 /\ SND (R.in_2i e2) = w2 /\
       R.lbl_2i e_epar = W2I /\ R.out_2i e_epar = u1 ==>
       (* Weakening case §73.12: erase box(w1) *)
       let (V_b, E_b) = exp_box R w1 in
       mll2i_cut_elim_step R
         (R with <|
           vertices := R.vertices DIFF ({u1; w1} ∪ V_b);
           edges    := (R.edges DIFF ({e_cut; e1; e2; e_epar} ∪ E_b)) ∪ {0};
           lbl_2i   := \e. if e = 0 then Cut2I else R.lbl_2i e;
           in_2i    := \e. if e = 0 then (u2, w2) else R.in_2i e;
           dep      := \v. if v IN R.dep w1 then {} else R.dep v
         |>)
   STRATEGY:
     Direct unfolding of mll2i_cut_elim_step_def; the three sub-cases
     (w/d/c) each produce a proof-structure satisfying the definition.
     Use 0 as the fresh cut edge identifier (or any e_cut NOTIN R.edges).
   DRAFT-TACTICS: cheat

   PROOF-OBLIGATION[stellaMLL2I.03]:
   GOAL: Dereliction case (ℓ_E(e_⋊) = D2I): analogous to stellaMLL2I.02.
   See §73.12 Definition (dereliction): removes dep of w1; adds two new cuts.
   DRAFT-TACTICS: cheat

   PROOF-OBLIGATION[stellaMLL2I.04]:
   GOAL: Contraction case (ℓ_E(e_⋊) = C2I): duplicates box with fresh names.
   See §73.12 Definition (contraction): σ renames, adds three new cuts.
   DRAFT-TACTICS: cheat
*)

(* §73.12  Reflexive-transitive closure R ↝* S *)
Definition mll2i_cut_elim_star_def :                    (* §73.12 *)
  mll2i_cut_elim_star = RTC mll2i_cut_elim_step
End

(* §73.12  A proof-structure is in normal form iff it has no cuts. *)
Definition mll2i_normal_def :                           (* §73.12 *)
  mll2i_normal (S : mll2i_ps) : bool = (cut_edges_2i S = {})
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.2  Exponential basis of representation                                   *)
(*                                                                              *)
(* The multiplicative basis 𝔹 is extended with:                               *)
(*   • ∈ F   — binary, left-associative: t • u • v := (t • u) • v             *)
(*   Y_i     — box variables (fresh per box index i)                           *)
(*   w, c, d — zero-arity constants                                            *)
(*                                                                              *)
(* In our term encoding:                                                        *)
(*   bullet_sym  = encode_psym (Neutral, 100)  — the • function symbol        *)
(*   wh_sym      = encode_psym (Neutral, 101)  — weakening constant w          *)
(*   c_sym       = encode_psym (Neutral, 102)  — contraction constant c        *)
(*   d_sym       = encode_psym (Neutral, 103)  — dereliction constant d        *)
(*   omega_sym   = encode_psym (Neutral, 104)  — black-hole symbol ω           *)
(*   box_var i   = Var (1000 + i)             — box variable Y_i              *)
(*                                                                              *)
(* (The specific numeric codes are conventions; they must not clash with        *)
(* dir_left/dir_right in §66.2 which use 1 and 2.)                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition bullet_sym_def :                             (* §74.2 *)
  bullet_sym : num = encode_psym (Neutral, 100)
End

Definition wh_sym_def :                                 (* §74.2 *)
  wh_sym : num = encode_psym (Neutral, 101)
End

Definition c_sym_def :                                  (* §74.2 *)
  c_sym : num = encode_psym (Neutral, 102)
End

Definition d_sym_def :                                  (* §74.2 *)
  d_sym : num = encode_psym (Neutral, 103)
End

Definition omega_sym_def :                              (* §74.7 *)
  omega_sym : num = encode_psym (Neutral, 104)
End

(* §74.2  Box variable Y_i: a fresh term variable for box i. *)
Definition box_var_def :                                (* §74.2 *)
  box_var (i : num) : term = Var (1000 + i)
End

(* §74.2  The • operation on terms: t • u = App bullet_sym [t; u] *)
Definition bullet_def :                                 (* §74.2 *)
  bullet (t : term) (u : term) : term = App bullet_sym [t; u]
End

(* §74.2  Constant terms for w, c, d (zero-arity): App sym [] *)
Definition wh_term_def :                                (* §74.2 *)
  wh_term : term = App wh_sym []
End

Definition d_term_def :                                 (* §74.2 *)
  d_term : term = App d_sym []
End

Definition c_term_def :                                 (* §74.2 *)
  c_term : term = App c_sym []
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.5  Path address pAddr_2I(v) extended for MLL2I                          *)
(*                                                                              *)
(* The MLL path address (§66.7) is extended with cases for:                    *)
(*   · W2I  (weakening, §74.5 base): pAddr_2I(v) = Var x (fresh)             *)
(*   · D2I  (dereliction):           pAddr_2I(v) = bullet(pAddr(v)) d_term    *)
(*   · C2I  (contraction): if pAddr(w_i) = t • u  then                        *)
(*           pAddr(w_1) = bullet t (bullet one_term u)                         *)
(*           pAddr(w_2) = bullet t (bullet r_term u)                           *)
(*   · ETens2I (⊛, §74.5): for fresh box var Y_i,                             *)
(*           pAddr(w_1) = bullet (App dir_left [pAddr(w_1)]) Y_i               *)
(*           pAddr(w_2) = bullet (App dir_right [pAddr(w_2)]) Y_i              *)
(*           all u in box(w_1): pAddr updated to bullet(pAddr(u)) Y_i          *)
(*   · EPar2I (⋊): same as Par2IL (left/right, multiplicative-style)          *)
(*                                                                              *)
(* We give a stub definition and specify the clauses as a PROOF-OBLIGATION.   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §74.5  Direction constants (reused from §66.2 via stellaMLLTheory). *)
(* dir_left  = encode_psym (Neutral, 1) — defined in stellaMLLTheory  *)
(* dir_right = encode_psym (Neutral, 2) — defined in stellaMLLTheory  *)

(* §74.5  "one" (left copy identifier) and "r" (right copy identifier) terms *)
Definition one_term_def :                               (* §74.5 *)
  one_term : term = App dir_left []
End

Definition r_term_def :                                 (* §74.5 *)
  r_term : term = App dir_right []
End

(* §74.5  Path address of atom v in MLL2I proof-structure S.
   Stub: the full inductive definition is given by PROOF-OBLIGATION[stellaMLL2I.05]. *)
Definition pAddr_2I_def :                               (* §74.5 *)
  pAddr_2I (S : mll2i_ps) (i : num) (v : num) : term =
    (* i = box-variable index counter (for ETens2I fresh Y_i allocation) *)
    (* Stub: return Var v as default; full definition is in proof obligation. *)
    Var v
End

(*
   PROOF-OBLIGATION[stellaMLL2I.05]:
   GOAL:
     !S i v.
     (* Ax2I case: v is a conclusion of an axiom link *)
     (?e. e IN ax_edges_2i S /\
          (v = FST (S.in_2i e) \/ v = SND (S.in_2i e))) ==>
       pAddr_2I S i v = Var v

     (* W2I case §74.5 base: conclusion of weakening *)
     /\ (?e. e IN weak_edges S /\ v = S.out_2i e) ==>
       pAddr_2I S i v = Var v

     (* D2I case §74.5: v = conclusion of dereliction with input v_d *)
     /\ (?e v_d. e IN derel_edges S /\
                 v = S.out_2i e /\ v_d = FST (S.in_2i e)) ==>
       pAddr_2I S i v = bullet (pAddr_2I S i v) d_term

     (* C2I case §74.5: v1,v2 are two inputs of contraction *)
     /\ (?e v1 v2 t u.
           e IN contr_edges S /\
           v1 = FST (S.in_2i e) /\ v2 = SND (S.in_2i e) /\
           pAddr_2I S i v1 = bullet t u) ==>
       pAddr_2I S i v1 = bullet t (bullet one_term u) /\
       pAddr_2I S i v2 = bullet t (bullet r_term u)

     (* EPar2I / Par2IL case §74.5: left premise → 1·pAddr, right → r·pAddr *)
     /\ (?e. e IN S.edges /\ (S.lbl_2i e = EPar2I \/ S.lbl_2i e = Par2IL) /\
             v = FST (S.in_2i e)) ==>
       pAddr_2I S i v = App dir_left [pAddr_2I S i (S.out_2i e)]

     /\ (?e. e IN S.edges /\ (S.lbl_2i e = EPar2I \/ S.lbl_2i e = Par2IL) /\
             v = SND (S.in_2i e)) ==>
       pAddr_2I S i v = App dir_right [pAddr_2I S i (S.out_2i e)]

     (* ETens2I case §74.5: left/right premises get bullet with fresh Y_i *)
     /\ (?e w1 w2.
           e IN etens_edges S /\
           w1 = FST (S.in_2i e) /\ w2 = SND (S.in_2i e)) ==>
       pAddr_2I S i w1 = bullet (App dir_left [pAddr_2I S i w1]) (box_var i) /\
       pAddr_2I S i w2 = bullet (App dir_right [pAddr_2I S i w2]) (box_var i)
   STRATEGY:
     Define pAddr_2I by structural induction on a depth-measure of S.
     The box-variable index i is threaded through to allocate fresh Y_i.
     For scaffold: state spec + cheat.
   DRAFT-TACTICS: cheat
*)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.5  Address of an atom v in S                                             *)
(*                                                                              *)
(* Two cases:                                                                   *)
(*   · Independent (no u with v ∈ box(u)):                                     *)
(*       addr_2I S v := App (encode_psym (Neutral, c)) [pAddr_2I S 0 v]       *)
(*       where c is the relevant conclusion vertex                              *)
(*   · Dependent (∃ u with v ∈ box(u)):                                        *)
(*       addr_2I S v := substitution pAddr_2I S 0 u with X replaced by        *)
(*       pAddr_2I S 0 v, wrapped in the conclusion symbol                      *)
(*                                                                              *)
(* For simplicity we give the independent case; the dependent case is          *)
(* specified by PROOF-OBLIGATION[stellaMLL2I.06].                              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §74.5  Independent address: c(pAddr_2I(v)). *)
Definition addr_2I_indep_def :                          (* §74.5 *)
  addr_2I_indep (S : mll2i_ps) (c : num) (v : num) : term =
    App (encode_psym (Neutral, c)) [pAddr_2I S 0 v]
End

(*
   PROOF-OBLIGATION[stellaMLL2I.06]:
   GOAL:
     !S v u c t.
       (* v is dependent: v ∈ box(u) for some u that is a left premise of ⊛ *)
       (?e. e IN etens_edges S /\ FST (S.in_2i e) = u /\ v IN FST (exp_box S u)) /\
       pAddr_2I S 0 u = t ==>
       (* dependent address = pAddr(u) with X_0 := pAddr(v), wrapped in c *)
       addr_2I_indep S c v =
         App (encode_psym (Neutral, c))
           [subst_apply (FEMPTY |+ (0, pAddr_2I S 0 v)) t]
   STRATEGY:
     This follows directly from §74.5 definition of addr_S for dependent atoms.
     The substitution replaces the placeholder variable X (encoded as Var 0)
     with pAddr_2I S 0 v in the path address of the box representative u.
   DRAFT-TACTICS: cheat
*)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.7  Black-hole star for weakened atom v                                   *)
(*                                                                              *)
(* v★ := [+addr_S(v), +ω(X), −ω(f(X))]                                        *)
(*                                                                              *)
(* where ω is a fresh symbol, f is a fresh unary function symbol.              *)
(* In our encoding:                                                             *)
(*   omega_sym = encode_psym (Neutral, 104)  — the ω symbol                   *)
(*   f_bh_sym  = encode_psym (Neutral, 105)  — the f function symbol          *)
(*                                                                              *)
(* The three rays:                                                              *)
(*   1. +addr_2I_indep S c v  — positive, the address ray                     *)
(*   2. +ω(X)                 — positive, fresh ω ray  (X = Var 0)            *)
(*   3. −ω(f(X))              — negative, ω applied to f(X)                   *)
(*                                                                              *)
(* This creates an infinite loop: any star connecting to ray 2 will have to    *)
(* match ray 3, which sends back ω(f(X)) again, ad infinitum.                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition f_bh_sym_def :                               (* §74.7 *)
  f_bh_sym : num = encode_psym (Neutral, 105)
End

(* §74.7  Black-hole star for weakened vertex v.
   v★ = [+addr(v), +ω(X), −ω(f(X))]                                          *)
Definition black_hole_star_def :                        (* §74.7 *)
  black_hole_star (S : mll2i_ps) (c : num) (v : num) : star =
    [ App (encode_psym (Pos, c)) [pAddr_2I S 0 v] ;          (* +addr(v)   *)
      App (encode_psym (Pos, encode_psym (Neutral, 104))) [Var 0] ;
                                                              (* +ω(X)      *)
      App (encode_psym (Neg, encode_psym (Neutral, 104)))     (* −ω(f(X))  *)
          [App f_bh_sym [Var 0]] ]
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.8  Weak(S) — set of weakened atoms                                       *)
(*                                                                              *)
(* Weak(S) := { u★ | ∃e ∈ E. ℓ(e) = w, out(e) = u }                          *)
(*                                                                              *)
(* In our encoding: the "conclusion" of a W2I edge e is out_2i(e).            *)
(* We build a list of black-hole stars for all weakening conclusions.          *)
(* The conclusion vertex of a W2I edge is the single conclusion out_2i(e).   *)
(* We use c = S.out_2i e as the conclusion symbol.                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §74.8  List of black-hole stars for all weakening edges. *)
Definition weak_set_def :                               (* §74.8 *)
  weak_set (S : mll2i_ps) : constellation =
    MAP (\e. black_hole_star S (S.out_2i e) (S.out_2i e))
        (SET_TO_LIST (weak_edges S))
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.9  Cut conclusion vertices for MLL2I                                     *)
(*                                                                              *)
(* Cut-conclusion vertices: the two endpoints of each cut edge in S.           *)
(* These receive positive polarity in the μ wrapper.                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition cut_concls_2i_def :                          (* §74.9 *)
  cut_concls_2i (S : mll2i_ps) : num set =
    { v | ?e. e IN cut_edges_2i S /\
              (v = FST (S.in_2i e) \/ v = SND (S.in_2i e)) }
End

(* §74.9  μ wrapper for MLL2I rays: upgrade polarity to Pos for cut conclusions. *)
Definition mu_ray_2i_def :                              (* §74.9 *)
  mu_ray_2i (S : mll2i_ps) (r : ray) : ray =
    case r of
      App h args =>
        let (_, name) = decode_psym h in
        if name IN cut_concls_2i S then
          App (encode_psym (Pos, name)) args
        else r
    | Var x => Var x
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.9  Vehicle Φ^ax_S and cut constellation Φ^cut_S for MLL2I               *)
(*                                                                              *)
(* Φ^ax_S  := Σ_{e ∈ Ax(S)} [μ(addr(←e)), μ(addr(→e))] + Σ_{u ∈ Weak(S)} u★ *)
(*                                                                              *)
(* Φ^cut_S := Σ_{e ∈ Cuts(S)} [−←e(X), −→e(X)]                               *)
(*                                                                              *)
(* Φ^comp_S := Φ^ax_S ⊎ Φ^cut_S                                               *)
(*                                                                              *)
(* Reuses stellaMLLTheory patterns for ax-stars and cut-stars.                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §74.9  Single axiom star for edge e (MLL2I version). *)
Definition ax_star_2i_def :                             (* §74.9 *)
  ax_star_2i (S : mll2i_ps) (e : num) : star =
    let lv = FST (S.in_2i e) in
    let rv = SND (S.in_2i e) in
    [ mu_ray_2i S (addr_2I_indep S lv lv) ;
      mu_ray_2i S (addr_2I_indep S rv rv) ]
End

(* §74.9  Vehicle Φ^ax_S = axiom stars + black-hole stars. *)
Definition Phi_ax_2I_def :                              (* §74.9 *)
  Phi_ax_2I (S : mll2i_ps) : constellation =
    MAP (ax_star_2i S) (SET_TO_LIST (ax_edges_2i S)) ++ weak_set S
End

(* §74.9  Single cut star for edge e (MLL2I version). *)
Definition cut_star_2i_def :                            (* §74.9 *)
  cut_star_2i (S : mll2i_ps) (e : num) : star =
    let lv = FST (S.in_2i e) in
    let rv = SND (S.in_2i e) in
    [ App (encode_psym (Neg, lv)) [Var 0] ;
      App (encode_psym (Neg, rv)) [Var 0] ]
End

(* §74.9  Cut constellation Φ^cut_S. *)
Definition Phi_cut_2I_def :                             (* §74.9 *)
  Phi_cut_2I (S : mll2i_ps) : constellation =
    MAP (cut_star_2i S) (SET_TO_LIST (cut_edges_2i S))
End

(* §74.9  Computational content Φ^comp_S = Φ^ax_S ⊎ Φ^cut_S. *)
Definition Phi_comp_2I_def :                            (* §74.9 *)
  Phi_comp_2I (S : mll2i_ps) : constellation =
    Phi_ax_2I S ++ Phi_cut_2I S
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.11  Structural equivalence for MLL2I                                     *)
(*                                                                              *)
(* We reuse struct_equiv from stellaMLLTheory directly (same definition).      *)
(* AEx_equiv from stellaMLLTheory is also reused by instantiation.            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §74.11  AEx equivalence for MLL2I (lifted from stellaMLLTheory pattern).   *)
Definition AEx_equiv_2I_def :                           (* §74.11 *)
  AEx_equiv_2I (Phi : constellation) (Phi' : constellation) : bool =
    ?gamma gamma'.
      gamma IN AEx_C Phi /\ gamma' IN AEx_C Phi' /\
      struct_equiv gamma gamma'
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.11  Simulation theorem: AEx(Φ^comp_R) ≃_S Φ^ax_S                       *)
(*                                                                              *)
(* STATEMENT (§74.11): For an MLL2I proof-net R such that R ↝* S              *)
(* with S in normal form:                                                       *)
(*                                                                              *)
(*   AEx(Φ^comp_R) ≃_S Φ^ax_S                                                 *)
(*                                                                              *)
(* i.e., the abstract execution of the computational content of R is           *)
(* structurally equivalent to the vehicle of S.                                *)
(*                                                                              *)
(* PROOF SKETCH (§74.11):                                                       *)
(*   All multiplicative cases were treated in Chapter 10 (Lemma 67.9).        *)
(*   The only new cut case for MLL2I: cut between ⋊ (EPar2I) and ⊛ (ETens2I). *)
(*   The left premises interact as in ⊗/⅋ cut-elimination.                    *)
(*   Right premises are multiplicative.                                         *)
(*   Three sub-cases (w/d/c) for the interaction between left premises:        *)
(*   1. Weakening: black-hole star prevents construction of saturated diagram; *)
(*      all stars erased.                                                       *)
(*   2. Dereliction: Y_j replaced by d, box opened, potential for              *)
(*      duplication cancelled.                                                  *)
(*   3. Contraction: n copies +u_i(t•u_i) match left premises; each           *)
(*      +v_i(w•Y_i) duplicated into n copies with copy identifiers u_i.        *)
(*   The simulation uses AEx (abstract execution), not IEx.                    *)
(*                                                                              *)
(* DEFERRED: proof-obligation stellaMLL2I.07                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL2I.07]:
   GOAL:
     !R S.
       mll2i_cut_elim_star R S /\ mll2i_normal S ==>
       AEx_equiv_2I (Phi_comp_2I R) (Phi_ax_2I S)
   STRATEGY:
     Induction on the number of steps in mll2i_cut_elim_star (= RTC).
     Base (R = S, mll2i_normal S):
       mll2i_normal S ==> cut_edges_2i S = {} ==> Phi_cut_2I S = []
       ==> Phi_comp_2I S = Phi_ax_2I S.
       AEx_equiv_2I (Phi_ax_2I S) (Phi_ax_2I S) follows from struct_equiv_refl.
     Inductive step (R0 ↝ R ↝* S):
       By IH: AEx_equiv_2I (Phi_comp_2I R) (Phi_ax_2I S).
       By one-step simulation (PROOF-OBLIGATION[stellaMLL2I.08]):
         AEx_equiv_2I (Phi_comp_2I R0) (Phi_comp_2I R).
       By transitivity of AEx_equiv_2I (struct_equiv_trans):
         AEx_equiv_2I (Phi_comp_2I R0) (Phi_ax_2I S).
     The one-step simulation (stellaMLL2I.08) covers:
       · Multiplicative cases (Tens2IL/Par2IL, Ax2I/Cut2I): same as §67.9.
       · EPar2I/ETens2I cut — three sub-cases (w/d/c):
           - Weakening: black-hole stars consume all rays from the box;
             no saturated diagram forms; AEx reduces to Phi_ax of S with box erased.
           - Dereliction: Y_j unified with d_term; box opened linearly.
           - Contraction: box duplicated; copy identifiers (1·u, r·u) separate copies.
     Relies on stellaExecutionTheory.AEx_C properties (aex_idempotent, aex_no_matchable).
   CITATION: §74.11 Theorem (Simulation of MLL2I cut-elimination).
   DRAFT-TACTICS: cheat (RTC induction + three-case analysis on cut type)
*)
Theorem sim_mll2i_cut_elim :                            (* §74.11 *)
  !R S.
    mll2i_cut_elim_star R S /\ mll2i_normal S ==>
    AEx_equiv_2I (Phi_comp_2I R) (Phi_ax_2I S)
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL2I.08]:
   GOAL:
     !R S.
       mll2i_cut_elim_step R S ==>
       AEx_equiv_2I (Phi_comp_2I R) (Phi_comp_2I S)
   STRATEGY:
     One-step simulation.  Case split on the type of cut edge e_cut in R:
     (a) Ax2I/Cut2I: same as stellaMLLTheory.sim_cut_step; reuse that argument.
     (b) Tens2IL/Par2IL: same multiplicative case; reuse.
     (c) EPar2I/ETens2I: new.  Sub-case on label of the ⋊ input e_epar:
         - W2I: black_hole_star v★ creates an omega-loop.  Any ray from
                the box of w1 that tries to match will be swallowed and
                no saturated diagram can form.  AEx eliminates all stars
                of box(w1); result matches Phi_comp of R with box erased.
         - D2I: the dereliction input v_d unifies Y_i = d_term.  This
                opens the box by substituting d for the box variable Y_i
                in all rays that have Y_i as a component.
         - C2I: the contraction inputs (v1, v2) unify Y_i = 1·u1, Y_i = r·u2
                creating two copies; the duplicated box rays split by
                copy identifiers.
   CITATION: §74.11 proof sketch, subcases §74.11(1–3).
   DRAFT-TACTICS: cheat (case split on EPar2I/ETens2I sub-cases)
*)
Theorem sim_mll2i_cut_step :                            (* §74.11 *)
  !R S.
    mll2i_cut_elim_step R S ==>
    AEx_equiv_2I (Phi_comp_2I R) (Phi_comp_2I S)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.12  SANITY: Φ^comp_2I of a cut-free proof-structure equals Φ^ax_2I     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem phi_comp_2i_cutfree :
  !S. mll2i_normal S ==> Phi_comp_2I S = Phi_ax_2I S
Proof
  rw [mll2i_normal_def, Phi_comp_2I_def, Phi_cut_2I_def, cut_edges_2i_def] >>
  simp [SET_TO_LIST_EMPTY]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §73.12  SANITY: mll2i_cut_elim_star is reflexive and transitive            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem mll2i_cut_elim_star_refl :
  !S. mll2i_cut_elim_star S S
Proof
  rw [mll2i_cut_elim_star_def, RTC_REFL]
QED

Theorem mll2i_cut_elim_star_trans :
  !R S T.
    mll2i_cut_elim_star R S /\ mll2i_cut_elim_star S T ==>
    mll2i_cut_elim_star R T
Proof
  rw [mll2i_cut_elim_star_def] >>
  metis_tac [RTC_TRANS]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §74.11  SANITY: AEx_equiv_2I is reflexive (follows from struct_equiv_refl) *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaMLL2I.09]:
   GOAL:   !Phi. AEx_equiv_2I Phi Phi
   STRATEGY:
     AEx_C is non-empty (for any Phi, Phi itself or any actualised diagram is
     in AEx_C Phi).  Pick gamma = gamma' the same element of AEx_C Phi.
     Apply struct_equiv_refl.
   DRAFT-TACTICS: cheat
*)
Theorem AEx_equiv_2I_refl :
  !Phi. AEx_equiv_2I Phi Phi
Proof
  cheat
QED

(*
   PROOF-OBLIGATION[stellaMLL2I.10]:
   GOAL:   !Phi Phi' Phi''.
     AEx_equiv_2I Phi Phi' /\ AEx_equiv_2I Phi' Phi'' ==>
     AEx_equiv_2I Phi Phi''
   STRATEGY:
     Witnesses: pick gamma from AEx_C Phi, gamma'' from AEx_C Phi'' with
     struct_equiv via the intermediate gamma' in AEx_C Phi'.
     Apply struct_equiv_trans from stellaMLLTheory.
   DRAFT-TACTICS:
     rw [AEx_equiv_2I_def] >>
     metis_tac [struct_equiv_trans]
*)
Theorem AEx_equiv_2I_trans :
  !Phi Phi' Phi''.
    AEx_equiv_2I Phi Phi' /\ AEx_equiv_2I Phi' Phi'' ==>
    AEx_equiv_2I Phi Phi''
Proof
  cheat
QED

val _ = export_theory ();
