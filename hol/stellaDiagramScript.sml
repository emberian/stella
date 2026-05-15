(* stellaDiagramScript.sml
   Dependency graph D[Phi;C] — Eng §49.10–§49.14.
   Clean restatement replacing the crashed-agent version.

   ══════════════════════════════════════════════════════════════════════════════
   GRAPH INSTANCE CHOICE
   ──────────────────────────────────────────────────────────────────────────────
   Eng's D[Phi;C] (§49.10) is an *undirected simple graph*:
     · vertices   = star indices (finite subset of num)
     · edges      = unordered, no self-loops
     · at most one edge per pair of stars ("a graph", not a multigraph)

   We use  fsgraph  from fsgraphTheory:
       Type fsgraph = :(unit, finiteG, noSL) udulgraph
   Properties:
     · undirectedG   — edges carry no direction            ✓
     · finiteG       — finitely many nodes                 ✓
     · noSL          — no self-loops                       ✓
     · one undirected edge per unordered pair (simple graph via noSL+udulgraph) ✓

   REUSED from genericGraphTheory / fsgraphTheory:
     · type :fsgraph                — the graph carrier
     · fsgAddNode, fsgAddNodes      — inserting star-index nodes
     · fsgAddEdges                  — bulk edge insertion from a set of edges
     · fsgedges, adjacent           — edge membership, adjacency predicate
     · degree_def                   — degree of a node (CARD of incident edges)
     · nodes, emptyG                — node set, empty graph

   NOTE on node representation:
     fsgraph nodes have type  :unit + num  (forced by the fsgraph type synonym).
     We represent star index  i  as  INR i : unit + num.

   DEFINED FRESH (this file):
     · ray, star, constellation     — type abbreviations
     · colours / colours_list       — set of neutral-name numbers in a ray (§48.8)
     · dep_edge_cond                — matchable + colour-subset (§49.10)
     · stars_dep                    — any matching ray pair between two stars
     · dep_graph                    — D[Phi;C] as fsgraph (§49.10)
     · IdRays                       — (i,j) ray indices of a constellation (§49.11)
     · pm_IdRays                    — coloured (Pos/Neg) rays only (§49.11)
     · adj_C_phi                    — adjacent stars to a given ray (§49.12)
     · deg_C_phi                    — degree of a ray = |adj| (§49.13)
     · ray_free, ray_det,           — free/deterministic/branching/co-branching
       ray_branch, ray_cobranch       (§49.12–§49.14)

   LIST VS BAG CHOICE:
     A constellation is defined as  :star list  (not a bag or set).  Justification:
     (1) HOL4's list infrastructure is simpler than multiset/bag.
     (2) Integer indexing  EL i Phi  provides the index map  I_Phi → star  directly.
     (3) The dependency graph is index-based (edge between index i and index j),
         so the list order does not affect the mathematical content of D[Phi;C].
     A bag would be equally correct but would require heavier combinatorial
     infrastructure for indexing.  A set would lose the ability to have duplicate
     stars.  We choose list.

   NOT ATTEMPTED (see ledger at end of file):
     · Prob(delta), AEx (Chapter 10)
     · Diagrams (sequences of constellations)

   PROOF POLICY:  every non-trivial proof is deferred to a PROOF-OBLIGATION block
   followed by `cheat`.  Closed computations that EVAL genuinely discharges are
   NOT debt.  Zero uses of new_axiom / mk_thm.
   ══════════════════════════════════════════════════════════════════════════════
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory pairTheory
     relationTheory;
open stellaTermTheory stellaPolarisedTheory stellaMatchTheory;
open fsgraphTheory genericGraphTheory;

val _ = new_theory "stellaDiagram";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.9  Type abbreviations: ray, star, constellation                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* A ray is a term (from stellaTermTheory) whose App head encodes a polarised
   symbol via encode_psym / decode_psym (from stellaPolarisedTheory).         *)
val _ = Parse.type_abbrev_pp ("ray", ``:stellaTerm$term``)

(* §48.9  A star is a finite list of rays.
   (Eng uses a finite indexed family; we use lists, so EL j (EL i Phi) is the
   j-th ray of the i-th star of constellation Phi.)                           *)
val _ = Parse.type_abbrev_pp ("star", ``:ray list``)

(* §49.10  A constellation Phi is a list of stars.
   Star i  = EL i Phi  (well-defined when i < LENGTH Phi).
   Ray (i,j) = EL j (EL i Phi).
   The index set  I_Phi = {0, ..., LENGTH Phi - 1}.                          *)
val _ = Parse.type_abbrev_pp ("constellation", ``:star list``)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.8  Colours of a ray                                                     *)
(*                                                                             *)
(* Verbatim spec:                                                               *)
(*   colours(t) = ∅               if t is uncoloured (Var or Neutral App)    *)
(*   colours(c(r₁..rₖ)) = {c} ∪ ⋃ colours(rᵢ)                              *)
(*                                  if c is coloured (positive or negative)   *)
(*   colours(c(r₁..rₖ)) = ⋃ colours(rᵢ)                                     *)
(*                                  if c is uncoloured (Neutral)              *)
(*                                                                             *)
(* In our encoding: a head symbol  h : num  encodes  (pol, name)  via         *)
(* decode_psym h = (pol, name).  The "name" (neutral neutral-symbol number)   *)
(* is  SND (decode_psym h).                                                   *)
(*                                                                             *)
(* A head h is "coloured" iff pol ∈ {Pos, Neg}.                               *)
(* colours(App h ts) = (if is_coloured h then {SND(decode_psym h)} else {}) *)
(*                     ∪ ⋃_i colours(EL i ts)                                *)
(* colours(Var _) = {}                                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Is an encoded head symbol coloured (Pos or Neg)?  *)
Definition is_coloured_def:
  is_coloured (h : num) : bool =
    let pol = FST (decode_psym h) in
    pol = Pos \/ pol = Neg
End

(* Neutral name of an encoded symbol (the part that identifies the predicate). *)
Definition sym_name_def:
  sym_name (h : num) : num = SND (decode_psym h)
End

(* §48.8: colours of a ray / list of rays — mutually recursive.
   We use Hol_defn to state the mutual recursion; the equations are extracted
   and saved manually.                                                         *)
val colours_defn = Hol_defn "colours" `
  (colours     (Var _)     = {}) /\
  (colours     (App h ts)  =
     (if is_coloured h then {sym_name h} else {}) UNION colours_list ts) /\
  (colours_list []         = {}) /\
  (colours_list (r :: rs)  = colours r UNION colours_list rs)`;

(* Hol_defn already saves the equations as "colours_def" in the theory.
   We just bind the ML values for local use.                                 *)
val colours_eqns = LIST_CONJ (Defn.eqns_of colours_defn);
val colours_ind  = save_thm ("colours_ind",
                              Option.valOf (Defn.ind_of colours_defn));

Theorem FINITE_colours :
  (!r  : ray.       FINITE (colours r)) /\
  (!rs : ray list.  FINITE (colours_list rs))
Proof
  HO_MATCH_MP_TAC colours_ind >>
  rw [colours_eqns] >>
  rw []
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.10  Dependency edge condition                                            *)
(*                                                                             *)
(* An edge between ray r and ray r' under colour set C (§49.10):              *)
(*   (a) matchable r r'  — compat heads + alpha-unifiable (§49.7)             *)
(*   (b) colours(r) ∪ colours(r') ⊆ C                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dep_edge_cond_def :
  dep_edge_cond (C : num set) (r : ray) (r' : ray) <=>
    matchable r r' /\ (colours r UNION colours r') SUBSET C
End

(*
   PROOF-OBLIGATION[stellaDiagram.01]:
   GOAL:   !C r r'. dep_edge_cond C r r' <=> dep_edge_cond C r' r
   STRATEGY: unfold dep_edge_cond_def; apply matchable_sym and UNION_COMM.
   DRAFT-TACTICS:
     rw [dep_edge_cond_def, matchable_sym, UNION_COMM]
*)
Theorem dep_edge_cond_sym :
  !C r r'. dep_edge_cond C r r' = dep_edge_cond C r' r
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.10  Stars dependency                                                     *)
(*                                                                             *)
(* Two stars s1 and s2 are C-dependent if there exists a ray r in s1 and a    *)
(* ray r' in s2 such that dep_edge_cond C r r'.                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition stars_dep_def :
  stars_dep (C : num set) (s1 : star) (s2 : star) <=>
    ?r r'. MEM r s1 /\ MEM r' s2 /\ dep_edge_cond C r r'
End

(*
   PROOF-OBLIGATION[stellaDiagram.02]:
   GOAL:   !C s1 s2. stars_dep C s1 s2 = stars_dep C s2 s1
   STRATEGY: unfold stars_dep_def; use dep_edge_cond_sym; swap existential
             witnesses.
   DRAFT-TACTICS:
     rw [stars_dep_def] >> metis_tac [dep_edge_cond_sym]
*)
Theorem stars_dep_sym :
  !C s1 s2. stars_dep C s1 s2 = stars_dep C s2 s1
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.11  IdRays                                                               *)
(*                                                                             *)
(* §49.11: IdRays(Phi) = { (i,j) | star i, ray j is a ray of Phi }           *)
(*   i.e., all valid (star-index, ray-index) pairs.                            *)
(* ±IdRays(Phi) = coloured rays only (head polarity Pos or Neg).              *)
(*                                                                             *)
(* We represent IdRays as a set of num × num pairs.                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition IdRays_def :
  IdRays (Phi : constellation) : (num # num) set =
    { (i, j) | i < LENGTH Phi /\ j < LENGTH (EL i Phi) }
End

Definition pm_IdRays_def :
  pm_IdRays (Phi : constellation) : (num # num) set =
    { (i, j) | (i, j) IN IdRays Phi /\
               is_coloured (case EL j (EL i Phi) of
                              App h _ => h
                            | Var _   => 0) }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.10  Dependency graph  D[Phi;C]                                          *)
(*                                                                             *)
(* Vertices: star indices {0, ..., LENGTH Phi - 1} ≅ INR 0, ..., INR (n-1).  *)
(* Edges   : { {INR i, INR j} | i < j  /\  stars_dep C (EL i Phi) (EL j Phi) *)
(*                            /\  i < LENGTH Phi /\ j < LENGTH Phi }.         *)
(*                                                                             *)
(* We build D[Phi;C] as an fsgraph by:                                         *)
(*  1. Adding nodes INR 0 .. INR (n-1) via fsgAddNodes.                        *)
(*  2. Adding edges via fsgAddEdges from the set of unordered pairs above.     *)
(*                                                                             *)
(* D[Phi] = D[Phi; ⋃_{(i,j) ∈ IdRays} colours(EL j (EL i Phi))]             *)
(*        = D[Phi; all colours appearing in Phi].                              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Node set of D[Phi;C]: all valid star-index embeddings. *)
Definition dep_nodes_def :
  dep_nodes (Phi : constellation) : (unit + num) set =
    IMAGE INR { i | i < LENGTH Phi }
End

(* Edge set of D[Phi;C]: unordered pairs {INR i, INR j} for dependent stars. *)
Definition dep_edges_def :
  dep_edges (Phi : constellation) (C : num set) :
      (unit + num) set set =
    { {INR i; INR j} |
      i < LENGTH Phi /\ j < LENGTH Phi /\ i <> j /\
      stars_dep C (EL i Phi) (EL j Phi) }
End

(* Auxiliary: add nodes {INR 0, ..., INR (n-1)} to a graph. *)
Definition add_star_nodes_def :
  add_star_nodes 0       G = G /\
  add_star_nodes (SUC n) G = fsgAddNode (INR n) (add_star_nodes n G)
End

(* §49.10  The dependency graph D[Phi;C].                                      *)
Definition dep_graph_def :
  dep_graph (Phi : constellation) (C : num set) : fsgraph =
    fsgAddEdges
      (dep_edges Phi C)
      (add_star_nodes (LENGTH Phi) emptyG)
End

(* §49.10  D[Phi] with all colours present in Phi.                             *)
Definition all_colours_def :
  all_colours (Phi : constellation) : num set =
    BIGUNION { colours (EL j (EL i Phi)) |
               i < LENGTH Phi /\ j < LENGTH (EL i Phi) }
End

Definition dep_graph_full_def :
  dep_graph_full (Phi : constellation) : fsgraph =
    dep_graph Phi (all_colours Phi)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.12  Adjacency set of a ray                                               *)
(*                                                                             *)
(* adj^C_Phi(i,j) = { i' | i' < LENGTH Phi /\ i' <> i /\                     *)
(*                          ?r'. MEM r' (EL i' Phi) /\                         *)
(*                               dep_edge_cond C (EL j (EL i Phi)) r' }       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition adj_C_def :
  adj_C (Phi : constellation) (C : num set) (i : num) (j : num) : num set =
    { i' | i' < LENGTH Phi /\ i' <> i /\
           ?r'. MEM r' (EL i' Phi) /\
                dep_edge_cond C (EL j (EL i Phi)) r' }
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.13  Degree of a ray                                                      *)
(*                                                                             *)
(* deg^C_Phi(i,j) = |adj^C_Phi(i,j)|                                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition deg_C_def :
  deg_C (Phi : constellation) (C : num set) (i : num) (j : num) : num =
    CARD (adj_C Phi C i j)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.12–14  Ray classification                                                *)
(*                                                                             *)
(* §49.12 free:        deg^C_Phi(i,j) = 0                                     *)
(* §49.13 deterministic: deg^C_Phi(i,j) = 1                                   *)
(* §49.14 branching:   deg^C_Phi(i,j) >= 2                                    *)
(* §49.14 co-branching: (i,j) is adjacent to a branching ray                  *)
(*   i.e., ∃i' r'. MEM r' (EL i' Phi) /\ dep_edge_cond C (EL j (EL i Phi)) r'*)
(*                /\ deg^C_Phi(i', INDEX r' (EL i' Phi)) >= 2                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition ray_free_def :
  ray_free (Phi : ray list list) (C : num set) (i : num) (j : num) <=>
    i < LENGTH Phi /\ j < LENGTH (EL i Phi) /\
    deg_C Phi C i j = 0
End

Definition ray_det_def :
  ray_det (Phi : ray list list) (C : num set) (i : num) (j : num) <=>
    i < LENGTH Phi /\ j < LENGTH (EL i Phi) /\
    deg_C Phi C i j = 1
End

Definition ray_branch_def :
  ray_branch (Phi : ray list list) (C : num set) (i : num) (j : num) <=>
    i < LENGTH Phi /\ j < LENGTH (EL i Phi) /\
    deg_C Phi C i j >= 2
End

(* co-branching: the ray at (i,j) is adjacent to at least one branching ray.
   We identify the "other" ray by its star index i' and its position in that
   star; we use INDEX to find the first occurrence.                           *)
Definition ray_cobranch_def :
  ray_cobranch (Phi : ray list list) (C : num set) (i : num) (j : num) <=>
    i < LENGTH Phi /\ j < LENGTH (EL i Phi) /\
    ?i'. i' IN adj_C Phi C i j /\
         ?j'. j' < LENGTH (EL i' Phi) /\
              ray_branch Phi C i' j'
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* Basic sanity: degree is finite                                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaDiagram.03]:
   GOAL:   !Phi C i j. FINITE (adj_C Phi C i j)
   STRATEGY: adj_C is a subset of {i' | i' < LENGTH Phi}, which is
             FINITE (by FINITE_COUNT or similar).  SUBSET_FINITE.
   DRAFT-TACTICS:
     rw [adj_C_def] >>
     irule SUBSET_FINITE >>
     qexists_tac `{ i' | i' < LENGTH Phi }` >>
     simp [FINITE_COUNT_EQ, SUBSET_DEF]
*)
Theorem FINITE_adj_C :
  !Phi C i j. FINITE (adj_C Phi C i j)
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* Sanity: every ray in bounds is exactly one of free/det/branching            *)
(*                                                                             *)
(* This follows from the fact that deg_C is a natural number,                 *)
(* so deg = 0 \/ deg = 1 \/ deg >= 2.                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem ray_class_partition :
  !Phi C i j.
    i < LENGTH Phi /\ j < LENGTH (EL i Phi) ==>
    ray_free Phi C i j \/ ray_det Phi C i j \/ ray_branch Phi C i j
Proof
  rw [ray_free_def, ray_det_def, ray_branch_def] >> decide_tac
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.10  Adjacency in D[Phi;C] corresponds to stars_dep                      *)
(*                                                                             *)
(* Theorem: for valid indices i <> j,                                          *)
(*   adjacent (dep_graph Phi C) (INR i) (INR j)                                *)
(*   <=> stars_dep C (EL i Phi) (EL j Phi)                                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(*
   PROOF-OBLIGATION[stellaDiagram.04]:
   GOAL:
     !Phi C i j.
       i < LENGTH Phi /\ j < LENGTH Phi /\ i <> j ==>
       (adjacent (dep_graph Phi C) (INR i) (INR j) <=>
        stars_dep C (EL i Phi) (EL j Phi))
   STRATEGY:
     Unfold dep_graph_def, fsgAddEdges, adjacent_fsg, fsgedges_fsgAddEdges_thm.
     An edge {INR i, INR j} is in dep_edges iff stars_dep (by dep_edges_def).
     The symmetry case i<j / j<i is handled by stars_dep_sym.
   DRAFT-TACTICS:
     rw [dep_graph_def, adjacent_fsg, fsgedges_fsgAddEdges_thm,
         dep_edges_def, stars_dep_sym] >>
     simp [INSERT2_lemma, PULL_EXISTS] >>
     metis_tac [stars_dep_sym]
*)
Theorem dep_graph_adjacent :
  !Phi C i j.
    i < LENGTH Phi /\ j < LENGTH Phi /\ i <> j ==>
    (adjacent (dep_graph Phi C) (INR i) (INR j) <=>
     stars_dep C (EL i Phi) (EL j Phi))
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY EXAMPLE 1: tiny constellation with one dependency edge               *)
(*                                                                             *)
(*   Phi = [ [+c(X)], [-c(0)] ]                                               *)
(*   C   = {0}  (the name of c is 0)                                           *)
(*                                                                             *)
(* Star 0: one ray r0 = +c(X) = App (encode_psym (Pos, 0)) [Var 0]           *)
(* Star 1: one ray r1 = -c(0) = App (encode_psym (Neg, 0)) [App 0 []]        *)
(*         (App 0 [] is the numeral-0 constant, head 0 = encode of Neutral/0) *)
(*                                                                             *)
(* Expected:                                                                   *)
(*   · colours(r0) = {0} ⊆ C                                                  *)
(*   · colours(r1) = {0} ⊆ C  (head Neg-0, name=0; sub-term App 0 [] is     *)
(*                               neutral at name 0, so colours(App 0 [])=∅   *)
(*                               since Neutral is uncoloured)                  *)
(*   · compat_enc(encode_psym(Pos,0))(encode_psym(Neg,0)) = T                *)
(*   · Hence dep_edge_cond C r0 r1 = T                                        *)
(*   · Hence D[Phi;C] has exactly one edge {INR 0, INR 1}                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition tiny_r0_def :
  tiny_r0 : ray = App (encode_psym (Pos, 0)) [Var 0]
End

Definition tiny_r1_def :
  tiny_r1 : ray = App (encode_psym (Neg, 0)) [App 0 []]
End

Definition tiny_Phi_def :
  tiny_Phi : constellation = [[tiny_r0]; [tiny_r1]]
End

Definition tiny_C_def :
  tiny_C : num set = {0}
End

(* colours of tiny_r0.
   encode_psym (Pos, 0) = 3*0+0 = 0.
   decode_psym 0 = (Pos, 0).  is_coloured 0 = T.  sym_name 0 = 0.
   colours_list [Var 0] = {}.
   colours tiny_r0 = {0} ∪ {} = {0}.
   Proof: unfold colours_eqns, is_coloured_def, sym_name_def, encode_psym,
          decode_psym, decode_pol, pol_code.                                  *)
(*
   PROOF-OBLIGATION[stellaDiagram.09]:
   GOAL:   colours tiny_r0 = {0}
   STRATEGY: simp with colours_eqns, is_coloured_def, sym_name_def,
             encode_psym_def, decode_psym_def, decode_pol_def, pol_code_def,
             tiny_r0_def.  This is a pure computation.
   DRAFT-TACTICS:
     simp [tiny_r0_def, colours_eqns, is_coloured_def, sym_name_def,
           encode_psym_def, decode_psym_def, decode_pol_def, pol_code_def]
*)
Theorem tiny_colours_r0 :
  colours tiny_r0 = {0}
Proof
  cheat
QED

(* colours of tiny_r1.
   encode_psym (Neg, 0) = 3*0+1 = 1. decode_psym 1 = (Neg, 0). is_coloured 1 = T.
   Sub-term App 0 []: encode head 0 = Pos/0 => is_coloured T, sym_name = 0.
   colours tiny_r1 = {0} ∪ ({0} ∪ {}) = {0}.                                 *)
(*
   PROOF-OBLIGATION[stellaDiagram.10]:
   GOAL:   colours tiny_r1 = {0}
   STRATEGY: same as stellaDiagram.09, unfolding colours_eqns + encoding defs.
   DRAFT-TACTICS:
     simp [tiny_r1_def, colours_eqns, is_coloured_def, sym_name_def,
           encode_psym_def, decode_psym_def, decode_pol_def, pol_code_def]
*)
Theorem tiny_colours_r1 :
  colours tiny_r1 = {0}
Proof
  cheat
QED

(* Closed computation: compat_enc of the two heads. *)
Theorem tiny_compat_enc :
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 0)) = T
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

(* alpha_unifiable tiny_r0 tiny_r1:
   We witness sigma = FEMPTY |+ (0, App 0 []).
   After even-rename: App (enc(Pos,0)) [Var 0]  (Var 0 maps to Var 0 since 2*0=0).
   After odd-rename:  App (enc(Neg,0)) [App 0 []] (no Vars, unchanged).
   MM run:
     Open:    compat_enc(Pos,0)(Neg,0)=T, arities match 1=1.
              Problem becomes [(Var 0, App 0 [])].
     Replace: 0 NOTIN vars_t(App 0 []) = {} ✓.
              Problem becomes [] (with sigma = {0 -> App 0 []}).
   This is NOT a closed EVAL computation (mm_reduces uses RTC),
   so we defer it.                                                             *)
(*
   PROOF-OBLIGATION[stellaDiagram.05]:
   GOAL:   alpha_unifiable tiny_r0 tiny_r1
   STRATEGY: Unfold alpha_unifiable_def; provide sigma = FEMPTY |+ (0, App 0 []).
             Run two mm_steps: Open then Replace.
             Show vars_t (App 0 []) = {} (so 0 NOTIN vars_t (App 0 [])).
   DRAFT-TACTICS:
     rw [alpha_unifiable_def] >>
     qexists_tac `FEMPTY |+ (0, App 0 [])` >>
     rw [mm_reduces_def] >>
     (* Open step *)
     irule RTC_TRANS >>
     qexists_tac `(FEMPTY, [(Var 0, App 0 [])])` >>
     conj_tac >| [
       rw [Once mm_step_cases, tiny_r0_def, tiny_r1_def,
           alpha_rename_def, vars_def, subst_def, FUN_FMAP_DEF,
           FINITE_vars, compat_enc_def, encode_decode, compat_sym_def],
       (* Replace step *)
       irule RTC_SINGLE >>
       rw [Once mm_step_cases, vars_def, FDOM_FEMPTY]
     ]
*)
Theorem tiny_alpha_unifiable :
  alpha_unifiable tiny_r0 tiny_r1
Proof
  cheat
QED

Theorem tiny_matchable :
  matchable tiny_r0 tiny_r1
Proof
  simp [matchable_def, tiny_r0_def, tiny_r1_def,
        compat_enc_def, encode_decode, compat_sym_def, tiny_alpha_unifiable]
QED

(* dep_edge_cond holds between r0 and r1. *)
Theorem tiny_dep_edge_cond :
  dep_edge_cond tiny_C tiny_r0 tiny_r1
Proof
  simp [dep_edge_cond_def, tiny_matchable, tiny_colours_r0, tiny_colours_r1,
        tiny_C_def, SUBSET_DEF]
QED

(*
   PROOF-OBLIGATION[stellaDiagram.11]:
   GOAL:   stars_dep tiny_C (EL 0 tiny_Phi) (EL 1 tiny_Phi)
   STRATEGY: Witnesses tiny_r0 and tiny_r1; follows from tiny_dep_edge_cond.
   DRAFT-TACTICS:
     rw [stars_dep_def, tiny_Phi_def] >>
     map_every qexists_tac [`tiny_r0`, `tiny_r1`] >>
     simp [tiny_dep_edge_cond]
*)
Theorem tiny_stars_dep :
  stars_dep tiny_C (EL 0 tiny_Phi) (EL 1 tiny_Phi)
Proof
  cheat
QED

(* There is exactly one edge in dep_edges tiny_Phi tiny_C. *)
(*
   PROOF-OBLIGATION[stellaDiagram.06]:
   GOAL:   dep_edges tiny_Phi tiny_C = { {INR 0; INR 1} }
   STRATEGY: Unfold dep_edges_def; LENGTH tiny_Phi = 2; the only pair with
             i < j < 2 and i <> j is (0,1).  stars_dep tiny_C (EL 0 ..)(EL 1 ..)
             = T by tiny_stars_dep.  stars_dep for (1,0) = T by stars_dep_sym,
             but the edge set uses {INR 0; INR 1} = {INR 1; INR 0}, so it is
             the same element.  Expand and simplify.
   DRAFT-TACTICS:
     rw [dep_edges_def, tiny_Phi_def, Once EXTENSION] >>
     simp [INSERT2_lemma, PULL_EXISTS] >>
     rw [EQ_IMP_THM] >>
     ... (case analysis on i, j < 2 and i <> j) ...
     metis_tac [tiny_stars_dep, stars_dep_sym]
*)
Theorem tiny_dep_edges_sing :
  dep_edges tiny_Phi tiny_C = { {INR 0; INR 1} }
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY EXAMPLE 2: deterministic vs free ray                                  *)
(*                                                                             *)
(*   Psi = [ [+c(X)], [-c(Y)], [n(Z)] ]  (n = neutral symbol, name 1)        *)
(*   C   = {0}   (colour set contains only name 0 = c)                        *)
(*                                                                             *)
(* · +c(X) in star 0 is compatible with -c(Y) in star 1.                     *)
(*   colours(+c(X)) = {0} ⊆ C; colours(-c(Y)) = {0} ⊆ C.                    *)
(*   => dep_edge_cond C (+c(X)) (-c(Y)) = T => adj_C Psi C 0 0 ⊇ {1}         *)
(* · n(Z) in star 2: compat_enc(encode(Neutral,1))(encode(Pos,0)) = F.        *)
(*   => no dep_edge with stars 0 or 1 => adj_C Psi C 2 0 = {}                *)
(*                                                                             *)
(* Expected:                                                                   *)
(*   · ray (0,0) = +c(X): det (deg = 1, adjacent to star 1 only)              *)
(*   · ray (2,0) = n(Z) : free (deg = 0)                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition det_r_pos_def :
  det_r_pos : ray = App (encode_psym (Pos, 0)) [Var 0]
End

Definition det_r_neg_def :
  det_r_neg : ray = App (encode_psym (Neg, 0)) [Var 1]
End

Definition det_r_neutral_def :
  det_r_neutral : ray = App (encode_psym (Neutral, 1)) [Var 2]
End

Definition det_Phi_def :
  det_Phi : constellation =
    [[det_r_pos]; [det_r_neg]; [det_r_neutral]]
End

Definition det_C_def :
  det_C : num set = {0}
End

(* compat_enc of neutral vs pos. *)
Theorem det_neutral_not_compat_pos :
  compat_enc (encode_psym (Neutral, 1)) (encode_psym (Pos, 0)) = F
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

(* compat_enc of neutral vs neg. *)
Theorem det_neutral_not_compat_neg :
  compat_enc (encode_psym (Neutral, 1)) (encode_psym (Neg, 0)) = F
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

(* Hence the neutral ray is not matchable with any ray in stars 0 or 1.
   Not matchable => not dep_edge_cond => adj_C Psi C 2 0 = {}.               *)
(*
   PROOF-OBLIGATION[stellaDiagram.07]:
   GOAL:   adj_C det_Phi det_C 2 0 = {}
   STRATEGY: Unfold adj_C_def; LENGTH det_Phi = 3, so i' ranges over {0,1,2}.
             i' = 2 excluded by i' <> i = 2.
             For i' = 0: dep_edge_cond det_C det_r_neutral det_r_pos =
               matchable det_r_neutral det_r_pos.
               matchable requires compat_enc(Neutral,1)(Pos,0) = F => matchable = F.
             For i' = 1: similarly compat_enc(Neutral,1)(Neg,0) = F => F.
             So adj_C = {} (empty set).
   DRAFT-TACTICS:
     rw [adj_C_def, det_Phi_def, dep_edge_cond_def, matchable_def,
         det_r_neutral_def, det_r_pos_def, det_r_neg_def,
         det_neutral_not_compat_pos, det_neutral_not_compat_neg] >>
     simp [EXTENSION]
*)
Theorem det_neutral_adj_empty :
  adj_C det_Phi det_C 2 0 = {}
Proof
  cheat
QED

Theorem det_neutral_ray_free :
  ray_free det_Phi det_C 2 0
Proof
  simp [ray_free_def, deg_C_def, det_neutral_adj_empty, det_Phi_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* SANITY EXAMPLE 3: Branching ray                                              *)
(*                                                                             *)
(*   Xi = [ [+c(X)], [-c(0)], [-c(1)] ]                                      *)
(*   C  = {0}                                                                  *)
(*                                                                             *)
(* Ray (0,0) = +c(X): compatible with -c(0) in star 1 AND -c(1) in star 2.   *)
(* => adj_C Xi C 0 0 ⊇ {1, 2} => deg >= 2 => branching.                      *)
(* We state this as a proof obligation.                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition branch_Phi_def :
  branch_Phi : constellation =
    [ [App (encode_psym (Pos, 0)) [Var 0]] ;
      [App (encode_psym (Neg, 0)) [App 0 []]] ;
      [App (encode_psym (Neg, 0)) [App 1 []]] ]
End

Definition branch_C_def :
  branch_C : num set = {0}
End

(*
   PROOF-OBLIGATION[stellaDiagram.08]:
   GOAL:   ray_branch branch_Phi branch_C 0 0
   STRATEGY: Show {1, 2} ⊆ adj_C branch_Phi branch_C 0 0,
             so CARD >= 2.  For each i' in {1,2}: provide the matching ray
             and show matchable holds (compat_enc(Pos,0)(Neg,0) = T,
             and alpha_unifiable by MM run).
   DRAFT-TACTICS:
     rw [ray_branch_def, deg_C_def, branch_Phi_def] >>
     `{1; 2} ⊆ adj_C branch_Phi branch_C 0 0` by
       (rw [adj_C_def, branch_Phi_def, dep_edge_cond_def, matchable_def,
            compat_enc_def, encode_decode, compat_sym_def] >>
        ... alpha_unifiable witnesses ...) >>
     `CARD (adj_C branch_Phi branch_C 0 0) >= 2` by
       (... subset_card ...) >>
     omega
*)
Theorem branch_ray_is_branching :
  ray_branch branch_Phi branch_C 0 0
Proof
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* PROOF-DEBT LEDGER                                                            *)
(*                                                                              *)
(* stellaDiagram.01  dep_edge_cond_sym                                          *)
(*   dep_edge_cond C r r' = dep_edge_cond C r' r                               *)
(*   (matchable_sym + UNION_COMM)                                               *)
(*                                                                              *)
(* stellaDiagram.02  stars_dep_sym                                              *)
(*   stars_dep C s1 s2 = stars_dep C s2 s1                                     *)
(*   (dep_edge_cond_sym + swap existential witnesses)                           *)
(*                                                                              *)
(* stellaDiagram.03  FINITE_adj_C                                               *)
(*   FINITE (adj_C Phi C i j)                                                   *)
(*   (adj_C ⊆ {i' | i' < LENGTH Phi} = count n, which is FINITE)              *)
(*                                                                              *)
(* stellaDiagram.04  dep_graph_adjacent                                         *)
(*   adjacent (dep_graph Phi C) (INR i) (INR j) <=> stars_dep C (EL i Phi) (EL j Phi)  *)
(*   (unfold fsgAddEdges + dep_edges_def + adjacent_fsg + stars_dep_sym)       *)
(*                                                                              *)
(* stellaDiagram.05  tiny_alpha_unifiable                                       *)
(*   alpha_unifiable tiny_r0 tiny_r1                                            *)
(*   (witness sigma = {0 -> App 0 []}; two-step MM: Open then Replace)         *)
(*                                                                              *)
(* stellaDiagram.06  tiny_dep_edges_sing                                        *)
(*   dep_edges tiny_Phi tiny_C = { {INR 0; INR 1} }                            *)
(*   (unique pair (i,j) with i<j<2 and stars_dep; case analysis)               *)
(*                                                                              *)
(* stellaDiagram.07  det_neutral_adj_empty                                      *)
(*   adj_C det_Phi det_C 2 0 = {}                                               *)
(*   (compat_enc(Neutral,1)(Pos/Neg,0) = F => matchable = F for all i')        *)
(*                                                                              *)
(* stellaDiagram.08  branch_ray_is_branching                                    *)
(*   ray_branch branch_Phi branch_C 0 0                                         *)
(*   (show {1,2} ⊆ adj_C; alpha_unifiable witnesses; CARD >= 2)               *)
(*                                                                              *)
(* stellaDiagram.09  tiny_colours_r0                                            *)
(*   colours tiny_r0 = {0}                                                      *)
(*   (simp with colours_eqns + encoding defs; pure computation)                *)
(*                                                                              *)
(* stellaDiagram.10  tiny_colours_r1                                            *)
(*   colours tiny_r1 = {0}                                                      *)
(*   (same as .09; App 0 [] also has is_coloured T since encode(Pos,0)=0)      *)
(*                                                                              *)
(* stellaDiagram.11  tiny_stars_dep                                             *)
(*   stars_dep tiny_C (EL 0 tiny_Phi) (EL 1 tiny_Phi)                          *)
(*   (witnesses tiny_r0, tiny_r1; follows from tiny_dep_edge_cond)             *)
(*                                                                              *)
(* INHERITED PROOF-DEBT (from stellaMatchScript):                               *)
(*   alpha_unifiable_sym — perm + swap_all argument (see stellaMatchScript.sml) *)
(*   matchable_sym relies on alpha_unifiable_sym (cheat-passed through)        *)
(*                                                                              *)
(* NEXT STEPS (not even stated here):                                           *)
(*   stellaDiagram.12+  Diagrams (sequences of constellations) — Ch.10         *)
(*   stellaDiagram.13+  Prob(delta) probability measure — Ch.10                *)
(*   stellaDiagram.14+  AEx (associativity exchange) — Ch.10                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val _ = export_theory ();
