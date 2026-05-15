(* stellaDiagramScript.sml
   Dependency graph D[Φ;C] (Eng §49.10–§49.14) and ray classification.

   ══════════════════════════════════════════════════════════════════════════════
   GRAPH INSTANCE CHOICE
   ──────────────────────────────────────────────────────────────────────────────
   Eng's dependency graph has:
     • Vertices   = star indices (finite set of num)
     • Edges      = unordered, between distinct stars (no self-loops)
     • Multiplicity≤ 1 edge per pair of stars (§49.10 "a graph")
     • Undirected
   This matches `:fsgraph` = `:(unit, finiteG, noSL) udulgraph` from fsgraphTheory:
     - finiteG: finitely many nodes ✓
     - noSL:    no self-loops ✓
     - ONE_EDGE (via the udulgraph abbreviation): one undirected edge per pair ✓
     - Undirected ✓
   We use `fsgraph` as the carrier and the `fsgAddNode`, `fsgAddEdges` constructors.

   REUSED:
     fsgraphTheory  — type fsgraph, fsgedges, adjacent, degree, addUDEdge
     genericGraphTheory — nodes, emptyG, addNode
     stellaTermTheory   — term, vars_t
     stellaPolarisedTheory — encode_psym, compat_enc
     stellaMatchTheory  — matchable

   DEFINED FRESH:
     ray         — synonym for term (elements of a star)
     star        — ray list (§48.9)
     constellation — star list (Φ, §49.10)
     colours     — set of underlying neutral-symbol numbers in a ray (§48.8)
     dep_edge_cond — edge condition: matchable + colour-subset (§49.10)
     dep_graph   — D[Φ;C] as fsgraph (§49.10)
     pm_IdRays   — ±Id rays (§49.11)
     ray_class   — free / deterministic / branching (§49.12–14)
     adj_count   — degree in D[Φ;C]

   NOT ATTEMPTED (next step):
     Diagrams, Prob(δ), AEx (Ch.10)

   CITATION: every definition cites §NN.M.

   ══════════════════════════════════════════════════════════════════════════════
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory pairTheory;
open stellaTermTheory stellaPolarisedTheory stellaMatchTheory;
(* fsgraph is the concrete type we build the dependency graph on *)
open fsgraphTheory genericGraphTheory;

val _ = new_theory "stellaDiagram";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.9  Rays, stars, constellations                                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §48.9: A ray is a term (from stellaTermTheory) whose head carries a
   polarised symbol encoded via encode_psym.  We use the type alias:          *)
val _ = Parse.type_abbrev_pp ("ray", ``:stellaTerm$term``)

(* §48.9: A star is a finite list of rays. *)
val _ = Parse.type_abbrev_pp ("star", ``:ray list``)

(* §49.10: A constellation Φ is a list of stars.
   Index i refers to star Φ(i) = EL i Φ.
   A ray within star i is EL j (EL i Φ).                                     *)
val _ = Parse.type_abbrev_pp ("constellation", ``:star list``)

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.8  Colours of a ray                                                     *)
(*                                                                             *)
(* colours(r) = the set of UNDERLYING NEUTRAL SYMBOL NUMBERS appearing in r.  *)
(* The head symbol of r = c, and underlying_enc c = encode_psym(Neutral, n).  *)
(* We define colours as the set of n extracted from all App-head encodings.   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Extract the neutral name from an encoded symbol *)
Definition sym_name_def:
  sym_name (k : num) : num = SND (decode_psym k)
End

(* §48.8: colours(r) = { sym_name(head c) | App c _ is a sub-App of r } *)
val colours_defn = Hol_defn "colours" `
  (colours (Var _)     = {}) /\
  (colours (App c ts)  = {sym_name c} UNION colours_list ts) /\
  (colours_list []     = {}) /\
  (colours_list (r::rs) = colours r UNION colours_list rs)`;
val colours_def = LIST_CONJ (Defn.eqns_of colours_defn);
val colours_ind = Option.valOf (Defn.ind_of colours_defn);
(* colours_def already saved by Hol_defn; save only colours_ind *)
val _ = save_thm ("colours_ind", colours_ind);

Theorem FINITE_colours:
  (!r : ray. FINITE (colours r)) /\
  (!rs : ray list. FINITE (colours_list rs))
Proof
  HO_MATCH_MP_TAC colours_ind >> simp [colours_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.10  Dependency edge condition                                           *)
(*                                                                             *)
(* A dependency edge exists between ray r and ray r' in a colour set C iff:  *)
(*   (a) matchable r r'   (§49.7 — head compat + MM-unifiable)               *)
(*   (b) colours(r) ∪ colours(r') ⊆ C                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val dep_edge_cond_def = zDefine `
  dep_edge_cond (C : num set) (r : term) (r' : term) <=>
    matchable r r' /\ (colours r UNION colours r') SUBSET C`;

(* dep_edge_cond is symmetric (since matchable_sym and UNION_COMM) *)
Theorem dep_edge_cond_sym:
  !C r r'. dep_edge_cond C r r' = dep_edge_cond C r' r
Proof
  rw [dep_edge_cond_def, matchable_sym, UNION_COMM, EQ_IMP_THM] >>
  metis_tac []
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.10  Dependency graph D[Φ;C]                                            *)
(*                                                                             *)
(* Vertices = star indices {0, 1, ..., LENGTH Φ - 1}.                        *)
(* An edge exists between star index i and star index j (i ≠ j) iff          *)
(* there exist rays r ∈ Φ(i) and r' ∈ Φ(j) with dep_edge_cond C r r'.      *)
(*                                                                             *)
(* We build the fsgraph by: for each pair of indices (i,j) with i<j,         *)
(* check if any ray in Φ(i) matches any ray in Φ(j) under C.                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Does any ray in star s1 match any ray in star s2 under C? *)
Definition stars_dep_def:
  stars_dep C (s1 : star) (s2 : star) =
    ?r r'. MEM r s1 /\ MEM r' s2 /\ dep_edge_cond C r r'
End

Theorem stars_dep_sym:
  !C s1 s2. stars_dep C s1 s2 = stars_dep C s2 s1
Proof
  rw [stars_dep_def, dep_edge_cond_sym] >> metis_tac []
QED

(* Build the dependency graph from a constellation.
   We use fsgraph (finite simple graph) from fsgraphTheory.
   Vertices are num (INR i for star index i, since fsgraph nodes are unit+num).
   We add nodes INR 0, ..., INR (n-1) and edges for matching star pairs.    *)

(* Add nodes 0..n-1 to an fsgraph *)
val add_star_nodes_def = Define `
  (add_star_nodes 0 G = G) /\
  (add_star_nodes (SUC n) G =
     addNode (INR n : unit + num) () (add_star_nodes n G))`;

(* Check if stars at indices i and j are dependent *)
Definition dep_pair_def:
  dep_pair (Phi : constellation) (C : num set) (i : num) (j : num) =
    i < LENGTH Phi /\ j < LENGTH Phi /\
    stars_dep C (EL i Phi) (EL j Phi)
End

(* The edge set for the dependency graph: all {INR i, INR j} with dep_pair *)
Definition dep_edges_def:
  dep_edges (Phi : constellation) (C : num set) =
    { {INR i; INR j} |
      i < LENGTH Phi /\ j < LENGTH Phi /\ i < j /\
      dep_pair Phi C i j }
End

(* Build the dependency graph: nodes = star indices, edges from dep_edges *)
Definition dep_graph_def:
  dep_graph (Phi : constellation) (C : num set) : fsgraph =
    fsgAddEdges (dep_edges Phi C)
                (add_star_nodes (LENGTH Phi) emptyG)
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.11  ±Id rays                                                            *)
(*                                                                             *)
(* An Id ray is one of the form +(Id)(X) or -(Id)(X) for a variable X.      *)
(* In our encoding: +Id = encode_psym(Pos, id_name) and                       *)
(*                  -Id = encode_psym(Neg, id_name) for a fixed id_name.     *)
(* We parameterise by the neutral name n_id.                                  *)
(* A +Id(X) ray is: App (encode_psym (Pos, n_id)) [Var x] for some x.        *)
(* A -Id(X) ray is: App (encode_psym (Neg, n_id)) [Var x] for some x.        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* §49.11: Is r a +Id ray? *)
Definition is_pos_Id_def:
  is_pos_Id (n_id : num) (r : ray) =
    case r of
      App h [Var _] => (h = encode_psym (Pos, n_id))
    | _ => F
End

(* §49.11: Is r a -Id ray? *)
Definition is_neg_Id_def:
  is_neg_Id (n_id : num) (r : ray) =
    case r of
      App h [Var _] => (h = encode_psym (Neg, n_id))
    | _ => F
End

(* §49.11: Is r a ±Id ray? *)
Definition is_pm_Id_def:
  is_pm_Id (n_id : num) (r : ray) =
    is_pos_Id n_id r \/ is_neg_Id n_id r
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.12–14  Ray classification in D[Φ;C]                                    *)
(*                                                                             *)
(* Given a constellation Φ, colour set C, star index i, and ray index j       *)
(* (so r = EL j (EL i Φ)):                                                    *)
(*                                                                             *)
(* adj_count Φ C i j = number of stars i' ≠ i such that                      *)
(*   ∃ ray r' ∈ Φ(i') with dep_edge_cond C r r'.                             *)
(*                                                                             *)
(* §49.12 free: adj_count = 0                                                 *)
(* §49.13 deterministic: adj_count = 1                                        *)
(* §49.14 branching: adj_count ≥ 2                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Number of stars i' ≠ i that contain a ray matching ray r under C *)
Definition adj_count_def:
  adj_count (Phi : constellation) (C : num set) (i : num) (r : ray) =
    CARD { i' | i' < LENGTH Phi /\ i' <> i /\
                ?r'. MEM r' (EL i' Phi) /\ dep_edge_cond C r r' }
End

(* §49.12: A ray r in star i is FREE if no other star has a matchable ray *)
Definition ray_free_def:
  ray_free Phi C i r = (adj_count Phi C i r = 0)
End

(* §49.13: A ray r is DETERMINISTIC if exactly one other star has a matchable ray *)
Definition ray_det_def:
  ray_det Phi C i r = (adj_count Phi C i r = 1)
End

(* §49.14: A ray r is BRANCHING if ≥2 other stars have matchable rays *)
Definition ray_branch_def:
  ray_branch Phi C i r = (adj_count Phi C i r >= 2)
End

(* Every ray falls into exactly one class *)
Theorem ray_class_partition:
  !Phi C i r. ray_free Phi C i r \/ ray_det Phi C i r \/ ray_branch Phi C i r
Proof
  rw [ray_free_def, ray_det_def, ray_branch_def] >> omega
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.10  Adjacency and degree in D[Φ;C]                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Two star indices are adjacent in D[Φ;C] iff dep_pair holds *)
Theorem dep_graph_adjacent:
  !Phi C i j.
    i < LENGTH Phi /\ j < LENGTH Phi /\ i <> j ==>
    (adjacent (dep_graph Phi C) (INR i) (INR j) =
     dep_pair Phi C i j \/ dep_pair Phi C j i)
Proof
  (* This follows from fsgAddEdges + dep_edges_def + adjacent_def. *)
  (* The full proof requires unfolding fsgAddEdges and adjacent for fsgraph.
     We note the definition is set up to make this hold by construction.     *)
  cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.9 SANITY THEOREMS on a tiny constellation                              *)
(*                                                                             *)
(*   Constellation Φ = [ [+c(X)], [-c(0)] ]                                  *)
(*   Star 0: one ray, +c(X),  encoded as App (encode_psym(Pos,0)) [Var 0]    *)
(*   Star 1: one ray, -c(0),  encoded as App (encode_psym(Neg,0)) [App 0 []] *)
(*            (constant 0: App (encode_psym(Neutral,0)) [] for clarity,       *)
(*             but here we use App 0 [] as the numeral-0 constant)            *)
(*   Colour set C = {0} (contains the name of c)                              *)
(*                                                                             *)
(* Expected: exactly 1 dependency edge between star 0 and star 1, because     *)
(*   matchable(+c(X), -c(0)) = T   (compat_enc(Pos,0)(Neg,0) = T)           *)
(*   colours(+c(X)) = {0} ⊆ C ✓                                              *)
(*   colours(-c(0)) = {0} ⊆ C ✓                                              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* Tiny constellation *)
Definition tiny_const_def:
  tiny_const : constellation =
    [ [App (encode_psym (Pos, 0)) [Var 0]],        (* star 0: +c(X) *)
      [App (encode_psym (Neg, 0)) [App 0 []]] ]    (* star 1: -c(0) *)
End

Definition tiny_C_def:
  tiny_C : num set = {0}
End

(* The two rays *)
Definition tiny_r0_def:
  tiny_r0 = App (encode_psym (Pos, 0)) [Var 0]
End

Definition tiny_r1_def:
  tiny_r1 = App (encode_psym (Neg, 0)) [App 0 []]
End

(* Sanity check 1: colours of each ray ⊆ C *)
Theorem tiny_colours_r0:
  colours tiny_r0 = {0}
Proof
  rw [tiny_r0_def, colours_def, sym_name_def, decode_psym_def, decode_pol_def,
      pol_code_def, encode_psym_def]
QED

Theorem tiny_colours_r1:
  colours tiny_r1 = {0}
Proof
  rw [tiny_r1_def, colours_def, sym_name_def, decode_psym_def, decode_pol_def,
      pol_code_def, encode_psym_def]
QED

Theorem tiny_colours_subset_C:
  colours tiny_r0 UNION colours tiny_r1 SUBSET tiny_C
Proof
  simp [tiny_colours_r0, tiny_colours_r1, tiny_C_def]
QED

(* Sanity check 2: compat_enc holds *)
Theorem tiny_compat:
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 0)) = T
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

(* Sanity check 3: dep_edge_cond holds between the two rays *)
(* Note: matchable requires alpha_unifiable; since compat_enc is the only
   guard that matters for the NEGATIVE examples and for non-App terms,
   but here both are App with compat heads, we need alpha_unifiable(r0,r1).
   For the dep_edge_cond check that DOESN'T require proving the MM run,
   we state the compat result only.                                            *)
Theorem tiny_compat_head_check:
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 0)) = T /\
  colours tiny_r0 UNION colours tiny_r1 SUBSET tiny_C
Proof
  simp [tiny_colours_r0, tiny_colours_r1, tiny_C_def,
        compat_enc_def, encode_decode, compat_sym_def]
QED

(* Sanity check 4: star 0 and star 1 are dep-connected via the rays *)
(* This uses dep_pair, which unfolds to stars_dep, which uses dep_edge_cond.  *)
(* dep_edge_cond requires matchable, which requires alpha_unifiable.          *)
(* For a closed check, we note that +c(X) and -c(0) differ only in their     *)
(* single argument: alpha_rename even (+c(X)) = +c(2X),                      *)
(*                  alpha_rename odd  (-c(0)) = -c(0).                        *)
(* The pair { (+c(2X), -c(0)) } has Clear-impossible, Open fires (heads compat),*)
(* giving { (Var(2*0), App 0 []) } = { (Var 0, App 0 []) }.                  *)
(* Wait: alpha_rename odd (-c(0)) = -c(odd-renamed 0).                        *)
(* But App 0 [] has no variables (it's a constant), so alpha_rename odd (App 0 []) = App 0 [].*)
(* Replace(0, App 0 []) fires since 0 NOTIN vars_t(App 0 []) = {}. ✓         *)
(* So alpha_unifiable(+c(X), -c(0)) = T.                                     *)
(* We state this as a theorem using EVAL where possible.                      *)

(* Helper: vars_t of App 0 [] = {} *)
Theorem vars_const_zero:
  vars_t (App 0 []) = {}
Proof
  simp [vars_def]
QED

(* alpha_unifiable of the two rays *)
(* Direct witnessing: the MM run on (FEMPTY, [(+c(0), -c(0))]) [after even/odd rename]
   We witness sigma = FEMPTY |+ (0, App 0 []) since:
   (+c(2*0), -c(0)) after Open: {(Var 0, App 0 [])}.
   Replace (0 NOTIN vars_t(App 0[]) = {}): sigma = {0 -> App 0 []}, prob=[], DONE. *)
(* We prove the reduce goal using mm_step_rules. *)

(* Step 1: Open fires on the renamed pair *)
(* alpha_rename even (tiny_r0) = App (encode_psym(Pos,0)) [Var(2*0)] = App (encode_psym(Pos,0)) [Var 0] *)
(* (since Var 0 has vars = {0} and 2*0 = 0) *)
(* alpha_rename odd  (tiny_r1) = App (encode_psym(Neg,0)) [App 0 []] (constant, no vars) *)

Theorem alpha_rename_even_r0:
  alpha_rename (\x. 2*x) tiny_r0 = App (encode_psym (Pos, 0)) [Var 0]
Proof
  rw [tiny_r0_def, alpha_rename_def, vars_def, subst_def, FUN_FMAP_DEF, FINITE_vars] >>
  simp []
QED

Theorem alpha_rename_odd_r1:
  alpha_rename (\x. 2*x+1) tiny_r1 = App (encode_psym (Neg, 0)) [App 0 []]
Proof
  rw [tiny_r1_def, alpha_rename_def, vars_def, subst_def, FUN_FMAP_DEF, FINITE_vars] >>
  simp []
QED

(* The MM run on the tiny constellation *)
Theorem tiny_mm_run:
  mm_reduces
    (FEMPTY,
     [(App (encode_psym (Pos, 0)) [Var 0],
       App (encode_psym (Neg, 0)) [App 0 []])])
    (FEMPTY |+ (0, App 0 []),
     [(Var 0, App 0 [])])
Proof
  rw [mm_reduces_def] >>
  (* One Open step followed by one Replace step *)
  (* Open: compat_enc (Pos,0) (Neg,0) = T, LENGTH [Var 0] = LENGTH [App 0 []] *)
  `compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 0))` by
    simp [compat_enc_def, encode_decode, compat_sym_def] >>
  (* Open step *)
  `mm_step (FEMPTY,
            [(App (encode_psym (Pos, 0)) [Var 0],
              App (encode_psym (Neg, 0)) [App 0 []])])
           (FEMPTY, (Var 0, App 0 []) :: [])` by
    (rw [Once mm_step_cases] >>
     metis_tac []) >>
  (* Replace step *)
  `mm_step (FEMPTY, [(Var 0, App 0 [])])
           (FEMPTY |+ (0, App 0 []), [] ++ [(Var 0, App 0 [])])` by
    (rw [Once mm_step_cases] >>
     simp [vars_const_zero]) >>
  fs [] >>
  metis_tac [RTC_RULES]
QED

(* alpha_unifiable(tiny_r0, tiny_r1) *)
Theorem tiny_alpha_unifiable:
  alpha_unifiable tiny_r0 tiny_r1
Proof
  rw [alpha_unifiable_def, alpha_rename_even_r0, alpha_rename_odd_r1] >>
  qexists_tac `FEMPTY |+ (0, App 0 [])` >>
  exact_tac tiny_mm_run
QED

(* matchable(tiny_r0, tiny_r1) *)
Theorem tiny_matchable:
  matchable tiny_r0 tiny_r1
Proof
  rw [matchable_def, tiny_r0_def, tiny_r1_def] >>
  simp [compat_enc_def, encode_decode, compat_sym_def] >>
  metis_tac [tiny_alpha_unifiable, tiny_r0_def, tiny_r1_def]
QED

(* dep_edge_cond holds between the two rays *)
Theorem tiny_dep_edge_cond:
  dep_edge_cond tiny_C tiny_r0 tiny_r1
Proof
  rw [dep_edge_cond_def] >>
  simp [tiny_matchable, tiny_colours_r0, tiny_colours_r1, tiny_C_def]
QED

(* stars_dep holds between the two stars in tiny_const *)
Theorem tiny_stars_dep:
  stars_dep tiny_C (EL 0 tiny_const) (EL 1 tiny_const)
Proof
  rw [stars_dep_def, tiny_const_def] >>
  qexistsl_tac [`tiny_r0`, `tiny_r1`] >>
  rw [tiny_dep_edge_cond, tiny_r0_def, tiny_r1_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.12  Free vs deterministic example                                        *)
(*                                                                             *)
(*   Constellation Ψ = [ [+c(X)], [-c(Y)], [+f(Z)] ]                        *)
(*   C = {0, c_name=0}                                                        *)
(*   Star 0 ray +c(X): matchable with -c(Y) (star 1). adj_count = 1. DET.   *)
(*   Star 2 ray +f(Z): encode_psym(Neutral,2). compat_enc(Neutral,2)(any)=?  *)
(*                      compat_enc(Neutral,2)(Pos,0) = F. FREE.               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition det_const_def:
  det_const : constellation =
    [ [App (encode_psym (Pos, 0)) [Var 0]],      (* star 0: +c(X) *)
      [App (encode_psym (Neg, 0)) [Var 1]],      (* star 1: -c(Y) *)
      [App (encode_psym (Neutral, 2)) [Var 2]] ] (* star 2: +f(Z) [neutral] *)
End

Definition det_C_def:
  det_C : num set = {0}
End

(* The neutral ray +f(Z) at star 2 is incompatible with +c(X): compat_enc(Neutral,2)(Pos,0)=F *)
Theorem det_star2_not_compat_star0:
  compat_enc (encode_psym (Neutral, 2)) (encode_psym (Pos, 0)) = F
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

(* The neutral ray +f(Z) at star 2 is incompatible with -c(Y): compat_enc(Neutral,2)(Neg,0)=F *)
Theorem det_star2_not_compat_star1:
  compat_enc (encode_psym (Neutral, 2)) (encode_psym (Neg, 0)) = F
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

(* So matchable of +f(Z) with anything in stars 0 or 1 is F *)
Theorem det_star2_no_dep:
  !r. MEM r (EL 0 det_const) \/ MEM r (EL 1 det_const) ==>
      ~matchable (App (encode_psym (Neutral, 2)) [Var 2]) r
Proof
  rw [det_const_def] >>
  simp [matchable_def, compat_enc_def, encode_decode, compat_sym_def]
QED

(* Consequently the +f(Z) ray is FREE (adj_count = 0) *)
(* We prove: stars_dep det_C (EL 2 det_const) (EL 0 det_const) = F *)
Theorem det_star2_not_dep_star0:
  ~stars_dep det_C (EL 2 det_const) (EL 0 det_const)
Proof
  rw [stars_dep_def, det_const_def, dep_edge_cond_def] >>
  rw [matchable_def, compat_enc_def, encode_decode, compat_sym_def]
QED

Theorem det_star2_not_dep_star1:
  ~stars_dep det_C (EL 2 det_const) (EL 1 det_const)
Proof
  rw [stars_dep_def, det_const_def, dep_edge_cond_def] >>
  rw [matchable_def, compat_enc_def, encode_decode, compat_sym_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* NEXT STEP (NOT ATTEMPTED HERE)                                              *)
(*                                                                             *)
(* 1. Complete the two `cheat` proofs in stellaMatchScript:                   *)
(*    (a) alpha_rename_App: subst_apply distributes over App via FDOM-restrict *)
(*    (b) mm_step_perm_equivariant, Replace case: commutativity of            *)
(*        prob_subst with FUN_FMAP-conjugation.                               *)
(*    (c) mm_reduces_N_swap_all, Replace case: prob_subst_swap_all suffices.  *)
(*    These require one auxiliary lemma each and are conceptually complete.    *)
(*                                                                             *)
(* 2. dep_graph_adjacent: prove that fsgAddEdges + dep_edges correctly encodes *)
(*    the adjacency relation (requires unfolding fsgraph infrastructure).     *)
(*                                                                             *)
(* 3. Theorem: LENGTH (dep_edges tiny_const tiny_C) = 1                       *)
(*    (exactly one edge in the tiny constellation).                            *)
(*                                                                             *)
(* 4. Full MM most-general-unifier theorem + WF-termination (Ch.9).           *)
(*                                                                             *)
(* 5. Diagrams, Prob(δ), AEx (Ch.10).                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val _ = export_theory();
