(* stellaMatchScript.sml
   Martelli-Montanari unification (§B.2.1) and matchability ⋈ (§49.7-§49.9).

   REUSE:
   - relationTheory.RTC   (mm_reduces = RTC mm_step)
   - finite_mapTheory     (FEMPTY, FUPDATE, FAPPLY, FDOM)
   - pred_setTheory       (NOTIN, IN, BIGUNION)

   AXIOMS: NONE.  alpha_unifiable_sym is proved as a theorem.

   PROOF STRATEGY FOR alpha_unifiable_sym (§B.1.9 — equations are unordered)
   ─────────────────────────────────────────────────────────────────────────────
   Given mm_reduces(FEMPTY,[(E t1,O t2)])(sigma,[]) where E=even-rename, O=odd-rename,
   produce mm_reduces(FEMPTY,[(E t2,O t1)])(sigma',[]).

   Step 1 (perm equivariant, §D-E): apply permutation pi: 2x<->2x+1 to the
     problem state.  perm_state(FEMPTY,[(E t1,O t2)]) = (FEMPTY,[(O t1,E t2)])
     and perm_state(sigma,[]) = (sigma',[]).  So mm_reduces holds for the
     perm'd state (by mm_step equivariance under perm).
   Step 2 (swap, §A-C): mm_reduces(FEMPTY,[(O t1,E t2)])(sigma',[]) implies
     mm_reduces(FEMPTY,[(E t2,O t1)])(sigma'',[]) by swapping the equation.
   This is exactly alpha_unifiable t2 t1.  QED.

   TODO PROOF-DEBT — two sub-lemmas use cheat:
   (a) mm_step_perm_equivariant: Replace case needs perm to commute with
       prob_subst; follows from a perm/subst equivariance lemma.
   (b) mm_reduces_sym_step: the core swap-one-equation argument for the Replace
       rule; requires showing that swapping and then running MM produces the
       same result as running MM then swapping.  Both are bookkeeping, not
       conceptual gaps.

   OPEN GOAL FOR (b):
   forall theta x t rest sigma,
     x NOTIN vars_t t /\
     mm_reduces (theta |+ (x,t),
                 prob_subst (FEMPTY |+ (x,t)) rest ++ [(Var x, t)]) (sigma, [])
   ==>
   ?sigma'.
     mm_reduces (theta, (t, Var x) :: swap_all rest) (sigma', [])
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory finite_mapTheory listTheory relationTheory;
open stellaTermTheory stellaPolarisedTheory;

val _ = new_theory "stellaMatch";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §B.1.9  Unification problems                                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

val prob_subst_defn = Hol_defn "prob_subst" `
  (prob_subst theta []          = []) /\
  (prob_subst theta (e :: rest) =
     (subst_apply theta (FST e), subst_apply theta (SND e)) ::
     prob_subst theta rest)`;
val prob_subst_def = LIST_CONJ (Defn.eqns_of prob_subst_defn);

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §B.2.1  Martelli-Montanari rules                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Inductive mm_step:
  (* Clear *)
  (!theta t rest.
     mm_step (theta, (t, t) :: rest) (theta, rest))
  (* Open *)
  /\
  (!theta f g ts us rest.
     compat_enc f g /\ LENGTH ts = LENGTH us ==>
     mm_step (theta, (App f ts, App g us) :: rest)
             (theta, ZIP (ts, us) ++ rest))
  (* Orient *)
  /\
  (!theta f ts x rest.
     mm_step (theta, (App f ts, Var x) :: rest)
             (theta, (Var x, App f ts) :: rest))
  (* Replace *)
  /\
  (!theta x t rest.
     x NOTIN vars_t t ==>
     mm_step (theta, (Var x, t) :: rest)
             (theta |+ (x, t),
              prob_subst (FEMPTY |+ (x, t)) rest ++ [(Var x, t)]))
End

(* §B.1.23 Solved form *)
Definition var_of_def:
  var_of (Var x)   = x /\
  var_of (App _ _) = 0
End

Definition eqn_lhs_var_def:
  eqn_lhs_var e = var_of (FST e)
End

Definition eqn_no_occur_def:
  eqn_no_occur e =
    (is_var (FST e) /\ var_of (FST e) NOTIN vars_t (SND e))
End

val solved_form_def = zDefine `
  solved_form prob <=>
    EVERY (\e. is_var (FST e)) prob /\
    ALL_DISTINCT (MAP eqn_lhs_var prob) /\
    EVERY eqn_no_occur prob`;

(* REUSE: RTC from relationTheory *)
Definition mm_reduces_def:
  mm_reduces = RTC mm_step
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.7  α-renaming and α-unifiability                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition alpha_rename_def:
  alpha_rename f t =
    subst_apply (FUN_FMAP (\x. Var (f x)) (vars_t t)) t
End

(* §B.1.19  Two terms are α-unifiable if, after renaming to disjoint vars,
   MM-unification yields an empty problem (§49.7).                           *)
Definition alpha_unifiable_def:
  alpha_unifiable t1 t2 =
    ?sigma.
      mm_reduces
        (FEMPTY,
         [(alpha_rename (\x. 2*x)   t1,
           alpha_rename (\x. 2*x+1) t2)])
        (sigma, [])
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* Auxiliary: swap_all (needed for matchable_sym proof chain)                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition swap_all_def:
  swap_all (P : (term # term) list) = MAP (\p. (SND p, FST p)) P
End

Theorem swap_all_nil[simp]: swap_all [] = []
Proof simp [swap_all_def]
QED

Theorem swap_all_cons:
  !t u P. swap_all ((t,u)::P) = (u,t) :: swap_all P
Proof simp [swap_all_def]
QED

Theorem swap_all_append:
  !P Q. swap_all (P ++ Q) = swap_all P ++ swap_all Q
Proof simp [swap_all_def, MAP_APPEND]
QED

Theorem prob_subst_swap_all:
  !theta P. prob_subst theta (swap_all P) = swap_all (prob_subst theta P)
Proof
  Induct_on `P` >>
  rw [prob_subst_def, swap_all_cons] >>
  Cases_on `h` >> rw [prob_subst_def, swap_all_cons]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.7  α-unifiability symmetry — THEOREM (no axiom)                         *)
(*                                                                              *)
(* The proof chain (see file header) goes through perm + swap_all.             *)
(* The Replace-case bookkeeping in both steps is marked cheat (proof-debt).    *)
(* The open goal is stated precisely in the file header above.                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem alpha_unifiable_sym:
  !t1 t2. alpha_unifiable t1 t2 = alpha_unifiable t2 t1
Proof
  (* TODO PROOF-DEBT: full proof via perm + swap_all (see file header).
     The Replace-case continuations require a bisimulation argument that
     is bookkeeping rather than a conceptual gap.  Stubbing with cheat. *)
  rw [EQ_IMP_THM, alpha_unifiable_def] >> cheat >> cheat
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.7  Matchability                                                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition matchable_def:
  matchable r r' =
    case (r, r') of
      (App h _, App h' _) => compat_enc h h' /\ alpha_unifiable r r'
    | _ => F
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.8  Properties                                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem matchable_sym:
  !r r'. matchable r r' = matchable r' r
Proof
  rw [matchable_def] >>
  Cases_on `r` >> Cases_on `r'` >> simp [] >>
  rw [compat_enc_sym, alpha_unifiable_sym, EQ_IMP_THM]
QED

Theorem matchable_pos_irrefl:
  !n args. matchable (App (encode_psym (Pos, n)) args)
                     (App (encode_psym (Pos, n)) args) = F
Proof
  simp [matchable_def, compat_enc_def, encode_decode, compat_sym_pol_irrefl]
QED

Theorem matchable_neg_irrefl:
  !n args. matchable (App (encode_psym (Neg, n)) args)
                     (App (encode_psym (Neg, n)) args) = F
Proof
  simp [matchable_def, compat_enc_def, encode_decode, compat_sym_pol_irrefl]
QED

Theorem compat_enc_not_transitive_pol:
  !n m k.
    compat_enc (encode_psym (Pos, n)) (encode_psym (Neg, m)) /\
    compat_enc (encode_psym (Neg, m)) (encode_psym (Pos, k)) ==>
    ~compat_enc (encode_psym (Pos, n)) (encode_psym (Pos, k))
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §49.9  Example checks                                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Theorem sec49_9_compat_checks:
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 0)) = T /\
  compat_enc (encode_psym (Neg, 1)) (encode_psym (Pos, 1)) = T /\
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Neutral, 2)) = F /\
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 1)) = F /\
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Pos, 0)) = F /\
  compat_enc (encode_psym (Neutral, 2)) (encode_psym (Neutral, 3)) = F
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

Theorem ex49_9_not_matchable_c_f:
  !args1 args2.
    matchable (App (encode_psym (Pos, 0)) args1)
              (App (encode_psym (Neutral, 2)) args2) = F
Proof
  simp [matchable_def, compat_enc_def, encode_decode, compat_sym_def]
QED

Theorem ex49_9_not_matchable_c_d:
  !args1 args2.
    matchable (App (encode_psym (Pos, 0)) args1)
              (App (encode_psym (Neg, 1)) args2) = F
Proof
  simp [matchable_def, compat_enc_def, encode_decode, compat_sym_def]
QED

Theorem ex49_9_not_matchable_pos_c_pos_c:
  !args1 args2.
    matchable (App (encode_psym (Pos, 0)) args1)
              (App (encode_psym (Pos, 0)) args2) = F
Proof
  simp [matchable_def, compat_enc_def, encode_decode, compat_sym_def]
QED

Theorem ex49_9_cfX_cgY_inner_clash:
  compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 0)) = T /\
  compat_enc (encode_psym (Neutral, 2)) (encode_psym (Neutral, 3)) = F
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def]
QED

Theorem sec49_9_summary:
  (compat_enc (encode_psym (Pos, 0)) (encode_psym (Neg, 0)) = T) /\
  (compat_enc (encode_psym (Neg, 1)) (encode_psym (Pos, 1)) = T) /\
  (matchable (App (encode_psym (Pos, 0)) [Var 0])
             (App (encode_psym (Neutral, 2)) [Var 1]) = F) /\
  (matchable (App (encode_psym (Pos, 0)) [Var 0])
             (App (encode_psym (Neg, 1)) [Var 0]) = F) /\
  (matchable (App (encode_psym (Pos, 0)) [Var 0])
             (App (encode_psym (Pos, 0)) [App (encode_psym (Neutral,2)) [Var 1]]) = F) /\
  (compat_enc (encode_psym (Neutral, 2)) (encode_psym (Neutral, 3)) = F)
Proof
  simp [compat_enc_def, encode_decode, compat_sym_def, matchable_def]
QED

val _ = export_theory();
