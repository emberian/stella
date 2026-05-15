(* stellaPolarisedScript.sml
   Polarised signature and rays (Eng §48.2–§48.7).

   REUSE: stellaTermTheory (term, subst_apply, vars_t), pred_setTheory.
   No external unification theory imported here.
*)

open HolKernel boolLib bossLib;
open arithmeticTheory pred_setTheory listTheory pairTheory;
open stellaTermTheory;

val _ = new_theory "stellaPolarised";

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.2  Polarity                                                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Datatype:
  polarity = Pos | Neg | Neutral
End

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.2  Polarised symbols  (polarity # num)                                 *)
(*                                                                             *)
(* A polarised symbol is  (pol, neutral_name)  where  neutral_name : num.    *)
(* We represent it as a pair — no separate type.                              *)
(*                                                                             *)
(* |·| on symbols: strip polarity → (Neutral, n).                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition underlying_sym_def:
  underlying_sym (pol : polarity, n : num) : polarity # num = (Neutral, n)
End

Theorem underlying_sym_neutral[simp]:
  underlying_sym (Neutral, n) = (Neutral, n)
Proof simp [underlying_sym_def]
QED

Theorem underlying_sym_pos[simp]:
  underlying_sym (Pos, n) = (Neutral, n)
Proof simp [underlying_sym_def]
QED

Theorem underlying_sym_neg[simp]:
  underlying_sym (Neg, n) = (Neutral, n)
Proof simp [underlying_sym_def]
QED

Theorem underlying_sym_idem[simp]:
  underlying_sym (underlying_sym c) = underlying_sym c
Proof
  Cases_on `c` >> simp [underlying_sym_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.3  Opposite polarity  op(·)                                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition op_sym_def:
  op_sym (pol : polarity, n : num) : polarity # num =
    case pol of
      Neutral => (Neutral, n)
    | Pos     => (Neg, n)
    | Neg     => (Pos, n)
End

Theorem op_sym_neutral[simp]: op_sym (Neutral, n) = (Neutral, n)
Proof simp [op_sym_def]
QED

Theorem op_sym_pos[simp]: op_sym (Pos, n) = (Neg, n)
Proof simp [op_sym_def]
QED

Theorem op_sym_neg[simp]: op_sym (Neg, n) = (Pos, n)
Proof simp [op_sym_def]
QED

Theorem op_sym_involution[simp]:
  !c. op_sym (op_sym c) = c
Proof
  Cases_on `c` >> rename1 `(p, n)` >>
  Cases_on `p` >> simp [op_sym_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.2  Polarised compatibility relation  c ⊂ d                             *)
(*                                                                             *)
(* c ⊂ d  ⟺  |c| = |d|  AND opposite-or-both-neutral                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition compat_sym_def:
  compat_sym (p1 : polarity, n1 : num) (p2 : polarity, n2 : num) =
    (n1 = n2 /\
     ((p1 = Pos /\ p2 = Neg) \/ (p1 = Neg /\ p2 = Pos) \/
      (p1 = Neutral /\ p2 = Neutral)))
End

Theorem compat_sym_sym:
  !c d. compat_sym c d = compat_sym d c
Proof
  Cases_on `c` >> Cases_on `d` >> simp [compat_sym_def] >> metis_tac []
QED

(* Note: compat_sym IS reflexive for Neutral symbols: (Neutral, n) ⊂ (Neutral, n).
   Anti-reflexivity only holds for POLARISED (Pos/Neg) symbols:
   +c ⊄ +c   and   -c ⊄ -c.                                                  *)
Theorem compat_sym_pol_irrefl:
  !n. ~compat_sym (Pos, n) (Pos, n) /\ ~compat_sym (Neg, n) (Neg, n)
Proof
  simp [compat_sym_def]
QED

(* Neutral is compatible with itself: (Neutral, n) ⊂ (Neutral, n). *)
Theorem compat_sym_neutral_refl[simp]:
  compat_sym (Neutral, n) (Neutral, n)
Proof
  simp [compat_sym_def]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.2  Encoding polarised symbols as numbers (for stellaTerm App fsym)    *)
(*                                                                             *)
(* encode_psym (pol, n) = 3*n + pol_code pol                                  *)
(*   pol_code Pos = 0, pol_code Neg = 1, pol_code Neutral = 2                *)
(*                                                                             *)
(* This is a total injective map  polarity # num -> num.                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition pol_code_def:
  pol_code Pos     = (0 : num) /\
  pol_code Neg     = 1 /\
  pol_code Neutral = 2
End

Definition encode_psym_def:
  encode_psym (pol : polarity, n : num) : num = 3 * n + pol_code pol
End

(* Decoding: extract polarity from encoded number mod 3, name from div 3.    *)
Definition decode_pol_def:
  decode_pol (k : num) : polarity =
    if k MOD 3 = 0 then Pos
    else if k MOD 3 = 1 then Neg
    else Neutral
End

Definition decode_psym_def:
  decode_psym (k : num) : polarity # num = (decode_pol k, k DIV 3)
End

Theorem encode_decode[simp]:
  !c. decode_psym (encode_psym c) = c
Proof
  Cases_on `c` >> rename1 `encode_psym (p, n)` >>
  Cases_on `p` >>
  simp [encode_psym_def, decode_psym_def, decode_pol_def, pol_code_def]
QED

(* Compatibility via encoded numbers (for use in stellaMatchScript). *)
Definition compat_enc_def:
  compat_enc (c : num) (d : num) =
    compat_sym (decode_psym c) (decode_psym d)
End

Theorem compat_enc_sym:
  !c d. compat_enc c d = compat_enc d c
Proof simp [compat_enc_def, compat_sym_sym]
QED

(* Anti-reflexivity for *polarised* encoded symbols only. *)
Theorem compat_enc_pol_irrefl:
  !n. ~compat_enc (encode_psym (Pos, n)) (encode_psym (Pos, n)) /\
      ~compat_enc (encode_psym (Neg, n)) (encode_psym (Neg, n))
Proof
  simp [compat_enc_def, encode_decode, compat_sym_pol_irrefl]
QED

(* ─────────────────────────────────────────────────────────────────────────── *)
(* §48.7  Underlying-term operator |·| on rays                                *)
(*                                                                             *)
(* A ray is a  term  (from stellaTermTheory) whose App function-symbol numbers*)
(* encode polarised symbols via encode_psym.                                  *)
(*                                                                             *)
(* |X|           = X                  (variables unchanged)                   *)
(* |c(r₁,…,rₙ)| = |c|(|r₁|,…,|rₙ|)  (strip head polarity, recurse)         *)
(*                                                                             *)
(* |c| = encode_psym (Neutral, n)  where decode_psym c = (_, n)              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

(* The underlying encoded number: set polarity to Neutral, keep name. *)
Definition underlying_enc_def:
  underlying_enc (k : num) : num =
    encode_psym (Neutral, SND (decode_psym k))
End

Theorem underlying_enc_neutral:
  !n. underlying_enc (encode_psym (Neutral, n)) = encode_psym (Neutral, n)
Proof
  simp [underlying_enc_def, encode_psym_def, decode_psym_def,
        decode_pol_def, pol_code_def]
QED

(* Underlying-term operator defined simultaneously over term and term list.  *)
val uterm_defn = Hol_defn "uterm" `
  (uterm_t (Var x)     = Var x) /\
  (uterm_t (App c ts)  = App (underlying_enc c) (uterm_l ts)) /\
  (uterm_l []          = []) /\
  (uterm_l (t :: ts)   = uterm_t t :: uterm_l ts)`;

val uterm_def = LIST_CONJ (Defn.eqns_of uterm_defn);
val uterm_ind = Option.valOf (Defn.ind_of uterm_defn);

(* |·| fixes variables. *)
Theorem uterm_t_var[simp]:
  uterm_t (Var x) = Var x
Proof simp [uterm_def]
QED

(* |·| is idempotent: applying twice gives the same result. *)
Theorem uterm_t_idem:
  (!t. uterm_t (uterm_t t) = uterm_t t) /\
  (!ts. uterm_l (uterm_l ts) = uterm_l ts)
Proof
  HO_MATCH_MP_TAC uterm_ind >>
  simp [uterm_def, underlying_enc_def, decode_psym_def, decode_pol_def,
        encode_psym_def, pol_code_def]
  >> rpt strip_tac
  >> simp [underlying_enc_neutral]
QED

val _ = export_theory();
