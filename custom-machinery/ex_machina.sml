structure ex_machina :> ex_machina =
struct

(****************)
(* Setup Voodoo *)
(****************)

open HolKernel Parse boolLib bossLib;

type thm = Thm.thm
type term = Term.term
type tactic = Abbrev.tactic
type thm_tactic = Abbrev.thm_tactic
type proof = Manager.proof
type proofs = Manager.proofs

(***************************)
(* Proof Manager Machinery *)
(***************************)

(* Holds up to 10 proofs save slots indexed 0-9
   For initialisation purposes, uses options and NONE to represent empty slots *)
val save_slots = Array.array (10,NONE: proof option)

(* Check that may be useful for having quickload on empty proof list add, not overwrite, top proof *)
fun no_proofs (Manager.PRFS (_::_)) = false |
    no_proofs (Manager.PRFS []) = true;

(* Check that guards against invalid slot number
   Returns slot number if valid, error otherwise *)
fun check_slot_bound slot = if 0 <= slot andalso slot <= 9 then slot else 
    raise mk_HOL_ERR "ex_machina" "check_slot_bound" "Only slots 0-9 are valid"

(* Check that guards against loading from emptry slot
   Returns proof in slot of valid, error otherwise *)
fun check_slot slot = case Array.sub (save_slots,slot) of
    SOME x => x |
    NONE => raise mk_HOL_ERR "ex_machina" "check_slot" ("No save data in slot " ^ Int.toString slot)

(* Quicksaving updates the array *)
fun quick_save slot =
    Array.update (save_slots,check_slot_bound slot,SOME $ Manager.current_proof $ proofManagerLib.status())

(* Quickloading updates proof stack based on array *)
(* --- Possible improvements:
    have quickload on empty proof stack add loaded proof to
    when top proof's goal differs from load slot's, have quickload add loaded proof to stack
    (basically have top proof overwritten iff it shares load slot's goal)
--- *)
fun quick_load slot = (
    proofManagerLib.drop();
    proofManagerLib.add $ check_slot slot)

(********************)
(* Tactic Machinery *)
(********************)

(* Check that guards against applying validations to non-single-element thm lists
   Returns singular element if valid, error otherwise *)
fun check_sing [x] = x |
    check_sing _ = raise mk_HOL_ERR "ex_machina" "check_sing" "Validation applied to illegal thm list"

(* Check that guards against using dest_disj on a non-disjuncion
   Returns return of dest_disj if valid, error otherwise *)
fun check_disj t = if is_disj t then dest_disj t else
    raise mk_HOL_ERR "ex_machina" "check_disj" "Term not disjunction"

(* Negates a term, by removing a '¬' if it exists *)
fun neg_tm t = if is_neg t then dest_neg t else mk_neg t

(*---------------------------------------------*
 *      A, ~t1 |- t2         A, t1 |- t2       *
 *    ----------------    -----------------    *
 *      A |- t1 ∨ t2        A |- ~t1 ∨ t2      *
 *---------------------------------------------*)
(* Derived rule for discharging part of a disjuncion
    Parameter t: term t1 (resp. ~t1) as it appears in the desired conjunct
    Unwritten parameter th: theorem of the form  Γ |- t2
    Return: theorem of the form  Γ-{~t1} |- t1 ∨ t2 (resp. Γ-{t1} |- ~t1 ∨ t2) *)
fun DISJ_DISCH1 t = if is_neg t then
    REWRITE_RULE [Once IMP_DISJ_THM] o DISCH (dest_neg t) else
    REWRITE_RULE [Once $ GSYM DISJ_EQ_IMP] o DISCH (mk_neg t)

(*---------------------------------------------*
 *      A, ~t2 |- t1         A, t2 |- t1       *
 *    ----------------    -----------------    *
 *      A |- t1 ∨ t2        A |- t1 ∨ ~t2      *
 *---------------------------------------------*)
(* Derived rule for discharging part of a disjuncion
    Parameter t: term t2 (resp. ~t2) as it appears in the desired conjunct
    Unwritten parameter th: theorem of the form  Γ |- t1
    Return: theorem of the form  Γ-{~t2} |- t1 ∨ t2 (resp. Γ-{t2} |- t1 ∨ ~t2) *)
fun DISJ_DISCH2 t = if is_neg t then
    REWRITE_RULE [Once IMP_DISJ_THM,Once DISJ_COMM] o DISCH (dest_neg t) else
    REWRITE_RULE [Once $ GSYM DISJ_EQ_IMP,Once DISJ_COMM] o DISCH (mk_neg t)

(* Tactic that reduces a goal t1 ∨ t2 to t1, but adds ~t2 as an assumption.
   If t2 itself is of the form ~t3, then t3 is added as an assuption (as opposed to ~~t3) *)
fun disj1_asm_tac (asl,w) =
    let
        val (d1,d2) = check_disj w
        val nd2 = neg_tm d2
    in
        ([(nd2::asl,d1)],DISJ_DISCH2 d2 o check_sing)
    end

(* Tactic that reduces a goal t1 ∨ t2 to t2, but adds ~t1 as an assumption.
   If t1 itself is of the form ~t3, then t3 is added as an assuption (as opposed to ~~t3) *)
fun disj2_asm_tac (asl,w) =
    let
        val (d1,d2) = check_disj w
        val nd1 = neg_tm d1
    in
        ([(nd1::asl,d2)],DISJ_DISCH1 d1 o check_sing)
    end

fun concl_tac th = mp_tac th >> impl_tac >| [all_tac,disch_tac]

fun chain_irule_at [] = all_tac |
    chain_irule_at ((pos,th,qex,ths)::l) =
        irule_at pos th >> SIMP_TAC pure_ss [PULL_EXISTS] >> qexistsl_tac qex >> simp ths >> chain_irule_at l

(**********************)
(* Quicksave Commands *)
(**********************)

(* Add to hol-mode.el *)
(* --- 

;; Quick-saving commands

(defun hol-quick-save (slot)
  "Save proof to quicksave slot."
  (interactive)
  (send-raw-string-to-hol (format "ex_machina.quick_save %d" slot) nil))

(defun hol-quick-load (slot)
  "Save proof to quicksave slot."
  (interactive)
  (send-raw-string-to-hol (format "ex_machina.quick_load %d" slot) hol-echo-commands-p))

(define-prefix-command 'holql-map)
(define-key hol-map "q" 'holql-map)

(define-prefix-command 'holqs-map)
(define-key holql-map "s" 'holqs-map)

(define-key holqs-map "0" (lambda() (interactive) (hol-quick-save 0)))
(define-key holql-map "0" (lambda() (interactive) (hol-quick-load 0)))
(define-key holqs-map "1" (lambda() (interactive) (hol-quick-save 1)))
(define-key holql-map "1" (lambda() (interactive) (hol-quick-load 1)))
(define-key holqs-map "2" (lambda() (interactive) (hol-quick-save 2)))
(define-key holql-map "2" (lambda() (interactive) (hol-quick-load 2)))
(define-key holqs-map "3" (lambda() (interactive) (hol-quick-save 3)))
(define-key holql-map "3" (lambda() (interactive) (hol-quick-load 3)))
(define-key holqs-map "4" (lambda() (interactive) (hol-quick-save 4)))
(define-key holql-map "4" (lambda() (interactive) (hol-quick-load 4)))
(define-key holqs-map "5" (lambda() (interactive) (hol-quick-save 5)))
(define-key holql-map "5" (lambda() (interactive) (hol-quick-load 5)))
(define-key holqs-map "6" (lambda() (interactive) (hol-quick-save 6)))
(define-key holql-map "6" (lambda() (interactive) (hol-quick-load 6)))
(define-key holqs-map "7" (lambda() (interactive) (hol-quick-save 7)))
(define-key holql-map "7" (lambda() (interactive) (hol-quick-load 7)))
(define-key holqs-map "8" (lambda() (interactive) (hol-quick-save 8)))
(define-key holql-map "8" (lambda() (interactive) (hol-quick-load 8)))
(define-key holqs-map "9" (lambda() (interactive) (hol-quick-save 9)))
(define-key holql-map "9" (lambda() (interactive) (hol-quick-load 9)))

--- *)

end
