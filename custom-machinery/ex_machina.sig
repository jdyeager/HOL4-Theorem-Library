signature ex_machina =
sig

(* For various type definitions *)
(* include Abbrev *)
type thm = Thm.thm
type term = Term.term
type 'a quotation = 'a Portable.frag list
type tactic = Abbrev.tactic
type thm_tactic = Abbrev.thm_tactic
type proof = Manager.proof
type proofs = Manager.proofs
datatype match_position = datatype thmpos_dtype.match_position

val disj1_asm_tac : tactic

val disj2_asm_tac : tactic

val quick_save : int -> unit

val quick_load : int -> proofs

val concl_tac : thm_tactic

val chain_irule_at : (match_position * thm * term quotation list * thm list) list -> tactic

end
