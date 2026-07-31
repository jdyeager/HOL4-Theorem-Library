open probabilityTheory;
open listspaceTheory;

(* Pe(N,K,A,uAc)=O(N^(-1/4)) *)

(* W x y is P(y|x) *)
Definition BDMC_def:
    BDMC cod W = (FINITE cod ∧
        ∀xi. xi < 2n ⇒ ∑ (W xi) cod = 1x)
End

(* Placeholder *)
Definition sym_cap_def:
    sym_cap cod W = 1r
End

Definition build_input_helper_def:
    build_input_helper N A uA uAc 0 = [] ∧
    build_input_helper N A uA uAc (SUC Nmn) = let n = N - Nmn in if n ∈ A then
         (HD uA)::(build_input_helper N A (TL uA) uAc Nmn) else
         (HD uAc)::(build_input_helper N A uA (TL uAc) Nmn)
End

Definition build_input_def:
    build_input A uA uAc = build_input_helper (LENGTH uA + LENGTH uAc) A uA uAc (LENGTH uA + LENGTH uAc)
End

(* Placeholder *)
Definition pc_encode_def:
    pc_encode u = u
End

Definition transmit_def:
    transmit Ws x w = MAP (λxi,Wi. Wi (xi,w)) (ZIP (x,Ws))
End

(* Placeholder *)
Definition pc_decode_def:
    pc_decode y = y
End

Definition pc_err_def:
    pc_err Ws A uAc (uA, w) =
        let u = build_input A uA uAc;
            x = pc_encode u; (* may need extra info *)
            y = transmit Ws x w;
            v = pc_decode y (* may need extra info *)
        in u ≠ v
End

(* I dunno, maybe requires W *)
(* Placeholder *)
Definition info_set_def:
    info_set (N:num) = {n | n < N}
End

(* I dunno, maybe requires W *)
(* Placeholder *)
Definition frozen_bits_def:
    frozen_bits (N:num) = []
End

Definition valid_Ws_def:
    valid_Ws N cod W pW Ws ⇔ LENGTH Ws = N ∧ ∀xi. xi < 2n ⇒
        indep_vars pW (λi w. (EL i Ws) (xi,w)) (K (cod, POW cod)) (count N) ∧
        ∀i yi. i < N ∧ yi ∈ cod ⇒
            prob pW ({w | (EL i Ws) (xi,w) = yi} ∩ p_space pW) = W xi yi
End

Definition uniform_discrete_prob_space_def:
    uniform_discrete_prob_space X = (X, POW X, (λs. &(CARD s) / &(CARD X)))
End

(* can prove CARD A (aka K) is floor(N*R) *)
Theorem th4:
    ∀cod W (R:real). BDMC cod W ∧ R < sym_cap cod W ⇒
        ∃(c:real). ∀(N:num) Ws pW.
            valid_Ws N cod W pW Ws ⇒
            let
                A = info_set N;
                uAc = frozen_bits N;
                pui = uniform_discrete_prob_space {0n; 1n};
                puA = pi_measure_space_list (GENLIST (K pui) (CARD A))
            in
                prob (puA × pW) ({uAw | pc_err Ws A uAc uAw} ∩ p_space (puA × pW)) ≤
                    Normal c * (&N powr (-1/4))
Proof
    cheat
QED

