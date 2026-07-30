open HolKernel Parse boolLib bossLib;
open ratTheory;
open realTheory;
open realLib;
open real_of_ratTheory;
open preamble basis;
open mlintTheory mlratTheory;
(* open ASCIInumbersTheory; *)

open ex_machina;
(*
open trivialTheory;
open trivialSimps;
*)
open sqrtTheory;
open lnTheory;
open seldonianTheory;

val _ = new_theory "seldonianProg";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];

(*
val _ = reveal "C";
val _ = augment_srw_ss [realSimps.REAL_ARITH_ss,TRIVIAL_ss];
*)

val _ = translation_extends "basisProg";

val _ = translate abs;
val _ = translate pow;

val _ = translate REAL_LIST_SUM_DEF;

(*
fetch "-" "rational_sqrt_helper_v_thm"
fetch "-" "rational_sqrt_helper_v_def"
fetch "-" "rational_sqrt_helper_side_def"
*)
val _ = translate rational_sqrt_helper_def;
(*
Theorem rational_sqrt_helper_side_T:
    ∀tol x est. rational_sqrt_helper_side tol x est
Proof
    irule rational_sqrt_helper_ind >> rw[] >>
    simp[Once $ fetch "-" "rational_sqrt_helper_side_def"]
QED
val _ = update_precondition rational_sqrt_helper_side_T;
*)

(*
fetch "-" "rational_sqrt_v_thm"
fetch "-" "rational_sqrt_v_def"
*)
val _ = translate rational_sqrt_def;

(*
fetch "-" "rational_log_helper_init_nub_v_thm"
fetch "-" "rational_log_helper_init_nub_v_def"
fetch "-" "rational_log_helper_init_nub_side_def"
*)
val _ = translate rational_log_helper_init_Nub_def;
Theorem rational_log_helper_init_nub_side_T:
    ∀tol ar N. rational_log_helper_init_nub_side tol ar N
Proof
    irule rational_log_helper_init_Nub_ind >> rw[] >>
    simp[Once $ fetch "-" "rational_log_helper_init_nub_side_def"] >>
    rw[REAL_NOT_LE,REAL_NOT_LT] >> irule REAL_LT_IMP_NE >>
    irule REAL_POW_1_LT >> simp[]
QED
val _ = update_precondition rational_log_helper_init_nub_side_T;

(*
fetch "-" "rational_log_helper_first_n_v_thm"
fetch "-" "rational_log_helper_first_n_v_def"
fetch "-" "rational_log_helper_first_n_side_def"
*)
val _ = translate rational_log_helper_first_N_def;
Theorem rational_log_helper_first_n_side_T:
    ∀tol ar Nlb Nub. rational_log_helper_first_n_side tol ar Nlb Nub
Proof
    irule rational_log_helper_first_N_ind >> rw[] >>
    simp[Once $ fetch "-" "rational_log_helper_first_n_side_def"] >>
    rw[REAL_NOT_LE,REAL_NOT_LT] >> irule REAL_LT_IMP_NE >>
    irule REAL_POW_1_LT >> simp[]
QED
val _ = update_precondition rational_log_helper_first_n_side_T;

(*
fetch "-" "rational_log_helper_n_v_thm"
fetch "-" "rational_log_helper_n_v_def"
*)
val _ = translate rational_log_helper_N_def;

(*
fetch "-" "rational_log_v_thm"
fetch "-" "rational_log_v_def"
*)
val _ = translate rational_log_def;

(*
fetch "-" "hoef_rat_math_core_v_thm"
fetch "-" "hoef_rat_math_core_v_def"
*)
val _ = translate hoef_rat_math_core_def;

(*
fetch "-" "extend_math_core_v_thm"
fetch "-" "extend_math_core_v_def"
*)
val _ = translate extend_math_core_def;

Definition fromString_frac_def:
    fromString_frac s = case OPT_MMAP mlint$fromString (tokens ($= #"/") s) of
        | SOME (n::d::[]) => if d = 0 then NONE else SOME ((real_of_int n) / (real_of_int d))
        | _ => NONE
End

Definition fromString_dec_def:
    fromString_dec s =
        let
            l = fields ($= #".") s;
            opi = mlint$fromString (concat l);
        in 
            case opi of NONE => NONE | SOME i =>
            case l of
                | (w::[]) => SOME (real_of_int i)
                | (w::d::[]) => SOME (real_of_int i / 10r pow strlen d)
                | _ => NONE
End

Definition fromString_sci_not_def:
    fromString_sci_not s = case (tokens (λc. c = #"e" ∨ c = #"E") s) of
        | [] => NONE
        | m::t => case fromString_dec m of
            | NONE => NONE
            | SOME r => case t of
                | [] => SOME r
                | e::[] => (case mlint$fromString e of
                    | NONE => NONE
                    | SOME i => let n = 10r pow (Num (ABS i)) in
                        SOME (r * (if 0 ≤ i then n else 1/n)))
                | _ => NONE
End

Definition fromString_def:
    fromString s = if (isSubstring «/» s) then fromString_frac s else fromString_sci_not s
End

Definition real_of_rational_def:
    real_of_rational r = real_of_int (pair_num r) / real_of_num (pair_denom r)
End

Definition rational_of_rat_def:
    rational_of_rat r = RatPair (RATN r) (RATD r)
End

Theorem int_toString_isDigit:
    ∀i:int c. MEM c (explode (toString i)) ⇒ c = #"~" ∨ isDigit c
Proof
    rw[mlintTheory.toString_def,num_to_chars_thm] >> disj2_tac >>
    metis_tac[EVERY_isDigit_num_to_dec_string,EVERY_MEM]
QED

Theorem isSubstring_char:
    ∀c s. isSubstring (strlit [c]) s ⇔ MEM c (explode s)
Proof
    strip_tac >> ntac 2 $ induct_on ‘s’
    >- simp[isSubstring_def] >>
    gs[isSubstring_SEG] >> rw[] >> Cases_on ‘c = h’
    >- (simp[] >> qexists ‘0’ >> simp[SEG1]) >>
    simp[] >> last_x_assum $ SUBST1_TAC o SYM >> reverse $ rw[EQ_IMP_THM]
    >- (qexists ‘SUC i’ >> gs[SEG1]) >>
    Cases_on ‘i’ >- gs[SEG1] >>
    gs[ADD] >> qexists ‘n’ >> gs[SEG1]
QED

Theorem tokens_sing:
    ∀P s. s ≠ «» ∧ (∀c. MEM c (explode s) ⇒ ¬P c) ⇒ tokens P s = [s]
Proof
    rw[] >> qspecl_then [‘explode s’,‘P’] mp_tac $ GEN_ALL TOKENS_unchanged >>
    simp[EVERY_MEM,TOKENS_eq_tokens_sym] >> disch_then kall_tac >>
    qexists ‘explode s’ >> rw[] >> gs[NULL_EQ] >>
    pop_assum $ assume_tac o AP_TERM “implode” >>
    pop_assum $ SUBST_ALL_TAC o SYM >> gs[implode_explode]
QED

Theorem int_toString_not_empty:
    ∀i:int. toString i ≠ «»
Proof
    reverse $ rw[mlintTheory.toString_def,num_to_chars_thm]
QED

Theorem fields_aux_sing:
    ∀P s ss n len. (∀c. MEM c (explode s) ⇒ ¬P c) ∧ n + len = strlen s ⇒
        fields_aux P s ss n len = [implode (REVERSE ss ++ DROP n (explode s))]
Proof
    ntac 2 strip_tac >> Induct_on ‘len’
    >- (simp[fields_aux_def] >> Cases_on ‘s’ >> simp[strlen_def]) >>
    rw[] >> simp[fields_aux_def,GSYM ADD1] >>
    ‘¬P (strsub s n)’ by (first_x_assum $ irule >> Cases_on ‘s’ >> simp[strsub_def] >>
        irule EL_MEM >> gs[strlen_def]) >>
    simp[] >> Cases_on ‘s’ >> simp[] >> rename [‘EL n s’] >>
    ‘n < STRLEN s’ by gs[strlen_def] >> pop_assum mp_tac >>
    rpt $ pop_assum kall_tac >> qid_specl_tac [‘s’,‘n’] >>
    Induct_on ‘n’ >> rw[] >> Cases_on ‘s’ >> gs[] >> simp[]
QED

Theorem fields_sing:
    ∀P s. (∀c. MEM c (explode s) ⇒ ¬P c) ⇒ fields P s = [s]
Proof
    rw[fields_def] >>
    drule_at_then Any (qspecl_then [‘""’,‘0’,‘strlen s’] mp_tac) fields_aux_sing >>
    simp[DROP]
QED

Theorem fromString_dec_int_toString:
    ∀i. fromString_dec (toString i) = SOME (real_of_int i)
Proof
    rw[fromString_dec_def] >>
    resolve_then Any (qspecl_then [‘i’,‘λc. c = #"e" ∨ c = #"E"’] concl_tac) int_toString_not_empty tokens_sing
    >- (rw[] >> CCONTR_TAC >> gs[] >> drule int_toString_isDigit >> EVAL_TAC) >>
    simp[fields_filter] >>
    ‘∀c. MEM c (explode (toString i)) ⇒ ¬($= #".") c’ by (rw[] >> CCONTR_TAC >>
         gs[] >> drule int_toString_isDigit >> EVAL_TAC) >>
    ‘EVERY ($¬ ∘ $= #".") (explode (toString i))’ by rw[EVERY_MEM] >>
    gs[GSYM FILTER_EQ_ID,fields_sing]
QED

Theorem fromString_sci_not_int_toString:
    ∀i. fromString_sci_not (toString i) = SOME (real_of_int i)
Proof
    rw[fromString_sci_not_def] >>
    resolve_then Any (qspecl_then [‘i’,‘λc. c = #"e" ∨ c = #"E"’] concl_tac) int_toString_not_empty tokens_sing
    >- (rw[] >> CCONTR_TAC >> gs[] >> drule int_toString_isDigit >> EVAL_TAC) >>
    simp[fromString_dec_int_toString]
QED

Theorem real_fromString_int_toString:
    ∀i. fromString (toString i) = SOME (real_of_int i)
Proof
    rw[] >> simp[fromString_def,isSubstring_char] >>
    ‘¬MEM #"/" (explode (toString i))’ by (CCONTR_TAC >> gs[] >>
        dxrule int_toString_isDigit >> simp[] >> EVAL_TAC) >>
    simp[fromString_sci_not_int_toString]
QED

Theorem fromString_frac_num_den:
    ∀(n:int) (d:num). d ≠ 0 ⇒
        fromString_frac (concat [toString n; implode "/"; toString (int_of_num d)]) =
            SOME (real_of_int n / real_of_num d)
Proof
    rw[fromString_frac_def] >>
    qspecl_then [‘$= #"/"’,‘toString n’,‘#"/"’,‘toString (int_of_num d)’] mp_tac tokens_append >>
    simp[concat_cons,EVAL “toString #"/"”] >> disch_then kall_tac >>
    qspecl_then [‘$= #"/"’,‘toString n’] concl_tac tokens_sing
    >- (rw[int_toString_not_empty] >> CCONTR_TAC >> gs[] >>
        drule int_toString_isDigit >> EVAL_TAC) >>
    qspecl_then [‘$= #"/"’,‘toString (int_of_num d)’] concl_tac tokens_sing
    >- (rw[int_toString_not_empty] >> CCONTR_TAC >> gs[] >>
        drule int_toString_isDigit >> EVAL_TAC) >>
    simp[]
QED

Theorem real_fromString_num_den:
    ∀(n:int) (d:num). d ≠ 0 ∧ d ≠ 1 ⇒
        fromString (concat [toString n; implode "/"; toString (int_of_num d)]) =
            SOME (real_of_int n / real_of_num d)
Proof
    simp[fromString_def,isSubstring_char,concat_cons,explode_strcat,fromString_frac_num_den]
QED

Theorem real_fromString_rational_toString:
    ∀r. fromString (toString (rational_of_rat r)) = SOME (real_of_rat r)
Proof
    rw[rational_of_rat_def,real_of_rat_def] >>
    ‘RATD r ≠ 0’ by simp[] >> rename [‘RatPair i d’] >>
    rw[mlratTheory.toString_def,real_fromString_int_toString,real_fromString_num_den]
QED

Theorem toString_int_neg:
    ∀i. i < 0 ⇒ toString (i:int) = «~» ^ toString (-i)
Proof
    rw[mlintTheory.toString_def] >> gs[integerTheory.INT_NOT_LE]
    >- metis_tac[integerTheory.INT_NOT_LE] >>
    simp[integerTheory.INT_ABS,GSYM implode_cons_str]
QED

Definition split_row_triple_def:
    split_row_triple [] = SOME ([],[]) ∧
    split_row_triple (r::a::b::t) = OPTION_MAP (λ(rt,abt). (r::rt,(a,b)::abt)) (split_row_triple t) ∧
    split_row_triple _ = NONE
End

Definition split_row_def:
    split_row [] = NONE ∧
    split_row (d::t) = OPTION_MAP (λ(rl,abl). (d,rl,abl)) (split_row_triple t)
End

(* OPT_MMAP (C OPTION_BIND pack_row ∘ OPT_MMAP fromString ∘ tokens (C MEM " (),;:")) ∘ tokens ($= #"\n") *)
Definition data_from_string_def:
    data_from_string s = OPT_MMAP (λr. OPTION_BIND (OPT_MMAP fromString
            (tokens (λc. c = #" " ∨ c = #"(" ∨ c = #")" ∨ c = #"," ∨ c = #";" ∨ c = #":") r)) split_row)
        (tokens ($= #"\n") s)
End

(*
αβγδ
1 1/1 -1.1 1.1 1/2 -1/2 1.2 -1/3 -1.3 1/3
1/2: (0, -1, 1), (1/2, -1e-1, 1e1)
1/3: 1.3 -3e1 1.3e2; 0 -3.2 2.3; -.5 -3/4 2/3

EVAL “pack_data «1 1/1 -1.1 1.1 1/2 -1/2 1.2 -1/3 -1.3 1/3\n1/2: (0, -1, 1), (1/2, -1e-1, 1e1)\n1/3: 1.3 -3e1 1.3e2; 0 -3.2 2.3; -.5 -3/4 2/3»”;
*)

Definition test_from_strings_def:
    test_from_strings lntol_str sqtol_str data_str =
        do
            lntol <- fromString lntol_str;
            sqtol <- fromString sqtol_str;
            d_rl_ex_l <- data_from_string data_str;
            SOME (extend_math_core (hoef_rat_math_core lntol sqtol) d_rl_ex_l)
        od
End

Definition test_from_data_def:
    test_from_data lntol_str sqtol_str d_rl_ex_l =
        do
            lntol <- fromString lntol_str;
            sqtol <- fromString sqtol_str;
            SOME (extend_math_core (hoef_rat_math_core lntol sqtol) d_rl_ex_l)
        od
End

Definition test_results_to_string_def:
    test_results_to_string NONE = «Fatal Error» ∧
    test_results_to_string (SOME T) = «Test Passed» ∧
    test_results_to_string (SOME F) = «Test Failed»
End

Definition output_from_data_string_def:
    output_from_data_string argv data_str_op =
        let res_op = do
            lntol_str <- oEL 0 argv;
            sqtol_str <- oEL 1 argv;
            data_str <- data_str_op;
            test_from_strings lntol_str sqtol_str data_str
        od in
            test_results_to_string res_op
End

val _ = translate oEL_def;
val _ = translate OPTION_BIND_def;
val _ = translate OPT_MMAP_def;

(*
fetch "-" "fromstring_pos_frac_v_thm"
fetch "-" "fromstring_pos_frac_v_def"
*)
val _ = translate fromString_frac_def;

(*
fetch "-" "fromstring_pos_dec_v_thm"
fetch "-" "fromstring_pos_dec_v_def"
*)
val _ = translate fromString_dec_def;

(*
fetch "-" "fromstring_pos_sci_not_v_thm"
fetch "-" "fromstring_pos_sci_not_v_def"
*)
val _ = translate fromString_sci_not_def;

(*
fetch "-" "fromstring_v_thm"
fetch "-" "fromstring_v_def"
*)
val _ = translate fromString_def;

(*
fetch "-" "split_row_triple_v_thm"
fetch "-" "split_row_triple_v_def"
*)
val _ = translate split_row_triple_def;

(*
fetch "-" "split_row_v_thm"
fetch "-" "split_row_v_def"
*)
val _ = translate split_row_def;

(*
fetch "-" "data_from_string_v_thm"
fetch "-" "data_from_string_v_def"
*)
val _ = translate data_from_string_def;

(*
fetch "-" "test_from_strings_v_thm"
fetch "-" "test_from_strings_v_def"
*)
val _ = translate test_from_strings_def;

(*
fetch "-" "test_results_to_string_v_thm"
fetch "-" "test_results_to_string_v_def"
*)
val _ = translate test_results_to_string_def;

(*
fetch "-" "output_from_data_string_v_thm"
fetch "-" "output_from_data_string_v_def"
*)
val _ = translate output_from_data_string_def;

Theorem file_content_SOME_imp_filename:
    ∀fs f fv s. file_content fs f = SOME s ⇒ inFS_fname fs f
Proof
    rw[file_content_def,AllCaseEqs ()] >> simp[inFS_fname_def,SF SFY_ss]
QED

(* DISSERTATION PROG *)
(*
fetch "-" "main_v_def"
*)
val _ = (append_prog o process_topdecs) ‘
    fun main () =
        let
            (* val _ = Runtime.debugMsg "foo" *)
            val argv = CommandLine.arguments ()
            val data_str_op = case oel 2 argv of
                  None => None
                | Some fname => TextIO.inputAllFrom (Some fname)
            val outp = output_from_data_string argv data_str_op
        in
            print (outp ^ "\n")
        end’;

Theorem seldonian_filter_spec:
    ∀p fs ename lntol_str sqtol_str fname lntol sqtol d_rl_ex_l.
        hasFreeFD fs ∧ (∃fv. FILENAME fname fv) ∧
        fromString lntol_str = SOME lntol ∧ fromString sqtol_str = SOME sqtol ∧
        do contents <- file_content fs fname; data_from_string (strlit contents) od = SOME d_rl_ex_l ⇒
        app (p:'ffi ffi_proj) main_v [Conv NONE []]
            (STDIO fs * COMMANDLINE [ename; lntol_str; sqtol_str; fname])
            (POSTv resv. &UNIT_TYPE () resv *
                STDIO (add_stdout fs (test_results_to_string
                    (SOME (extend_math_core (hoef_rat_math_core lntol sqtol) d_rl_ex_l)) ^ «\n»)))
Proof
    rpt strip_tac >> pop_assum mp_tac >> rw[] >> xcf_with_def $ fetch "-" "main_v_def" >>
    xmatch >> xlet_auto >- (xret >> xsimpl) >>
    xlet_auto >- (qexistsl [‘STDIO fs’,‘ename’] >> xsimpl) >>
    xlet ‘POSTv fnamev. &OPTION_TYPE FILENAME (SOME fname) fnamev * STDIO fs’
    >- (xapp_spec $ INST_TYPE [“:α” |-> “:mlstring”] $ fetch "-" "oel_v_thm" >> xsimpl >>
        first_x_assum $ irule_at Any >> simp[oEL_def] >> gs[OPTION_TYPE_def,FILENAME_def]) >>
    reverse $ xlet ‘POSTv data_strv. &OPTION_TYPE STRING_TYPE (SOME (strlit contents)) data_strv * STDIO fs’
    >- (ntac 2 (xlet_auto >- xsimpl) >> xapp >>
        gs[output_from_data_string_def,test_results_to_string_def,oEL_def,test_from_strings_def]) >>
    pop_assum mp_tac >> rw[OPTION_TYPE_def] >> xmatch >>
    simp[v_of_pat_norest_def,v_of_pat_def,AllCaseEqs ()] >>
    reverse conj_tac >- (EVAL_TAC >> simp[]) >>
    xlet_auto >- (xret >> xsimpl) >>
    xapp_spec inputAllFrom_SOME_spec >> qexistsl [‘emp’,‘fs’,‘fname’] >>
    xsimpl >> rw[OPTION_TYPE_def]
QED

(* DISSERTATION PROG SPEC *)
Theorem seldonian_filter_whole_prog_spec:
     ∀cl fs ename lntol_str sqtol_str fname lntol sqtol d_rl_ex_l.
        hasFreeFD fs ∧ (∃fv. FILENAME fname fv) ∧
        fromString lntol_str = SOME lntol ∧ fromString sqtol_str = SOME sqtol ∧
        do contents <- file_content fs fname; data_from_string (strlit contents) od = SOME d_rl_ex_l ∧
        cl = [ename; lntol_str; sqtol_str; fname] ⇒
        whole_prog_spec main_v cl fs NONE
        (λfsp. fsp = add_stdout fs
            (test_results_to_string (SOME (extend_math_core (hoef_rat_math_core lntol sqtol) d_rl_ex_l)) ^ «\n»))
Proof
    rw[whole_prog_spec_def] >>
    qmatch_goalsub_abbrev_tac ‘_ with numchars := _ = fsp’ >>
    qexists_tac ‘fsp’ >>
    simp[Abbr ‘fsp’,GSYM add_stdo_with_numchars,with_same_numchars] >>
    irule_at Any app_wgframe >> irule_at Any seldonian_filter_spec >>
    qexistsl [‘sqtol_str’,‘sqtol’,‘lntol_str’,‘lntol’,‘fv’,‘fs’,‘fname’,‘ename’,‘d_rl_ex_l’,‘emp’] >>
    xsimpl
QED

val (call_thm_seldonian_filter, seldonian_filter_prog_tm) =
    whole_prog_thm (get_ml_prog_state ()) "main" $ UNDISCH $ SPEC_ALL seldonian_filter_whole_prog_spec;

Definition seldonian_filter_prog_def:
    seldonian_filter_prog = ^seldonian_filter_prog_tm
End

Theorem seldonian_filter_semantics = call_thm_seldonian_filter
    |> ONCE_REWRITE_RULE[GSYM seldonian_filter_prog_def]
    |> DISCH_ALL
    |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
    |> GEN_ALL

val _ = export_theory();
