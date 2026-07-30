open HolKernel Parse boolLib bossLib;
open simpLib;
open combinTheory;
open pairTheory;
open pred_setTheory;
open listTheory;
open arithmeticTheory;
open realTheory;
open realLib;
open real_sigmaTheory;
open transcTheory;
open extrealTheory;
open sigma_algebraTheory;
open real_borelTheory;
open borelTheory;
open measureTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

open ex_machina;
open trivialTheory;
open trivialSimps;
open while_measureTheory;
open sqrtTheory;
open lnTheory;
open hoeffdingTheory;

val _ = new_theory "seldonian";

val _ = reveal "C";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss,TRIVIAL_ss];

(*** General Real Stuff ***)

Definition extend_math_core_def:
    extend_math_core math_core [] = T ∧
    extend_math_core math_core ((d,rl,ex)::t) =
        (math_core d rl ex ∧ extend_math_core math_core t)
End

Theorem extend_math_core_alt:
    ∀math_core d_rl_ex_l. extend_math_core math_core d_rl_ex_l ⇔
        ∀d rl ex. MEM (d,rl,ex) d_rl_ex_l ⇒ math_core d rl ex
Proof
    rw[] >> Induct_on ‘d_rl_ex_l’ >- (simp[extend_math_core_def]) >>
    qx_gen_tac ‘h’ >> ‘∃d rl ex. h = (d,rl,ex)’ by metis_tac[PAIR] >> gvs[] >>
    simp[extend_math_core_def] >> metis_tac[]
QED

Definition extend_valid_funs_def:
    extend_valid_funs valid_funs Dp [] = T ∧
    extend_valid_funs valid_funs Dp ((g,ghat,exfun)::t) =
        (valid_funs Dp g ghat exfun ∧ extend_valid_funs valid_funs Dp t)
End

Theorem extend_valid_funs_alt:
    ∀valid_funs Dp funsl. extend_valid_funs valid_funs Dp funsl ⇔
        ∀g ghat exfun. MEM (g,ghat,exfun) funsl ⇒ valid_funs Dp g ghat exfun
Proof
    rw[] >> Induct_on ‘funsl’ >- (simp[extend_valid_funs_def]) >>
    qx_gen_tac ‘h’ >> ‘∃g ghat exfun. h = (g,ghat,exfun)’ by metis_tac[PAIR] >> gvs[] >>
    simp[extend_valid_funs_def] >> metis_tac[]
QED

Definition seldonian_algorithm_def:
    seldonian_algorithm math_core model data d_ghat_exf_l =
        if extend_math_core math_core
            (MAP (λ(d,ghat,exfun). (d,ghat model data,exfun model data)) d_ghat_exf_l)
        then SOME model else NONE
End

Theorem seldonian_algorithm_NONE:
    ∀math_core model data d_ghat_exf_l. seldonian_algorithm math_core model data d_ghat_exf_l = NONE ⇔
        ∃d ghat exfun. MEM (d,ghat,exfun) d_ghat_exf_l ∧ ¬math_core d (ghat model data) (exfun model data)
Proof
    rw[seldonian_algorithm_def,extend_math_core_alt] >>
    simp[MEM_MAP,PULL_EXISTS,LAMBDA_PROD,EXISTS_PROD]
QED

Theorem seldonian_algorithm_SOME:
    ∀math_core model data d_ghat_exf_l. seldonian_algorithm math_core model data d_ghat_exf_l = SOME model ⇔
        ∀d ghat exfun. MEM (d,ghat,exfun) d_ghat_exf_l ⇒ math_core d (ghat model data) (exfun model data)
Proof
    rw[seldonian_algorithm_def,extend_math_core_alt] >>
    simp[MEM_MAP,PULL_EXISTS,LAMBDA_PROD,EXISTS_PROD]
QED

Theorem seldonian_algorithm_cases:
    ∀math_core model data d_ghat_exf_l.
        seldonian_algorithm math_core model data d_ghat_exf_l = NONE ∨
        seldonian_algorithm math_core model data d_ghat_exf_l = SOME model
Proof
    rw[seldonian_algorithm_def]
QED

Definition valid_math_core_def:
    valid_math_core valid_funs math_core = ∀Dp g ghat exfun d model.
        prob_space Dp ∧ valid_funs Dp g ghat exfun ⇒
            let
                fail_set = {D | ¬math_core d (ghat model D) (exfun model D)} ∩ p_space Dp
            in
                fail_set ∈ events Dp ∧
                (0r < d ∧ 0x < g model ⇒ Normal (1 - d) ≤ prob Dp fail_set)
End

Definition constraint_satisfied_def:
    constraint_satisfied g NONE = T ∧
    constraint_satisfied g (SOME model) = (g model ≤ 0x)
End

Theorem constraint_satisfied_alt:
    ∀g out. constraint_satisfied g out ⇔ out = NONE ∨ g (THE out) ≤ 0
Proof
    rw[] >> Cases_on ‘out’ >> simp[constraint_satisfied_def]
QED

Theorem constraint_satisfied_seldonian_algorithm:
    ∀math_core model data d_ghat_exf_l g.
        constraint_satisfied g (seldonian_algorithm math_core model data d_ghat_exf_l) ⇔
        g model ≤ 0 ∨
        ∃d ghat exfun. MEM (d,ghat,exfun) d_ghat_exf_l ∧ ¬math_core d (ghat model data) (exfun model data)
Proof
    rw[constraint_satisfied_alt] >>
    qspecl_then [‘math_core’,‘model’,‘data’,‘d_ghat_exf_l’] assume_tac seldonian_algorithm_cases >>
    gs[] >> gs[seldonian_algorithm_NONE,seldonian_algorithm_SOME] >> metis_tac[]
QED

(* extend_valid_funs_alt *)
Theorem seldonian_algorithm_constraint_satisfied_event:
    ∀math_core valid_funs Dp model g_d_ghat_exf_l. prob_space Dp ∧
        valid_math_core valid_funs math_core ∧
        extend_valid_funs valid_funs Dp (MAP (λ(g,d,ghat,exfun). (g,ghat,exfun)) g_d_ghat_exf_l) ⇒
        ∀g. ({D | constraint_satisfied g
            (seldonian_algorithm math_core model D (MAP SND g_d_ghat_exf_l))} ∩ p_space Dp) ∈
            events Dp
Proof
    rw[] >> reverse $ Cases_on ‘0 < g model’
    >- (gs[extreal_not_lt] >> qmatch_goalsub_abbrev_tac ‘(s ∩ _) ∈ _’ >>
        ‘s = UNIV’ by (rw[Abbr ‘s’,EXTENSION] >>
            rw[seldonian_algorithm_def,constraint_satisfied_def]) >>
        pop_assum SUBST1_TAC >> simp[EVENTS_SPACE]) >>
    simp[constraint_satisfied_seldonian_algorithm,GSYM extreal_not_lt] >>
    qmatch_goalsub_abbrev_tac ‘s ∈ _’ >>
    ‘s = BIGUNION (IMAGE (λ(d,ghat,exfun). {D |
      ¬math_core d (ghat model D) (exfun model D)} ∩ p_space Dp)
      (set (MAP SND g_d_ghat_exf_l)))’ by (
        simp[Abbr ‘s’,Once EXTENSION,PULL_EXISTS,LAMBDA_PROD,EXISTS_PROD] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac ‘s’ >> irule EVENTS_COUNTABLE_UNION >>
    simp[image_countable,finite_countable,FINITE_LIST_TO_SET] >>
    simp[SUBSET_DEF,PULL_EXISTS,LAMBDA_PROD,EXISTS_PROD] >>
    pop_assum kall_tac >> qx_genl_tac [‘d’,‘ghat’,‘exfun’] >> rw[] >>
    gvs[extend_valid_funs_alt,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    gs[valid_math_core_def,IMP_CONJ_THM,FORALL_AND_THM] >>
    last_x_assum $ irule_at Any >> simp[] >> first_x_assum $ irule_at Any >>
    pop_assum $ irule_at Any
QED

(*
Theorem seldonian_algorithm_constraint_satisfied_event:
    ∀math_core valid_funs Dp model g_d_ghat_exf_l. prob_space Dp ∧
        valid_math_core valid_funs math_core ∧
        (∀g d ghat exfun. MEM (g,d,ghat,exfun) g_d_ghat_exf_l ⇒ valid_funs Dp g ghat exfun) ⇒
        ∀g. ({D | constraint_satisfied g
            (seldonian_algorithm math_core model D (MAP SND g_d_ghat_exf_l))} ∩ p_space Dp) ∈
            events Dp
Proof
    rw[] >> reverse $ Cases_on ‘0 < g model’
    >- (gs[extreal_not_lt] >> qmatch_goalsub_abbrev_tac ‘(s ∩ _) ∈ _’ >>
        ‘s = UNIV’ by (rw[Abbr ‘s’,EXTENSION] >>
            rw[seldonian_algorithm_def,constraint_satisfied_def]) >>
        pop_assum SUBST1_TAC >> simp[EVENTS_SPACE]) >>
    simp[constraint_satisfied_seldonian_algorithm,GSYM extreal_not_lt] >>
    qmatch_goalsub_abbrev_tac ‘s ∈ _’ >>
    ‘s = BIGUNION (IMAGE (λ(d,ghat,exfun). {D |
      ¬math_core d (ghat model D) (exfun model D)} ∩ p_space Dp)
      (set (MAP SND g_d_ghat_exf_l)))’ by (
        simp[Abbr ‘s’,Once EXTENSION,PULL_EXISTS,LAMBDA_PROD,EXISTS_PROD] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac ‘s’ >> irule EVENTS_COUNTABLE_UNION >>
    simp[image_countable,finite_countable,FINITE_LIST_TO_SET] >>
    simp[SUBSET_DEF,PULL_EXISTS,LAMBDA_PROD,EXISTS_PROD] >>
    pop_assum kall_tac >> qx_genl_tac [‘d’,‘ghat’,‘exfun’] >> rw[] >>
    gs[valid_math_core_def,IMP_CONJ_THM,FORALL_AND_THM] >>
    last_x_assum $ irule_at Any >> simp[] >> first_x_assum $ irule_at Any >>
    gs[MEM_EL] >> qexistsl [‘EL n (MAP FST g_d_ghat_exf_l)’,‘d’,‘n’] >> simp[EL_MAP]
QED
*)

Theorem seldonian_algorithm_constraint_satisfied_prob:
    ∀math_core valid_funs Dp model g_d_ghat_exf_l. prob_space Dp ∧
        valid_math_core valid_funs math_core ∧
        extend_valid_funs valid_funs Dp (MAP (λ(g,d,ghat,exfun). (g,ghat,exfun)) g_d_ghat_exf_l) ⇒
        ∀d g ghat exfun. 0 < d ∧ MEM (g,d,ghat,exfun) g_d_ghat_exf_l ⇒
            Normal (1 - d) ≤ prob Dp ({D | constraint_satisfied g
                (seldonian_algorithm math_core model D (MAP SND g_d_ghat_exf_l))} ∩ p_space Dp)
Proof
    rw[] >> drule_all_then assume_tac seldonian_algorithm_constraint_satisfied_event >>
    ‘valid_funs Dp g ghat exfun’ by (
        gvs[extend_valid_funs_alt,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >> metis_tac[]) >>
    gs[valid_math_core_def,IMP_CONJ_THM,FORALL_AND_THM] >>
    ntac 2 $ last_x_assum $ drule_at_then (Pos $ el 2) assume_tac >> gs[] >>
    ntac 2 $ first_x_assum $ qspecl_then [‘d’,‘model’] assume_tac >> gs[] >>
    reverse $ Cases_on ‘0 < g model’
    >- (gs[extreal_not_lt] >> qmatch_goalsub_abbrev_tac ‘prob _ (s ∩ _)’ >>
        ‘s = UNIV’ by (rw[Abbr ‘s’,EXTENSION] >>
            rw[seldonian_algorithm_def,constraint_satisfied_def]) >>
        pop_assum SUBST1_TAC >> simp[PROB_UNIV]) >>
    gs[] >> irule le_trans >> first_x_assum $ irule_at Any >>
    irule PROB_INCREASING >> simp[] >>
    simp[SUBSET_DEF] >> qx_gen_tac ‘D’ >> strip_tac >>
    qmatch_goalsub_abbrev_tac ‘constraint_satisfied _ out’ >>
    ‘out = NONE’ suffices_by simp[constraint_satisfied_def] >>
    qunabbrev_tac ‘out’ >>
    simp[seldonian_algorithm_NONE] >> qexistsl [‘d’,‘ghat’,‘exfun’] >> simp[] >>
    qspecl_then [‘SND’,‘g_d_ghat_exf_l’,‘(g,d,ghat,exfun)’] mp_tac MEM_MAP_f >> simp[]
QED

(*
Theorem seldonian_algorithm_constraint_satisfied_prob:
    ∀math_core valid_funs Dp model g_d_ghat_exf_l. prob_space Dp ∧
        valid_math_core valid_funs math_core ∧
        (∀g d ghat exfun. MEM (g,d,ghat,exfun) g_d_ghat_exf_l ⇒ valid_funs Dp g ghat exfun) ⇒
        ∀d g ghat exfun. 0 < d ∧ MEM (g,d,ghat,exfun) g_d_ghat_exf_l ⇒
            Normal (1 - d) ≤ prob Dp ({D | constraint_satisfied g
                (seldonian_algorithm math_core model D (MAP SND g_d_ghat_exf_l))} ∩ p_space Dp)
Proof
    rw[] >> drule_all_then assume_tac seldonian_algorithm_constraint_satisfied_event >>
    last_x_assum $ drule_then assume_tac >>
    gs[valid_math_core_def,IMP_CONJ_THM,FORALL_AND_THM] >>
    ntac 2 $ last_x_assum $ drule_at_then (Pos $ el 2) assume_tac >> gs[] >>
    ntac 2 $ first_x_assum $ qspecl_then [‘d’,‘model’] assume_tac >> gs[] >>
    reverse $ Cases_on ‘0 < g model’
    >- (gs[extreal_not_lt] >> qmatch_goalsub_abbrev_tac ‘prob _ (s ∩ _)’ >>
        ‘s = UNIV’ by (rw[Abbr ‘s’,EXTENSION] >>
            rw[seldonian_algorithm_def,constraint_satisfied_def]) >>
        pop_assum SUBST1_TAC >> simp[PROB_UNIV]) >>
    gs[] >> irule le_trans >> first_x_assum $ irule_at Any >>
    irule PROB_INCREASING >> simp[] >>
    simp[SUBSET_DEF] >> qx_gen_tac ‘D’ >> strip_tac >>
    qmatch_goalsub_abbrev_tac ‘constraint_satisfied _ out’ >>
    ‘out = NONE’ suffices_by simp[constraint_satisfied_def] >>
    qunabbrev_tac ‘out’ >>
    simp[seldonian_algorithm_NONE] >> qexistsl [‘d’,‘ghat’,‘exfun’] >> simp[] >>
    qspecl_then [‘SND’,‘g_d_ghat_exf_l’,‘(g,d,ghat,exfun)’] mp_tac MEM_MAP_f >> simp[]
QED
*)

Theorem extend_math_core_seldonian_filter:
    ∀math_core valid_funs Dp model g_d_ghat_exf_l. prob_space Dp ∧
        valid_math_core valid_funs math_core ∧
        extend_valid_funs valid_funs Dp (MAP (λ(g,d,ghat,exfun). (g,ghat,exfun)) g_d_ghat_exf_l) ⇒
        ∀d g ghat exfun. 0 < d ∧ MEM (g,d,ghat,exfun) g_d_ghat_exf_l ∧ 0 < g model ⇒
            Normal (1 − d) ≤ prob Dp ({D | ¬extend_math_core math_core
                (MAP (λ(g,d,ghat,exfun). (d,ghat model D,exfun model D)) g_d_ghat_exf_l)} ∩ p_space Dp)
Proof
    rw[] >> drule_all seldonian_algorithm_constraint_satisfied_prob >>
    simp[seldonian_algorithm_def,constraint_satisfied_def,COND_RAND,MAP_MAP_o,o_DEF,LAMBDA_PROD] >>
    disch_then $ qspec_then ‘model’ mp_tac >> simp[ineq_imp]
QED

(*
Theorem extend_math_core_seldonian_filter:
    ∀math_core valid_funs Dp model g_d_ghat_exf_l. prob_space Dp ∧
        valid_math_core valid_funs math_core ∧
        (∀g d ghat exfun. MEM (g,d,ghat,exfun) g_d_ghat_exf_l ⇒ valid_funs Dp g ghat exfun) ⇒
        ∀d g ghat exfun. 0 < d ∧ MEM (g,d,ghat,exfun) g_d_ghat_exf_l ∧ 0 < g model ⇒
            Normal (1 − d) ≤ prob Dp ({D | ¬extend_math_core math_core
                (MAP (λ(g,d,ghat,exfun). (d,ghat model D,exfun model D)) g_d_ghat_exf_l)} ∩ p_space Dp)
Proof
    rw[] >> drule_all seldonian_algorithm_constraint_satisfied_prob >>
    simp[seldonian_algorithm_def,constraint_satisfied_def,COND_RAND,MAP_MAP_o,o_DEF,LAMBDA_PROD] >>
    disch_then $ qspec_then ‘model’ mp_tac >> simp[ineq_imp]
QED
*)

Definition safe_output_def:
    safe_output gl NONE = T ∧
    safe_output [] (SOME model) = T ∧
    safe_output (gh::gt) (SOME model) = (gh model ≤ 0x ∧ safe_output gt (SOME model))
End

Theorem safe_output_alt:
    ∀gs out. safe_output gs out ⇔ out = NONE ∨
        ∃model. out = SOME model ∧ ∀g. MEM g gs ⇒ g model ≤ 0
Proof
    rw[] >> Cases_on ‘out’ >> simp[safe_output_def] >> rename [‘SOME model’] >>
    Induct_on ‘gs’ >> simp[safe_output_def] >> metis_tac[]
QED

(*** Hoeffding's ***)

(* math for hoeffding-based seldonian test, assumes CI bounded from above *)
(* input rl: real list; list of estimates *)
(* input abl: (a,b) list; list of bounds *)
(* input d: real; δ for a test *)
(* outbut: boolean; passes test *)
Definition hoef_real_math_core_def:
    hoef_real_math_core d rl abl =
        if LENGTH abl ≠ LENGTH rl then F
        else
            let
                n = LENGTH rl;
                est = REAL_LIST_SUM rl / &n;
                c = sqrt (ln d⁻¹ * REAL_LIST_SUM (MAP (λ(a,b). (b - a)²) abl) / (2 * (&n)²))
            in
                est + c ≤ 0
End

Definition hoef_valid_funs_def:
    hoef_valid_funs Dp g ghat ablf ⇔
        (∀model data. data ∈ p_space Dp ⇒ ghat model data ≠ []) ∧
        ∃abln. (∀model data. data ∈ p_space Dp ⇒ ablf model data = abln model (LENGTH (ghat model data))) ∧
            ∀model n.
                let
                    sn = {D | LENGTH (ghat model D) = n} ∩ p_space Dp;
                    Dpn = cond_prob_space Dp sn;
                    abl = abln model n
                in
                    sn ∈ events Dp ∧
                    LENGTH abl = n ∧
                    ∃Xl. LENGTH Xl = n ∧
                        (∀X. MEM X Xl ⇒ real_random_variable X Dpn) ∧
                        (∀data. data ∈ p_space Dpn ⇒
                            MAP Normal (ghat model data) = MAP (λX. X data) Xl) ∧
                        (sn ∉ null_set Dp ⇒
                            indep_vars Dpn (C EL Xl) (K Borel) (count n) ∧
                            (∀X. MEM X Xl ⇒ expectation Dpn X = g model) ∧
                            (∀i. i < n ⇒ AE data::Dpn.
                                Normal (FST (EL i abl)) ≤ (EL i Xl) data ∧
                                (EL i Xl) data ≤ Normal (SND (EL i abl))))
End

Theorem hoef_valid_funs_skolem:
    ∀Dp g ghat ablf. hoef_valid_funs Dp g ghat ablf ⇔
        (∀model data. data ∈ p_space Dp ⇒ ghat model data ≠ []) ∧
        ∃Xsk ask bsk.
            (∀model data. data ∈ p_space Dp ⇒
                let
                    n = LENGTH (ghat model data)
                in
                    ablf model data = GENLIST (λi. (ask model n i,bsk model n i)) n) ∧
            ∀model n.
                let
                    sn = {D | LENGTH (ghat model D) = n} ∩ p_space Dp;
                    Dpn = cond_prob_space Dp sn
                in
                    sn ∈ events Dp ∧
                    (∀i. i < n ⇒ real_random_variable (Xsk model n i) Dpn) ∧
                    (∀data. data ∈ p_space Dpn ⇒
                        ghat model data = GENLIST (λi. real (Xsk model n i data)) n) ∧
                    (sn ∉ null_set Dp ⇒
                        indep_vars Dpn (Xsk model n) (K Borel) (count n) ∧
                        (∀i. i < n ⇒ expectation Dpn (Xsk model n i) = g model) ∧
                        ∀i. i < n ⇒ AE D::Dpn. Normal (ask model n i) ≤ Xsk model n i D ∧
                            Xsk model n i D ≤ Normal (bsk model n i))
Proof
    rw[hoef_valid_funs_def,EQ_IMP_THM] >> simp[]
    >- (gs[PULL_EXISTS,SKOLEM_THM] >> pop_assum mp_tac >>
        rename [‘MEM _ (Xlf _ _)’] >> disch_tac >>
        qexistsl [‘λmodel n i. EL i (Xlf model n)’,
            ‘λmodel n i. FST (EL i (abln model n))’,‘λmodel n i. SND (EL i (abln model n))’] >>
        conj_tac >- (rw[] >> metis_tac[GENLIST_ID]) >>
        rpt gen_tac >> last_x_assum $ qspecl_then [‘model’,‘n’] assume_tac >>
        gs[C_DEF,rich_listTheory.EL_MEM] >> rw[] >>
        first_x_assum $ dxrule_at Any >> disch_then $ mp_tac o AP_TERM “MAP real” >>
        simp[MAP_MAP_o,o_DEF] >> disch_then kall_tac >> simp[GSYM GENLIST_EL_MAP]) >>
    qexists ‘λmodel n. GENLIST (λi. (ask model n i,bsk model n i)) n’ >>
    conj_tac >> rw[] >> first_x_assum $ qspecl_then [‘model’,‘n’] assume_tac >> gs[] >>
    qexists ‘GENLIST (Xsk model n) n’ >> simp[MEM_GENLIST,PULL_EXISTS] >> conj_tac
    >- (rw[MAP_GENLIST,o_DEF] >> simp[GENLIST_FUN_EQ] >> qx_gen_tac ‘i’ >>
        rw[] >> Cases_on ‘Xsk model n i data’ >> gs[real_random_variable_def]) >>
    strip_tac >> first_x_assum $ drule_then assume_tac >> gs[] >>
    qpat_x_assum ‘indep_vars _ _ _ _’ mp_tac >>
    qmatch_abbrev_tac ‘_ Dpn Xf1 _ _ ⇒ _ Dpn Xf2 _ _’ >>
    rw[indep_vars_def] >> first_x_assum $ drule_all_then mp_tac >>
    qmatch_abbrev_tac ‘_ _ (BIGINTER s1) = v1 ⇒ _ _ (BIGINTER s2) = v2’ >>
    ‘s1 = s2 ∧ v1 = v2’ suffices_by simp[] >> qunabbrevl_tac [‘s1’,‘s2’,‘v1’,‘v2’] >>
    irule_at Any EXTREAL_PROD_IMAGE_EQ >> irule_at Any IMAGE_CONG >>
    csimp[] >> qx_gen_tac ‘i’ >> strip_tac >>
    ‘Xf1 i = Xf2 i’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
    gs[SUBSET_DEF,EL_GENLIST]
QED

Theorem hoef_valid_funs_paper:
    ∀Dp g ghat ablf. hoef_valid_funs Dp g ghat ablf ⇔ ∀model.
        let
            M = (λD. LENGTH (ghat model D));
            sm = (λm. {D | LENGTH (ghat model D) = m} ∩ p_space Dp);
            Dpm = (λm. cond_prob_space Dp (sm m))
        in
            (∀m. sm m ∈ events Dp) ∧
            (∀D. D ∈ p_space Dp ⇒ M D ≠ 0) ∧
            ∃Xsk ask bsk.
                (∀D. D ∈ p_space Dp ⇒ let m = M D in
                    ghat model D = GENLIST (λj. real (Xsk m j D)) m ∧
                    ablf model D = GENLIST (λj. (ask m j,bsk m j)) m) ∧
                ∀m.
                    (∀j. j < m ⇒ real_random_variable (Xsk m j) (Dpm m)) ∧
                    (sm m ∉ null_set Dp ⇒
                        indep_vars (Dpm m) (Xsk m) (K Borel) (count m) ∧
                        (∀j. j < m ⇒ expectation (Dpm m) (Xsk m j) = g model) ∧
                        ∀j. j < m ⇒ AE D::(Dpm m). Normal (ask m j) ≤ Xsk m j D ∧
                            Xsk m j D ≤ Normal (bsk m j))
Proof
    rw[hoef_valid_funs_skolem,EQ_IMP_THM] >> simp[]
    >- (qexistsl [‘Xsk model’,‘ask model’,‘bsk model’] >> simp[] >>
        gs[p_space_cond_prob_space])
    >- (gs[PULL_EXISTS,SKOLEM_THM] >>
        rename [‘Normal (ask _ _ _) ≤ Xsk _ _ _ _ ∧ Xsk _ _ _ _ ≤ Normal (bsk _ _ _)’] >>
        qexistsl [‘Xsk’,‘ask’,‘bsk’] >> simp[] >> gs[p_space_cond_prob_space])
QED

Theorem valid_math_core_hoef_real:
    valid_math_core hoef_valid_funs hoef_real_math_core
Proof
    simp[valid_math_core_def] >> rpt gen_tac >> disch_tac >>
    gs[hoef_valid_funs_skolem] >>
    ntac 3 $ last_x_assum $ qspec_then ‘model’ assume_tac >>
    map_every qabbrev_tac [‘N = λD. LENGTH (ghat model D)’,
        ‘sn = λn. {D | LENGTH (ghat model D) = n} ∩ p_space Dp’,
        ‘Jn = λn. if sn n ∉ null_set Dp then count n else ∅’,
        ‘Dpn = λn. cond_prob_space Dp (sn n)’,
        ‘an = λn. ask model n’, ‘bn = λn. bsk model n’, ‘Xn = λn. Xsk model n’] >>
    gs[FORALL_AND_THM] >> ‘∀n i. i ∈ Jn n ⇒ i < n’ by rw[Abbr ‘Jn’] >>
    qmatch_goalsub_abbrev_tac ‘prob _ test_s’ >>
    qspecl_then [‘Dp’,‘Xn’,‘an’,‘bn’,‘Jn’,‘N’,‘d’]
        (mp_tac o SRULE [LET_DEF]) hoeffding_ineq_inf_neg_avg_ci >>
    simp[] >> qmatch_goalsub_abbrev_tac ‘prob _ hoef_s’ >>
    qabbrev_tac ‘v = {D | sn (N D) ∈ null_set Dp} ∩ p_space Dp’ >>
    ‘v ∈ null_set Dp’ by (
        ‘v = BIGUNION (IMAGE (λn. if sn n ∈ null_set Dp then sn n else ∅) UNIV)’ by (
            simp[Abbr ‘v’,Abbr ‘sn’,Once EXTENSION,PULL_EXISTS,IN_APP,COND_RATOR]) >>
        pop_assum SUBST1_TAC >> irule NULL_SET_BIGUNION >>
        simp[COND_RAND,COND_RATOR,prob_space_measure_space] >>
        rw[] >> disj2_tac >> simp[NULL_SET_THM,prob_space_measure_space]) >>
    ‘(0 < g model ⇒ ∀D. D ∈ p_space Dp DIFF v ⇒ D ∈ hoef_s ⇒ D ∈ test_s) ∧
      test_s ∈ events Dp’ suffices_by (
        rw[] >> gs[] >> qpat_x_assum ‘_ ⇒ _’ concl_tac
        >- (rw[Abbr ‘Jn’,indep_vars_empty]) >>
        irule le_trans >> gs[] >> first_x_assum $ irule_at Any >>
        irule_at Any PROB_INCREASING_AE >> gs[] >>
        simp[AE_DEF] >> qexists ‘v’ >> gs[IN_APP,p_space_def]) >>
    gs[hoef_real_math_core_def,REAL_NOT_LE] >>
    map_every qabbrev_tac [‘tst_f = λD. REAL_LIST_SUM (ghat model D) / &N D +
          sqrt (REAL_LIST_SUM (MAP (λ(a,b). (b − a)²) (exfun model D)) * ln d⁻¹ / (2 * (&N D)²))’,
        ‘hoef_f = λD. (&CARD (Jn (N D)))⁻¹ * ∑ (C (Xn (N D)) D) (Jn (N D)) +
          Normal (sqrt (ln d⁻¹ * ∑ (λn. (bn (N D) n − an (N D) n)²) (Jn (N D)) / (2 * (&CARD (Jn (N D)))²)))’,
        ‘hoef_c = λD. expectation (Dpn (N D)) (λy. (&CARD (Jn (N D)))⁻¹ * ∑ (C (Xn (N D)) y) (Jn (N D)))’] >>
    ‘test_s = {D | 0 < tst_f D} ∩ p_space Dp’ by (
        simp[EXTENSION,Abbr ‘test_s’] >> qx_gen_tac ‘D’ >>
        Cases_on ‘D ∈ p_space Dp’ >> simp[]) >>
    pop_assum SUBST1_TAC >> gs[] >> qunabbrevl_tac [‘test_s’,‘hoef_s’] >>
    ‘∀D. D ∈ p_space Dp ∧ ¬(v D) ⇒ hoef_c D = g model’ by (
        qunabbrevl_tac [‘tst_f’,‘hoef_f’,‘hoef_c’,‘v’,‘Jn’] >> gs[SF PROB_ss] >> rw[] >>
        ‘prob_space (Dpn (N D))’ by (simp[Abbr ‘Dpn’] >>
            irule prob_space_cond_prob_space >> simp[SF PROB_ss] >> gs[IN_APP,null_set_def]) >>
        ‘∀i. i < N D ⇒ integrable (Dpn (N D)) (Xn (N D) i)’ by (
            rw[] >> irule integrable_AE_bounded_Borel_measurable >>
            irule_at Any prob_space_finite_measure_space >> simp[] >> metis_tac[]) >>
        map_every (qspecl_then [‘Dpn (N D)’,‘Xn (N D)’,‘count (N D)’] mp_tac)
            [integral_sum,integrable_sum] >>
        gs[SF PROB_ss] >> simp[C_DEF] >> qmatch_goalsub_abbrev_tac ‘∫ _ SX’ >> rw[] >>
        ‘N D ≠ 0’ by (CCONTR_TAC >> last_x_assum $ drule >> gs[Abbr ‘N’]) >>
        simp[extreal_of_num_def,extreal_inv_def,integral_cmul] >>
        ‘∑ (λi. ∫ (Dpn (N D)) (Xn (N D) i)) (count (N D)) =
            ∑ (λi. g model) (count (N D))’ by (irule EXTREAL_SUM_IMAGE_EQ' >> simp[]) >>
        pop_assum SUBST1_TAC >>
        qspec_then ‘count (N D)’ mp_tac EXTREAL_SUM_IMAGE_FINITE_CONST >> simp[] >>
        disch_then $ qspecl_then [‘λi. g model’,‘g model’] mp_tac >> simp[] >>
        disch_then kall_tac >>
        simp[extreal_of_num_def,mul_assoc,extreal_mul_def] >> simp[normal_1]) >>
    ‘∀D. D ∈ p_space Dp ⇒ hoef_f D = if v D then 0 else Normal (tst_f D)’ by (
        rw[Abbr ‘v’,Abbr ‘tst_f’,Abbr ‘hoef_f’,Abbr ‘Jn’,SQRT_0] >- gs[] >>
        ‘D ∈ p_space (Dpn (N D))’ by simp[Abbr ‘Dpn’,Abbr ‘sn’,p_space_cond_prob_space] >>
        ntac 3 $ last_x_assum $ drule >> rw[] >>
        simp[MAP_GENLIST,REAL_LIST_SUM_GENLIST_REAL_SUM_IMAGE,o_DEF,Once $ GSYM extreal_add_def] >>
        ‘∀a b c. a = b ⇒ a + c = b + c:extreal’ by simp[] >> pop_assum irule >>
        ‘N D ≠ 0’ by (CCONTR_TAC >> gs[]) >> simp[GSYM extreal_div_eq,extreal_div_def] >>
        simp[GSYM extreal_of_num_def,GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
        ‘∑ (λi. Normal (real (Xn (N D) i D))) (count (N D)) =
            ∑ (C (Xn (N D)) D) (count (N D))’ suffices_by (simp[Once mul_comm]) >>
        irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >> qx_gen_tac ‘i’ >> strip_tac >>
        gs[SF PROB_ss] >> Cases_on ‘Xn (N D) i D’ >> gs[]) >>
    conj_tac
    >- (rw[IN_APP] >> irule REAL_LTE_TRANS >> qexists ‘real (g model)’ >> Cases_on ‘g model’ >> gs[]) >>
    gs[SF PROB_ss] >>
    qspec_then ‘measurable_space Dp’ (irule_at Any o SRULE []) in_borel_measurable_gt_imp >>
    simp[] >> qunabbrevl_tac [‘hoef_f’,‘hoef_c’] >> ntac 2 $ pop_assum kall_tac >>
    ‘∀n. tst_f ∈ borel_measurable (measurable_space (Dpn n))’ suffices_by (
        simp[measurable_def,FUNSET,FORALL_AND_THM] >> strip_tac >> conj_tac
        >- (qx_gen_tac ‘D’ >> rw[] >> last_x_assum $ irule >> qexists ‘N D’ >>
            simp[Abbr ‘Dpn’,Abbr ‘sn’,Abbr ‘N’,m_space_cond_prob_space]) >>
        rw[] >> first_x_assum $ dxrule_then assume_tac >>
        ‘PREIMAGE tst_f s ∩ m_space Dp =
          BIGUNION (IMAGE (λn. PREIMAGE tst_f s ∩ m_space (Dpn n)) UNIV)’ suffices_by (
            disch_then SUBST1_TAC >> irule MEASURE_SPACE_BIGUNION >> rw[] >>
            irule $ SRULE [SF PROB_ss] in_events_cond_prob_space_imp >> simp[] >>
            qexists ‘sn n’ >> simp[]) >>
        simp[Once EXTENSION,PULL_EXISTS] >> qx_gen_tac ‘D’ >> rw[EQ_IMP_THM] >> simp[]
        >- (qexists ‘N D’ >> simp[Abbr ‘Dpn’,Abbr ‘sn’,Abbr ‘N’,m_space_cond_prob_space])
        >- (pop_assum mp_tac >> simp[Abbr ‘Dpn’,Abbr ‘sn’,Abbr ‘N’,m_space_cond_prob_space])) >>
    rw[Abbr ‘tst_f’] >>
    chain_irule_at [
        (Any,in_borel_measurable_add,[‘λD. ∑ (λi. real (Xn n i D)) (count n) / (&n)’,
            ‘λD. sqrt (∑ (λi. (bn n i − an n i)²) (count n) * ln d⁻¹ / (2 * (&n)²))’],[]),
        (Pos last,borel_measurable_const,[],[]),
        (Pos last,in_borel_measurable_div,[‘λD. &n’,‘λD. ∑ (λi. real (Xn n i D)) (count n)’],[]),
        (Pos $ el 2,borel_measurable_const,[],[]),
        (Pos hd,INST_TYPE [“:β”|->“:num”] in_borel_measurable_sum,
            [‘count n’,‘λi. real ∘ Xn n i’],[])] >>
    ‘sigma_algebra (measurable_space (Dpn n))’ by (simp[Abbr ‘Dpn’] >>
        irule $ SRULE [SF PROB_ss] sigma_algebra_event_space_cond_prob_space >> simp[]) >>
    simp[] >> conj_tac >- simp[in_borel_measurable_from_Borel] >>
    qx_gen_tac ‘D’ >> rw[] >>
    ‘D ∈ m_space Dp ∧ N D = n’ by (pop_assum mp_tac >>
        simp[Abbr ‘Dpn’,Abbr ‘sn’,Abbr ‘N’,m_space_cond_prob_space]) >>
    ntac 2 $ first_x_assum $ drule >>
    simp[MAP_GENLIST,REAL_LIST_SUM_GENLIST_REAL_SUM_IMAGE,o_DEF]
QED

(* DISSERTATION RAT CORE *)
Definition hoef_rat_math_core_def:
    hoef_rat_math_core lntol sqtol d rl abl =
        if lntol ≤ 0r ∨ sqtol ≤ 0r ∨ d ≤ 0 ∨ 1 < d ∨ rl = [] ∨ LENGTH abl ≠ LENGTH rl then F
        else
            let
                n = LENGTH rl;
                est = REAL_LIST_SUM rl / &n;
                lndi = rational_log lntol d⁻¹ + lntol;
                cc = lndi * REAL_LIST_SUM (MAP (λ(a,b). (b - a)²) abl) / (2 * (&n)²);
                c = rational_sqrt sqtol cc + sqtol
            in
                est + c ≤ 0
End

Theorem hoef_real_math_core_hoef_rat_math_core:
    ∀d rl abl. 0 < d ∧ d ≤ 1 ∧ rl ≠ [] ∧ ¬hoef_real_math_core d rl abl ⇒
        ∀lntol sqtol. 0 < lntol ∧ 0 < sqtol ⇒ ¬hoef_rat_math_core lntol sqtol d rl abl
Proof
    rw[] >> qpat_x_assum ‘¬ _’ mp_tac >>
    simp[hoef_real_math_core_def,hoef_rat_math_core_def,REAL_NOT_LE,iffRL REAL_NOT_LE] >>
    Cases_on ‘LENGTH abl = LENGTH rl’ >> simp[] >>
    qmatch_goalsub_abbrev_tac ‘_ < est + realc ⇒ _ < _ + ratc’ >>
    disch_tac >> irule REAL_LTE_TRANS >> pop_assum $ irule_at Any >> simp[] >>
    UNABBREV_ALL_TAC >> qmatch_goalsub_abbrev_tac ‘sqrt (bas * _ / len)’ >>
    irule REAL_LE_TRANS >> qexists ‘sqrt (bas * (rational_log lntol d⁻¹ + lntol) / len)’ >>
    irule_at Any SQRT_MONO_LE >> irule_at (Pos last) REAL_LT_IMP_LE >>
    resolve_then Any (irule_at Any o SRULE [REAL_LT_SUB_RADD,Once REAL_ADD_COMM])
        rational_sqrt_accuracy (cj 2 $ iffLR ABS_BOUNDS_LT) >>
    simp[SF CONJ_ss,REAL_LE_TRANS] >> Cases_on ‘abl = []’
    >- simp[Abbr ‘bas’,REAL_LIST_SUM_DEF,FOLDR] >>
    ‘0 < len’ by (simp[Abbr ‘len’] >> CCONTR_TAC >> gs[]) >>
    simp[REAL_LE_RDIV_CANCEL] >> irule_at Any REAL_LE_LMUL_IMP >>
    irule_at Any REAL_LE_MUL >> irule_at (Pos last) REAL_LT_IMP_LE >>
    resolve_then Any (irule_at Any o SRULE [REAL_LT_SUB_RADD,Once REAL_ADD_COMM])
        rational_log_accuracy (cj 2 $ iffLR ABS_BOUNDS_LT) >>
    simp[] >> irule_at Any LN_POS >> simp[Abbr ‘bas’,REAL_LIST_SUM_REAL_SUM_IMAGE] >>
    irule_at Any REAL_SUM_IMAGE_POS >> first_x_assum $ SUBST1_TAC o SYM >> simp[EL_MAP,PAIR_FUN2]
QED

Theorem valid_math_core_hoef_rat:
    ∀lntol sqtol. 0 < lntol ∧ 0 < sqtol ⇒
        valid_math_core hoef_valid_funs (hoef_rat_math_core lntol sqtol)
Proof
    rw[] >> simp[valid_math_core_def] >> rpt gen_tac >>
    strip_tac >> reverse $ conj_asm1_tac
    >- (rw[] >> reverse $ Cases_on ‘d ≤ 1’
        >- (irule le_trans >> qexists ‘0’ >> simp[] >> irule PROB_POSITIVE >> simp[]) >>
        assume_tac valid_math_core_hoef_real >>
        gs[valid_math_core_def] >> pop_assum $ drule_all_then assume_tac >>
        pop_assum $ qspecl_then [‘d’,‘model’] assume_tac >> gs[] >>
        irule le_trans >> pop_assum $ irule_at Any >> irule PROB_INCREASING >>
        gs[hoef_valid_funs_def] >> simp[SUBSET_DEF,hoef_real_math_core_hoef_rat_math_core]) >>
    gs[hoef_valid_funs_skolem] >> ntac 3 $ last_x_assum $ qspec_then ‘model’ assume_tac >>
    map_every qabbrev_tac [‘N = λD. LENGTH (ghat model D)’,
        ‘sn = λn. {D | LENGTH (ghat model D) = n} ∩ p_space Dp’,
        ‘Jn = λn. if sn n ∉ null_set Dp then count n else ∅’,
        ‘Dpn = λn. cond_prob_space Dp (sn n)’,
        ‘an = λn. ask model n’, ‘bn = λn. bsk model n’, ‘Xn = λn. Xsk model n’] >>
    gs[FORALL_AND_THM] >> simp[hoef_rat_math_core_def,REAL_NOT_LE] >>
    Cases_on ‘0 < d’ >> simp[EVENTS_SPACE] >>
    Cases_on ‘1 < d’ >> simp[EVENTS_SPACE] >> ntac 2 $ pop_assum kall_tac >>
    qabbrev_tac ‘tst_f = λD. REAL_LIST_SUM (ghat model D) / &N D +
        (rational_sqrt sqtol (REAL_LIST_SUM (MAP (λ(a,b). (b − a)²) (exfun model D)) *
        (rational_log lntol d⁻¹ + lntol) / (2 * (&N D)²)) + sqtol)’ >>
    gs[SF PROB_ss] >>
    ‘∀n. tst_f ∈ borel_measurable (measurable_space (Dpn n))’ suffices_by (rw[] >>
        ‘{D | LENGTH (exfun model D) = N D ⇒ ghat model D = [] ∨ 0 < tst_f D} ∩ m_space Dp =
          BIGUNION (IMAGE (λn. {D | 0 < tst_f D} ∩ m_space (Dpn n)) UNIV)’ by (
            csimp[Once EXTENSION,PULL_EXISTS] >> qx_gen_tac ‘D’ >> rw[EQ_IMP_THM] >> simp[]
            >| [qexists ‘N D’,pop_assum mp_tac] >>
            simp[Abbr ‘Dpn’,Abbr ‘sn’,Abbr ‘N’,m_space_cond_prob_space]) >>
        pop_assum SUBST1_TAC >> irule MEASURE_SPACE_BIGUNION >> rw[] >>
        irule $ SRULE [SF PROB_ss] in_events_cond_prob_space_imp >>
        simp[] >> qexists ‘sn n’ >> simp[] >>
        qspec_then ‘measurable_space Dp’ (irule o SRULE []) in_borel_measurable_gt_imp >>
        simp[Abbr ‘Dpn’,cond_prob_space_def,events_def] >>
        irule SIGMA_ALGEBRA_RESTRICT >> simp[] >> qexists ‘m_space Dp’ >> simp[]) >>
    rw[Abbr ‘tst_f’] >>
    chain_irule_at [
        (Any,in_borel_measurable_add,[‘λD. ∑ (λi. real (Xn n i D)) (count n) / (&n)’,
            ‘λD. rational_sqrt sqtol (∑ (λi. (bn n i − an n i)²) (count n) *
              (rational_log lntol d⁻¹ + lntol) / (2 * (&n)²)) + sqtol’],[]),
        (Pos last,borel_measurable_const,[],[]),
        (Pos last,in_borel_measurable_div,[‘λD. &n’,‘λD. ∑ (λi. real (Xn n i D)) (count n)’],[]),
        (Pos $ el 2,borel_measurable_const,[],[]),
        (Pos hd,INST_TYPE [“:β”|->“:num”] in_borel_measurable_sum,
            [‘count n’,‘λi. real ∘ Xn n i’],[])] >>
    ‘sigma_algebra (measurable_space (Dpn n))’ by (simp[Abbr ‘Dpn’] >>
        irule $ SRULE [SF PROB_ss] sigma_algebra_event_space_cond_prob_space >> simp[]) >>
    simp[] >> conj_tac >- simp[in_borel_measurable_from_Borel] >>
    qx_gen_tac ‘D’ >> rw[] >>
    ‘D ∈ m_space Dp ∧ N D = n’ by (pop_assum mp_tac >>
        simp[Abbr ‘Dpn’,Abbr ‘sn’,Abbr ‘N’,m_space_cond_prob_space]) >>
    ntac 2 $ first_x_assum $ drule >>
    simp[MAP_GENLIST,REAL_LIST_SUM_GENLIST_REAL_SUM_IMAGE,o_DEF]
QED

Theorem hoef_rat_seld_alg_constraint_satisfied:
    ∀lntol sqtol Dp model g_d_ghat_abf_l. 0 < lntol ∧ 0 < sqtol ∧ prob_space Dp ∧
        extend_valid_funs hoef_valid_funs Dp (MAP (λ(g,d,ghat,abf). (g,ghat,abf)) g_d_ghat_abf_l) ⇒
        ∀d g ghat abf. 0 < d ∧ MEM (g,d,ghat,abf) g_d_ghat_abf_l ⇒
            Normal (1 − d) ≤
                prob Dp ({D | constraint_satisfied g
                    (seldonian_algorithm (hoef_rat_math_core lntol sqtol)
                    model D (MAP SND g_d_ghat_abf_l))} ∩ p_space Dp)
Proof
    metis_tac[valid_math_core_hoef_rat,seldonian_algorithm_constraint_satisfied_prob]
QED

(* DISSERTATION RATIONAL RESULT *)
Theorem extend_hoef_rat_math_core_seldonian_filter:
    ∀lntol sqtol Dp model g_d_ghat_abf_l. 0 < lntol ∧ 0 < sqtol ∧ prob_space Dp ∧
        extend_valid_funs hoef_valid_funs Dp (MAP (λ(g,d,ghat,abf). (g,ghat,abf)) g_d_ghat_abf_l) ⇒
        ∀d g ghat exfun. 0 < d ∧ MEM (g,d,ghat,exfun) g_d_ghat_abf_l ∧ 0 < g model ⇒
            Normal (1 − d) ≤ prob Dp ({D | ¬extend_math_core (hoef_rat_math_core lntol sqtol)
                (MAP (λ(g,d,ghat,exfun). (d,ghat model D,exfun model D)) g_d_ghat_abf_l)} ∩ p_space Dp)
Proof
    metis_tac[valid_math_core_hoef_rat,extend_math_core_seldonian_filter]
QED

(*
Theorem hoef_rat_seld_alg_constraint_satisfied:
    ∀lntol sqtol Dp model g_d_ghat_abf_l. 0 < lntol ∧ 0 < sqtol ∧ prob_space Dp ∧
        (∀g d ghat abf. MEM (g,d,ghat,abf) g_d_ghat_abf_l ⇒ hoef_valid_funs Dp g ghat abf) ⇒
        ∀d g ghat abf. 0 < d ∧ MEM (g,d,ghat,abf) g_d_ghat_abf_l ⇒
            Normal (1 − d) ≤
                prob Dp ({D | constraint_satisfied g
                    (seldonian_algorithm (hoef_rat_math_core lntol sqtol)
                    model D (MAP SND g_d_ghat_abf_l))} ∩ p_space Dp)
Proof
    metis_tac[valid_math_core_hoef_rat,seldonian_algorithm_constraint_satisfied_prob]
QED

Theorem extend_hoef_rat_math_core_seldonian_filter:
    ∀lntol sqtol Dp model g_d_ghat_abf_l. 0 < lntol ∧ 0 < sqtol ∧ prob_space Dp ∧
        (∀g d ghat abf. MEM (g,d,ghat,abf) g_d_ghat_abf_l ⇒ hoef_valid_funs Dp g ghat abf) ⇒
        ∀d g ghat exfun. 0 < d ∧ MEM (g,d,ghat,exfun) g_d_ghat_abf_l ∧ 0 < g model ⇒
            Normal (1 − d) ≤ prob Dp ({D | ¬extend_math_core (hoef_rat_math_core lntol sqtol)
                (MAP (λ(g,d,ghat,exfun). (d,ghat model D,exfun model D)) g_d_ghat_abf_l)} ∩ p_space Dp)
Proof
    metis_tac[valid_math_core_hoef_rat,extend_math_core_seldonian_filter]
QED
*)

(* SND UNZIP -> MAP SND
SRULE [UNZIP_MAP,seldonian_algorithm_def] hoef_rat_seld_alg_constraint_satisfied

Theorem extend_math_core_constraint_satisfied_prob =
    hoef_rat_seld_alg_constraint_satisfied |>
        SRULE [UNZIP_MAP,MAP_MAP_o,o_DEF,LAMBDA_PROD,seldonian_algorithm_def,constraint_satisfied_def,COND_RAND]
*)

val _ = export_theory();
