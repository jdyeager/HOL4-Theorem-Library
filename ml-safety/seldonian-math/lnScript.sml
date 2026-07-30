open HolKernel Parse boolLib bossLib;
open simpLib;
open combinTheory;
open pairTheory;
open prim_recTheory;
open pred_setTheory;
open WhileTheory;
open listTheory;
open arithmeticTheory;
open realTheory;
open realLib;
open iterateTheory;
open real_sigmaTheory;
open real_topologyTheory;
open transcTheory;
open sigma_algebraTheory;
open real_borelTheory;

open ex_machina;
open trivialTheory;
open hyper_trigTheory;
open while_measureTheory;
open natsaTheory;
(*
open trivialSimps;
*)

val _ = new_theory "ln";

val _ = reveal "C";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];
(*
val _ = augment_srw_ss [realSimps.REAL_ARITH_ss,TRIVIAL_ss];
*)

(* Arithmetc Theory *)
Theorem FACT_NOT_ZERO:
    ∀n. FACT n ≠ 0
Proof
    simp[FACT_LESS,LESS_NOT_EQ]
QED

Theorem REAL_POW_1_LT:
    ∀n x. n ≠ 0 ∧ 0 ≤ x ∧ x < 1 ⇒ x pow n < 1r
Proof
    rw[] >> qspecl_then [‘n’,‘x’,‘1’] mp_tac REAL_POW_LT2 >> simp[]
QED

Theorem INFSUM_FINITE_DIFF:
    ∀f s t. t ⊆ s ∧ FINITE t ∧ summable s f ⇒ suminf s f − sum t f = suminf (s DIFF t) f
Proof
    rw[] >> irule SERIES_UNIQUE >> qexistsl [‘f’,‘s DIFF t’] >>
    conj_asm1_tac >- (irule_at Any SUMS_FINITE_DIFF >> simp[SUMS_INFSUM]) >>
    simp[SUMS_INFSUM,summable_def] >> pop_assum $ irule_at Any
QED

Theorem SUMS_REINDEX_TO_0:
    ∀k a l. (a sums l) (from k) ⇔ ((λx. a (x + k)) sums l) UNIV
Proof
    rw[] >> qspecl_then [‘k’,‘a’,‘l’,‘0’] mp_tac SUMS_REINDEX >>
    simp[FROM_0]
QED

(*** General Real Stuff ***)

Definition REAL_LIST_SUM_DEF:
    REAL_LIST_SUM = FOLDR $+ 0r
End

Theorem REAL_LIST_SUM_ALT:
    REAL_LIST_SUM = FOLDL $+ 0r
Proof
    rw[REAL_LIST_SUM_DEF,FUN_EQ_THM] >> irule $ GSYM FOLDL_EQ_FOLDR >>
    simp[ASSOC_DEF,COMM_DEF]
QED

Theorem REAL_LIST_SUM_REAL_SUM_IMAGE:
    ∀l. REAL_LIST_SUM l = ∑ (C EL l) (count (LENGTH l))
Proof
    Induct_on ‘l’ >> gs[REAL_LIST_SUM_DEF] >>
    pop_assum kall_tac >> rw[] >>
    qspecl_then [‘C EL (h::l)’,‘0’,‘IMAGE (λn. n + 1) (count (LENGTH l))’] mp_tac REAL_SUM_IMAGE_INSERT >>
    ‘0 INSERT IMAGE (λn. n + 1) (count (LENGTH l)) = (count1 (LENGTH l))’ by (
        simp[EXTENSION,PULL_EXISTS,EQ_IMP_THM] >> qx_gen_tac ‘i’ >>
        Cases_on ‘i’ >> simp[] >> disch_then $ irule_at Any >> simp[]) >>
    ‘IMAGE (λn. n + 1) (count (LENGTH l)) DELETE 0 = IMAGE (λn. n + 1) (count (LENGTH l))’ by
        simp[EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
    ‘INJ (λn. n + 1) (count (LENGTH l)) (IMAGE (λn. n + 1) (count (LENGTH l)))’ by rw[INJ_DEF] >>
    simp[REAL_SUM_IMAGE_IMAGE,o_DEF] >> disch_then kall_tac >> simp[GSYM ADD1,EL,C_DEF]
QED

Theorem REAL_LIST_SUM_GENLIST_SUM_NUMSEG:
    ∀f n. REAL_LIST_SUM (GENLIST f (SUC n)) = sum {0 .. n} f
Proof
    rw[] >> Induct_on ‘n’ >- simp[GENLIST,REAL_LIST_SUM_DEF,SUM_SING_NUMSEG] >>
    gs[GENLIST,REAL_LIST_SUM_ALT,SUM_CLAUSES_NUMSEG] >> simp[Once FOLDL_SNOC]
QED

Theorem REAL_LIST_SUM_GENLIST_REAL_SUM_IMAGE:
     ∀f n. REAL_LIST_SUM (GENLIST f n) = ∑ f (count n)
Proof
    rw[] >> Cases_on ‘n’ >- simp[REAL_LIST_SUM_DEF] >>
    simp[SRULE [sum_real,REAL_SUM_IMAGE_EQ_sum] REAL_LIST_SUM_GENLIST_SUM_NUMSEG]
QED

(* Rational Log with Polynomial *)

(* takes ar = abs ((x-1)/(x+1)) to save compute time *)
(* using 2N+1 (not 2N) as next N saves computes and prevents stall on N=0 *)
Definition rational_log_helper_init_Nub_def:
    rational_log_helper_init_Nub tol ar N =
        if tol ≤ 0r ∨ ar < 0r ∨ 1 ≤ ar then 0
        else
            let
                rsq = ar * ar;
                Np = 2 * N + 1;
            in
                if 2 * ar * rsq pow N / (&Np * (1 - rsq)) < tol then N
                else rational_log_helper_init_Nub tol ar Np
Termination
    qabbrev_tac ‘remf = λar N. 2r * (ar * ar² pow N) / (&(2 * N + 1) * (1 − ar²))’ >>
    simp[Excl "RMUL_LTNORM"] >> irule_at Any WF_measure >> simp[measure_thm] >>
    ‘∀tol ar. ∃miN. ∀N. 0 < tol ∧ 0 ≤ ar ∧ ar < 1 ∧ miN ≤ N ⇒ (remf ar N < tol)’ suffices_by (
        rw[SKOLEM_THM] >> rename [‘miN _ _ ≤ _’] >> qexists ‘λ(tol,ar,N). miN tol ar - N’ >>
        rw[] >> last_x_assum $ dxrule_at Concl >> gs[]) >>
    rw[GSYM AND_IMP_INTRO,RIGHT_EXISTS_IMP_THM,RIGHT_FORALL_IMP_THM] >>
    ‘∃M. remf ar M < tol’ suffices_by (
        rw[] >> qexists ‘M’ >> rw[] >> irule REAL_LET_TRANS >>
        first_x_assum $ irule_at (Pos hd) >>
        simp[Abbr ‘remf’] >> Cases_on ‘ar = 0’ >- simp[] >>
        rpt $ irule_at Any REAL_LE_MUL2 >> csimp[] >>
        rpt $ irule_at Any REAL_LE_MUL >> csimp[] >>
        irule_at Any REAL_POW_ANTIMONO >> simp[REAL_SUB_LE] >>
        irule REAL_POW_1_LE >> simp[]) >>
    simp[Abbr ‘remf’] >> Cases_on ‘ar = 0’ >- (qexists ‘0’ >> simp[]) >>
    ‘∀c. 0 < c ⇒ ∃M. ar² pow M < c * &(2 * M + 1)’ suffices_by (
        disch_then $ qspec_then ‘tol / (2 * ar * (1 − ar²)⁻¹)’ mp_tac >>
        ‘0 < ar’ by simp[] >> ‘0 < 1 - ar²’ by simp[REAL_SUB_LT,REAL_POW_1_LT] >>
        simp[REAL_LT_MUL]) >>
    rw[] >> irule_at Any REAL_LET_TRANS >> irule_at Any REAL_POW_1_LE >>
    simp[REAL_POW_1_LE] >> qspec_then ‘(1 / c - 1) / 2’ mp_tac REAL_BIGNUM >>
    simp[REAL_LT_SUB_RADD]
End

Definition rational_log_poly_error_def:
    rational_log_poly_error ar N =
        2r * ar pow (2 * N + 1) / (&(2 * N + 1) * (1 - ar²))
End

Theorem rational_log_poly_error_thm:
    ∀r N. -1 < r ∧ r < 1 ⇒
        2 * abs (suminf (from N) ((λi. (&(2 * i + 1))⁻¹ * r pow (2 * i + 1)))) ≤
        rational_log_poly_error (abs r) N
Proof
    rw[rational_log_poly_error_def,Excl "RMUL_LEQNORM"] >>
    qmatch_goalsub_abbrev_tac ‘_ ≤ _ * gu / nk’ >> simp[] >>
    qabbrev_tac ‘f = λ(r:real) i. (&(2 * i + 1))⁻¹ * r pow (2 * i + 1)’ >>
    simp[SF ETA_ss] >> irule REAL_LE_TRANS >> irule_at (Pos hd) SERIES_BOUND >>
    qexistsl [‘from N’,‘f (abs r)’,‘f r’,‘suminf (from N) (f (abs r))’] >>
    ‘∀rar. -1 < rar ∧ rar < 1 ⇒ summable (from N) (f rar)’ by (rw[] >>
        drule_all_then mp_tac ATANH_POLYNOMIAL_SUMMABLE >> simp[SF ETA_ss] >>
        rw[] >> irule SUMMABLE_FROM_ELSEWHERE >> qexists ‘0’ >> simp[FROM_0]) >>
    simp[SUMS_INFSUM] >> conj_tac
    >- simp[Abbr ‘f’,REAL_ABS_MUL,ABS_INV,GSYM POW_ABS] >>
    qabbrev_tac ‘ar = abs r’ >> ‘0 ≤ ar ∧ ar < 1 ∧ r² = ar²’ by simp[Abbr ‘ar’] >>
    pop_assum SUBST_ALL_TAC >> ntac 2 $ last_x_assum kall_tac >>
    qpat_x_assum ‘Abbrev _’ kall_tac >> Cases_on ‘ar = 0’
    >- (unabbrev_all_tac >> simp[POW_0',INFSUM_0]) >>
    first_x_assum $ drule_at Any >> simp[] >> disch_tac >>
    gs[GSYM SUMS_INFSUM] >> dxrule_all_then assume_tac $ iffLR SUMS_REINDEX_TO_0 >>
    drule_then (SUBST1_TAC o SYM) INFSUM_UNIQUE >>
    qunabbrev_tac ‘f’ >> gs[] >> qmatch_abbrev_tac ‘_ _ f ≤ (_:real)’ >>
    resolve_then Any (dxrule_then assume_tac) SUMS_SUMMABLE (iffRL SUMS_INFSUM) >>
    dxrule_then (qspec_then ‘1 / gu’ assume_tac) SERIES_CMUL >>
    drule_then (mp_tac o SYM) INFSUM_UNIQUE >> simp[Abbr ‘gu’] >>
    disch_then kall_tac >> qunabbrev_tac ‘f’ >> gs[] >> qmatch_abbrev_tac ‘_ _ f ≤ (_:real)’ >>
    resolve_then Any (dxrule_then assume_tac) SUMS_SUMMABLE (iffRL SUMS_INFSUM) >>
    ‘abs ar² < 1’ by rw[abs,POW_2_LT_1] >> simp[Abbr ‘nk’,REAL_INV_MUL',GSYM INFSUM_GEOM] >>
    dxrule_then (qspec_then ‘&(2 * N + 1)’ assume_tac) SERIES_CMUL >>
    drule_then (SUBST1_TAC o SYM) INFSUM_UNIQUE >> irule SERIES_DROP_LE >>
    ntac 2 $ irule_at Any $ iffRL SUMS_INFSUM >> irule_at Any SUMMABLE_GEOM >>
    dxrule_then (irule_at Any) SUMS_SUMMABLE >> rw[Abbr ‘f’] >>
    simp[REAL_POW_POW,LEFT_ADD_DISTRIB,REAL_POW_ADD]
QED

Theorem rational_log_helper_init_Nub_thm:
    ∀tol ar N. 0 < tol ∧ 0 ≤ ar ∧ ar < 1 ⇒
        rational_log_poly_error ar (rational_log_helper_init_Nub tol ar N) < tol
Proof
    recInduct rational_log_helper_init_Nub_ind >> rw[] >>
    simp[Once rational_log_helper_init_Nub_def] >> rw[] >>
    simp[rational_log_poly_error_def,POW_ADD,GSYM REAL_POW_POW]
QED

Definition rational_log_helper_first_N_def:
    rational_log_helper_first_N tol ar Nlb Nub =
        if tol ≤ 0r ∨ ar < 0r ∨ 1 ≤ ar ∨ Nub ≤ SUC Nlb then Nub
        else
            let
                rsq = ar * ar;
                N = (Nlb + Nub) DIV 2;
            in
                if 2 * ar * rsq pow N / (&(2 * N + 1) * (1 - rsq)) < tol then
                    rational_log_helper_first_N tol ar Nlb N
                else
                    rational_log_helper_first_N tol ar N Nub
Termination
    irule_at Any WF_measure >> simp[measure_thm] >>
    qexists ‘λ(_,_,Nlb,Nub). Nub - Nlb’ >> reverse $ rw[NOT_LESS_EQUAL]
    >- simp[DIV_LT_X] >>
    ‘0 < (Nlb + Nub) DIV 2 − Nlb’ suffices_by simp[] >>
    simp[GSYM SUB_LESS_0,X_LT_DIV]
End

Theorem rational_log_helper_first_N_thm:
    ∀tol ar Nlb Nub. 0 < tol ∧ 0 ≤ ar ∧ ar < 1 ∧ rational_log_poly_error ar Nub < tol ⇒
        rational_log_poly_error ar (rational_log_helper_first_N tol ar Nlb Nub) < tol
Proof
    recInduct rational_log_helper_first_N_ind >> rw[] >>
    simp[Once rational_log_helper_first_N_def] >> rw[] >>
    first_x_assum irule >> simp[] >>
    simp[rational_log_poly_error_def,POW_ADD,GSYM REAL_POW_POW]
QED

Definition rational_log_helper_N_def:
    rational_log_helper_N tol ar =
        rational_log_helper_first_N tol ar 0 (rational_log_helper_init_Nub tol ar 0)
End

Theorem rational_log_helper_N_thm:
    ∀tol ar. 0 < tol ∧ 0 ≤ ar ∧ ar < 1 ⇒
        rational_log_poly_error ar (rational_log_helper_N tol ar) < tol
Proof
    rw[rational_log_helper_N_def] >> irule rational_log_helper_first_N_thm >>
    simp[rational_log_helper_init_Nub_thm]
QED

Definition rational_log_def:
    rational_log tol x =
        if tol ≤ 0r ∨ x ≤ 0r then 0
        else
            let
                r = (x - 1) / (x + 1);
                rsq = r * r;
                N = rational_log_helper_N tol (abs r);
            in
                2 * r * REAL_LIST_SUM (GENLIST (λn. rsq pow n / &(2*n+1)) N)
End

Theorem rational_log_thm:
    ∀tol x. 0 < tol ∧ 0 < x ⇒ ∃N.
        rational_log_poly_error (abs ((x - 1) / (x + 1))) N < tol ∧
        rational_log tol x = 2 * sum (if N = 0 then ∅ else {0 .. N - 1})
            (λi. (&(2 * i + 1))⁻¹ * ((x - 1) / (x + 1)) pow (2 * i + 1))
Proof
    ntac 3 strip_tac >> qabbrev_tac ‘r = (x - 1) / (x + 1)’ >>
    irule_at Any rational_log_helper_N_thm >> simp[] >> conj_asm1_tac
    >- simp[Abbr ‘r’,ABS_BOUNDS_LT] >>
    qabbrev_tac ‘N = rational_log_helper_N tol (abs r)’ >>
    Cases_on ‘N’ >> simp[rational_log_def]
    >- simp[REAL_LIST_SUM_DEF,FOLDR,SUM_CLAUSES] >>
    simp[REAL_LIST_SUM_GENLIST_SUM_NUMSEG,real_div,GSYM SUM_LMUL] >>
    irule SUM_EQ' >> rw[] >> simp[REAL_POW_POW,GSYM pow,ADD1]
QED

Theorem rational_log_accuracy:
    ∀tol x. 0 < tol ∧ 0 < x ⇒ abs (ln x - rational_log tol x) < tol
Proof
    rw[] >> qspecl_then [‘tol’,‘x’] mp_tac rational_log_thm >> rw[] >>
    pop_assum mp_tac >> qmatch_goalsub_abbrev_tac ‘2 * sum s f’ >>
    disch_tac >> drule HALF_LN_POLYNOMIAL_SUMMABLE >>
    rw[LN_POLYNOMIAL,ETA_THM,GSYM REAL_SUB_LDISTRIB,REAL_ABS_MUL] >>
    qspecl_then [‘f’,‘UNIV’,‘s’] mp_tac INFSUM_FINITE_DIFF >>
    impl_tac >- rw[Abbr ‘s’,FINITE_NUMSEG] >> disch_then SUBST1_TAC >>
    ‘UNIV DIFF s = from N’ by rw[Abbr ‘s’,EXTENSION,from_def,numseg] >>
    pop_assum SUBST1_TAC >> irule REAL_LET_TRANS >> first_x_assum $ irule_at Any >>
    qspecl_then [‘(x − 1) / (x + 1)’,‘N’] mp_tac rational_log_poly_error_thm >>
    simp[Abbr ‘f’]
QED

(* Rational Exp with Polynomial *)

Definition rational_exp_helper_init_Nub_def:
    rational_exp_helper_init_Nub tol ax N =
        if tol ≤ 0r ∨ ax < 0r ∨ &SUC N ≤ ax then 0
        else if ax pow SUC N / (&FACT N * (&SUC N - ax)) < tol then N
        else rational_exp_helper_init_Nub tol ax (2 * N + 1)
Termination
    qabbrev_tac ‘remf = λ(ax:real) N. ax pow SUC N / (&FACT N * (&SUC N - ax))’ >> 
    simp[] >> irule_at Any WF_measure >> simp[measure_thm] >>
    ‘∀tol ax. ∃miN. ∀N. 0 < tol ∧ 0 ≤ ax ∧ ax < &SUC N ∧ miN ≤ N ⇒ (remf ax N < tol)’ suffices_by (
        rw[SKOLEM_THM] >> rename [‘miN _ _ ≤ _’] >> qexists ‘λ(tol,ax,N). miN tol ax - N’ >>
        rw[] >> last_x_assum $ dxrule_at Concl >> gs[]) >>
    rw[GSYM AND_IMP_INTRO,RIGHT_EXISTS_IMP_THM,RIGHT_FORALL_IMP_THM] >>
    qabbrev_tac ‘eterm = λN. (&FACT N)⁻¹ * ax pow SUC N’ >>
    ‘∀N. eterm (SUC N) = ax * eterm N / &SUC N’ by (
        rw[Abbr ‘eterm’,GSYM ADD_SUC,FACT,pow] >>
        ‘((&(FACT N * SUC N))⁻¹):real = (&FACT N)⁻¹ * (&SUC N)⁻¹’
            by simp[GSYM REAL_INV_MUL',REAL_MUL,Excl "RMUL_EQNORM1"] >>
        pop_assum SUBST1_TAC >> simp[]) >>
    ‘∀N. 0 ≤ eterm N’ by (
        rw[Abbr ‘eterm’] >> irule REAL_LE_MUL >> simp[]) >>
    ‘∀N n. ax < &SUC N ⇒ eterm (N + n) ≤ ((ax / &SUC N) pow n) * eterm N’ by (
        strip_tac >> simp[RIGHT_FORALL_IMP_THM] >> strip_tac >>
        Induct_on ‘n’ >- simp[] >> simp[pow] >> irule REAL_LE_TRANS >>
        drule_all_then (irule_at Any o SRULE []) REAL_LE_LMUL_IMP >>
        simp[GSYM ADD_SUC] >> rpt $ irule_at Any REAL_LE_MUL2 >> simp[] >>
        irule_at Any REAL_LE_MUL >> simp[]) >>
    ‘∃M. ax < &SUC M ∧ remf ax M < tol’ suffices_by (
        rw[] >> qexists ‘M’ >> rw[] >> irule REAL_LET_TRANS >>
        first_x_assum $ irule_at (Pos hd) >> simp[Abbr ‘remf’] >>
        irule REAL_LE_MUL2 >> simp[REAL_LE_SUB_CANCEL2] >>
        ‘∃n. N = M + n’ by (qexists ‘N - M’ >> simp[]) >>
        pop_assum SUBST_ALL_TAC >> irule_at Any REAL_LE_TRANS >>
        first_x_assum $ irule_at Any >> simp[] >>
        irule_at Any REAL_LE_MUL2 >> simp[POW_LE]) >>
    ‘∃M. ax < &SUC M’ by (
        qspec_then ‘ax’ (qx_choose_then ‘M’ assume_tac) REAL_BIGNUM >>
        qexists ‘M’ >> irule_at Any REAL_LT_TRANS >> qexists ‘&M’ >> simp[]) >>
    ‘∃n. remf ax (M + n) < tol’ suffices_by (rw[] >> qexists ‘M + n’ >>
        simp[] >> irule_at Any REAL_LTE_TRANS >> qexists ‘&SUC M’ >> simp[]) >>
    simp[Abbr ‘remf’,real_div,REAL_INV_MUL'] >> irule_at Any REAL_LET_TRANS >>
    ‘∃n. eterm (M + n) < tol’ suffices_by (rw[] >>
        pop_assum $ irule_at Any >> qexists ‘SUC n’ >>
        qspecl_then [‘eterm (M + SUC n)’,‘eterm (M + n)’,
            ‘(&SUC (M + SUC n) − ax)⁻¹’,‘1’] mp_tac REAL_LE_MUL2 >>
        simp[] >> disch_then irule >> simp[GSYM ADD_SUC,REAL_SUB_LE] >>
        irule_at Any REAL_INV_LE_1 >> simp[REAL_LE_SUB_LADD] >>
        irule_at (Pos hd) REAL_LE_TRANS >> qexists ‘1 + &SUC M’ >> simp[] >>
        irule_at (Pos last) REAL_LE_TRANS >> qexists ‘&SUC M’ >> simp[] >>
        qspecl_then [‘ax’,‘&SUC (M + n)’,‘eterm (M + n)’,‘eterm (M + n)’] mp_tac REAL_LE_MUL2 >>
        simp[] >> disch_then irule >>
        irule REAL_LE_TRANS >> qexists ‘&SUC M’ >> simp[]) >>
    first_x_assum $ drule_then assume_tac >>
    irule_at Any REAL_LET_TRANS >> pop_assum $ irule_at Any >>
    Cases_on ‘ax = 0’ >- (qexists ‘1’ >> simp[] >> irule REAL_LT_MUL >> simp[]) >>
    ‘eterm M ≠ 0’ by simp[Abbr ‘eterm’,FACT_LESS,LESS_NOT_EQ] >>
    ‘∃n. (ax / &SUC M) pow n < tol / eterm M’ suffices_by (
        ‘0 < eterm M’ suffices_by simp[] >> simp[REAL_LT_LE]) >>
    irule_at Any REAL_ARCH_POW_INV >> simp[REAL_LT_LE]
End

Definition rational_exp_poly_error_def:
    rational_exp_poly_error (ax:real) N =
        ax pow SUC N / (&FACT N * (&SUC N - ax))
End

Theorem rational_exp_poly_error_thm:
    ∀x N. abs x < &SUC N ⇒
        abs (suminf (from (SUC N)) (λi. (&FACT i)⁻¹ * x pow i)) ≤
        rational_exp_poly_error (abs x) N
Proof
    rw[] >> irule SERIES_BOUND >>
    map_every qabbrev_tac [‘M = SUC N’,‘ax = abs x’,‘c = (&FACT M)⁻¹ * ax pow M’,‘r = ax / &M’] >>
    qexistsl [‘λi. (&FACT i)⁻¹ * x pow i’,‘λi. c * r pow (i - M)’,‘from M’] >>
    simp[SUMS_INFSUM] >> irule_at Any SUMMABLE_FROM_ELSEWHERE >>
    qexists ‘0’ >> simp[FROM_0,EXP_POLYNOMIAL_SUMMABLE] >>
    ‘0 ≤ ax ∧ 0 < M’ by simp[Abbr ‘ax’,Abbr ‘M’] >> conj_tac
    >- (qunabbrevl_tac [‘c’,‘r’] >>
        rw[from_def,FACT_LESS,LESS_NOT_EQ,ABS_MUL,ABS_INV,GSYM POW_ABS] >>
        ‘&FACT i * ax pow M * ax pow (i − M) = &FACT i * ax pow i’ by (
            simp[GSYM REAL_POW_ADD]) >>
        pop_assum SUBST1_TAC >>
        qspecl_then [‘c’,‘a * d’,‘b’] (irule o SRULE []) REAL_LE_LMUL_IMP >>
        simp[] >> ntac 4 $ last_x_assum kall_tac >> Induct_on ‘i - M’
        >- (rw[] >> ‘i = M’ by simp[] >> simp[]) >>
        rw[] >> ‘i = M + SUC v’ by simp[] >> pop_assum SUBST_ALL_TAC >> gs[] >>
        simp[pow,ADD_CLAUSES,FACT] >>
        first_x_assum $ qspecl_then [‘M + v’,‘M’] mp_tac >> simp[] >> disch_tac >>
        dxrule_at_then Any (qspecl_then [‘&M’,‘&SUC (M + v)’] mp_tac) REAL_LE_MUL2 >>
        simp[] >> disch_then irule >> irule REAL_LE_MUL >> simp[]) >>
    ‘rational_exp_poly_error ax N = c * (1 − r)⁻¹’ by (
        simp[Abbr ‘c’,Abbr‘r’,Abbr ‘M’,rational_exp_poly_error_def,real_div,REAL_INV_MUL',FACT] >>
        ‘∀m n. ((&(m * n))⁻¹):real = (&m)⁻¹ * (&n)⁻¹’ by metis_tac[GSYM REAL_MUL,REAL_INV_MUL'] >>
        simp[REAL_SUB_LDISTRIB,REAL_SUB_RDISTRIB]) >>
    pop_assum SUBST1_TAC >> qabbrev_tac ‘f = λi. r pow (i - M)’ >> simp[] >>
    irule SERIES_CMUL >> simp[SUMS_REINDEX_TO_0,Abbr ‘f’] >>
    irule SUMS_GEOM >> simp[Abbr ‘r’,REAL_ABS_DIV]
QED

Theorem rational_exp_helper_init_Nub_thm:
    ∀tol ax N. 0 < tol ∧ 0 ≤ ax ∧ ax < &SUC N ⇒
        rational_exp_poly_error ax (rational_exp_helper_init_Nub tol ax N) < tol
Proof
    recInduct rational_exp_helper_init_Nub_ind >> rw[] >>
    simp[Once rational_exp_helper_init_Nub_def] >> rw[]
    >- simp[rational_exp_poly_error_def] >>
    first_x_assum irule >> simp[] >> irule REAL_LT_TRANS >>
    first_x_assum $ irule_at Any >> simp[]
QED

Theorem rational_exp_helper_init_Nub_le:
    ∀tol ax N. 0 < tol ∧ 0 ≤ ax ∧ ax < &SUC N ⇒
        N ≤ rational_exp_helper_init_Nub tol ax N
Proof
    recInduct rational_exp_helper_init_Nub_ind >> rw[] >>
    simp[Once rational_exp_helper_init_Nub_def] >> rw[] >>
    irule LESS_EQ_TRANS >> first_x_assum $ irule_at Any >> simp[] >>
    irule REAL_LT_TRANS >> first_x_assum $ irule_at Any >> simp[]
QED

Definition rational_exp_helper_first_N_def:
    rational_exp_helper_first_N tol ax Nlb Nub =
        if tol ≤ 0r ∨ ax < 0r ∨ &SUC Nub ≤ ax ∨ &SUC Nlb ≤ ax ∨ Nub ≤ SUC Nlb then Nub
        else
            let
                N = (Nlb + Nub) DIV 2;
            in
                if ax pow SUC N / (&FACT N * (&SUC N - ax)) < tol then
                    rational_exp_helper_first_N tol ax Nlb N
                else
                    rational_exp_helper_first_N tol ax N Nub
Termination
    irule_at Any WF_measure >> simp[measure_thm] >>
    qexists ‘λ(_,_,Nlb,Nub). Nub - Nlb’ >> reverse $ rw[NOT_LESS_EQUAL]
    >- simp[DIV_LT_X] >>
    ‘0 < (Nlb + Nub) DIV 2 − Nlb’ suffices_by simp[] >>
    simp[GSYM SUB_LESS_0,X_LT_DIV]
End

Theorem rational_exp_helper_first_N_thm:
    ∀tol ax Nlb Nub. 0 < tol ∧ 0 ≤ ax ∧ ax < &SUC Nlb ∧ ax < &SUC Nub ∧
        rational_exp_poly_error ax Nub < tol ⇒
        rational_exp_poly_error ax (rational_exp_helper_first_N tol ax Nlb Nub) < tol
Proof
    recInduct rational_exp_helper_first_N_ind >> rw[] >>
    simp[Once rational_exp_helper_first_N_def] >> rw[] >>
    first_x_assum $ irule_at Any >> last_x_assum kall_tac >>
    simp[] >> irule_at (Pos hd) REAL_LT_TRANS >> qexists ‘&SUC Nlb’ >>
    simp[X_LT_DIV] >> simp[rational_exp_poly_error_def]
QED

Theorem rational_exp_helper_first_N_lt:
    ∀tol ax Nlb Nub. 0 < tol ∧ 0 ≤ ax ∧ ax < &SUC Nlb ∧ ax < &SUC Nub ⇒
        ax < &SUC (rational_exp_helper_first_N tol ax Nlb Nub)
Proof
    recInduct rational_exp_helper_first_N_ind >> rw[] >>
    simp[Once rational_exp_helper_first_N_def] >> rw[] >>
    first_x_assum $ irule_at Any >> simp[] >>
    irule REAL_LTE_TRANS >> qexists ‘&SUC Nlb’ >> simp[X_LE_DIV]
QED

Definition rational_exp_helper_N_def:
    rational_exp_helper_N tol ax =
        let N = &flr ax;
        in rational_exp_helper_first_N tol ax N (rational_exp_helper_init_Nub tol ax N)
End

Theorem rational_exp_helper_N_thm:
    ∀tol ax. 0 < tol ∧ 0 ≤ ax ⇒
        rational_exp_poly_error ax (rational_exp_helper_N tol ax) < tol
Proof
    rw[rational_exp_helper_N_def] >> irule rational_exp_helper_first_N_thm >>
    irule_at Any rational_exp_helper_init_Nub_thm >> simp[] >> conj_asm1_tac
    >- (qspec_then ‘ax’ mp_tac NUM_FLOOR_LT >> simp[REAL_LT_SUB_RADD,REAL]) >>
    irule_at Any REAL_LTE_TRANS >> first_assum $ irule_at Any >>
    simp[] >> irule rational_exp_helper_init_Nub_le >> simp[]
QED

Theorem rational_exp_helper_N_lt:
    ∀tol ax. 0 < tol ∧ 0 ≤ ax ⇒ ax < &SUC (rational_exp_helper_N tol ax)
Proof
    rw[rational_exp_helper_N_def] >> irule rational_exp_helper_first_N_lt >>
    conj_asm1_tac >- (qspec_then ‘ax’ mp_tac NUM_FLOOR_LT >> simp[REAL_LT_SUB_RADD,ADD1]) >>
    simp[] >> irule REAL_LTE_TRANS >> first_assum $ irule_at Any >>
    simp[] >> irule rational_exp_helper_init_Nub_le >> simp[]
QED

Definition rational_exp_def:
    rational_exp tol x =
        let
            Nm1 = rational_exp_helper_N tol (abs x);
        in
            REAL_LIST_SUM (GENLIST (λn. x pow n / &FACT n) (SUC Nm1))
End

Theorem rational_exp_thm:
    ∀tol x. 0 < tol ⇒ ∃N. abs x < &SUC N ∧
        rational_exp_poly_error (abs x) N < tol ∧
        rational_exp tol x = sum {0 .. N} (λn. x pow n / &FACT n)
Proof
    ntac 3 strip_tac >> irule_at Any rational_exp_helper_N_thm >>
    simp[rational_exp_def,REAL_LIST_SUM_GENLIST_SUM_NUMSEG] >>
    irule rational_exp_helper_N_lt >> simp[]
QED

Theorem rational_exp_accuracy:
    ∀tol x. 0 < tol ⇒ abs (exp x - rational_exp tol x) < tol
Proof
    rw[] >> qspecl_then [‘tol’,‘x’] mp_tac rational_exp_thm >> rw[] >>
    pop_assum mp_tac >> qmatch_goalsub_abbrev_tac ‘sum s f’ >>
    disch_tac >> qspec_then ‘x’ mp_tac EXP_POLYNOMIAL_SUMMABLE >>
    gs[real_div] >> rw[exp,ETA_THM,GSYM seqTheory.suminf_univ] >>
    qspecl_then [‘f’,‘UNIV’,‘s’] mp_tac INFSUM_FINITE_DIFF >>
    impl_tac >- rw[Abbr ‘s’,FINITE_NUMSEG] >> disch_then SUBST1_TAC >>
    ‘UNIV DIFF s = from (SUC N)’ by rw[Abbr ‘s’,EXTENSION,from_def,numseg] >>
    pop_assum SUBST1_TAC >> irule REAL_LET_TRANS >> first_x_assum $ irule_at Any >>
    drule_all rational_exp_poly_error_thm >> simp[]
QED

(* Rational Log with Newtons *)

(* Measurability *)

Theorem natsa_measurable_rational_log_helper_init_Nub:
    (λ(tol,ar,N). rational_log_helper_init_Nub tol ar N) ∈ measurable (borel × borel × natsa) natsa
Proof[exclude_frags = REAL_ARITH]
    ‘sigma_algebra natsa ∧ sigma_algebra borel ∧ sigma_algebra (borel × natsa) ∧ sigma_algebra (borel × borel) ∧
      sigma_algebra (borel × borel × natsa) ∧ sigma_algebra (natsa × borel × borel)’ by (
        rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >>
        simp[sigma_algebra_borel,SIGMA_ALGEBRA_NATSA]) >>
    ‘space natsa = UNIV ∧ space borel = UNIV ∧ space (borel × natsa) = UNIV ∧ space (borel × borel) = UNIV ∧
      space (borel × borel × natsa) = UNIV ∧ space (natsa × borel × borel) = UNIV’ by (
        simp[SPACE_PROD_SIGMA,space_borel,SPACE_NATSA,CROSS_UNIV]) >>
    map_every qabbrev_tac [‘errP = λ(tol,ar,N:num). tol ≤ 0r ∨ ar < 0r ∨ 1 ≤ ar’,
        ‘endP = λ(tol,ar,N). 2 * ar pow (2*N+1) / (&(2*N+1) * (1r − ar pow 2)) < tol’,
        ‘recP = λtaN. ¬errP taN ∧ ¬endP taN’,
        ‘f = λ(tol:real,ar:real,N:num). (tol,ar,2*N+1)’,
        ‘g = λ(tol,ar,N). if errP (tol,ar,N) then 0 else N’] >>
    qspecl_then [‘recP’,‘f’] concl_tac $ iffRL WF_IFF_IND
    >- (qx_gen_tac ‘Q’ >> simp[FORALL_PROD] >> strip_tac >> qx_genl_tac [‘tol’,‘ar’,‘N’] >>
        qspec_then ‘λtol ar N. Q (tol,ar,N)’ (irule o SRULE []) rational_log_helper_init_Nub_ind >>
        pop_assum mp_tac >> UNABBREV_ALL_TAC >> simp[REAL_POW_POW,REAL_POW_ADD]) >>
    gs[] >> irule IN_MEASURABLE_TAILREC_ALT >> simp[] >>
    qexistsl [‘recP’,‘R’,‘f’,‘g’] >> simp[] >> conj_tac
    >- (qspecl_then [‘recP’,‘f’,‘R’] mp_tac WHILE_INDUCTION >> simp[] >>
        disch_then $ qspec_then ‘λx. foo x = bar x’ $ irule o SRULE [] >>
        simp[FORALL_PROD] >> qx_genl_tac [‘tol’,‘ar’,‘N’] >> rw[] >>
        simp[Once TAILREC_TAILCALL,TAILCALL_def] >> reverse $ Cases_on ‘recP (tol,ar,N)’ >> gs[]
        >- (UNABBREV_ALL_TAC >> simp[Once rational_log_helper_init_Nub_def] >>
            gs[REAL_POW_POW,REAL_POW_ADD]) >>
        qpat_x_assum ‘_ = _’ $ SUBST1_TAC o SYM >> UNABBREV_ALL_TAC >>
        simp[Once rational_log_helper_init_Nub_def] >> gs[REAL_POW_POW,REAL_POW_ADD]) >>
    irule_at (Pos $ el 2) IN_MEASURABLE_IF >> qexistsl [‘SND ∘ SND’,‘λtaN. 0’,‘errP’] >>
    simp[Abbr ‘g’,FORALL_PROD] >> ntac 2 $ pop_assum kall_tac >>
    ‘recP = UNIV DIFF (errP UNION endP)’ by simp[Abbr ‘recP’,EXTENSION,IN_APP] >>
    pop_assum SUBST1_TAC >> irule_at Any SIGMA_ALGEBRA_DIFF >> irule_at Any SIGMA_ALGEBRA_UNION >>
    ‘errP = {taN | FST taN ≤ 0} ∪ {taN | (FST ∘ SND) taN < 0} ∪ {taN | 1 ≤ (FST ∘ SND) taN}’ by (
        simp[EXTENSION,FORALL_PROD,Abbr ‘errP’,DISJ_ASSOC]) >>
    ‘endP = {taN | (λ(tol,ar,N). 2 * (ar pow (2 * N + 1) * (1 − ar²)⁻¹)) taN <
      (λ(tol,ar,N). tol * &(2 * N + 1)) taN}’ by (
        simp[EXTENSION,FORALL_PROD,Abbr ‘endP’]) >>
    ntac 2 $ pop_assum SUBST1_TAC >> ntac 2 $ irule_at Any SIGMA_ALGEBRA_UNION >>
    map_every (fn th => qspec_then ‘borel × borel × natsa’ mp_tac th >>
        simp[Excl "o_THM"] >> disch_then $ irule_at Any)
        [in_borel_measurable_le_imp,in_borel_measurable_lt_imp,
            in_borel_measurable_ge_imp,in_borel_measurable_lt2_imp] >>
    UNABBREV_ALL_TAC >> qpat_assum ‘space (borel × _ × _) = _’ $ SUBST1_TAC o SYM >>
    irule_at Any SIGMA_ALGEBRA_SPACE >> simp[] >>
    chain_irule_at [
        (Pos last,INST_TYPE [“:β”|->“:num#real#real”] IN_MEASURABLE_COMP,[‘λ(N,tol,ar). (tol,ar,2 * N + 1)’,
            ‘λ(tol,ar,N). (N,tol,ar)’,‘natsa × borel × borel’],[FORALL_PROD]),
        (Pos $ el 4,INST_TYPE [“:β”|->“:num#real#real”] IN_MEASURABLE_COMP,[‘λ(N,tol,ar). tol * &(2 * N + 1)’,
            ‘λ(tol,ar,N). (N,tol,ar)’,‘natsa × borel × borel’],[FORALL_PROD,SF CONJ_ss]),
        (Pos $ el 4,INST_TYPE [“:β”|->“:num#real#real”] IN_MEASURABLE_COMP,
            [‘λ(N,tol,ar). 2 * (ar pow (2 * N + 1) * (1 − ar²)⁻¹)’,‘λ(tol,ar,N). (N,tol,ar)’,
            ‘natsa × borel × borel’],[FORALL_PROD,SF CONJ_ss])] >>
    simp[IN_MEASURABLE_PROD_NATSA_ELIM,GSYM FORALL_AND_THM,LEFT_AND_FORALL_THM,RIGHT_AND_FORALL_THM] >>
    qx_gen_tac ‘N’ >> simp[LAMBDA_PROD] >>
    chain_irule_at [
        (Pos $ el 7,IN_MEASURABLE_CONST,[‘0’],[FORALL_PROD]),
        (Pos $ el 3,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λ(tol,ar,N). (tol,ar)’,‘SND ∘ SND’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘FST ∘ SND’,‘FST’],[FORALL_PROD,SF CONJ_ss]),
        (Pos $ el 3,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λ(tol,ar). (ar,2*N+1)’,‘FST’],[FORALL_PROD]),
        (Pos $ el 2,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λta. 2*N+1’,‘SND’],[FORALL_PROD]),
        (Any,MEASURABLE_CONST,[],[]),
        (Pos $ el 4,in_borel_measurable_mul,[‘λta. &(2 * N + 1)’,‘FST’],[FORALL_PROD]),
        (Any,borel_measurable_const,[],[]),
        (Pos $ el 3,in_borel_measurable_mul,[‘λ(tol,ar). ar pow (2 * N + 1) * (1 − ar²)⁻¹’,‘λta. 2’],[FORALL_PROD]),
        (Any,borel_measurable_const,[],[]),
        (Pos hd,in_borel_measurable_mul,[‘λ(tol,ar). (1 − ar²)⁻¹’,‘λ(tol,ar). ar pow (2 * N + 1)’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_pow,[‘2*N+1’,‘SND’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,in_borel_measurable_inv,[‘λ(tol,ar). 1 − ar²’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_sub,[‘λ(tol,ar). ar²’,‘λta. 1’],[FORALL_PROD]),
        (Any,borel_measurable_const,[],[]),
        (Pos hd,in_borel_measurable_pow2,[‘SND’],[FORALL_PROD,SF CONJ_ss])] >>
    ntac 2 (irule_at Any MEASURABLE_COMP >> qexists ‘borel × natsa’) >> simp[SF CONJ_ss] >>
    rpt $ irule_at Any MEASURABLE_FST >> rpt $ irule_at Any MEASURABLE_SND >> simp[]
QED

Theorem natsa_measurable_rational_log_helper_first_N:
    (λ(tol,ar,Nlb,Nub). rational_log_helper_first_N tol ar Nlb Nub) ∈
        measurable (borel × borel × natsa × natsa) natsa
Proof[exclude_frags = REAL_ARITH]
    ‘sigma_algebra natsa ∧ sigma_algebra borel ∧
      sigma_algebra (natsa × natsa) ∧ sigma_algebra (borel × borel) ∧
      sigma_algebra (natsa × borel × borel) ∧ sigma_algebra (borel × natsa × natsa) ∧
      sigma_algebra (natsa × natsa × borel × borel) ∧
      sigma_algebra (borel × borel × natsa × natsa)’ by (
        rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >>
        simp[sigma_algebra_borel,SIGMA_ALGEBRA_NATSA]) >>
    ‘space natsa = UNIV ∧ space borel = UNIV ∧ space (natsa × natsa) = UNIV ∧
      space (borel × borel × natsa × natsa) = UNIV’ by (
        simp[SPACE_PROD_SIGMA,space_borel,SPACE_NATSA,CROSS_UNIV]) >>
    map_every qabbrev_tac [‘recP = λ(tol,ar,Nlb,Nub). 0r < tol ∧ 0r ≤ ar ∧ ar < 1 ∧ SUC Nlb < Nub’,
        ‘casP = λ(tol,ar,Nlb,Nub).
            2 * ar pow (2*((Nlb + Nub) DIV 2)+1) / (&(2*((Nlb + Nub) DIV 2)+1) * (1r − ar pow 2)) < tol’,
        ‘f = λ(tol,ar,Nlb,Nub). if casP (tol,ar,Nlb,Nub)
            then (tol,ar,Nlb,(Nlb + Nub) DIV 2) else (tol,ar,(Nlb + Nub) DIV 2,Nub)’] >>
    qspecl_then [‘recP’,‘f’] concl_tac $ iffRL WF_IFF_IND
    >- (qx_gen_tac ‘Q’ >> simp[FORALL_PROD] >> strip_tac >> qx_genl_tac [‘tol’,‘ar’,‘Nlb’,‘Nub’] >>
        qspec_then ‘λtol ar Nlb Nub. Q (tol,ar,Nlb,Nub)’ (irule o SRULE []) rational_log_helper_first_N_ind >>
        UNABBREV_ALL_TAC >> rw[] >> first_x_assum $ irule_at Any >> rw[] >>
        gs[REAL_POW_POW,REAL_POW_ADD,REAL_NOT_LE,REAL_NOT_LT]) >>
    gs[] >> irule IN_MEASURABLE_TAILREC_ALT >> simp[] >>
    qexistsl [‘recP’,‘R’,‘f’,‘SND ∘ SND ∘ SND’] >> simp[] >> conj_tac
    >- (qspecl_then [‘recP’,‘f’,‘R’] mp_tac WHILE_INDUCTION >> simp[] >>
        disch_then $ qspec_then ‘λx. foo x = bar x’ $ irule o SRULE [] >>
        simp[FORALL_PROD] >> qx_genl_tac [‘tol’,‘ar’,‘Nlb’,‘Nub’] >>
        ntac 2 $ pop_assum kall_tac >> rw[] >>
        simp[Once TAILREC_TAILCALL,TAILCALL_def] >>
        reverse $ Cases_on ‘recP (tol,ar,Nlb,Nub)’ >> gs[]
        >- (UNABBREV_ALL_TAC >> simp[Once rational_log_helper_first_N_def] >>
            gs[REAL_NOT_LE,REAL_NOT_LT]) >>
        qpat_x_assum ‘_ = _’ $ SUBST1_TAC o SYM >> UNABBREV_ALL_TAC >>
        simp[Once rational_log_helper_first_N_def] >>
        gs[iffRL REAL_NOT_LE,iffRL REAL_NOT_LT,REAL_POW_POW,REAL_POW_ADD] >> rw[]) >>
    ntac 2 $ pop_assum kall_tac >> irule_at (Pos hd) IN_MEASURABLE_IF >>
    qexistsl [‘λ(tol,ar,Nlb,Nub). (tol,ar,(Nlb + Nub) DIV 2,Nub)’,
        ‘λ(tol,ar,Nlb,Nub). (tol,ar,Nlb,(Nlb + Nub) DIV 2)’,‘casP’] >>
    simp[Abbr ‘f’,FORALL_PROD] >>
    ‘recP = {taNN | 0 < FST taNN} ∩ {taNN | 0 ≤ (FST ∘ SND) taNN} ∩ {taNN | (FST ∘ SND) taNN < 1} ∩
      {taNN | (λ(tol,ar,Nlb,Nub). &SUC Nlb) taNN < (λ(tol,ar,Nlb,Nub). real_of_num Nub) taNN}’ by (
        simp[EXTENSION,FORALL_PROD,Abbr ‘recP’,CONJ_ASSOC]) >>
    ‘casP = {taNN | (λ(tol,ar,Nlb,Nub). 2 * (ar pow (2 * ((Nlb + Nub) DIV 2) + 1) * (1 − ar²)⁻¹)) taNN <
      (λ(tol,ar,Nlb,Nub). tol * &(2 * ((Nlb + Nub) DIV 2) + 1)) taNN}’ by (
        simp[EXTENSION,FORALL_PROD,Abbr ‘casP’]) >>
    ntac 2 $ pop_assum SUBST1_TAC >> UNABBREV_ALL_TAC >> ntac 3 $ irule_at Any SIGMA_ALGEBRA_INTER >>
    map_every (fn th => qspec_then ‘borel × borel × natsa × natsa’ mp_tac th >>
        simp[Excl "o_THM"] >> disch_then $ irule_at Any)
        [in_borel_measurable_gt_imp,in_borel_measurable_ge_imp,
            in_borel_measurable_lt_imp,in_borel_measurable_lt2_imp,in_borel_measurable_lt2_imp] >>
    map_every (fn (n,tm) =>
        irule_at (Pos $ el n) $ INST_TYPE [“:β”|->“:num#num#real#real”] IN_MEASURABLE_COMP >>
        qexistsl [tm,‘λ(tol,ar,Nlb,Nub). (Nlb,Nub,tol,ar)’,‘natsa × natsa × borel × borel’] >>
        simp[FORALL_PROD,SF CONJ_ss]) [
            (8,‘λ(Nlb,Nub,tol,ar). (tol,ar,(Nlb + Nub) DIV 2,Nub)’),
            (9,‘λ(Nlb,Nub,tol,ar). (tol,ar,Nlb,(Nlb + Nub) DIV 2)’),
            (7,‘λ(Nlb,Nub,tol,ar). &Nub’), (7,‘λ(Nlb,Nub,tol,ar). &SUC Nlb’),
            (7,‘λ(Nlb,Nub,tol,ar). tol * &(2 * ((Nlb + Nub) DIV 2) + 1)’),
            (7,‘λ(Nlb,Nub,tol,ar). 2 * (ar pow (2 * ((Nlb + Nub) DIV 2) + 1) * (1 − ar²)⁻¹)’)] >>
    simp[IN_MEASURABLE_PROD_NATSA_ELIM,GSYM FORALL_AND_THM,LEFT_AND_FORALL_THM,RIGHT_AND_FORALL_THM] >>
    qx_genl_tac [‘Nlb’,‘Nub’] >> simp[LAMBDA_PROD] >>
    chain_irule_at [
        (Pos $ el 6,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar,Nlb,Nub). (Nub,tol,ar)’,‘FST ∘ SND ∘ SND’],[FORALL_PROD]),
        (Pos $ el 2,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar,Nlb,Nub). (tol,ar)’,‘SND ∘ SND ∘ SND’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘FST ∘ SND’,‘FST’],[FORALL_PROD,SF CONJ_ss]),
        (Pos $ el 7,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar). (ar,(Nlb + Nub) DIV 2,Nub)’,‘FST’],[FORALL_PROD]),
        (Pos $ el 2,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar). ((Nlb + Nub) DIV 2,Nub)’,‘SND’],[FORALL_PROD]),
        (Pos $ el 2,IN_MEASURABLE_CONST,[‘((Nlb + Nub) DIV 2,Nub)’],[FORALL_PROD]),
        (Pos $ el 8,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar). (ar,Nlb,(Nlb + Nub) DIV 2)’,‘FST’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar). (Nlb,(Nlb + Nub) DIV 2)’,‘SND’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_CONST,[‘(Nlb,(Nlb + Nub) DIV 2)’],[FORALL_PROD]),
        (Pos $ el 7,in_borel_measurable_const,[‘&Nlb’],[FORALL_PROD]),
        (Pos $ el 6,in_borel_measurable_const,[‘&SUC Nlb’],[FORALL_PROD]),
        (Pos $ el 5,in_borel_measurable_mul,
            [‘(λ(tol,ar). &(2 * ((Nlb + Nub) DIV 2) + 1))’,‘FST’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,in_borel_measurable_const,[‘&(2 * ((Nlb + Nub) DIV 2) + 1)’],[FORALL_PROD]),
        (Pos $ el 4,in_borel_measurable_mul,[‘(λ(tol,ar). ar pow (2 * ((Nlb + Nub) DIV 2) + 1) * (1 − ar²)⁻¹)’,
            ‘λ(tol,ar). 2’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_const,[‘2’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_mul,[‘(λ(tol,ar). (1 − ar²)⁻¹)’,
            ‘λ(tol,ar). ar pow (2 * ((Nlb + Nub) DIV 2) + 1)’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_pow,[‘2 * ((Nlb + Nub) DIV 2) + 1’,‘SND’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,in_borel_measurable_inv,[‘λ(tol,ar). 1 − ar²’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_sub,[‘(λ(tol,ar). ar²)’,‘λ(tol,ar). 1’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_const,[‘1’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_pow2,[‘SND’],[FORALL_PROD,SF CONJ_ss])] >>
    rpt $ irule_at Any MEASURABLE_COMP >> rpt $ irule_at Any MEASURABLE_FST >>
    rpt $ irule_at Any MEASURABLE_SND >> simp[]
QED

Theorem natsa_measurable_rational_log_helper_N:
    (λ(tol,ar). rational_log_helper_N tol ar) ∈ measurable (borel × borel) natsa
Proof[exclude_frags = REAL_ARITH]
    ‘sigma_algebra natsa ∧ sigma_algebra borel ∧ sigma_algebra (natsa × natsa) ∧
      sigma_algebra (borel × natsa) ∧ sigma_algebra (borel × borel) ∧
      sigma_algebra (borel × natsa × natsa)’ by (
        rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >>
        simp[sigma_algebra_borel,SIGMA_ALGEBRA_NATSA]) >>
    chain_irule_at [
        (Any,INST_TYPE [“:β”|->“:real#real#num#num”] IN_MEASURABLE_COMP,
            [‘borel × borel × natsa × natsa’,
            ‘λ(tol,ar). (tol,ar,0,rational_log_helper_init_Nub tol ar 0)’,
            ‘λ(tol,ar,Nlb,Nub). rational_log_helper_first_N tol ar Nlb Nub’],
            [rational_log_helper_N_def,FORALL_PROD]),
        (Any,natsa_measurable_rational_log_helper_first_N,[],[]),
        (Any,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘FST’,‘λ(tol,ar). (ar,0,rational_log_helper_init_Nub tol ar 0)’],[FORALL_PROD]),
        (Any,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar). (0,rational_log_helper_init_Nub tol ar 0)’,‘SND’],[FORALL_PROD]),
        (Pos $ el 2,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar). rational_log_helper_init_Nub tol ar 0’,‘λta. 0’],[FORALL_PROD]),
        (Any,MEASURABLE_CONST,[],[FORALL_PROD]),
        (Pos hd,INST_TYPE [“:β”|->“:real#real#num”] IN_MEASURABLE_COMP,
            [‘λ(tol,ar,N). rational_log_helper_init_Nub tol ar N’,
            ‘λ(tol,ar). (tol,ar,0)’,‘borel × borel × natsa’],[FORALL_PROD]),
        (Any,natsa_measurable_rational_log_helper_init_Nub,[],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA_WEAK,
            [‘λ(tol,ar). (ar,0)’,‘FST’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λta. 0’,‘SND’],[FORALL_PROD,SF CONJ_ss]),
        (Any,MEASURABLE_CONST,[],[FORALL_PROD]),
        (Any,MEASURABLE_FST,[],[]), (Any,MEASURABLE_SND,[],[])]
QED

Theorem borel_measurable_rational_log:
    (λ(tol,x). rational_log tol x) ∈ borel_measurable (borel × borel)
Proof
    ‘sigma_algebra natsa ∧ sigma_algebra borel ∧ sigma_algebra (borel × borel)’ by (
        rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >>
        simp[sigma_algebra_borel,SIGMA_ALGEBRA_NATSA]) >>
    chain_irule_at [
        (Any,IN_MEASURABLE_IF,[‘{tx | FST tx ≤ 0} ∪ {tx | SND tx ≤ 0}’,‘λtx. 0’,
            ‘(λ(N,r). 2 * r * REAL_LIST_SUM (GENLIST (λn. r pow (2*n) / &(2 * n + 1)) N)) ∘
            (λ(tol,x). (rational_log_helper_N tol (abs ((x − 1) / (x + 1)))),(x − 1) / (x + 1))’],
            [GSYM REAL_POW_POW,POW_MUL,real_div,FORALL_PROD,rational_log_def,space_borel_2d]),
        (Any,borel_measurable_const,[],[]), (Any,SIGMA_ALGEBRA_UNION,[],[]),
        (Any,MEASURABLE_COMP,[‘natsa × borel’],[FORALL_PROD,REAL_LIST_SUM_GENLIST_REAL_SUM_IMAGE]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λ(tol,x). (x + 1)⁻¹ * (x − 1)’,
            ‘λ(tol,x). rational_log_helper_N tol (abs ((x + 1)⁻¹ * (x − 1)))’],[FORALL_PROD]),
        (Pos hd,INST_TYPE [“:β”|->“:real#real”] IN_MEASURABLE_COMP,
            [‘λ(tol,ar). rational_log_helper_N tol ar’,
            ‘λ(tol,x). (tol,abs ((x + 1)⁻¹ * (x − 1)))’,‘borel × borel’],
            [FORALL_PROD,natsa_measurable_rational_log_helper_N]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λ(tol,x). abs ((x + 1)⁻¹ * (x − 1))’,‘FST’],[FORALL_PROD]),
        (Pos $ el 2,in_borel_measurable_abs,[‘λ(tol,x). (x + 1)⁻¹ * (x − 1)’],[FORALL_PROD,SF CONJ_ss]),
        (Pos $ el 2,in_borel_measurable_mul,[‘λ(tol,x). (x − 1)’,‘λ(tol,x). (x + 1)⁻¹’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_inv,[‘λ(tol,x). x + 1’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_add,[‘λtx. 1’,‘SND’],[FORALL_PROD]),
        (Pos $ el 3,in_borel_measurable_sub,[‘λtx. 1’,‘SND’],[FORALL_PROD,SF CONJ_ss]),
        (Pos $ el 2,borel_measurable_const,[],[FORALL_PROD])] >>
    qspec_then ‘borel × borel’ mp_tac in_borel_measurable_le_imp >> simp[space_borel_2d] >>
    disch_then (fn th => ntac 2 $ irule_at Any th) >>
    simp[MEASURABLE_FST,MEASURABLE_SND,IN_MEASURABLE_PROD_NATSA_ELIM] >> qx_gen_tac ‘N’ >>
    chain_irule_at [
        (Any,in_borel_measurable_mul,[‘λr. 2’,‘λr. r * ∑ (λn. (&(2 * n + 1))⁻¹ * r² pow n) (count N)’],
            [borel_measurable_const]),
        (Any,in_borel_measurable_mul,[‘I’,‘λr. ∑ (λn. (&(2 * n + 1))⁻¹ * r² pow n) (count N)’],
            [MEASURABLE_I]),
        (Any,INST_TYPE [“:β”|->“:num”] in_borel_measurable_sum,
            [‘λn r. (&(2 * n + 1))⁻¹ * r² pow n’,‘count N’],[])] >>
    qx_gen_tac ‘n’ >> rw[] >>
    chain_irule_at [
        (Any,in_borel_measurable_mul,[‘λr. r² pow n’,‘λr. (&(2 * n + 1))⁻¹’],
            [borel_measurable_const,REAL_POW_POW]),
        (Any,in_borel_measurable_pow,[‘I’,‘2*n’],[MEASURABLE_I])]
QED

Theorem borel_measurable_rational_log_tol:
    ∀tol. rational_log tol ∈ borel_measurable borel
Proof
    rw[] >> assume_tac borel_measurable_rational_log >>
    dxrule_at Any IN_MEASURABLE_FROM_PROD_SIGMA >>
    simp[sigma_algebra_borel,space_borel,SF ETA_ss]
QED

val _ = export_theory();
