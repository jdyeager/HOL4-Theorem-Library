open HolKernel Parse boolLib bossLib;
open markerTheory;
open combinTheory;
open pred_setTheory;
open cardinalTheory;
open arithmeticTheory;
open realTheory;
open realLib;
open limTheory;
open seqTheory;
open transcTheory;
open real_sigmaTheory;
open extrealTheory;
open sigma_algebraTheory;
open measureTheory;
open borelTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

open ex_machina;
open trivialTheory;
open trivialSimps;

val _ = new_theory "hoeffding";

val _ = reveal "C";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss,TRIVIAL_ss];

Theorem hoeffding_lemma:
    ∀p X a b c. prob_space p ∧ real_random_variable X p ∧ expectation p X = 0 ∧
        a ≤ 0 ∧ 0 ≤ b ∧ (AE x::p. Normal a ≤ X x ∧ X x ≤ Normal b) ⇒
        expectation p (λx. (exp (Normal c * X x))) ≤ Normal (exp (c² * (b − a)² / 8))
Proof
    rw[prob_space_def,real_random_variable_def,random_variable_def,p_space_def,events_def,expectation_def] >>
    rename [`f ∈ Borel_measurable (measurable_space m)`] >>
    `integrable m f` by (irule integrable_AE_bounded_Borel_measurable >>
        simp[finite_measure_space_def,finite_def] >> qexistsl_tac [`a`,`b`] >> simp[]) >>
    irule le_trans >> Cases_on `b = a`
    >- (rw[EXP_0] >> dxrule_all_then assume_tac $ iffLR REAL_LE_ANTISYM >> rw[] >> fs[le_antisym] >>
        qexists_tac `∫ m (λx. Normal 1)` >> irule_at Any integral_mono_AE >> simp[integral_const] >>
        qspecl_then [`m`,`λx. f x = Normal 0`,`λx. exp (Normal c * f x) ≤ Normal 1`]
            (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[extreal_mul_def,extreal_exp_def,EXP_0]) >>
    `0 < b - a` by simp[] >> fs[] >> rw[] >>
    qexists_tac `∫ m (λx. Normal (exp (a * c) * (b − a)⁻¹) * (Normal b − f x) +
        Normal (exp (b * c) * (b − a)⁻¹) * (f x − Normal a))` >>
    irule_at Any integral_mono_AE >> simp[] >>
    qspecl_then [`m`,`λx. Normal a ≤ f x ∧ f x ≤ Normal b`,`λx. exp (Normal c * f x) ≤
        Normal (exp (a * c) * (b − a)⁻¹) * (Normal b − f x) +
        Normal (exp (b * c) * (b − a)⁻¹) * (f x − Normal a)`]
        (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_subset >>
    map_every (fn (th,tms,ths) => qspecl_then tms assume_tac th >> rfs ths) [
        (integral_sub',[`m`,`λx. Normal b`,`f`],[integral_const,integrable_const]),
        (integral_sub',[`m`,`f`,`λx. Normal a`],[integral_const,integrable_const,extreal_ainv_def]),
        (integrable_sub',[`m`,`λx. Normal b`,`f`],[integral_const,integrable_const]),
        (integrable_sub',[`m`,`f`,`λx. Normal a`],[integral_const,integrable_const]),
        (integral_cmul,[`m`,`λx. Normal b − f x`,`exp (c * a) * (b − a)⁻¹`],[extreal_mul_def]),
        (integral_cmul,[`m`,`λx. f x − Normal a`,`exp (c * b) * (b − a)⁻¹`],[extreal_mul_def]),
        (integrable_cmul,[`m`,`λx. Normal b − f x`,`exp (c * a) * (b − a)⁻¹`],[]),
        (integrable_cmul,[`m`,`λx. f x − Normal a`,`exp (c * b) * (b − a)⁻¹`],[]),
        (integral_add',[`m`,`λx. Normal (exp (a * c) * (b − a)⁻¹) * (Normal b − f x)`,
            `λx. Normal (exp (b * c) * (b − a)⁻¹) * (f x − Normal a)`],[extreal_add_def])] >>
    NTAC 9 $ pop_assum kall_tac >> CONJ_TAC
    >- (rw[] >> Cases_on `f x` >> rfs[] >> pop_assum kall_tac >>
        simp[extreal_mul_def,extreal_exp_def,extreal_sub_def,extreal_add_def] >>
        `∀x1:real x2 x3 x4. x1 = x2 ∧ x3 = x4 ∧ x1 ≤ x3 ⇒ x2 ≤ x4` by simp[] >> pop_assum irule >>
        rename [`z ∈ _`] >> map_every qabbrev_tac [`t = (b − a)⁻¹ * (b − r)`,`x = a * c`,`y = b * c`] >>
        qexistsl_tac [`exp (t * x + (1 − t) * y)`,`t * exp x + (1 − t) * exp y`] >>
        simp[] >> irule_at Any $ SIMP_RULE (srw_ss ()) [convex_fn] exp_convex >>
        UNABBREV_ALL_TAC >> simp[EXP_NZ] >> irule_at (Pos hd) IRULER >>
        `(1 − (b − a)⁻¹ * (b − r)) = (b − a)⁻¹ * (r - a)` by (
            irule REAL_EQ_LMUL_IMP >> qexists_tac `(b − a)` >> simp[REAL_SUB_LDISTRIB]) >>
        pop_assum SUBST1_TAC >> simp[] >> Cases_on `c = 0` >> simp[] >>
        irule REAL_EQ_LMUL_IMP >> qexists_tac `c⁻¹ * (b − a)` >> qmatch_abbrev_tac `_ ∧ r1 = r2` >>
        rfs[REAL_ADD_LDISTRIB] >> UNABBREV_ALL_TAC >> simp[REAL_SUB_LDISTRIB]) >>
    map_every (fn pt => qpat_x_assum pt kall_tac) [`measure_space _`,`measure _ _ = _`,
        `_ ∈ Borel_measurable _`,`∫ _ _ = _`,`integrable _ _`,`∀x. _`,`AE x::m. _`] >>
    map_every qabbrev_tac [`h = c * (b - a)`,`p = -a * (b − a)⁻¹`,
        `L = λh. - h * p + ln (1 - p + p * exp h)`,`dL = λh. - p + p * exp h * (1 - p + p * exp h)⁻¹`,
        `ddL = λh. p * exp h * (1 - p + p * exp h)⁻¹ * (1 - p * exp h * (1 - p + p * exp h)⁻¹)`,
        `dLs = λn:num. if n = 0 then L else if n = 1 then dL else ddL`] >>
    `∀h. 0 < 1 − p + p * exp h` by (UNABBREV_ALL_TAC >> rw[] >> Cases_on `a = 0` >> simp[] >>
        irule REAL_LET_ADD >> NTAC 2 $ irule_at Any REAL_LT_MUL >> simp[EXP_POS_LT,REAL_SUB_LE]) >>
    `∀x1:real x2 x3 x4. x1 = x2 ∧ x3 = x4 ∧ x1 ≤ x3 ⇒ x2 ≤ x4` by simp[] >> pop_assum irule >>
    qexistsl_tac [`exp (L h)`,`exp (h² / 8)`] >> rw[]
    >| [UNABBREV_ALL_TAC,UNABBREV_ALL_TAC >> simp[POW_MUL],simp[EXP_MONO_LE]]
    >- (simp[EXP_ADD] >> pop_assum $ qspec_then `c * (b - a)` assume_tac >>
        simp[iffRL EXP_LN] >> irule REAL_EQ_LMUL_IMP >> qabbrev_tac `r = (b − a)⁻¹` >>
        qexists_tac `r⁻¹` >> qmatch_abbrev_tac `_ ∧ r1 = r2` >> 
        rfs[REAL_ADD_LDISTRIB,REAL_SUB_LDISTRIB,EXP_SUB,EXP_NEG] >> UNABBREV_ALL_TAC >>
        simp[nonzerop_def,EXP_NZ]) >>
    `(∀h. (L diffl dL h) h) ∧ (∀h. (dL diffl ddL h) h)` by (simp[GSYM FORALL_AND_THM] >>
        qx_gen_tac `hx` >> qunabbrevl_tac [`L`,`dL`,`ddL`,`dLs`] >> simp[] >>
        irule_at Any $ SIMP_RULE (srw_ss ()) [GSYM REAL_NEG_MINUS1] $
            Diff.DIFF_CONV ``λh:real. -h * p + ln (1 − p + p * exp h)`` >> simp[] >>
        qspec_then `hx` mp_tac $ SIMP_RULE (srw_ss ()) [GSYM REAL_NEG_MINUS1] $
            Diff.DIFF_CONV ``λh:real. -p + p * exp h * (1 − p + p * exp h)⁻¹`` >>
        simp[REAL_POS_NZ,REAL_SUB_LDISTRIB,real_sub,REAL_NEG_LMUL]) >>
    `L 0 = 0 ∧ dL 0 = 0` by (qunabbrevl_tac [`L`,`dL`] >> simp[EXP_0,REAL_SUB_ADD,LN_1]) >>
    `∀h. ddL h ≤ 1 / 4` by (qunabbrev_tac `ddL` >> qx_gen_tac `hx` >> CONV_TAC EVAL >>
        qmatch_abbrev_tac `r:real * _ ≤ _` >> rpt $ pop_assum kall_tac >> simp[] >>
        `∃t. r = t + 1 / 2` by (qexists_tac `r - 1 / 2` >> simp[]) >> pop_assum SUBST1_TAC >>
        `4 * ((t + 1 / 2) * (1 − (t + 1 / 2))) = 1 - 4 * t²` suffices_by (
            strip_tac >> pop_assum SUBST1_TAC >> simp[REAL_LE_SUB_RADD]) >>
        simp[REAL_ADD_RDISTRIB,REAL_ADD_LDISTRIB,REAL_SUB_LDISTRIB]) >>
    `(∀m. m < 2 ⇒ ∀t. (dLs m diffl dLs (SUC m) t) t)` by rw[Abbr `dLs`] >> qunabbrev_tac `dLs` >>
    dxrule_at_then Any (qspecl_then [`L`,`h`]
        (assume_tac o CONV_RULE EVAL o SIMP_RULE (srw_ss ()) [])) MCLAURIN_GEN >>
    rfs[] >> first_x_assum $ qspec_then `t` mp_tac >> qpat_x_assum `2 * _ = _` mp_tac >>
    rpt $ pop_assum kall_tac >> rw[] >>
    dxrule_at_then Any (qspec_then `h²` mp_tac) REAL_LE_LMUL_IMP >> simp[]
QED

Theorem hoeffding_lemma_gen:
    ∀p X a b c. prob_space p ∧ real_random_variable X p ∧ (AE x::p. Normal a ≤ X x ∧ X x ≤ Normal b) ⇒
        expectation p (λx. (exp (Normal c * (X x − expectation p X)))) ≤ Normal (exp (c² * (b − a)² / 8))
Proof
    rw[] >>
    `integrable p X ∧ ∃r. expectation p X = Normal r` by (
        fs[prob_space_def,real_random_variable_def,random_variable_def,
            expectation_def,p_space_def,events_def] >>
        CONJ_ASM1_TAC >| [irule integrable_AE_bounded_Borel_measurable,irule integrable_normal_integral] >>
        simp[finite_measure_space_def,finite_def,SF SFY_ss]) >>
    simp[] >>
    qspecl_then [`p`,`λx. X x - Normal r`,`a - r`,`b - r`,`c`]
        (irule o SIMP_RULE (srw_ss ()) [REAL_SUB_TRIANGLE_NEG]) hoeffding_lemma >>
    fs[prob_space_def,real_random_variable_def,random_variable_def,expectation_def,p_space_def,events_def] >>
    simp[REAL_LE_SUB_LADD,REAL_LE_SUB_RADD] >> rpt CONJ_TAC
    >- (qspecl_then [`p`,`X`,`λx. Normal r`] assume_tac integral_sub >>
        rfs[integral_const,integrable_const,extreal_sub_def])
    >- (qspecl_then [`p`,`λx. Normal a ≤ X x ∧ X x ≤ Normal b`,
            `λx. Normal (a − r) ≤ X x − Normal r ∧ X x − Normal r ≤ Normal (b − r)`]
            (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[] >> Cases_on `X x` >> fs[extreal_sub_def])
    >- (qspecl_then [`p`,`X`,`λx. Normal b`]  mp_tac integral_mono_AE >>
        simp[integral_const] >> disch_then irule >>
        qspecl_then [`p`,`λx. Normal a ≤ X x ∧ X x ≤ Normal b`,`λx. X x ≤ Normal b`] mp_tac AE_subset >>
        simp[])
    >- (qspecl_then [`p`,`λx. Normal a`,`X`]  mp_tac integral_mono_AE >>
        simp[integral_const] >> disch_then irule >>
        qspecl_then [`p`,`λx. Normal a ≤ X x ∧ X x ≤ Normal b`,`λx. Normal a ≤ X x`] mp_tac AE_subset >>
        simp[])
    >- (irule IN_MEASURABLE_BOREL_SUB >> simp[] >>
        qexistsl_tac [`X`,`λx. Normal r `] >> simp[IN_MEASURABLE_BOREL_CONST'])
    >- (NTAC 2 strip_tac >> Cases_on `X x` >> rfs[extreal_sub_def])
QED

Theorem hoeffding_ineq:
    ∀p X a b J t. prob_space p ∧ FINITE J ∧ 0 ≤ t ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        (∀n. n ∈ J ⇒ AE x::p. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)) ∧ indep_vars p X (K Borel) J ⇒
        prob p ({x | Normal t ≤ ∑ (C X x) J - expectation p (λy. ∑ (C X y) J)} ∩ p_space p) ≤
        Normal (exp (-2 * t² / ∑ (λn. (b n - a n)²) J))
Proof
    rw[] >> Cases_on `t = 0`
    >- (rw[EXP_0,normal_0,normal_1] >> irule PROB_LE_1 >> simp[] >>
        qspecl_then [`λx. ∑ (C X x) J − expectation p (λy. ∑ (C X y) J)`,`p`]  
            (irule o SIMP_RULE (srw_ss ()) [SYM p_space_def,SYM events_def]) $
            cj 2 IN_MEASURABLE_BOREL_ALL_MEASURE >>
        simp[event_space_def] >> irule_at (Pos last) IN_MEASURABLE_BOREL_SUB >>
        qexistsl_tac [`λx. expectation p (λy. ∑ (C X y) J)`,`λx. ∑ (C X x) J`] >> simp[] >>
        irule_at (Pos (el 2)) IN_MEASURABLE_BOREL_CONST >>
        qexistsl_tac [`expectation p (λy. ∑ (C X y) J)`] >> simp[] >>
        qspecl_then [`measurable_space p`,`X`,`λx. ∑ (C X x) J`,`J`] (irule_at Any) IN_MEASURABLE_BOREL_SUM >>
        fs[real_random_variable,p_space_def,events_def] >> simp[EXTREAL_SUM_IMAGE_NOT_INFTY,C_DEF]) >>
    `0 < t` by simp[] >> fs[] >> rw[] >> REVERSE $ Cases_on `∃n. n ∈ J ∧ 0 < (λn. (b n − a n)²) n`
    >- (fs[Once DISJ_EQ_IMP,Once CONJ_COMM,le_antisym] >>
        `AE x::p. ∑ (C X x) J = Normal (∑ a J)` by (simp[GSYM EXTREAL_SUM_IMAGE_NORMAL] >>
            qspecl_then [`p`,`X`,`λn x. Normal (a n)`,`J`]
                (irule o SIMP_RULE (srw_ss ()) [C_SIMP]) AE_eq_sum >>
            fs[SF PROB_ss]) >>
        `expectation p (λy. ∑ (C X y) J) = Normal (∑ a J)` by (irule EQ_TRANS >>
            qexists_tac `expectation p (λx. Normal (∑ a J))` >>
            irule_at Any expectation_cong_AE >> simp[expectation_const]) >>
        irule eqle_trans >> qexists_tac `0` >> simp[EXP_POS_LE,prob_def] >>
        irule $ iffLR AE_iff_measurable >> fs[SF PROB_ss] >>
        qspecl_then [`λx. ∑ (C X x) J − Normal (∑ a J)`,`p`]
            (irule_at Any o SIMP_RULE (srw_ss ()) []) $ cj 2 IN_MEASURABLE_BOREL_ALL_MEASURE >>
        qexists_tac `λx. ¬(Normal t ≤ ∑ (C X x) J − Normal (∑ a J))` >> simp[EXTENSION] >>
        irule_at Any IN_MEASURABLE_BOREL_SUB >> qexistsl_tac [`λx. Normal (∑ a J)`,`λx. ∑ (C X x) J`] >>
        simp[IN_MEASURABLE_BOREL_CONST'] >> drule_then (irule_at Any) IN_MEASURABLE_BOREL_SUM >>
        qexists_tac `X` >> simp[] >> rw[] >- simp[C_DEF] >- simp[CONJ_COMM] >>
        qspecl_then
            [`m`,`λx. ∑ (C X x) J = Normal (∑ a J)`,`λx. ¬(Normal t ≤ ∑ (C X x) J − Normal (∑ a J))`]
            (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[] >> simp[extreal_sub_def]) >>
    dxrule_at_then (Pos (el 3)) (drule_then assume_tac) REAL_SUM_IMAGE_POS_LT >> rfs[] >>
    `∀s. 0 < s ⇒ prob p ({x | Normal (exp (s * t)) ≤
      exp (Normal s * (∑ (C X x) J − expectation p (λy. ∑ (C X y) J)))} ∩ p_space p) ≤
      Normal (exp (-s * t + s² * ∑ (λn. (b n − a n)²) J / 8))` suffices_by (
        qabbrev_tac `ssq = ∑ (λn. (b n − a n)²) J` >> rw[] >> `0 < 4 * t / ssq` by simp[] >>
        qabbrev_tac `s = 4 * t / ssq` >> first_x_assum $ drule_then mp_tac >>
        qmatch_abbrev_tac `_ (prob _ (s1 ∩ _)) x1 ⇒ _ (prob _ (s2 ∩ _)) x2` >>
        `s1 = s2 ∧ x1 = x2` suffices_by simp[] >> qunabbrevl_tac [`s1`,`x1`,`s2`,`x2`] >>
        simp[EXP_INJ,GSYM extreal_exp_def,GSYM extreal_mul_def,EXTENSION,exp_mono_le,le_lmul] >>
        irule REAL_EQ_LMUL_IMP >> qexists_tac `8 * ssq` >> qmatch_abbrev_tac `_ ∧ r1 = r2` >>
        rfs[REAL_ADD_LDISTRIB] >> qunabbrevl_tac [`s`,`r1`,`r2`] >> simp[POW_MUL]) >>
    rw[] >> irule le_trans >>
    qexists_tac `(Normal (exp (s * t)))⁻¹ * expectation p
        (λx. exp (Normal s * (∑ (C X x) J − expectation p (λy. ∑ (C X y) J))))` >>
    qspecl_then
        [`p`,`λx. exp (Normal s * (∑ (C X x) J − expectation p (λy. ∑ (C X y) J)))`,`Normal (exp (s * t))`]
        (irule_at Any o SIMP_RULE (srw_ss ()) [o_DEF,abs_exp]) prob_markov_ineq >>
    simp[EXP_POS_LT,EXP_NZ,EXP_ADD,GSYM extreal_mul_def,extreal_inv_def,
        GSYM EXP_NEG,REAL_NEG_LMUL,le_lmul,GSYM REAL_SUM_IMAGE_CMUL,GSYM REAL_SUM_IMAGE_CDIV,
        EXP_SUM,GSYM EXTREAL_PROD_IMAGE_NORMAL,Excl "REALMULCANON"] >>
    irule_at Any eqle_trans >>
    qexists_tac `∏ (λn. expectation p (λx. exp (Normal s * (X n x − expectation p (X n))))) J` >>
    irule_at Any EXTREAL_PROD_IMAGE_LE >> simp[] >> CONJ_TAC
    >- (qx_gen_tac `n` >> disch_tac >> irule_at Any expectation_pos >> simp[exp_pos] >>
        irule hoeffding_lemma_gen >> simp[]) >>
    irule_at Any EQ_TRANS >>
        qexists_tac `expectation p (λx. ∏ (λn. exp (Normal s * (X n x − expectation p (X n)))) J)` >>
    qspecl_then [`p`,`λn x. exp (Normal s * (X n x − expectation p (X n)))`,`J`]
        (irule_at Any o SIMP_RULE (srw_ss ()) [o_DEF,C_SIMP]) indep_vars_expectation >>
    simp[] >> irule_at Any expectation_cong >> simp[] >> CONJ_ASM1_TAC
    >- (rw[] >> irule EQ_TRANS >> qexists_tac `exp (∑ (λn. Normal s * (X n x − expectation p (X n))) J)` >>
        qspecl_then [`λn. Normal s * (X n x − expectation p (X n))`,`J`]
            (irule_at Any o SIMP_RULE (srw_ss ()) [o_DEF]) exp_sum >> simp[exp_inj] >>
        irule_at Any EQ_SYM >> irule_at Any EQ_TRANS >>
        qexists_tac `Normal s * ∑ (λn. X n x − expectation p (X n)) J` >>
        drule_then (qspecl_then [`λn. X n x − expectation p (X n)`,`s`]
            (irule_at Any o SIMP_RULE (srw_ss ()) [])) EXTREAL_SUM_IMAGE_CMUL >> simp[eq_lmul] >>
        irule_at Any EQ_TRANS >> qexists_tac `∑ (C X x) J − ∑ (λn. expectation p (X n)) J` >>
        drule_then (qspecl_then [`C X x`,`(λn. expectation p (X n))`]
            (irule_at Any o SIMP_RULE (srw_ss ()) [])) EXTREAL_SUM_IMAGE_SUB >>
        irule_at Any IRULER >> simp[C_DEF] >> NTAC 3 $ irule_at (Pos last) AND_IMP_OR >>
        irule_at Any $ GSYM expectation_sum >> simp[GSYM FORALL_IMP_CONJ_THM] >>
        qx_gen_tac `n` >> disch_tac >> NTAC 2 $ first_x_assum $ drule_then assume_tac >>
        rfs[SF PROB_ss] >> CONJ_ASM1_TAC
        >- (irule integrable_AE_bounded_Borel_measurable >>
            simp[finite_measure_space_def,finite_def] >> qexistsl_tac [`a n`,`b n`] >> simp[]) >>
        Cases_on `∫ p (X n)` >> rfs[integrable_finite_integral] >>
        Cases_on `X n x` >> rfs[] >> simp[extreal_sub_def,extreal_mul_def]) >>
    irule_at Any $ iffLR integrable_cong >>
    qexists_tac `λx. ∏ (λn. exp (Normal s * (X n x − expectation p (X n)))) J` >>
    simp[iffLR prob_space_def,SYM p_space_def] >> pop_assum kall_tac >>
    qspecl_then [`p`,`λn x. exp (Normal s * (X n x − expectation p (X n)))`,`J`]
        (irule_at Any o SIMP_RULE (srw_ss ()) [C_SIMP]) indep_vars_integrable >> simp[] >>
    qspecl_then [`p`,`X`,`(K Borel):β -> extreal algebra`,`J`,`λn x. exp (Normal s * (x − expectation p (X n)))`]
        (irule_at Any o SIMP_RULE (srw_ss ()) [random_variable_def,o_DEF]) indep_vars_cong >>
    simp[] >> fs[real_random_variable] >> simp[GSYM FORALL_IMP_CONJ_THM] >> NTAC 2 strip_tac >>
    NTAC 2 $ first_x_assum $ drule_then assume_tac >> rfs[event_space_def] >>
    drule_at_then (Pos (el 3)) assume_tac integrable_AE_bounded_Borel_measurable >>
    rfs[prob_space_finite_measure_space] >> drule_all_then assume_tac expectation_normal >> fs[] >>
    irule_at Any integrable_AE_bounded_Borel_measurable >>
    qexistsl_tac [`exp (s * (b n - r))`,`0`] >> simp[prob_space_finite_measure_space] >>
    irule_at (Pos (el 3)) IN_MEASURABLE_BOREL_COMP_BOREL >>
    qexistsl_tac [`X n`,`λx. exp (Normal s * (x − Normal r))`] >> csimp[normal_0,exp_pos] >>
    qspecl_then [`p`,`λx. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)`,
        `λx. exp (Normal s * (X n x − Normal r)) ≤ Normal (exp (s * (b n − r)))`]
        (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_subset >>
    qexists_tac `a` >> simp[SYM p_space_def] >>
    map_every (fn (th,qel) => irule_at Any th >> qexistsl_tac qel >> simp[SIGMA_ALGEBRA_BOREL]) [
        (IN_MEASURABLE_BOREL_EXP,[`λx. Normal s * (x − Normal r)`]),
        (IN_MEASURABLE_BOREL_CMUL,[`s`,`λx. x − Normal r`]),
        (IN_MEASURABLE_BOREL_SUB,[`λx. Normal r`,`λx. x`])] >>
    simp[SIGMA_ALGEBRA_BOREL,IN_MEASURABLE_BOREL_CONST',IN_MEASURABLE_BOREL_BOREL_I] >>
    simp[Once $ GSYM AND_IMP_INTRO,GSYM FORALL_IMP_CONJ_THM] >> NTAC 2 strip_tac >>
    Cases_on `X n x` >> rfs[] >> rename [`Normal Xx − Normal Ex`] >>
    simp[extreal_sub_def,extreal_mul_def,extreal_exp_def,EXP_MONO_LE]
QED

(* variants *)
Theorem hoeffding_ineq_strict:
    ∀p X a b J t. prob_space p ∧ FINITE J ∧ 0 ≤ t ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        (∀n. n ∈ J ⇒ AE x::p. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)) ∧ indep_vars p X (K Borel) J ⇒
        prob p ({x | Normal t < ∑ (C X x) J - expectation p (λy. ∑ (C X y) J)} ∩ p_space p) ≤
        Normal (exp (-2 * t² / ∑ (λn. (b n - a n)²) J))
Proof
    rw[] >> drule_all_then mp_tac hoeffding_ineq >>
    DISCH_THEN $ C (resolve_then (Pos $ el 2) irule) le_trans >> irule PROB_INCREASING >>
    fs[SF PROB_ss] >> qabbrev_tac `f = (λx. ∑ (C X x) J − ∫ p (λy. ∑ (C X y) J))` >>
    simp[SUBSET_DEF,iffRL le_lt] >>
    map_every (fn n => irule_at Any $ cj n IN_MEASURABLE_BOREL_ALL_MEASURE) [2,4] >> simp[Abbr `f`] >>
    irule IN_MEASURABLE_BOREL_SUB' >> simp[] >>
    qexistsl_tac [`λx. ∑ (C X x) J`,`λx. ∫ p (λy. ∑ (C X y) J)`] >> simp[IN_MEASURABLE_BOREL_CONST'] >>
    irule IN_MEASURABLE_BOREL_SUM' >> simp[] >> qexistsl_tac [`X`,`J`] >> simp[C_DEF]
QED

Theorem hoeffding_ineq_delta:
    ∀p X a b J d. prob_space p ∧ FINITE J ∧ 0 < d ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        (∀n. n ∈ J ⇒ AE x::p. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)) ∧ indep_vars p X (K Borel) J ⇒
        prob p ({x | Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b n - a n)²) J / 2)) <
            ∑ (C X x) J - expectation p (λy. ∑ (C X y) J)} ∩ p_space p) ≤ Normal d
Proof
    rw[] >> qmatch_abbrev_tac `_ _ s ≤ _:extreal` >>
    `s ∈ events p` by (fs[SF PROB_ss,Abbr `s`] >>
        qabbrev_tac `f = (λx. ∑ (C X x) J − ∫ p (λy. ∑ (C X y) J))` >> simp[] >>
        irule $ cj 4 IN_MEASURABLE_BOREL_ALL_MEASURE >> simp[] >>
        irule IN_MEASURABLE_BOREL_SUB' >> simp[Abbr `f`] >>
        qexistsl_tac [`λx. ∑ (C X x) J`,`λx. ∫ p (λy. ∑ (C X y) J)`] >> simp[IN_MEASURABLE_BOREL_CONST'] >>
        irule IN_MEASURABLE_BOREL_SUM' >> simp[] >> qexistsl_tac [`X`,`J`] >> simp[C_DEF]) >>
    REVERSE $ Cases_on `d < 1`
    >- (gvs[GSYM real_lte] >> irule le_trans >> qexists_tac `Normal 1` >> simp[normal_1] >>
        irule PROB_LE_1 >> simp[]) >>
    Cases_on `∑ (λn. (b n − a n)²) J = 0`
    >- (`prob p s = 0` suffices_by simp[] >> fs[Abbr `s`,SQRT_0,normal_0] >> Cases_on `J = ∅`
        >- simp[EXTREAL_SUM_IMAGE_EMPTY,expectation_zero,PROB_EMPTY] >>
        drule_then mp_tac REAL_SUM_IMAGE_NONZERO >>
        DISCH_THEN $ qspec_then `λn. (b n − a n)²` mp_tac >> simp[DISJ_EQ_IMP] >> DISCH_TAC >>
        fs[le_antisym] >> simp[PROB_ZERO_AE_EQ] >> simp[Once DISJ_COMM,DISJ_EQ_IMP] >>
        qspecl_then [`p`,`λn x. Normal (a n) = X n x`,`J`]
            (dxrule_at_then (Pos $ el 3) assume_tac o SIMP_RULE (srw_ss ()) []) AE_BIGINTER >>
        rfs[finite_countable,prob_space_measure_space] >>
        REVERSE $ qsuff_tac `AE x::p. ∑ (C X x) J = Normal (∑ a J)`
        >- (qspecl_then [`p`,`λx. ∀n. n ∈ J ⇒ Normal (a n) = X n x`,
                `λx. ∑ (C X x) J = Normal (∑ a J)`]
                (dxrule_then irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
            rw[GSYM EXTREAL_SUM_IMAGE_NORMAL] >> irule EXTREAL_SUM_IMAGE_EQ' >> simp[]) >>
        pop_assum kall_tac >> rw[] >>
        qspecl_then [`p`,`λx. ∑ (C X x) J = Normal (∑ a J)`,
            `λx. x ∈ p_space p ⇒ ¬(0 < ∑ (C X x) J − expectation p (λy. ∑ (C X y) J))`]
            (drule_then irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[] >> `expectation p (λy. ∑ (C X y) J) = Normal (∑ a J)` suffices_by rw[extreal_sub_def] >>
        irule EQ_TRANS >> qexists_tac `expectation p (λy. Normal (∑ a J))` >>
        irule_at Any expectation_cong_AE >> simp[expectation_const]) >>
    `0 ≤ ln d⁻¹ * ∑ (λn. (b n − a n)²) J / 2` by (simp[real_div] >>
        map_every (irule_at Any) [REAL_LE_MUL,LN_POS,REAL_SUM_IMAGE_POS,REAL_INV_1_LE] >> simp[]) >>
    simp[Abbr `s`] >> drule_then assume_tac SQRT_POS_LE >>
    `∀x1:extreal x2 x3. x1 ≤ x2 ∧ x2 = x3 ⇒ x1 ≤ x3` by simp[] >>
    drule_all_then mp_tac hoeffding_ineq_strict >> DISCH_THEN $ pop_assum o resolve_then Any irule >>
    simp[SQRT_POW_2] >> simp[real_div,LN_INV,EXP_LN]
QED

(*
Theorem hoeffding_ineq_inf_delta:
    ∀p X a b N d. prob_space p ∧ 0 < d ∧ (∀n. real_random_variable (X n) p) ∧
        (∀n. AE x::p. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)) ∧
        (∀n. indep_vars p X (K Borel) (count n)) ∧
        (∀n. ({x | N x = n} ∩ p_space p) ∈ events p) ⇒
        prob p ({x | Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b n - a n)²) (count (N x)) / 2)) <
            ∑ (C X x) (count (N x)) - expectation p (λy. ∑ (C X y) (count (N x)))} ∩ p_space p) ≤ Normal d
Proof
    cheat
QED
*)

Theorem hoeffding_ineq_avg_delta:
    ∀p X a b J d. prob_space p ∧ FINITE J ∧ 0 < d ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        (∀n. n ∈ J ⇒ AE x::p. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)) ∧ indep_vars p X (K Borel) J ⇒
        prob p ({x | Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b n - a n)²) J / (2 * (&CARD J)²))) <
            (&CARD J)⁻¹ * ∑ (C X x) J - expectation p (λy. (&CARD J)⁻¹ * ∑ (C X y) J)} ∩ p_space p) ≤ Normal d
Proof
    rw[] >> qmatch_abbrev_tac `_ _ s ≤ _:extreal` >>
    `s ∈ events p` by (fs[SF PROB_ss,Abbr `s`] >>
        qabbrev_tac `f = (λx. (&CARD J)⁻¹ * ∑ (C X x) J − ∫ p (λy. (&CARD J)⁻¹ * ∑ (C X y) J))` >> simp[] >>
        irule $ cj 4 IN_MEASURABLE_BOREL_ALL_MEASURE >> simp[] >>
        irule IN_MEASURABLE_BOREL_SUB' >> simp[Abbr `f`] >>
        qexistsl_tac [`λx. (&CARD J)⁻¹ * ∑ (C X x) J`,`λx. ∫ p (λy. (&CARD J)⁻¹ * ∑ (C X y) J)`] >>
        simp[IN_MEASURABLE_BOREL_CONST'] >> irule IN_MEASURABLE_BOREL_MUL' >> simp[] >>
        qexistsl_tac [`λx. (&CARD J)⁻¹`,`λx. ∑ (C X x) J`] >> simp[IN_MEASURABLE_BOREL_CONST'] >>
        irule IN_MEASURABLE_BOREL_SUM' >> simp[] >> qexistsl_tac [`X`,`J`] >> simp[C_DEF]) >>
    REVERSE $ Cases_on `d < 1`
    >- (gvs[GSYM real_lte] >> irule le_trans >> qexists_tac `Normal 1` >> simp[normal_1] >>
        irule PROB_LE_1 >> simp[]) >>
    qunabbrev_tac `s` >> Cases_on `J = ∅`
    >- simp[REAL_SUM_IMAGE_EMPTY,SQRT_0,normal_0,EXTREAL_SUM_IMAGE_EMPTY,expectation_zero,PROB_EMPTY] >>
    `∀x1:extreal x2 x3. x1 ≤ x3 ∧ x1 = x2 ⇒ x2 ≤ x3` by simp[] >>
    drule_all_then mp_tac hoeffding_ineq_delta >> DISCH_THEN $ pop_assum o resolve_then Any irule >>
    irule PROB_CONG_AE >> fs[SF PROB_ss] >> rw[]
    >- (qabbrev_tac `f = (λx. ∑ (C X x) J − ∫ p (λy. ∑ (C X y) J))` >> simp[] >>
        irule $ cj 4 IN_MEASURABLE_BOREL_ALL_MEASURE >> simp[] >>
        irule IN_MEASURABLE_BOREL_SUB' >> simp[Abbr `f`] >>
        qexistsl_tac [`λx. ∑ (C X x) J`,`λx. ∫ p (λy. ∑ (C X y) J)`] >> simp[IN_MEASURABLE_BOREL_CONST'] >>
        irule IN_MEASURABLE_BOREL_SUM' >> simp[] >> qexistsl_tac [`X`,`J`] >> simp[C_DEF]) >>
    qspecl_then [`p`,`λn x. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)`,`J`]
        (dxrule_at_then (Pos $ el 3) assume_tac o SIMP_RULE (srw_ss ()) []) AE_BIGINTER >>
    rfs[finite_countable] >> qpat_x_assum `_ ∈ measurable_sets m` kall_tac >>
    `integrable p (λy. ∑ (C X y) J)` by (irule integrable_AE_bounded_Borel_measurable >>
        simp[finite_measure_space_def,finite_def] >> drule_then (irule_at Any) IN_MEASURABLE_BOREL_SUM' >>
        qexistsl_tac [`X`,`∑ b J`,`∑ a J`] >>
        qspecl_then [`p`,`λx. ∀n. n ∈ J ⇒ Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)`,
            `λx. Normal (∑ a J) ≤ ∑ (C X x) J ∧ ∑ (C X x) J ≤ Normal (∑ b J)`]
            (dxrule_then (irule_at Any) o SIMP_RULE (srw_ss ()) []) AE_subset >>
        simp[C_DEF,GSYM EXTREAL_SUM_IMAGE_NORMAL] >> qx_gen_tac `x` >> DISCH_TAC >>
        NTAC 2 $ irule_at Any EXTREAL_SUM_IMAGE_MONO' >> simp[]) >>
    simp[extreal_of_num_def,extreal_inv_def,integral_cmul] >>
    map_every qabbrev_tac [`rt = sqrt (ln d⁻¹ * ∑ (λn. (b n − a n)²) J / 2)`,
        `rton = sqrt (ln d⁻¹ * ∑ (λn. (b n − a n)²) J / (2 * (&CARD J)²))`,
        `ef = ∫ p (λy. ∑ (C X y) J)`,`n = Normal (&CARD J)⁻¹`] >>
    qspecl_then [`p`,`λx. ∀n. n ∈ J ⇒ Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)`,
        `λx. Normal rt < ∑ (C X x) J − ef ∧ x ∈ m_space p ⇔ Normal rton < n * ∑ (C X x) J − efon ∧ x ∈ m_space p`]
        (dxrule_then irule o SIMP_RULE (srw_ss ()) []) AE_subset >> rw[] >>
    `∃f. ∑ (C X x) J = ∑ (Normal ∘ f) J` by (irule_at Any EXTREAL_SUM_IMAGE_EQ' >>
        simp[GSYM SKOLEM_THM] >> qx_gen_tac `m` >> rw[RIGHT_EXISTS_IMP_THM] >>
        first_x_assum dxrule >> Cases_on `X m x` >> simp[]) >>
    drule_all_then assume_tac integrable_normal_integral >> fs[] >> qunabbrevl_tac [`ef`,`n`] >>
    simp[o_DEF,EXTREAL_SUM_IMAGE_NORMAL,extreal_mul_def,extreal_sub_def] >>
    `rton = (&CARD J)⁻¹ * rt` suffices_by (DISCH_THEN SUBST1_TAC >>
        `0r < (&CARD J)⁻¹` by simp[GSYM REAL_LT_NZ,CARD_EQ_0] >>
        dxrule_then (qspecl_then [`rt`,`∑ f J − r`] $ SUBST1_TAC o SYM) REAL_LT_LMUL >> simp[]) >>
    qunabbrevl_tac [`rt`,`rton`] >> qabbrev_tac `ds = ln d⁻¹ * ∑ (λn. (b n − a n)²) J` >>
    `0 ≤ ds` by (qunabbrev_tac `ds` >>
        map_every (irule_at Any) [REAL_LE_MUL,LN_POS,REAL_SUM_IMAGE_POS,REAL_INV_1_LE] >> simp[]) >>
    simp[SQRT_DIV,SQRT_MUL,POW_2_SQRT]
QED

Theorem hoeffding_ineq_avg_ci:
    ∀p X a b J d. prob_space p ∧ FINITE J ∧ 0 < d ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        (∀n. n ∈ J ⇒ AE x::p. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)) ∧ indep_vars p X (K Borel) J ⇒
        Normal (1 - d) ≤ prob p ({x | (&CARD J)⁻¹ * ∑ (C X x) J -
            Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b n - a n)²) J / (2 * (&CARD J)²))) ≤
            expectation p (λy. (&CARD J)⁻¹ * ∑ (C X y) J)} ∩ p_space p)
Proof
    rw[] >> Cases_on `J = ∅`
    >- simp[REAL_SUM_IMAGE_EMPTY,SQRT_0,normal_0,EXTREAL_SUM_IMAGE_EMPTY,
        expectation_zero, PROB_UNIV,GSYM normal_1] >>
    drule_all hoeffding_ineq_avg_delta >> qmatch_abbrev_tac `prob p s ≤ _ ⇒ _ ≤ prob p t` >>
    `s ∈ events p ∧ t ∈ events p` by (fs[SF PROB_ss,Abbr `s`,Abbr `t`] >>
        map_every qabbrev_tac [`f = (λx. (&CARD J)⁻¹ * ∑ (C X x) J − ∫ p (λy. (&CARD J)⁻¹ * ∑ (C X y) J))`,
            `g = (λx. (&CARD J)⁻¹ * ∑ (C X x) J -
            Normal (sqrt (ln d⁻¹ * ∑ (λn. (b n − a n)²) J / (2 * (&CARD J)²))))`] >> simp[] >>
        map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> simp[] >> qexistsl_tac qex >> simp ths) [
            (Any,cj 4 IN_MEASURABLE_BOREL_ALL_MEASURE,[],[Abbr `f`]),
            (Any,cj 3 IN_MEASURABLE_BOREL_ALL_MEASURE,[],[Abbr `g`]),
            (Pos last,IN_MEASURABLE_BOREL_SUB',
                [`λx. ∫ p (λy. (&CARD J)⁻¹ * ∑ (C X y) J)`,`λx. (&CARD J)⁻¹ * ∑ (C X x) J`],
                [IN_MEASURABLE_BOREL_CONST']),
            (Pos last,IN_MEASURABLE_BOREL_SUB',
                [`λx. Normal (sqrt (ln d⁻¹ * ∑ (λn. (b n − a n)²) J / (2 * (&CARD J)²)))`,
                `λx. (&CARD J)⁻¹ * ∑ (C X x) J`],[IN_MEASURABLE_BOREL_CONST']),
            (Any,IN_MEASURABLE_BOREL_MUL',[`λx. (&CARD J)⁻¹`,`λx. ∑ (C X x) J`],
                [IN_MEASURABLE_BOREL_CONST']),
            (Any,IN_MEASURABLE_BOREL_SUM',[`X`,`J`],[C_DEF])]) >>
    `prob p t = prob p (p_space p DIFF s)` suffices_by (DISCH_THEN SUBST1_TAC >> simp[PROB_COMPL] >>
        `0 ≤ prob p s ∧ prob p s ≤ 1` by simp[PROB_POSITIVE,PROB_LE_1] >>
        Cases_on `prob p s` >> fs[GSYM normal_0,GSYM normal_1] >> simp[extreal_sub_def]) >>
    qspecl_then [`p`,`λn x. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)`,`J`]
        (dxrule_at_then (Pos $ el 3) assume_tac o SIMP_RULE (srw_ss ()) []) AE_BIGINTER >>
    rfs[finite_countable,prob_space_measure_space] >> irule PROB_CONG_AE >> simp[EVENTS_COMPL] >>
    `integrable p (λy. ∑ (C X y) J)` by (irule integrable_AE_bounded_Borel_measurable >>
        simp[prob_space_finite_measure_space] >> drule_then (irule_at Any) IN_MEASURABLE_BOREL_SUM' >>
        qexistsl_tac [`X`,`∑ b J`,`∑ a J`] >>
        qspecl_then [`p`,`λx. ∀n. n ∈ J ⇒ Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)`,
            `λx. Normal (∑ a J) ≤ ∑ (C X x) J ∧ ∑ (C X x) J ≤ Normal (∑ b J)`]
            (dxrule_then (irule_at Any) o SIMP_RULE (srw_ss ()) []) AE_subset >>
        simp[C_DEF,GSYM EXTREAL_SUM_IMAGE_NORMAL] >> fs[SF PROB_ss] >> qx_gen_tac `x` >>
        DISCH_TAC >> NTAC 2 $ irule_at Any EXTREAL_SUM_IMAGE_MONO' >> simp[]) >>
    qspecl_then [`p`,`λx. ∀n. n ∈ J ⇒ Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)`,
        `λx. x ∈ t ⇔ x ∈ p_space p ∧ x ∉ s`]
        (dxrule_then (irule_at Any) o SIMP_RULE (srw_ss ()) [GSYM p_space_def]) AE_subset >>
    qx_gen_tac `x` >> DISCH_TAC >>
    `∃f. ∑ (C X x) J = ∑ (Normal ∘ f) J` by (irule_at Any EXTREAL_SUM_IMAGE_EQ' >>
        simp[GSYM SKOLEM_THM] >> qx_gen_tac `m` >> rw[RIGHT_EXISTS_IMP_THM] >>
        first_x_assum dxrule >> Cases_on `X m x` >> simp[]) >>
    drule_at_then Any assume_tac integrable_normal_integral >> rfs[SF PROB_ss] >>
    simp[Abbr `s`,Abbr `t`,extreal_of_num_def,integral_cmul,extreal_inv_def,
        o_DEF,EXTREAL_SUM_IMAGE_NORMAL,extreal_mul_def,extreal_sub_def]
QED

(* DISSERTATION CI *)
Theorem hoeffding_ineq_neg_avg_ci:
    ∀p X a b J d. prob_space p ∧ FINITE J ∧ 0 < d ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        (∀n. n ∈ J ⇒ AE x::p. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)) ∧
        indep_vars p X (K Borel) J ⇒
        Normal (1 - d) ≤ prob p ({x | expectation p (λy. (&CARD J)⁻¹ * ∑ (C X y) J) ≤
            (&CARD J)⁻¹ * ∑ (C X x) J +
            Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b n - a n)²) J / (2 * (&CARD J)²)))} ∩ p_space p)
Proof
    rw[] >>
    ‘∀n. n ∈ J ⇒ real_random_variable ((λn x. -X n x) n) p’ by (rw[] >>
        irule real_random_variable_ainv >> simp[]) >>
    ‘∀n. n ∈ J ⇒ AE x::p. Normal ((λn. -b n) n) ≤ (λn x. -X n x) n x ∧
      (λn x. -X n x) n x ≤ Normal ((λn. -a n) n)’ by (rw[] >>
        qspecl_then [‘p’,‘λx. Normal (a n) ≤ X n x ∧ X n x ≤ Normal (b n)’,
            ‘λx. Normal (-b n) ≤ -X n x ∧ -X n x ≤ Normal (-a n)’] (irule o SRULE []) AE_subset >>
        simp[] >> qx_gen_tac ‘x’ >> Cases_on ‘X n x’ >> simp[extreal_ainv_def]) >>
    ‘indep_vars p (λn x. -X n x) (K Borel) J’ by (
        ‘(λn x. -X n x) = (λn. (K (λx. -x)) n ∘ X n)’ by simp[FUN_EQ_THM] >>
        pop_assum SUBST1_TAC >> irule indep_vars_cong >> simp[real_random_variable_random_variable] >>
        rw[] >> irule IN_MEASURABLE_BOREL_MINUS >> simp[SIGMA_ALGEBRA_BOREL] >>
        qexists_tac ‘I’ >> simp[SIGMA_ALGEBRA_BOREL,MEASURABLE_I]) >>
    drule_all_then mp_tac hoeffding_ineq_avg_ci >> ntac 3 $ pop_assum kall_tac >>
    qmatch_abbrev_tac ‘_ ≤ prob _ (CIlb ∩ _) ⇒ _ ≤ prob _ (CIub ∩ _)’ >>
    ‘∀x. x ∈ p_space p ⇒ (x ∈ CIlb ⇔ x ∈ CIub)’ suffices_by (strip_tac >>
        ‘(CIlb ∩ p_space p) = (CIub ∩ p_space p)’ suffices_by simp[] >>
        rw[EXTENSION] >> metis_tac[]) >>
    UNABBREV_ALL_TAC >> rw[] >>
    ‘(λn. (-a n − -b n)²) = (λn. (b n − a n)²)’ by simp[FUN_EQ_THM,SUB_POW_2] >>
    pop_assum SUBST1_TAC >> qmatch_abbrev_tac ‘_ - Normal c ≤ _ ⇔ _’ >>
    ‘∀z. z ∈ p_space p ⇒ (&CARD J)⁻¹ * ∑ (C (λn x. -X n x) z) J = - ((&CARD J)⁻¹ * ∑ (C X z) J)’ by (
        rw[] >> drule_then (qspecl_then [‘C X z’,‘-1’] mp_tac) EXTREAL_SUM_IMAGE_CMUL >>
        simp[normal_minus1,GSYM neg_minus1,C_DEF] >> gs[real_random_variable_def] >>
        DISCH_THEN kall_tac >> simp[mul_rneg]) >>
    ‘∀z. z ∈ p_space p ⇒ ∑ (C (λn x. -X n x) z) J = -∑ (C X z) J’ by (
        rw[] >> drule_then (qspecl_then [‘C X z’,‘-1’] mp_tac) EXTREAL_SUM_IMAGE_CMUL >>
        simp[normal_minus1,GSYM neg_minus1,C_DEF] >> DISCH_THEN irule >>
        gs[real_random_variable_def]) >>
    ‘expectation p (λy. (&CARD J)⁻¹ * ∑ (C (λn x. -X n x) y) J) =
      -expectation p (λy. (&CARD J)⁻¹ * ∑ (C X y) J)’ suffices_by (
        strip_tac >> simp[] >> qmatch_abbrev_tac ‘_ ⇔ Eest ≤ est + Normal c’ >>
        Cases_on ‘Eest’ >> Cases_on ‘est’ >>
        simp[extreal_ainv_def,extreal_sub_def,extreal_add_def]) >>
    irule EQ_TRANS >>
    qspecl_then [‘p’,‘λy. (&CARD J)⁻¹ * ∑ (C X y) J’,‘-1’]
        (irule_at Any o SRULE [normal_minus1,GSYM neg_minus1]) expectation_cmul >>
    irule_at Any expectation_cong >> simp[] >> ntac 2 $ pop_assum kall_tac >>
    Cases_on ‘J = ∅’ >- simp[prob_space_measure_space,integrable_zero] >>
    ‘(&CARD J)⁻¹ = Normal (&CARD J)⁻¹’ by (
        ‘&CARD J ≠ 0r’ by simp[] >> simp[GSYM extreal_inv_def,GSYM extreal_of_num_def]) >>
    pop_assum SUBST1_TAC >>
    qspecl_then [‘m’,‘λx. ∑ (C X x) J’,‘(&CARD J)⁻¹’] (irule o SRULE []) integrable_cmul >>
    simp[C_DEF] >> irule_at Any integrable_sum' >> rw[prob_space_measure_space] >>
    irule integrable_AE_bounded_Borel_measurable >> simp[prob_space_finite_measure_space] >>
    fs[real_random_variable,event_space_def] >> metis_tac[]
QED

Theorem hoeffding_ineq_inf_neg_avg_ci_event:
    ∀p XM a b JM M d. let pm = (λm. cond_prob_space p ({x | M x = m} ∩ p_space p)) in
        prob_space p ∧ 0 < d ∧ (∀m:num. FINITE (JM m)) ∧
        (∀m. {x | M x = m} ∩ p_space p ∈ events p) ∧
        (∀m n. n ∈ JM m ⇒ real_random_variable (XM m n) (pm m)) ∧
        (∀m n. n ∈ JM m ⇒ AE x::(pm m). Normal (a m n) ≤ XM m n x ∧ XM m n x ≤ Normal (b m n)) ∧
        (∀m. indep_vars (pm m) (XM m) (K Borel) (JM m)) ⇒
        ({x | expectation (pm (M x)) (λy. (&CARD (JM (M x)))⁻¹ * ∑ (C (XM (M x)) y) (JM (M x))) ≤
            (&CARD (JM (M x)))⁻¹ * ∑ (C (XM (M x)) x) (JM (M x)) +
            Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b (M x) n - a (M x) n)²) (JM (M x)) /
            (2 * (&CARD (JM (M x)))²)))} ∩ p_space p) ∈ events p
Proof
    rw[] >> qmatch_abbrev_tac ‘est_ub ∈ _’ >>
    map_every qabbrev_tac [‘M_set = (λm. {x | M x = m} ∩ p_space p)’,
        ‘pm = (λm. cond_prob_space p (M_set m))’] >> fs[] >>
    ‘est_ub = BIGUNION (IMAGE (λm. est_ub ∩ M_set m) 𝕌(:num))’ by (
        simp[EXTENSION,IN_BIGUNION_IMAGE] >> qx_gen_tac ‘x’ >> rw[EQ_IMP_THM] >>
        qexists ‘M x’ >> UNABBREV_ALL_TAC >> gs[]) >>
    pop_assum SUBST1_TAC >> gs[SF PROB_ss] >> irule MEASURE_SPACE_BIGUNION >>
    simp[] >> qx_gen_tac ‘m’ >> map_every qabbrev_tac [‘J = JM m’,‘X = XM m’] >>
    ‘est_ub ∩ M_set m ∈ measurable_sets (pm m)’ suffices_by (
        simp[Abbr ‘pm’,cond_prob_space_def,measurable_sets_def,events_def] >>
        rw[] >> simp[] >> irule MEASURE_SPACE_INTER >> simp[]) >>
    ‘est_ub ∩ M_set m = ({x | ∫ (pm m) (λy. (&CARD J)⁻¹ * ∑ (C X y) J) ≤
      (λx. (&CARD J)⁻¹ * ∑ (C X x) J +
      Normal (sqrt (ln d⁻¹ * ∑ (λn. (b m n − a m n)²) J / (2 * (&CARD J)²)))) x} ∩ m_space (pm m))’ by (
        UNABBREV_ALL_TAC >> simp[EXTENSION,m_space_cond_prob_space] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >>
    ‘sigma_algebra (measurable_space (pm m))’ by (
        simp[Abbr ‘pm’,cond_prob_space_def] >> ‘M_set m ∈ measurable_sets p’ by simp[] >>
        drule_all MEASURE_SPACE_RESTRICTED >> simp[measure_space_def,INTER_COMM,events_def]) >>
    chain_irule_at [
        (Any,cj 2 IN_MEASURABLE_BOREL_ALL_MEASURE,[],[]),
        (Any,IN_MEASURABLE_BOREL_ADD',
            [‘λx. (&CARD J)⁻¹ * ∑ (C X x) J’,
            ‘λx. Normal (sqrt (ln d⁻¹ * ∑ (λn. (b m n − a m n)²) J / (2 * (&CARD J)²)))’],[]),
        (Pos last,IN_MEASURABLE_BOREL_CONST,
            [‘Normal (sqrt (ln d⁻¹ * ∑ (λn. (b m n − a m n)²) J / (2 * (&CARD J)²)))’],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',[‘λx. (&CARD J)⁻¹’,‘λx. ∑ (C X x) J’],[]),
        (Pos hd,IN_MEASURABLE_BOREL_CONST,[‘(&CARD J)⁻¹’],[]),
        (Any,IN_MEASURABLE_BOREL_SUM',[‘X’,‘J’],[C_DEF,Abbr ‘X’,Abbr ‘J’])]
QED

Theorem hoeffding_ineq_inf_neg_avg_ci_prob:
    ∀p XM a b JM M d. let pm = (λm. cond_prob_space p ({x | M x = m} ∩ p_space p)) in
        prob_space p ∧ 0 < d ∧ (∀m:num. FINITE (JM m)) ∧
        (∀m. {x | M x = m} ∩ p_space p ∈ events p) ∧
        (∀m n. n ∈ JM m ⇒ real_random_variable (XM m n) (pm m)) ∧
        (∀m n. n ∈ JM m ⇒ AE x::(pm m). Normal (a m n) ≤ XM m n x ∧ XM m n x ≤ Normal (b m n)) ∧
        (∀m. indep_vars (pm m) (XM m) (K Borel) (JM m)) ⇒
        Normal (1 - d) ≤ prob p ({x |
            expectation (pm (M x)) (λy. (&CARD (JM (M x)))⁻¹ * ∑ (C (XM (M x)) y) (JM (M x))) ≤
            (&CARD (JM (M x)))⁻¹ * ∑ (C (XM (M x)) x) (JM (M x)) +
            Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b (M x) n - a (M x) n)²) (JM (M x)) /
            (2 * (&CARD (JM (M x)))²)))} ∩ p_space p)
Proof
    rw[] >> qmatch_abbrev_tac ‘_:extreal ≤ prob _ est_ub’ >>
    map_every qabbrev_tac [‘M_set = (λm. {x | M x = m} ∩ p_space p)’,
        ‘pm = (λm. cond_prob_space p (M_set m))’] >> fs[] >>
    ‘est_ub ∈ events p’ by (
        UNABBREV_ALL_TAC >> metis_tac[hoeffding_ineq_inf_neg_avg_ci_event]) >>
    reverse $ Cases_on ‘d < 1’
    >- (gs[REAL_NOT_LT] >> irule le_trans >> qexists ‘Normal 0’ >>
        simp[extreal_le_def,normal_0,PROB_POSITIVE]) >>
    qspecl_then [‘1r’,‘d’] (gs o single o SYM) REAL_SUB_LT >>
    ‘suminf (λm. Normal (1 - d) * prob p (M_set m)) = Normal (1 - d) ∧
      suminf (λm. prob p (est_ub ∩ M_set m)) = prob p est_ub ∧
      suminf (λm. Normal (1 - d) * prob p (M_set m)) ≤ suminf (λm. prob p (est_ub ∩ M_set m))’
        suffices_by (rw[] >> gs[]) >>
    rpt conj_tac
    >- (irule EQ_TRANS >>
        qspecl_then [‘prob p ∘ M_set’,‘Normal (1 - d)’] (irule_at Any o SRULE []) ext_suminf_cmul >>
        simp[PROB_POSITIVE] >> ‘suminf (prob p ∘ M_set) = 1’ suffices_by simp[] >>
        drule_then (SUBST1_TAC o SYM) PROB_UNIV >> irule (GSYM PROB_COUNTABLY_ADDITIVE) >>
        simp[FUNSET,Abbr ‘M_set’,Once EXTENSION,DISJOINT_ALT] >> qx_gen_tac ‘x’ >>
        reverse $ Cases_on ‘x ∈ p_space p’ >> simp[]
        >- (qx_gen_tac ‘s’ >> simp[GSYM IMP_DISJ_THM] >> rw[EXTENSION] >> metis_tac[])
        >- (qexists ‘{y | M y = M x} ∩ p_space p’ >> simp[] >> qexists ‘M x’ >> simp[]))
    >- (‘(λm. prob p (est_ub ∩ M_set m)) = prob p ∘ (λm. (est_ub ∩ M_set m))’ by simp[FUN_EQ_THM] >>
        pop_assum SUBST1_TAC >> irule (GSYM PROB_COUNTABLY_ADDITIVE) >>
        simp[FUNSET,EVENTS_INTER] >> simp[Abbr ‘M_set’,Once EXTENSION,DISJOINT_ALT] >>
        qx_gen_tac ‘x’ >> Cases_on ‘x ∈ est_ub’ >> simp[]
        >- (qexists ‘est_ub ∩ ({y | M y = M x} ∩ p_space p)’ >>
            simp[SF SFY_ss,PROB_SPACE_IN_PSPACE] >> qexists ‘M x’ >> simp[])
        >- (qx_gen_tac ‘s’ >> simp[GSYM IMP_DISJ_THM] >> rw[EXTENSION] >>
            metis_tac[PROB_SPACE_IN_PSPACE])) >>
    irule ext_suminf_mono >> simp[] >>
    ConseqConv.CONSEQ_REWRITE_TAC ([le_mul],[],[]) >> simp[PROB_POSITIVE] >>
    qx_gen_tac ‘m’ >> Cases_on ‘prob p (M_set m) = 0’ >- simp[PROB_POSITIVE,EVENTS_INTER] >>
    ‘Normal (1 − d) ≤ prob p (est_ub ∩ M_set m) / prob p (M_set m)’ suffices_by (
        ‘∃c. prob p (M_set m) = Normal c ∧ 0 < c’ suffices_by metis_tac[le_rdiv] >>
        ‘0 < prob p (M_set m)’ by simp[PROB_POSITIVE,lt_le] >>
        ‘prob p (M_set m) ≤ 1’ by simp[PROB_LE_1] >>
        Cases_on ‘prob p (M_set m)’ >> gvs[]) >>
    simp[GSYM cond_prob_def,GSYM prob_cond_prob_space_alt] >>
    map_every qabbrev_tac [‘J = JM m’,‘X = XM m’] >>
    ‘est_ub ∩ M_set m = ({x |
      expectation (pm m) (λy. (&CARD J)⁻¹ * ∑ (C X y) J) ≤ (&CARD J)⁻¹ * ∑ (C X x) J +
      Normal (sqrt (ln d⁻¹ * ∑ (λn. (b m n − a m n)²) J / (2 * (&CARD J)²)))} ∩ p_space (pm m))’ by (
        UNABBREV_ALL_TAC >> simp[EXTENSION,p_space_cond_prob_space] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >> irule hoeffding_ineq_neg_avg_ci >>
    qunabbrevl_tac [‘pm’,‘J’,‘X’] >> simp[prob_space_cond_prob_space]
QED

Theorem hoeffding_ineq_inf_neg_avg_ci:
    ∀p XM a b JM M d. let pm = (λm. cond_prob_space p ({x | M x = m} ∩ p_space p)) in
        prob_space p ∧ 0 < d ∧ (∀m:num. FINITE (JM m)) ∧
        (∀m. {x | M x = m} ∩ p_space p ∈ events p) ∧
        (∀m n. n ∈ JM m ⇒ real_random_variable (XM m n) (pm m)) ∧
        (∀m n. n ∈ JM m ⇒ AE x::(pm m). Normal (a m n) ≤ XM m n x ∧ XM m n x ≤ Normal (b m n)) ∧
        (∀m. indep_vars (pm m) (XM m) (K Borel) (JM m)) ⇒
        let ci_set = ({x |
            expectation (pm (M x)) (λy. (&CARD (JM (M x)))⁻¹ * ∑ (C (XM (M x)) y) (JM (M x))) ≤
            (&CARD (JM (M x)))⁻¹ * ∑ (C (XM (M x)) x) (JM (M x)) +
            Normal (sqrt ((ln d⁻¹) * ∑ (λn. (b (M x) n - a (M x) n)²) (JM (M x)) /
            (2 * (&CARD (JM (M x)))²)))} ∩ p_space p)
        in ci_set ∈ events p ∧ Normal (1 - d) ≤ prob p ci_set
Proof
    metis_tac[hoeffding_ineq_inf_neg_avg_ci_event,hoeffding_ineq_inf_neg_avg_ci_prob]
QED

val _ = export_theory();
