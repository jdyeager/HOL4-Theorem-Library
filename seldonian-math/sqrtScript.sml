open HolKernel Parse boolLib bossLib;
open simpLib;
open combinTheory;
open pairTheory;
open pred_setTheory;
open WhileTheory;
(* open listTheory; *)
open arithmeticTheory;
open realTheory;
open realLib;
(* open real_sigmaTheory; *)
open transcTheory;
(*
open util_probTheory;
open extrealTheory;
open sigma_algebraTheory;
open borelTheory;
open measureTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;
*)
open sigma_algebraTheory;
open real_borelTheory;

open ex_machina;
open trivialTheory;
open while_measureTheory;
(*
open trivialSimps;
*)

val _ = new_theory "sqrt";

(*
val _ = reveal "C";
*)

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];

Definition rational_sqrt_wfrel_def:
    rational_sqrt_wfrel tol x est =
        if est² = x then 0n
        else clg (logr 4 ((est² - x) / tol²))
End

Definition rational_sqrt_helper_def:
    rational_sqrt_helper tol x est =
        if tol ≤ 0 ∨ x ≤ 0r ∨ est ≤ 0 then 0
        else if abs (est² - x) ≤ tol² then est
        else rational_sqrt_helper tol x ((est + x/est)/2)
Termination
    WF_REL_TAC
        ‘inv_image ((λa b. ¬(a ⇒ b)) LEX $<) (λ(tol,x,est). (x < est²,rational_sqrt_wfrel tol x est))’
    >- simp[WF_NIMP] >> ntac 3 strip_tac >>
    map_every qabbrev_tac [‘estp = (est + x / est) / 2’,‘estpc = (est - x / est) / 2’] >>
    rw[REAL_NOT_LE,REAL_NOT_LT] >>
    ‘estp² - x = estpc²’ by (UNABBREV_ALL_TAC >> simp[REAL_SUB_LDISTRIB] >>
        simp[ADD_POW_2,SUB_POW_2,REAL_POS_NZ] >> simp[real_sub,REAL_NEG_LMUL] >>
        ‘2 * x + -4 * x = -2 * x’ suffices_by metis_tac[REAL_ADD_ASSOC] >>
        simp[GSYM REAL_ADD_RDISTRIB]) >>
    ‘x < estp²’ by (simp[Once (GSYM REAL_SUB_LT),Abbr ‘estpc’,REAL_POS_NZ] >>
        CCONTR_TAC >> gvs[] >> ‘0 < tol²’ by simp[REAL_POS_NZ] >>
        dxrule_all REAL_LTE_TRANS >> simp[]) >>
    simp[] >> (*disj2_asm_tac*) Cases_on ‘est² ≤ x’ >> simp[] (*end*) >> gs[REAL_NOT_LE] >>
    simp[rational_sqrt_wfrel_def,REAL_LT_IMP_NE] >> irule NUM_CEILING_STEP >>
    qmatch_abbrev_tac ‘_ ∧ logr _ nest + 1r ≤ logr _ oest’ >>
    ‘∀lx ly lxy lz c:real. lxy = lx + ly ∧ ly = c ∧ lxy ≤ lz ⇒ lx + c ≤ lz’ by simp[] >>
    pop_assum $ irule_at Any >> map_every (irule_at Any) [LOGR_POS_LT,logr_b,logr_mul,LOGR_MONO_LE_IMP] >>
    csimp[] >> simp[Abbr ‘oest’,Abbr ‘nest’] >>
    ‘0 < tol²’ by simp[REAL_POS_NZ] >> simp[REAL_LT_RDIV_EQ,REAL_LE_RDIV_EQ,REAL_POS_NZ] >>
    ‘0 ≤ est² − x’ by simp[REAL_SUB_LE,REAL_LE_LT] >> dxrule_then SUBST_ALL_TAC $ iffRL ABS_REFL >>
    simp[Abbr ‘estpc’,REAL_LT_IMP_NE] >>
    ‘∀a b c:real. a * a ≤ a * b ∧ a * b = c ⇒ a² ≤ c’ by simp[] >> pop_assum irule >>
    irule_at Any REAL_LE_LMUL_IMP >> qexists_tac ‘est’ >>
    simp[REAL_SUB_LDISTRIB,REAL_POS_NZ,REAL_SUB_LE,REAL_LE_SUB_RADD,REAL_LT_IMP_LE]
End

Definition rational_sqrt_def:
    rational_sqrt tol x = rational_sqrt_helper tol x x
End

Theorem rational_sqrt_pos_le:
    ∀x tol. 0 ≤ rational_sqrt tol x
Proof
    simp[rational_sqrt_def] >>
    ‘∀tol x est. (λtol x est. 0 ≤ rational_sqrt_helper tol x est) tol x est’ suffices_by simp[] >>
    irule rational_sqrt_helper_ind >> rw[] >> simp[Once rational_sqrt_helper_def] >>
    rw[] >> gs[REAL_NOT_LE,REAL_LT_IMP_LE]
QED

Theorem rational_sqrt_0:
    ∀tol. rational_sqrt tol 0 = 0
Proof
    rw[rational_sqrt_def,Once rational_sqrt_helper_def]
QED

Theorem rational_sqrt_pos_lt:
    ∀x tol. 0 < tol ∧ 0 < x ⇒ 0 < rational_sqrt tol x
Proof
    simp[rational_sqrt_def] >>
    ‘∀tol x est. (λtol x est. 0 < tol ∧ 0 < x ∧ 0 < est ⇒ 0 < rational_sqrt_helper tol x est) tol x est’
        suffices_by simp[] >>
    irule rational_sqrt_helper_ind >> rw[] >> simp[Once rational_sqrt_helper_def] >>
    simp[iffRL REAL_NOT_LE] >> rw[] >> gs[REAL_NOT_LE] >>
    last_x_assum irule >> irule REAL_LT_ADD >> simp[REAL_POS_NZ]
QED

Theorem rational_sqrt_post_condition:
    ∀tol x. 0 < tol ∧ 0 ≤ x ⇒ abs ((rational_sqrt tol x)² - x) ≤ tol²
Proof
    rw[] >> reverse $ gs[REAL_LE_LT] >- simp[rational_sqrt_0,REAL_POS_NZ] >> simp[GSYM REAL_LE_LT] >>
    rpt $ pop_assum mp_tac >> simp[rational_sqrt_def] >>
    ‘∀tol x est. (λtol x est. 0 < tol ∧ 0 < x ∧ 0 < est ⇒
      abs ((rational_sqrt_helper tol x est)² - x) ≤ tol²) tol x est’
        suffices_by simp[] >>
    irule rational_sqrt_helper_ind >> rw[] >> simp[Once rational_sqrt_helper_def] >>
    gs[iffRL REAL_NOT_LE] >> rw[] >> last_x_assum irule >> simp[] >>
    irule REAL_LT_ADD >> simp[REAL_POS_NZ]
QED

Theorem rational_sqrt_accuracy:
    ∀tol x. 0 < tol ∧ 0 ≤ x ⇒ abs (sqrt x - rational_sqrt tol x) < tol
Proof
    rw[] >> reverse $ gs[REAL_LE_LT] >- simp[SQRT_0,rational_sqrt_0] >>
    qabbrev_tac ‘est = rational_sqrt tol x’ >>
    ‘0 < est ∧ abs (est² - x) ≤ tol²’ by (simp[Abbr ‘est’,rational_sqrt_pos_lt] >>
        irule rational_sqrt_post_condition >> simp[REAL_LE_LT]) >>
    qpat_x_assum ‘Abbrev _’ kall_tac >>
    ‘0 < sqrt x’ by simp[SQRT_POS_LT] >> qabbrev_tac ‘rtx = sqrt x’ >>
    ‘x = rtx²’ by simp[Abbr ‘rtx’,SQRT_POW2,REAL_LE_LT] >> pop_assum SUBST_ALL_TAC >>
    pop_assum kall_tac >> qpat_x_assum ‘0 < rtx²’ kall_tac >>
    irule $ iffLR REAL_POW_2_MONO_LT >> simp[REAL_LT_IMP_LE] >>
    wlog_tac ‘rtx ≤ est’ [‘rtx’,‘est’,‘tol’]
    >- (first_x_assum $ qspecl_then [‘est’,‘rtx’,‘tol’] mp_tac >>
        gs[REAL_NOT_LE,REAL_LT_IMP_LE,SUB_POW_2]) >>
    pop_assum mp_tac >> rw[REAL_LE_LT] >> simp[REAL_LT_IMP_NE] >>
    ‘abs (est² − rtx²) = (est² − rtx²)’ by (simp[ABS_REFL,REAL_SUB_LE] >>
        irule $ iffRL REAL_POW_2_MONO_LE >> simp[REAL_LT_IMP_LE]) >>
    pop_assum SUBST_ALL_TAC >> irule REAL_LTE_TRANS >>
    qpat_x_assum ‘_ ≤ _’ $ irule_at Any >> simp[SUB_POW_2] >>
    simp[REAL_LT_SUB_LADD] >>
    ‘rtx² + est² − 2 * (est * rtx) + rtx² = (est² + (rtx² + rtx²)) - 2 * (est * rtx)’ by (
        simp[real_sub] >> metis_tac[REAL_ADD_COMM,REAL_ADD_ASSOC]) >>
    pop_assum SUBST1_TAC >> simp[REAL_LT_SUB_RADD,REAL_DOUBLE]
QED

(* Measurability *)

Theorem borel_measurable_rational_sqrt_helper:
    (λ(tol,x,est). rational_sqrt_helper tol x est) ∈ borel_measurable (borel × borel × borel)
Proof[exclude_frags = REAL_ARITH]
    ‘sigma_algebra borel ∧ sigma_algebra (borel × borel) ∧ sigma_algebra (borel × borel × borel)’ by (
        rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >> simp[sigma_algebra_borel]) >>
    ‘space borel = UNIV ∧ space (borel × borel) = UNIV ∧ space (borel × borel × borel) = UNIV’ by (
        simp[SPACE_PROD_SIGMA,space_borel,CROSS_UNIV]) >>
    map_every qabbrev_tac [‘P = λ(tol,x,est). ¬(tol ≤ 0r ∨ x ≤ 0r ∨ est ≤ 0r ∨ abs (est² − x) ≤ tol²)’,
        ‘f = λ(tol:real,x,est). (tol,x,(est + x / est) / 2r)’,
        ‘g = λ(tol,x,est). if tol ≤ 0r ∨ x ≤ 0r ∨ est ≤ 0r then 0 else est’] >>
    qspecl_then [‘P’,‘f’] concl_tac $ iffRL WF_IFF_IND
    >- (qx_gen_tac ‘Q’ >> simp[FORALL_PROD] >> strip_tac >> qx_genl_tac [‘tol’,‘x’,‘est’] >>
        qspec_then ‘λtol x est. Q (tol,x,est)’ (irule o SRULE []) rational_sqrt_helper_ind >>
        pop_assum mp_tac >> UNABBREV_ALL_TAC >> simp[]) >>
    gs[] >> irule IN_MEASURABLE_TAILREC_ALT >> simp[] >>
    qexistsl [‘P’,‘R’,‘f’,‘g’] >> simp[] >> conj_tac
    >- (qspecl_then [‘P’,‘f’,‘R’] mp_tac WHILE_INDUCTION >> simp[] >>
        disch_then $ qspec_then ‘λx. foo x = bar x’ $ irule o SRULE [] >>
        simp[FORALL_PROD] >> qx_genl_tac [‘tol’,‘x’,‘est’] >> rw[] >>
        simp[Once TAILREC_TAILCALL,TAILCALL_def] >> reverse $ Cases_on ‘P (tol,x,est)’ >> gs[]
        >- (simp[Once rational_sqrt_helper_def,Abbr ‘P’,Abbr ‘g’] >> gs[]) >>
        qpat_x_assum ‘_ = _’ $ SUBST1_TAC o SYM >>
        simp[Once rational_sqrt_helper_def,Abbr ‘P’,Abbr ‘f’] >> gs[]) >>
    gs[REAL_NOT_LE] >> UNABBREV_ALL_TAC >> ntac 2 $ pop_assum kall_tac >>
    chain_irule_at [
        (Pos $ el 2,IN_MEASURABLE_IF,[‘λ(tol,x,est). est’,‘λ(tol,x,est). 0’,
            ‘{(tol,x,est) | tol ≤ 0 ∨ x ≤ 0 ∨ est ≤ 0}’],[FORALL_PROD,EXISTS_PROD]),
        (Pos $ el 4,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λ(tol,x,est). (x,(est + x / est) / 2)’,‘λ(tol,x,est). tol’],
            [FORALL_PROD]),
        (Pos $ el 2,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘λ(tol,x,est). (est + x / est) / 2’,‘λ(tol,x,est). x’],
            [FORALL_PROD]),
        (Pos $ el 2,in_borel_measurable_div,[‘λ(tol,x,est). 2’,‘λ(tol,x,est). (est + x / est)’],
            [FORALL_PROD]),
        (Pos hd,in_borel_measurable_add,[‘λ(tol,x,est). x / est’,‘λ(tol,x,est). est’],
            [FORALL_PROD,SF CONJ_ss]),
        (Pos hd,in_borel_measurable_div,[‘λ(tol,x,est). est’,‘λ(tol,x,est). x’],
            [FORALL_PROD,SF CONJ_ss]),
        (Pos hd,in_borel_measurable_const,[‘2’],[FORALL_PROD]),
        (Pos $ el 4,in_borel_measurable_const,[‘0’],[FORALL_PROD])] >>
    simp[borel_measurable_const] >>
    ‘(λ(tol,x,est). 0r < tol ∧ 0r < x ∧ 0r < est ∧ tol² < abs (est² − x)) =
      {txe | (λ(tol,x,est). tol²) txe < (λ(tol,x,est). abs (est² − x)) txe} DIFF
      {(tol,x,est) | tol ≤ 0 ∨ x ≤ 0 ∨ est ≤ 0}’ by (
        simp[EXTENSION,FORALL_PROD,REAL_NOT_LE] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >> irule_at Any SIGMA_ALGEBRA_DIFF >> simp[] >>
    ‘{(tol,x,est) | tol ≤ 0r ∨ x ≤ 0r ∨ est ≤ 0r} = {txe | (λ(tol,x,est). tol) txe ≤ 0} ∪
      {txe | (λ(tol,x,est). x) txe ≤ 0} ∪ {txe | (λ(tol,x,est). est) txe ≤ 0}’ by (
        simp[EXTENSION,FORALL_PROD,DISJ_ASSOC]) >>
    pop_assum SUBST1_TAC >> rpt $ irule_at Any SIGMA_ALGEBRA_UNION >> simp[] >>
    qabbrev_tac ‘bbb = borel × borel × borel’ >>
    qspec_then ‘bbb’ mp_tac in_borel_measurable_le_imp >> simp[] >>
    disch_then (fn th => ntac 3 $ irule_at Any th) >>
    qspec_then ‘bbb’ mp_tac in_borel_measurable_lt2_imp >>
    simp[Abbr ‘bbb’] >> disch_then $ irule_at Any >>
    chain_irule_at [
        (Pos hd,in_borel_measurable_pow2,[‘λ(tol,x,est). tol’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,in_borel_measurable_abs,[‘λ(tol,x,est). est² − x’],[FORALL_PROD]),
        (Pos hd,in_borel_measurable_sub,[‘λ(tol,x,est). x’,‘λ(tol,x,est). est²’],[FORALL_PROD,SF CONJ_ss]),
        (Pos hd,in_borel_measurable_pow2,[‘λ(tol,x,est). est’],[FORALL_PROD,SF CONJ_ss]),
        (Pos $ el 2,IN_MEASURABLE_EQ,[‘FST’],[FORALL_PROD]),
        (Pos $ el 2,INST_TYPE [“:β”|->“:real # real”] IN_MEASURABLE_COMP,
            [‘FST’,‘SND’,‘borel × borel’],[FORALL_PROD]),
        (Pos $ el 4,INST_TYPE [“:β”|->“:real # real”] IN_MEASURABLE_COMP,
            [‘SND’,‘SND’,‘borel × borel’],[FORALL_PROD,SF CONJ_ss]),
        (Any,MEASURABLE_FST,[],[]), (Any,MEASURABLE_FST,[],[]),
        (Any,MEASURABLE_SND,[],[]), (Any,MEASURABLE_SND,[],[])]
QED

Theorem borel_measurable_rational_sqrt:
    (λ(tol,x). rational_sqrt tol x) ∈ borel_measurable (borel × borel)
Proof
    ‘sigma_algebra borel ∧ sigma_algebra (borel × borel) ∧ sigma_algebra (borel × borel × borel)’ by (
        rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >> simp[sigma_algebra_borel]) >>
    ‘space borel = UNIV ∧ space (borel × borel) = UNIV ∧ space (borel × borel × borel) = UNIV’ by (
        simp[SPACE_PROD_SIGMA,space_borel,CROSS_UNIV]) >>
    chain_irule_at [
        (Any,INST_TYPE [“:β”|->“:real # real # real”] IN_MEASURABLE_COMP,
            [‘borel × borel × borel’,‘λ(tol,x). (tol,x,x)’,‘λ(tol,x,est). rational_sqrt_helper tol x est’],
            [FORALL_PROD,rational_sqrt_def,borel_measurable_rational_sqrt_helper]),
        (Any,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘FST’,‘λ(tol,x). (x,x)’],[FORALL_PROD]),
        (Any,IN_MEASURABLE_PROD_SIGMA_WEAK,[‘SND’,‘SND’],[FORALL_PROD,SF CONJ_ss]),
        (Any,MEASURABLE_FST,[],[]), (Any,MEASURABLE_SND,[],[])]
QED

Theorem borel_measurable_rational_sqrt_tol:
    ∀tol. rational_sqrt tol ∈ borel_measurable borel
Proof
    rw[] >> assume_tac borel_measurable_rational_sqrt >>
    dxrule_at Any IN_MEASURABLE_FROM_PROD_SIGMA >>
    simp[sigma_algebra_borel,space_borel,SF ETA_ss]
QED

val _ = export_theory();
