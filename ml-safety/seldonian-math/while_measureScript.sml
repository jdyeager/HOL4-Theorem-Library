open HolKernel Parse boolLib bossLib;
open simpLib;
open combinTheory;
open relationTheory;
open pairTheory;
open pred_setTheory;
open listTheory;
open arithmeticTheory;
open WhileTheory;
open realTheory;
open realLib;
open real_sigmaTheory;
open transcTheory;
open extrealTheory;
open sigma_algebraTheory;
(*
open borelTheory;
open measureTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;
*)

open ex_machina;
open trivialTheory;
open trivialSimps;

val _ = new_theory "while_measure";

(*
val _ = reveal "C";
*)

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss,TRIVIAL_ss];

Theorem WF_IFF_IND:
    ∀B C. (∃R. WF R ∧ (∀v. B v ⇒ R (C v) v)) ⇔
        ∀P. (∀v. (B v ⇒ P (C v)) ⇒ P v) ⇒ ∀v. P v
Proof
    rw[EQ_IMP_THM] >- metis_tac[WHILE_INDUCTION] >>
    map_every qabbrev_tac [‘TRM = λv n. ¬B (FUNPOW C n v)’,‘f = λv. $LEAST (TRM v)’] >>
    last_assum $ qspec_then ‘λv. ∃n. TRM v n’ mp_tac >> simp[] >> disch_then concl_tac
    >- (strip_tac >> reverse $ Cases_on ‘B v’ >> simp[]
        >- (qexists ‘0’ >> simp[Abbr ‘TRM’]) >>
        rw[] >> qexists ‘SUC n’ >> gs[Abbr ‘TRM’,FUNPOW]) >>
    qexists ‘inv_image $< f’ >> simp[WF_inv_image] >>
    rw[] >> first_assum $ qspec_then ‘v’ mp_tac >> first_x_assum $ qspec_then ‘C v’ mp_tac >>
    ntac 2 (strip_tac >> dxrule_then assume_tac $ SRULE [PULL_EXISTS] LEAST_EXISTS_IMP) >>
    rw[] >> simp[Abbr ‘f’] >> spose_not_then assume_tac >>
    gs[NOT_LESS,LESS_EQ_IFF_LESS_SUC] >>
    ‘∃n. $LEAST (TRM v) = SUC n’ by (Cases_on ‘$LEAST (TRM v)’ >> gs[Abbr ‘TRM’,FUNPOW]) >>
    gs[] >> first_x_assum $ dxrule_then mp_tac >> gs[Abbr ‘TRM’,FUNPOW]
QED

(*
Definition LOOPN_DEF:
    LOOPN 0 g x = x ∧
    LOOPN (SUC n) g x = LOOPN n g (g x)
End

Theorem LOOPN_0:
    LOOPN 0 = K I
Proof
    rw[FUN_EQ_THM,LOOPN_DEF]
QED

Theorem LOOPN_1:
    LOOPN 1 = I
Proof
    rw[FUN_EQ_THM,EVAL “LOOPN 1 g x”]
QED

Theorem LOOPN_SUC:
    ∀n g. LOOPN (SUC n) g = LOOPN n g ∘ g
Proof
    rw[FUN_EQ_THM,LOOPN_DEF]
QED
*)

Theorem IN_MEASURABLE_CONST_STRONG:
    ∀a b k f. space a ∈ subsets a ∧ ∅ ∈ subsets a ∧ k ∈ space b ∧
        (∀x. x ∈ space a ⇒ f x = k) ⇒ f ∈ measurable a b
Proof
    rw[IN_MEASURABLE,FUNSET] >> Cases_on ‘k ∈ s’
    >- (‘PREIMAGE f s ∩ space a = space a’ suffices_by simp[] >>
        rw[EXTENSION] >> Cases_on ‘x ∈ space a’ >> simp[])
    >- (‘PREIMAGE f s ∩ space a = ∅’ suffices_by simp[] >>
        rw[EXTENSION] >> Cases_on ‘x ∈ space a’ >> simp[])
QED

Theorem IN_MEASURABLE_FUNPOW:
    ∀a n g f. sigma_algebra a ∧ g ∈ measurable a a ∧ (∀x. x ∈ space a ⇒ f x = FUNPOW g n x) ⇒
        f ∈ measurable a a
Proof
    Induct_on ‘n’ >> rw[FUNPOW]
    >- (irule IN_MEASURABLE_EQ >> qexists ‘I’ >> simp[MEASURABLE_I]) >>
    irule $ INST_TYPE [“:β” |-> “:α”] IN_MEASURABLE_COMP >>
    qexistsl [‘a’,‘g’,‘FUNPOW g n’] >> simp[] >> last_x_assum irule >>
    simp[] >> qexists ‘g’ >> simp[]
QED

Theorem MEASURABLE_FUNPOW:
    ∀a n g. sigma_algebra a ∧ g ∈ measurable a a ⇒ FUNPOW g n ∈ measurable a a
Proof
    rw[] >> irule IN_MEASURABLE_FUNPOW >> simp[] >> qexistsl [‘g’,‘n’] >> simp[]
QED

Theorem IN_MEASURABLE_WHILE:
    ∀a P g f. sigma_algebra a ∧ P ∩ space a ∈ subsets a ∧
        (∀x. x ∈ space a ⇒ ∃n. ¬P (FUNPOW g n x)) ∧ g ∈ measurable a a ∧
        (∀x. x ∈ space a ⇒ f x = WHILE P g x) ⇒ f ∈ measurable a a
Proof
    rw[] >>
    ‘space a DIFF P ∈ subsets a’ by (
        simp[Once $ GSYM DIFF_INTER2] >> irule SIGMA_ALGEBRA_DIFF >>
        simp[SIGMA_ALGEBRA_SPACE]) >>
    ‘∃N. ∀x. x ∈ space a ⇒ ¬P (FUNPOW g (N x) x) ∧ ∀n. n < N x ⇒ P (FUNPOW g n x)’ by (
        simp[GSYM SKOLEM_THM] >> rw[RIGHT_EXISTS_IMP_THM] >>
        qexists ‘$LEAST (λn. ¬P (FUNPOW g n x))’ >>
        qspec_then ‘(λn. ¬P (FUNPOW g n x))’ mp_tac LEAST_EXISTS_IMP >> simp[]) >>
    ‘∀x. x ∈ space a ⇒ f x = FUNPOW g (N x) x’ by (
        gen_tac >> Induct_on ‘N x’
        >- (rw[] >> first_x_assum $ drule >> simp[FUNPOW,Once WHILE]) >>
        rw[] >> first_x_assum $ qspecl_then [‘N’,‘g x’] mp_tac >> simp[] >>
        ‘N x = SUC (N (g x))’ suffices_by (disch_tac >> gvs[IN_MEASURABLE,FUNSET] >>
            disch_tac >> simp[FUNPOW,Once WHILE] >> ‘P x’ suffices_by simp[] >>
            first_x_assum $ drule_then $ qspec_then ‘0’ mp_tac o cj 2 >> simp[FUNPOW]) >>
        ‘g x ∈ space a’ by gs[IN_MEASURABLE,FUNSET] >>
        first_assum $ dxrule >> first_x_assum $ dxrule >>
        rename [‘SUC n = N x’] >> pop_assum $ SUBST1_TAC o SYM >> rw[] >>
        first_x_assum $ qspec_then ‘n’ assume_tac >>
        first_x_assum $ qspec_then ‘SUC (N (g x))’ assume_tac >> gs[FUNPOW]) >>
    qpat_x_assum ‘∀x. _ ⇒ ∃n. _’ kall_tac >> qpat_x_assum ‘∀x. _ ⇒ _ = WHILE _ _ _’ kall_tac >>
    drule_all_then assume_tac MEASURABLE_FUNPOW >> simp[IN_MEASURABLE] >> conj_tac
    >- gs[IN_MEASURABLE,FUNSET] >> rw[] >>
    map_every qabbrev_tac [‘noP = space a DIFF P’,
        ‘pgn = λt n. PREIMAGE (FUNPOW g n) t ∩ space a’, ‘sNn = λn. {x | N x = n} ∩ space a’] >>
    ‘∀t n. t ∈ subsets a ⇒ pgn t n ∈ subsets a’ by (
        rw[Abbr ‘pgn’] >> irule $ cj 2 $ iffLR IN_MEASURABLE >>
        first_x_assum $ irule_at Any >> simp[]) >>
    ‘∀n. sNn n ∈ subsets a’ by (rw[Abbr ‘sNn’] >>
        ‘{x | N x = n} ∩ space a = pgn noP n DIFF BIGUNION (IMAGE (pgn noP) (count n))’ suffices_by (
            disch_then SUBST1_TAC >> irule SIGMA_ALGEBRA_DIFF >> simp[] >>
            irule SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[SUBSET_DEF,PULL_EXISTS]) >>
        rw[Once EXTENSION,Abbr ‘pgn’,PULL_EXISTS] >>
        ‘∀bl br. bl ∨ ¬br ⇔ br ⇒ bl’ by metis_tac[] >> simp[] >> pop_assum kall_tac >>
        Cases_on ‘x ∈ space a’ >> simp[] >>
        ‘∀n. FUNPOW g n x ∈ space a’ by (gs[IN_MEASURABLE,FUNSET]) >>
        simp[Abbr ‘noP’,IN_APP] >> Cases_on ‘N x = n’ >> simp[] >- gvs[] >>
        last_x_assum $ drule_then assume_tac >>
        ‘N x < n ∨ n < N x’ by simp[] >> simp[SF SFY_ss]) >>
    ‘PREIMAGE f s ∩ space a = BIGUNION (IMAGE (λn. sNn n ∩ pgn s n) 𝕌(:num))’ suffices_by (
        disch_then SUBST1_TAC >> irule SIGMA_ALGEBRA_COUNTABLE_UNION >>
        rw[SUBSET_DEF,PULL_EXISTS] >> irule SIGMA_ALGEBRA_INTER >> simp[]) >>
    rw[Once EXTENSION,PULL_EXISTS,Abbr ‘sNn’,Abbr ‘pgn’] >>
    Cases_on ‘x ∈ space a’ >> simp[]
QED

Theorem MEASURABLE_WHILE:
    ∀a P g. sigma_algebra a ∧ P ∩ space a ∈ subsets a ∧
        (∀x. x ∈ space a ⇒ ∃n. ¬P (FUNPOW g n x)) ∧ g ∈ measurable a a ⇒
        WHILE P g ∈ measurable a a
Proof
    rw[] >> irule IN_MEASURABLE_WHILE >> simp[] >> qexistsl [‘P’,‘g’] >> simp[]
QED

Theorem IN_MEASURABLE_IF:
    ∀a b P f g h. sigma_algebra a ∧ sigma_algebra b ∧ P ∩ space a ∈ subsets a ∧
        f ∈ measurable a b ∧ g ∈ measurable a b ∧
        (∀x. x ∈ space a ⇒ h x = if P x then f x else g x) ⇒ h ∈ measurable a b
Proof
    rw[] >>
    ‘space a DIFF P ∈ subsets a’ by (
        simp[Once $ GSYM DIFF_INTER2] >> irule SIGMA_ALGEBRA_DIFF >>
        simp[SIGMA_ALGEBRA_SPACE]) >>
    gs[IN_MEASURABLE,FUNSET] >> rw[] >>
    ‘PREIMAGE h s ∩ space a = ((PREIMAGE f s ∩ space a) ∩ (P ∩ space a)) ∪
      ((PREIMAGE g s ∩ space a) ∩ (space a DIFF P))’ suffices_by (disch_then SUBST1_TAC >>
        irule SIGMA_ALGEBRA_UNION >> ntac 2 (irule_at Any SIGMA_ALGEBRA_INTER >> simp[])) >>
    rw[EXTENSION,PULL_EXISTS] >> Cases_on ‘x ∈ space a’ >> simp[] >>
    Cases_on ‘P x’ >> simp[IN_APP]
QED

Theorem MEASURABLE_IF:
    ∀a b P f g. sigma_algebra a ∧ sigma_algebra b ∧ P ∩ space a ∈ subsets a ∧
        f ∈ measurable a b ∧ g ∈ measurable a b ⇒
        (λx. if P x then f x else g x) ∈ measurable a b
Proof
    rw[] >> irule IN_MEASURABLE_IF >> simp[] >> qexistsl [‘P’,‘f’,‘g’] >> simp[]
QED

Theorem TAILREC_INDUCTION:
    ∀R f. WF R ∧ (∀x. ISL (f x) ⇒ R (OUTL (f x)) x) ⇒
        ∀P. (∀x. (ISL (f x) ⇒ P (OUTL (f x))) ⇒ P x) ⇒ ∀x. P x
Proof
    rw[] >> irule WF_INDUCTION_THM >>
    qexists ‘λy x. y = OUTL (f x) ∧ R y x’ >> irule_at Any WF_SUBSET >>
    first_assum $ irule_at Any >> simp[]
QED

Theorem TAILREC_EQ_WHILE:
    ∀R f. WF R ∧ (∀x. ISL (f x) ⇒ R (OUTL (f x)) x) ⇒
        TAILREC f = OUTR ∘ f ∘ WHILE (ISL ∘ f) (OUTL ∘ f)
Proof
    rw[FUN_EQ_THM] >>
    drule_then (drule_then (
        qspec_then ‘λx. TAILREC f x = OUTR (f (WHILE (ISL ∘ f) (OUTL ∘ f) x))’ (irule o SRULE [])))
        TAILREC_INDUCTION >>
    rw[] >> simp[Once TAILREC] >> reverse $ Cases_on ‘f x’ >> simp[Once WHILE] >> gs[]
QED

Theorem WHILE_EQ_TAILREC:
    ∀R P f. WF R ∧ (∀x. P x ⇒ R (f x) x) ⇒
        WHILE P f = TAILREC (λx. if P x then INL (f x) else INR x)
Proof
    rw[FUN_EQ_THM] >>
    drule_then (drule_then (
        qspec_then ‘λx. WHILE P f x = TAILREC (λx. if P x then INL (f x) else INR x) x’ (irule o SRULE [])))
        WHILE_INDUCTION >>
    rw[] >> simp[Once TAILREC] >> reverse $ Cases_on ‘P s’ >> simp[Once WHILE]
QED

Theorem IN_MEASURABLE_TAILREC:
    ∀a b R f g. sigma_algebra a ∧ sigma_algebra b ∧ WF R ∧ (∀x. ISL (f x) ⇒ R (OUTL (f x)) x) ∧
        (ISL ∘ f) ∩ space a ∈ subsets a ∧ (OUTL ∘ f) ∈ measurable a a ∧ (OUTR ∘ f) ∈ measurable a b ∧
        (∀x. x ∈ space a ⇒ g x = TAILREC f x) ⇒ g ∈ measurable a b
Proof
    rw[] >> irule $ INST_TYPE [“:β”|->“:α”] IN_MEASURABLE_COMP >> simp[] >>
    qexistsl [‘a’,‘WHILE (ISL ∘ f) (OUTL ∘ f)’,‘OUTR ∘ f’] >>
    simp[] >> conj_tac >- metis_tac[SRULE [FUN_EQ_THM] TAILREC_EQ_WHILE] >>
    irule MEASURABLE_WHILE >> simp[] >> qpat_x_assum ‘WF R’ mp_tac >>
    CONV_TAC CONTRAPOS_CONV >> simp[WF_DEF,GSYM IMP_DISJ_THM] >> rw[] >>
    qexists ‘IMAGE (λn. FUNPOW (OUTL ∘ f) n x) 𝕌(:num)’ >> rw[PULL_EXISTS] >>
    qexists ‘SUC n’ >> simp[FUNPOW_SUC]
QED

Theorem MEASURABLE_TAILREC:
    ∀a b R f. sigma_algebra a ∧ sigma_algebra b ∧ WF R ∧ (∀x. ISL (f x) ⇒ R (OUTL (f x)) x) ∧
        (ISL ∘ f) ∩ space a ∈ subsets a ∧ (OUTL ∘ f) ∈ measurable a a ∧ (OUTR ∘ f) ∈ measurable a b ⇒
        TAILREC f ∈ measurable a b
Proof
    rw[] >> irule IN_MEASURABLE_TAILREC >> simp[] >> qexistsl [‘R’,‘f’] >> simp[]
QED

Theorem IN_MEASURABLE_TAILREC_ALT:
    ∀a b R P f g h. sigma_algebra a ∧ sigma_algebra b ∧ WF R ∧ (∀x. P x ⇒ R (f x) x) ∧
        P ∩ space a ∈ subsets a ∧ f ∈ measurable a a ∧ g ∈ measurable a b ∧
        (∀x. x ∈ space a ⇒ h x = TAILREC (λx. if P x then INL (f x) else INR (g x)) x) ⇒ h ∈ measurable a b
Proof
    rw[] >> qmatch_asmsub_abbrev_tac ‘TAILREC Pfg’ >>
    qabbrev_tac ‘PfI = λx. if P x then INL (f x) else INR x’ >>
    ‘TAILREC Pfg = g ∘ TAILREC PfI’ by (rw[FUN_EQ_THM] >> drule TAILREC_INDUCTION >>
        disch_then $ qspecl_then [‘Pfg’,‘λx. TAILREC Pfg x = g (TAILREC PfI x)’,‘x’] mp_tac >>
        simp[] >> disch_then irule >> ‘∀x. ISL (Pfg x) = P x’ by rw[Abbr ‘Pfg’] >>
        simp[] >> rw[Abbr ‘Pfg’,Abbr ‘PfI’] >> ntac 2 (simp[Once TAILREC] >> irule EQ_SYM) >>
        Cases_on ‘P x’ >> gs[]) >>
    irule $ INST_TYPE [“:β”|->“:α”] IN_MEASURABLE_COMP >> qexistsl [‘a’,‘TAILREC PfI’,‘g’] >>
    simp[] >> irule IN_MEASURABLE_WHILE >> simp[] >> qexistsl [‘P’,‘f’] >>
    drule_all WHILE_EQ_TAILREC >> simp[] >> disch_then kall_tac >> qpat_x_assum ‘WF R’ mp_tac >>
    CONV_TAC CONTRAPOS_CONV >> simp[WF_DEF,GSYM IMP_DISJ_THM] >> rw[] >>
    qexists ‘IMAGE (λn. FUNPOW f n x) 𝕌(:num)’ >> rw[PULL_EXISTS] >>
    qexists ‘SUC n’ >> simp[FUNPOW_SUC]
QED

val _ = export_theory();
