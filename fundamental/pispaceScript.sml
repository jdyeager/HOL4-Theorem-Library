open HolKernel Parse boolLib bossLib;
open ex_machina;
open simpLib;
open markerTheory;
open combinTheory;
open pairTheory;
open pred_setTheory;
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
open trivialTheory;
open trivialSimps;

val _ = new_theory "pispace";

val _ = reveal "C";

val _ = augment_srw_ss [TRIVIAL_ss];

val name_to_thname = fn s => ({Thy = "pispace", Name = s}, DB.fetch "pispace" s);

val _ = augment_srw_ss
  [rewrites_with_names
    [({Thy = "measure", Name = "sigma_finite_measure_space_measure_space"},
    DB.fetch "measure" "sigma_finite_measure_space_measure_space")]]

(*
val _ = reveal "C";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];
*)

(*
val pi_pair_def = Define `pi_pair (n:num) f e = (λi. if (i = n) then e else f i)`;

val pi_cross_def = Define `pi_cross (n:num) fs s = {pi_pair n f e | f ∈ fs ∧ e ∈ s}`;

val pi_prod_sets_def = Define `pi_prod_sets n fsts sts = {pi_cross n fs s | fs ∈ fsts ∧ s ∈ sts}`;

val pi_m_space_def = Define `(pi_m_space 0 mss = {(λi. ARB)}) ∧
    (pi_m_space (SUC n) mss = pi_cross n (pi_m_space n mss) (m_space (mss n)))`;

val pi_measurable_sets_def = Define `(pi_measurable_sets 0 mss = POW {(λi. ARB)}) ∧
    (pi_measurable_sets (SUC n) mss = subsets (sigma (pi_m_space (SUC n) mss)
    (pi_prod_sets n (pi_measurable_sets n mss) (measurable_sets (mss n)))))`;

val pi_measure_def = Define `(pi_measure 0 mss = (λfs. if (fs = ∅) then 0 else 1)) ∧
    (pi_measure (SUC n) mss = (λfs. real (integral (mss n)
    (λe. Normal (pi_measure n mss ((PREIMAGE (λf. pi_pair n f e) fs) ∩ (pi_m_space n mss)))))))`;

val pi_measure_space_def = Define `pi_measure_space n mss =
    (pi_m_space n mss, pi_measurable_sets n mss, pi_measure n mss)`;

val pi_id_msp_def = Define `pi_id_msp = ({(λi:num. ARB:α)},POW {(λi:num. ARB:α)},
    (λfs:(num->α)->bool. if fs = ∅ then (0:real) else 1))`;

val measurability_preserving_def = Define `measurability_preserving a b = {f |
    sigma_algebra a ∧ sigma_algebra b ∧ BIJ f (space a) (space b) ∧
    (∀s. s ∈ subsets a ⇒ IMAGE f s ∈ subsets b) ∧
    ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}`;

val measure_preserving_def = Define `measure_preserving m0 m1 = {f |
    f ∈ measurability_preserving (m_space m0,measurable_sets m0) (m_space m1,measurable_sets m1) ∧
    ∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))}`;

val isomorphic_def = Define `isomorphic m0 m1 ⇔ ∃f. f ∈ measure_preserving m0 m1`;
*)

Definition pi_pair_def:
    pi_pair 0 f e = (λi. ARB) ∧
    pi_pair (SUC n) f e = f(| n |-> e|)
End

Definition pi_cross_def:
    pi_cross (n:num) fs s = {pi_pair n f e | f ∈ fs ∧ e ∈ s}
End

Theorem in_pi_cross:
    ∀n fs s gs. gs ∈ pi_cross n fs s ⇔ ∃f e. gs = pi_pair n f e ∧ f ∈ fs ∧ e ∈ s
Proof
    rw[pi_cross_def]
QED

Definition pi_rect_def:
    pi_rect (n:num) si = {f | ∀i:num. if i < n then f i ∈ si i else f i = ARB}
End

Theorem in_pi_rect:
    ∀n si f. f ∈ pi_rect n si ⇔ (∀i. i < n ⇒ f i ∈ si i) ∧ (∀i. n ≤ i ⇒ f i = ARB)
Proof
    rw[pi_rect_def] >> eq_tac >> rw[] >> first_x_assum $ qspec_then ‘i’ mp_tac >> simp[]
QED

(*
(* not true if say si 0 and ti 0 both ∅, and si,ti differ elsewhere *)
Theorem pi_rect_eq:
    ∀n si ti. pi_rect n si = pi_rect n ti ⇔ ∀i. i < n ⇒ si i = ti i
Proof
    reverse $ rw[EQ_IMP_THM] >- simp[EXTENSION,in_pi_rect] >>
    
QED
*)

(* could generalise to f ∈ pi_rect fn fr ∧ g ∈ pi_rect gn gr, where fn,gn ≤ n *)
Theorem in_rect_pi_pair_eq:
    ∀n si f g x y. f ∈ pi_rect n si ∧ g ∈ pi_rect n si ⇒
        (pi_pair (SUC n) f x = pi_pair (SUC n) g y ⇔ f = g ∧ x = y)
Proof
    rw[pi_pair_def] >> eq_tac >> simp[] >> simp[FUN_EQ_THM] >> strip_tac >> reverse conj_tac
    >- (first_x_assum $ qspec_then ‘n’ mp_tac >> simp[UPDATE_APPLY]) >>
    qx_gen_tac ‘i’ >> first_x_assum $ qspec_then ‘i’ mp_tac >> Cases_on ‘i = n’ >>
    simp[UPDATE_APPLY] >> DISCH_THEN kall_tac >> fs[in_pi_rect]
QED

Theorem pi_rect_recur:
    (∀si. pi_rect 0 si = {K (ARB: α)}) ∧
    ∀n (si: num -> α -> bool). pi_rect (SUC n) si = pi_cross (SUC n) (pi_rect n si) (si n)
Proof
    rw[pi_rect_def,pi_cross_def,pi_pair_def] >> simp[EXTENSION] >- simp[FUN_EQ_THM] >>
    qx_gen_tac ‘f’ >> eq_tac >> rw[]
    >- (qexistsl_tac [‘f⦇n ↦ ARB⦈’,‘f n’] >> simp[UPDATE_EQ,APPLY_UPDATE_ID] >> reverse conj_tac
        >- (first_x_assum $ qspec_then ‘n’ mp_tac >> simp[]) >>
        qx_gen_tac ‘i’ >> first_x_assum $ qspec_then ‘i’ assume_tac >>
        (* test case for DISJ_CASESL_TAC *)
        qspecl_then [‘i’,‘n’] (DISJ_CASES_THENL [assume_tac,assume_tac,assume_tac]) LESS_LESS_CASES >>
        gvs[APPLY_UPDATE_THM])
    >- (rename [‘f⦇n ↦ e⦈’] >> first_x_assum $ qspec_then ‘i’ assume_tac >>
        ‘i < n ∨ i = n ∨ i = SUC n ∨ SUC n < i’ by simp[] >> gvs[APPLY_UPDATE_THM])
QED

(*
Definition pi_m_space_def:
    pi_m_space 0 mn = {(λi. ARB)} ∧
    pi_m_space (SUC n) mn = pi_cross (SUC n) (pi_m_space n mn) (m_space (mn n))
End
*)

Definition pi_prod_sets_def:
    pi_prod_sets n fsts sts = {pi_cross n fs s | fs ∈ fsts ∧ s ∈ sts}
End

Definition pi_rect_sets_def:
    pi_rect_sets n = IMAGE (pi_rect n) ∘ pi_rect n
End

(*
(* not true if say pi_rect n fr = ∅, but the empty set comes from another index in stsi *)
Theorem pi_rect_in_pi_rect_sets:
    ∀n stsi fr. pi_rect n fr ∈ pi_rect_sets n stsi ⇔ ∀i. i < n ⇒ fr i ∈ stsi i
Proof
    reverse $ rw[EQ_IMP_THM,pi_rect_sets_def]
    >- (qexists_tac ‘λi. if i < n then fr i else ARB’ >> simp[pi_rect_def]) >>
    rename [‘gr ∈ pi_rect _ _’] >> gs[EXTENSION] >> simp[]
    last_x_assum $ qspec_then ‘f’ assume_tac >>
    gs[in_pi_rect]
QED
*)

(* RENAME:in_pi_rect_sets_imp *)
Theorem pi_rect_in_pi_rect_sets_imp:
    ∀n stsi fr. (∀i. i < n ⇒ fr i ∈ stsi i) ⇒ pi_rect n fr ∈ pi_rect_sets n stsi
Proof
    rw[pi_rect_sets_def] >> qexists_tac ‘λi. if i < n then fr i else ARB’ >> simp[pi_rect_def]
QED

Theorem pi_rect_update:
    ∀n m fs s. n ≤ m ⇒ pi_rect n fs⦇m ↦ s⦈ = pi_rect n fs
Proof
    simp[EXTENSION,pi_rect_def,UPDATE_APPLY]
QED

Theorem pi_rect_sets_recur:
    (∀stsi. pi_rect_sets 0 stsi = {{K (ARB: α)}}) ∧
    ∀n (stsi: num -> (α -> bool) -> bool).
        pi_rect_sets (SUC n) stsi = pi_prod_sets (SUC n) (pi_rect_sets n stsi) (stsi n)
Proof
    rw[pi_rect_sets_def,pi_prod_sets_def,pi_rect_recur] >>
    simp[Once EXTENSION,PULL_EXISTS,pi_rect_recur] >>
    qx_gen_tac ‘fs’ >> eq_tac >> rw[] >> rename [‘fs ∈ _ _ _’]
    >- (gvs[pi_cross_def,pi_pair_def] >> rename [‘fs ∈ _ _ stsi’,‘s ∈ stsi _’] >> qexistsl_tac [‘s’,‘fs’] >>
        simp[EXTENSION,PULL_EXISTS,UPDATE_APPLY,pi_rect_update])
    >- (qexists_tac ‘fs⦇n ↦ s⦈’ >> simp[UPDATE_APPLY,pi_rect_update] >>
        simp[pi_cross_def,pi_pair_def] >> qexistsl_tac [‘fs’,‘s’] >> simp[])
QED

Definition pi_sigma_def:
    pi_sigma n sai = sigma (pi_rect n (space ∘ sai)) (pi_rect_sets n (subsets ∘ sai))
End

Theorem space_pi_sigma:
    ∀n sai. space (pi_sigma n sai) = pi_rect n (space ∘ sai)
Proof
    simp[pi_sigma_def,SPACE_SIGMA]
QED

Theorem pi_cross_empty:
    ∀n fs s. pi_cross n fs s = ∅ ⇔ fs = ∅ ∨ s = ∅
Proof
    simp[pi_cross_def,EXTENSION,LEFT_FORALL_OR_THM,RIGHT_FORALL_OR_THM]
QED

Theorem pi_rect_empty:
    ∀n si. pi_rect n si = ∅ ⇔ ∃i. i < n ∧ si i = ∅
Proof
    Induct_on ‘n’ >> rw[pi_rect_recur,pi_cross_empty] >>
    pop_assum kall_tac >> eq_tac >> rw[]
    >| [qexists_tac ‘i’,qexists_tac ‘n’,all_tac] >> simp[] >>
    Cases_on ‘i = n’ >> gvs[] >> disj1_tac >> qexists_tac ‘i’ >> simp[]
QED

Theorem pi_rect_empty_imp:
    ∀n i si. i < n ∧ si i = ∅ ⇒ pi_rect n si = ∅
Proof
    metis_tac[pi_rect_empty]
QED

Theorem pi_rect_sets_empty:
    ∀n ssi. pi_rect_sets n ssi = ∅ ⇔ ∃i. i < n ∧ ssi i = ∅
Proof
    simp[pi_rect_sets_def,pi_rect_empty]
QED

Theorem pi_rect_sets_empty_imp:
    ∀n i ssi. i < n ∧ ssi i = ∅ ⇒ pi_rect_sets n ssi = ∅
Proof
    metis_tac[pi_rect_sets_empty]
QED

Theorem pi_rect_sets_sing_empty:
    ∀n i ssi. i < n ∧ ssi i = ∅ ⇒ pi_rect_sets n ssi = ∅
Proof
    metis_tac[pi_rect_sets_empty]
QED

Theorem subset_class_pi_rect_sets:
    ∀n sai. (∃fr. ∀i. i < n ⇒ fr i ∈ subsets (sai i) ∧ fr i ≠ ∅) ⇒
        (subset_class (pi_rect n (space ∘ sai)) (pi_rect_sets n (subsets ∘ sai)) ⇔
        ∀i. i < n ⇒ subset_class (space (sai i)) (subsets (sai i)))
Proof
    rw[subset_class_def,pi_rect_sets_def,pi_rect_def,SUBSET_DEF,PULL_EXISTS] >>
    reverse $ eq_tac >- metis_tac[] >>
    fs[GSYM MEMBER_NOT_EMPTY,GSYM RIGHT_EXISTS_AND_THM,GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
    rw[] >> rename [‘s ∈ subsets (sai i)’,‘e ∈ s’] >>
    first_x_assum $ qspec_then ‘λj. if j < n then fr⦇i ↦ s⦈ j else ARB’ $
        concl_tac o SIMP_RULE (srw_ss()) []
    >- (qx_gen_tac ‘j’ >> Cases_on ‘i = j’ >> rw[UPDATE_APPLY]) >>
    first_x_assum $ qspec_then ‘λj. if j < n then f⦇i ↦ e⦈ j else ARB’ $
        concl_tac o SIMP_RULE (srw_ss()) []
    >- (qx_gen_tac ‘j’ >> Cases_on ‘i = j’ >> rw[UPDATE_APPLY]) >>
    first_x_assum dxrule >> simp[UPDATE_APPLY]
QED

Theorem subset_class_pi_rect_sets_imp:
    ∀n sai. (∀i. i < n ⇒ subset_class (space (sai i)) (subsets (sai i))) ⇒
        subset_class (pi_rect n (space ∘ sai)) (pi_rect_sets n (subsets ∘ sai))
Proof
    rw[subset_class_def,pi_rect_sets_def,pi_rect_def,SUBSET_DEF,PULL_EXISTS] >> metis_tac[]
QED

(*
preconditions should now be minimal
*)
Theorem pi_sigma_recur:
    (∀sai. pi_sigma 0 sai = ({K (ARB: α)},POW {K ARB})) ∧
    ∀n (sai: num -> α algebra).
        pi_rect n (space ∘ sai) ∈ (pi_rect_sets n (subsets ∘ sai)) ⇒
        pi_sigma (SUC n) sai = sigma (pi_rect (SUC n) (space ∘ sai))
        (pi_prod_sets (SUC n) (subsets (pi_sigma n sai)) (subsets (sai n)))
Proof
    rw[] >> simp[Once pi_sigma_def]
    >- (simp[pi_rect_recur,pi_rect_sets_recur,GSYM SIGMA_POW] >>
        irule SIGMA_CONG_ALT >> irule_at (Pos hd) SIGMA_LOWER_BOUNDED >> simp[SET_IN_POW] >>
        ‘subset_class {(K: α -> num -> α) ARB} {{K ARB}}’ by simp[subset_class_def] >>
        dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >> rw[SUBSET_DEF,IN_POW_SING]
        >- (dxrule_then mp_tac SIGMA_ALGEBRA_SPACE >> simp[SPACE_SIGMA])
        >- (dxrule_then mp_tac SIGMA_ALGEBRA_EMPTY >> simp[])) >>
    irule SIGMA_CONG_ALT >> irule_at (Pos hd) SIGMA_LOWER_BOUNDED >> conj_tac
    >- (rw[SUBSET_DEF] >> gvs[pi_rect_sets_def] >> rename [‘_ _ fs ∈ _’] >>
        gvs[pi_rect_recur] >> simp[pi_prod_sets_def] >> pop_assum mp_tac >>
        simp[Once pi_cross_def,pi_pair_def] >> rw[] >> rename [‘fs⦇n ↦ s⦈’] >> simp[UPDATE_APPLY] >>
        qexistsl_tac [‘pi_rect n fs’,‘s’] >> simp[pi_rect_update] >>
        simp[pi_sigma_def] >> irule IN_SIGMA >> simp[pi_rect_sets_def]) >>
    simp[pi_sigma_def,sigma_def,SUBSET_DEF,pi_prod_sets_def,pi_rect_sets_recur,PULL_EXISTS] >>
    qx_genl_tac [‘fs’,‘s’] >> rw[] >> Cases_on ‘s = ∅’
    >- (‘∅ ∈ P’ by fs[sigma_algebra_def,algebra_def] >>
        ‘pi_cross (SUC n) fs s = ∅’ suffices_by simp[] >> simp[EXTENSION,pi_cross_def]) >>
    fs[GSYM MEMBER_NOT_EMPTY] >> rename[‘_ _ _ s ∈ _’,‘e ∈ s’] >>
    last_x_assum $ qspec_then ‘{fs | pi_cross (SUC n) fs s ∈ P ∧ ∀f i. n ≤ i ∧ f ∈ fs ⇒ f i = ARB}’ $
        irule o cj 1 o SIMP_RULE (srw_ss ()) [] >>
    rw[SIGMA_ALGEBRA_ALT_DIFF]
    >- (gvs[pi_rect_sets_def,pi_rect_def] >> first_x_assum $ qspec_then ‘i’ mp_tac >> simp[])
    >- (dxrule_then assume_tac SIGMA_ALGEBRA_SUBSET_CLASS >> gs[subset_class_def] >>
        qx_gen_tac ‘fr’ >> rw[] >> first_x_assum $ dxrule >>
        simp[SUBSET_DEF,pi_rect_def,pi_cross_def,PULL_EXISTS] >> rw[] >>
        first_x_assum $ drule_all_then assume_tac >> fs[] >>
        first_x_assum $ qspec_then ‘i’ mp_tac >> simp[pi_pair_def,UPDATE_APPLY])
    >- (fs[in_pi_rect])
    >- (rename [‘pi_cross (SUC n) (fs DIFF gs) s’] >> dxrule_then mp_tac SIGMA_ALGEBRA_DIFF >> simp[] >>
        DISCH_THEN $ qspecl_then [‘pi_cross (SUC n) fs s’,‘pi_cross (SUC n) gs s’] mp_tac >>
        simp[] >> qmatch_abbrev_tac ‘hs1 ∈ _ ⇒ hs2 ∈ _’ >> ‘hs1 = hs2’ suffices_by simp[] >>
        UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac ‘f’ >>
        simp[pi_cross_def,pi_pair_def] >> eq_tac >> strip_tac >> rw[] >> rename [‘f⦇n ↦ e⦈’]
        >| [metis_tac[],metis_tac[],all_tac] >> rename [‘f⦇n ↦ x⦈ = g⦇n ↦ y⦈’] >> disj1_tac >>
        strip_tac >> ‘f = g’ suffices_by (strip_tac >> fs[]) >>
        fs[FUN_EQ_THM] >> qx_gen_tac ‘i’ >> first_x_assum $ qspec_then ‘i’ mp_tac >>
        Cases_on ‘i < n’ >> simp[UPDATE_APPLY])
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[] >>
        DISCH_THEN $ qspec_then `IMAGE (λfs. pi_cross (SUC n) fs s) c` mp_tac >>
        ‘BIGUNION (IMAGE (λfs. pi_cross (SUC n) fs s) c) = pi_cross (SUC n) (BIGUNION c) s’ suffices_by (
            DISCH_THEN SUBST1_TAC >> DISCH_THEN irule >> simp[image_countable] >>
            fs[SUBSET_DEF,PULL_EXISTS]) >>
        simp[EXTENSION,IN_BIGUNION_IMAGE] >> qx_gen_tac ‘f’ >>
        simp[pi_cross_def,pi_pair_def] >> eq_tac >> strip_tac >> rw[] >- metis_tac[] >>
        rename [‘f⦇n ↦ e⦈’,‘f ∈ t’] >> qexists_tac ‘t’ >> simp[] >>
        qexistsl_tac [‘f’,‘e’] >> simp[])
    >- (gvs[SUBSET_DEF] >> first_x_assum $ dxrule_then assume_tac >> rfs[])
QED

Theorem pi_sigma_recur_alt:
    (∀sai. pi_sigma 0 sai = ({K (ARB: α)},POW {K ARB})) ∧
    ∀n (sai: num -> α algebra). (∀i. i < n ⇒ space (sai i) ∈ subsets (sai i)) ⇒
        pi_sigma (SUC n) sai = sigma (pi_rect (SUC n) (space ∘ sai))
        (pi_prod_sets (SUC n) (subsets (pi_sigma n sai)) (subsets (sai n)))
Proof
    simp[pi_sigma_recur] >> rw[] >> irule $ cj 2 pi_sigma_recur >>
    simp[pi_rect_sets_def] >> qexists_tac ‘λi. if i < n then space (sai i) else ARB’ >>
    simp[pi_rect_def]
QED

(*
Theorem pi_sigma_recur:
    (∀sai. pi_sigma 0 sai = ({K (ARB: α)},POW {K ARB})) ∧
    ∀n (sai: num -> α algebra). (∀i. i < n ⇒ space (sai i) ∈ subsets (sai i)) ⇒
        pi_sigma (SUC n) sai = sigma (pi_rect (SUC n) (space ∘ sai))
        (pi_prod_sets (SUC n) (subsets (pi_sigma n sai)) (subsets (sai n)))
Proof
    rw[] >> simp[Once pi_sigma_def]
    >- (simp[pi_rect_recur,pi_rect_sets_recur,GSYM SIGMA_POW] >>
        irule SIGMA_CONG_ALT >> irule_at (Pos hd) SIGMA_LOWER_BOUNDED >> simp[SET_IN_POW] >>
        ‘subset_class {(K: α -> num -> α) ARB} {{K ARB}}’ by simp[subset_class_def] >>
        dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >> rw[SUBSET_DEF,IN_POW_SING]
        >- (dxrule_then mp_tac SIGMA_ALGEBRA_SPACE >> simp[SPACE_SIGMA])
        >- (dxrule_then mp_tac SIGMA_ALGEBRA_EMPTY >> simp[])) >>
    irule SIGMA_CONG_ALT >> irule_at (Pos hd) SIGMA_LOWER_BOUNDED >> conj_tac
    >- (rw[SUBSET_DEF] >> gvs[pi_rect_sets_def] >> rename [‘_ _ fs ∈ _’] >>
        gvs[pi_rect_recur] >> simp[pi_prod_sets_def] >> pop_assum mp_tac >>
        simp[Once pi_cross_def,pi_pair_def] >> rw[] >> rename [‘fs⦇n ↦ s⦈’] >> simp[UPDATE_APPLY] >>
        qexistsl_tac [‘pi_rect n fs’,‘s’] >> simp[pi_rect_update] >>
        simp[pi_sigma_def] >> irule IN_SIGMA >> simp[pi_rect_sets_def]) >>
    simp[pi_sigma_def,sigma_def,SUBSET_DEF,pi_prod_sets_def,pi_rect_sets_recur,PULL_EXISTS] >>
    qx_genl_tac [‘fs’,‘s’] >> rw[] >> Cases_on ‘s = ∅’
    >- (‘∅ ∈ P’ by fs[sigma_algebra_def,algebra_def] >>
        ‘pi_cross (SUC n) fs s = ∅’ suffices_by simp[] >> simp[EXTENSION,pi_cross_def]) >>
    fs[GSYM MEMBER_NOT_EMPTY] >> rename[‘_ _ _ s ∈ _’,‘e ∈ s’] >>
    last_x_assum $ qspec_then ‘{fs | pi_cross (SUC n) fs s ∈ P ∧ ∀f i. n ≤ i ∧ f ∈ fs ⇒ f i = ARB}’ $
        irule o cj 1 o SIMP_RULE (srw_ss ()) [] >>
    rw[SIGMA_ALGEBRA_ALT_DIFF]
    >- (gvs[pi_rect_sets_def,pi_rect_def] >> first_x_assum $ qspec_then ‘i’ mp_tac >> simp[])
    >- (dxrule_then assume_tac SIGMA_ALGEBRA_SUBSET_CLASS >> gs[subset_class_def] >>
        qx_gen_tac ‘fr’ >> rw[] >> first_x_assum $ dxrule >>
        simp[SUBSET_DEF,pi_rect_def,pi_cross_def,PULL_EXISTS] >> rw[] >>
        first_x_assum $ drule_all_then assume_tac >> fs[] >>
        first_x_assum $ qspec_then ‘i’ mp_tac >> simp[pi_pair_def,UPDATE_APPLY])
    >- (first_x_assum irule >> simp[pi_rect_sets_def] >>
        qexists_tac ‘λi. if i < n then space (sai i) else ARB’ >> simp[pi_rect_def])
    >- (gvs[pi_rect_def] >> first_x_assum $ qspec_then ‘i’ mp_tac >> simp[])
    >- (rename [‘pi_cross (SUC n) (fs DIFF gs) s’] >> dxrule_then mp_tac SIGMA_ALGEBRA_DIFF >> simp[] >>
        DISCH_THEN $ qspecl_then [‘pi_cross (SUC n) fs s’,‘pi_cross (SUC n) gs s’] mp_tac >>
        simp[] >> qmatch_abbrev_tac ‘hs1 ∈ _ ⇒ hs2 ∈ _’ >> ‘hs1 = hs2’ suffices_by simp[] >>
        UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac ‘f’ >>
        simp[pi_cross_def,pi_pair_def] >> eq_tac >> strip_tac >> rw[] >> rename [‘f⦇n ↦ e⦈’]
        >| [metis_tac[],metis_tac[],all_tac] >> rename [‘f⦇n ↦ x⦈ = g⦇n ↦ y⦈’] >> disj1_tac >>
        strip_tac >> ‘f = g’ suffices_by (strip_tac >> fs[]) >>
        fs[FUN_EQ_THM] >> qx_gen_tac ‘i’ >> first_x_assum $ qspec_then ‘i’ mp_tac >>
        Cases_on ‘i < n’ >> simp[UPDATE_APPLY])
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[] >>
        DISCH_THEN $ qspec_then `IMAGE (λfs. pi_cross (SUC n) fs s) c` mp_tac >>
        ‘BIGUNION (IMAGE (λfs. pi_cross (SUC n) fs s) c) = pi_cross (SUC n) (BIGUNION c) s’ suffices_by (
            DISCH_THEN SUBST1_TAC >> DISCH_THEN irule >> simp[image_countable] >>
            fs[SUBSET_DEF,PULL_EXISTS]) >>
        simp[EXTENSION,IN_BIGUNION_IMAGE] >> qx_gen_tac ‘f’ >>
        simp[pi_cross_def,pi_pair_def] >> eq_tac >> strip_tac >> rw[] >- metis_tac[] >>
        rename [‘f⦇n ↦ e⦈’,‘f ∈ t’] >> qexists_tac ‘t’ >> simp[] >>
        qexistsl_tac [‘f’,‘e’] >> simp[])
    >- (gvs[SUBSET_DEF] >> first_x_assum $ dxrule_then assume_tac >> rfs[])
QED
*)

(*
Definition pi_measurable_sets_def:
    pi_measurable_sets 0 mn = POW {(λi. ARB)} ∧
    pi_measurable_sets (SUC n) mn = subsets (sigma (pi_m_space (SUC n) mn)
        (pi_prod_sets (SUC n) (pi_measurable_sets n mn) (measurable_sets (mn n))))
End

(*
Theorem pi_measurable_sets_alt =
    pi_measurable_sets_def
        |> SIMP_RULE (srw_ss()) [pi_prod_sets_def, pi_cross_def, pi_pair_alt]
*)

Definition pi_sig_alg_def:
    pi_sig_alg n mn = (pi_m_space n mn,pi_measurable_sets n mn)
End
*)

Definition pi_measure_rec_lex_def:
    pi_measure_rec_lex (INL (n,_)) = (n,0) ∧
    pi_measure_rec_lex (INR (n,_)) = (n,SUC 0)
End

(*
    (λfs. if (fs = ∅) then 0 else 1)
    pi_sigma n sai = sigma (pi_rect n (space ∘ sai)) (pi_rect_sets n (subsets ∘ sai))
    prod_measure_space_def
*)
Definition pi_measure_rec_def:
    pi_measure 0 mi = C 𝟙 (K ARB) ∧
    pi_measure (SUC n) mi =
        (λfs. ∫⁺ (mi n) (λe. ∫⁺ (pi_measure_space n mi) (λf. 𝟙 fs (pi_pair (SUC n) f e)))) ∧
    pi_measure_space n mi =
        (pi_rect n (m_space ∘ mi), subsets (pi_sigma n (measurable_space ∘ mi)), pi_measure n mi)
Termination
    WF_REL_TAC `inv_image ($< LEX $<) pi_measure_rec_lex` >> simp[pi_measure_rec_lex_def]
End

Theorem pi_measure_def:
    (∀mi. pi_measure 0 mi = C 𝟙 (K (ARB: α))) ∧
    (∀n mi. pi_measure (SUC n) mi =
        (λfs. ∫⁺ (mi n) (λe. ∫⁺ (pi_measure_space n mi) (λf. 𝟙 fs (pi_pair (SUC n) f (e: α))))))
Proof
    simp[pi_measure_rec_def]
QED

Theorem pi_measure_space_def:
    ∀n mi. pi_measure_space n mi =
        (pi_rect n (m_space ∘ mi), subsets (pi_sigma n (measurable_space ∘ mi)), pi_measure n mi)
Proof
    simp[pi_measure_rec_def]
QED

Theorem pi_measure_alt =
    pi_measure_def |> SIMP_RULE (srw_ss()) [pi_pair_def, combinTheory.C_DEF]

Theorem m_space_pi_measure_space:
    ∀n mi. m_space (pi_measure_space n mi) = pi_rect n (m_space ∘ mi)
Proof
    simp[pi_measure_space_def]
QED

Theorem in_m_space_pi_measure_space_imp:
    ∀n mi f. f ∈ m_space (pi_measure_space n mi) ⇒ f ∈ ((count n) --> (m_space ∘ mi))
Proof
    simp[DFUNSET,pi_measure_space_def,in_pi_rect]
QED

Theorem m_space_pi_measure_space_recur:
    (∀(mi: num -> α m_space). m_space (pi_measure_space 0 mi) = {K ARB}) ∧
    ∀n (mi: num -> α m_space). m_space (pi_measure_space (SUC n) mi) =
        pi_cross (SUC n) (m_space (pi_measure_space n mi)) (m_space (mi n))
Proof
    simp[m_space_pi_measure_space,pi_rect_recur]
QED

Theorem in_m_space_pi_measure_space_recur:
    (∀(mi: num -> α m_space) f. f ∈ m_space (pi_measure_space 0 mi) ⇔ f = K ARB) ∧
    ∀n (mi: num -> α m_space) fe. fe ∈ m_space (pi_measure_space (SUC n) mi) ⇔
        ∃f e. fe = pi_pair (SUC n) f e ∧ f ∈ m_space (pi_measure_space n mi) ∧ e ∈ m_space (mi n)
Proof
    simp[m_space_pi_measure_space_recur,in_pi_cross,PULL_EXISTS]
QED

Theorem pi_pair_in_m_space_pi_measure_space_imp:
    (∀mi f (e: α). pi_pair 0 f e ∈ m_space (pi_measure_space 0 mi)) ∧
    ∀n mi f (e: α). f ∈ m_space (pi_measure_space n mi) ∧ e ∈ m_space (mi n) ⇒
        pi_pair (SUC n) f e ∈ m_space (pi_measure_space (SUC n) mi)
Proof
    rw[pi_measure_space_def,pi_rect_def,pi_pair_def] >> last_x_assum $ qspec_then ‘i’ mp_tac >>
    ‘i < n ∨ i = n ∨ SUC n ≤ i’ by simp[] >> simp[UPDATE_APPLY]
QED

Theorem measurable_sets_pi_measure_space:
    ∀n mi. measurable_sets (pi_measure_space n mi) = subsets (pi_sigma n (measurable_space ∘ mi))
Proof
    simp[pi_measure_space_def,pi_sigma_def]
QED

Theorem measurable_space_pi_measure_space:
    ∀n mi. measurable_space (pi_measure_space n mi) = pi_sigma n (measurable_space ∘ mi)
Proof
    simp[pi_measure_space_def,pi_sigma_def,o_DEF,SIGMA_REDUCE]
QED

Theorem measure_pi_measure_space:
    ∀n mi. measure (pi_measure_space n mi) = pi_measure n mi
Proof
    simp[pi_measure_space_def]
QED

(*
Theorem m_space_pi_measure_space:
    ∀n mn. m_space (pi_measure_space n mn) = pi_m_space n mn
Proof
    simp[pi_measure_space_def]
QED

Theorem measurable_sets_pi_measure_space:
    ∀n mn. measurable_sets (pi_measure_space n mn) = pi_measurable_sets n mn
Proof
    simp[pi_measure_space_def]
QED

Theorem measure_pi_measure_space:
    ∀n mn. measure (pi_measure_space n mn) = pi_measure n mn
Proof
    simp[pi_measure_space_def]
QED

Theorem measurable_space_pi_measure_space:
    ∀n mn. measurable_space (pi_measure_space n mn) = pi_sig_alg n mn
Proof
    simp[pi_measure_space_def,pi_sig_alg_def]
QED

Theorem re_pi_sig_alg:
    ∀n mn. (pi_m_space n mn,pi_measurable_sets n mn) = pi_sig_alg n mn
Proof
    simp[pi_sig_alg_def]
QED

Theorem space_pi_sig_alg:
    ∀n mn. space (pi_sig_alg n mn) = pi_m_space n mn
Proof
    simp[pi_sig_alg_def]
QED

Theorem subsets_pi_sig_alg:
    ∀n mn. subsets (pi_sig_alg n mn) = pi_measurable_sets n mn
Proof
    simp[pi_sig_alg_def]
QED

val PI_MSP_ss = named_rewrites_with_names "PI_MSP" $ map name_to_thname [
    "m_space_pi_measure_space","measurable_sets_pi_measure_space","measure_pi_measure_space",
    "re_pi_sig_alg","space_pi_sig_alg","subsets_pi_sig_alg"];

val _ = augment_srw_ss [PI_MSP_ss];
*)

Definition pow_measure_space_def:
    pow_measure_space n m = pi_measure_space n (K m)
End

Definition measurability_preserving_def:
    measurability_preserving a b = {f |
        sigma_algebra a ∧ sigma_algebra b ∧ BIJ f (space a) (space b) ∧
        (∀s. s ∈ subsets a ⇒ IMAGE f s ∈ subsets b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}
End

Definition measure_preserving_def:
    measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (measurable_space m0) (measurable_space m1) ∧
        ∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))}
End

Definition isomorphic_def:
    isomorphic m0 m1 ⇔ ∃f. f ∈ measure_preserving m0 m1
End

(*
Definition pi_id_msp_def:
    pi_id_msp = ({(λi:num. ARB:α)},POW {(λi:num. ARB:α)},
        (λfs:(num->α)->bool. if fs = ∅ then (0:extreal) else 1))
End
*)

(* alternate representations *)

Theorem in_measurability_preserving:
    ∀f a b. f ∈ measurability_preserving a b ⇔
        sigma_algebra a ∧ sigma_algebra b ∧ BIJ f (space a) (space b) ∧
        (∀s. s ∈ subsets a ⇒ IMAGE f s ∈ subsets b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a
Proof
    simp[measurability_preserving_def]
QED

Theorem in_measurability_preserving_alt:
    ∀f a b. f ∈ measurability_preserving a b ⇔ ∃ar br.
        sigma (space a) ar = a ∧ sigma (space b) br = b ∧ subset_class (space a) ar ∧
        subset_class (space b) br ∧ BIJ f (space a) (space b) ∧
        (∀s. s ∈ ar ⇒ IMAGE f s ∈ br) ∧ (∀s. s ∈ br ⇒ PREIMAGE f s ∩ space a ∈ ar)
Proof
    rw[in_measurability_preserving] >> eq_tac >> strip_tac
    >- (qexistsl_tac [`subsets a`,`subsets b`] >> simp[SIGMA_STABLE,SIGMA_ALGEBRA_SUBSET_CLASS]) >>
    NTAC 2 $ (dxrule_then mp_tac SIGMA_ALGEBRA_SIGMA >> simp[] >> strip_tac) >> CONJ_TAC
    >- (qspecl_then [`space a`,`b`,`f`] mp_tac PREIMAGE_SIGMA_ALGEBRA >> simp[iffLR BIJ_ALT] >>
        `ar ⊆ IMAGE (λs. PREIMAGE f s ∩ space a) (subsets b)` suffices_by (NTAC 2 strip_tac >>
            dxrule_all_then mp_tac SIGMA_PROPERTY_WEAK >> simp[] >> rw[SUBSET_DEF] >>
            first_x_assum $ dxrule_then assume_tac >> gvs[] >> rename [`PREIMAGE f s`] >>
            drule_all_then assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[BIJ_IMAGE_PREIMAGE,SF SFY_ss]) >>
        simp[SUBSET_DEF] >> qx_gen_tac `s` >> strip_tac >> first_x_assum $ drule_then assume_tac >>
        qexists_tac `IMAGE f s` >> irule_at Any EQ_SYM >> irule_at Any BIJ_PREIMAGE_IMAGE >>
        qexists_tac `space b` >> simp[] >> irule_at Any SIGMA_ALGEBRA_SUBSET_SPACE >> simp[] >>
        map_every (fn sp => qspecl_then sp mp_tac SIGMA_SUBSET_SUBSETS) [[`space a`,`ar`],[`space b`,`br`]] >>
        simp[SUBSET_DEF])
    >- (drule_all_then mp_tac IMAGE_SIGMA_ALGEBRA >>
        `br ⊆ IMAGE (IMAGE f) (subsets a)` suffices_by (NTAC 2 strip_tac >>
            dxrule_all_then mp_tac SIGMA_PROPERTY_WEAK >> simp[] >> rw[SUBSET_DEF] >>
            first_x_assum $ dxrule_then assume_tac >> gvs[] >> rename [`IMAGE f s`] >>
            drule_all_then assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[BIJ_PREIMAGE_IMAGE,SF SFY_ss]) >>
        simp[SUBSET_DEF] >> qx_gen_tac `s` >> strip_tac >> first_x_assum $ drule_then assume_tac >>
        qexists_tac `PREIMAGE f s ∩ space a` >> irule_at Any EQ_SYM >> irule_at Any BIJ_IMAGE_PREIMAGE >>
        qexists_tac `space b` >> simp[] >> irule_at Any SIGMA_ALGEBRA_SUBSET_SPACE >> simp[] >>
        map_every (fn sp => qspecl_then sp mp_tac SIGMA_SUBSET_SUBSETS) [[`space a`,`ar`],[`space b`,`br`]] >>
        simp[SUBSET_DEF])
QED

Theorem measure_preserving_alt:
    ∀m0 m1. measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (measurable_space m0) (measurable_space m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}
Proof
    rw[measure_preserving_def,EXTENSION] >> eq_tac >> rw[] >>
    Q.RENAME_TAC [`f ∈ measurability_preserving _ _`]
    >- (first_x_assum (qspec_then `PREIMAGE f s ∩ m_space m0` assume_tac) >>
        rfs[measurability_preserving_def] >> `(IMAGE f (PREIMAGE f s ∩ m_space m0)) = s` suffices_by simp[] >>
        irule BIJ_IMAGE_PREIMAGE >> qexists_tac `m_space m1` >> simp[] >>
        qspec_then `measurable_space m1` assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> rfs[])
    >- (first_x_assum (qspec_then `IMAGE f s` assume_tac) >> rfs[measurability_preserving_def] >>
        `(PREIMAGE f (IMAGE f s) ∩ m_space m0) = s` suffices_by simp[] >> irule BIJ_PREIMAGE_IMAGE >>
        simp[GSYM RIGHT_EXISTS_AND_THM] >> qexists_tac `m_space m1` >> simp[] >>
        qspec_then `measurable_space m0` assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> rfs[])
QED

Theorem measure_preserving_full:
    ∀m0 m1. measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (measurable_space m0) (measurable_space m1) ∧
        (∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}
Proof
    rw[EXTENSION] >> eq_tac >> rw[]
    >- (fs[measure_preserving_def])
    >- (fs[measure_preserving_def])
    >- (fs[measure_preserving_alt])
    >- (simp[measure_preserving_def])
QED

Theorem in_measure_preserving:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇔
        f ∈ measurability_preserving (measurable_space m0) (measurable_space m1) ∧
        ∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))
Proof
    simp[measure_preserving_def]
QED

Theorem in_measure_preserving_alt:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇔
        f ∈ measurability_preserving (measurable_space m0) (measurable_space m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))
Proof
    simp[measure_preserving_alt]
QED

Theorem in_measure_preserving_full:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇔
        f ∈ measurability_preserving (measurable_space m0) (measurable_space m1) ∧
        (∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))
Proof
    simp[measure_preserving_full]
QED

Theorem measurability_preserving_measurable:
    ∀a b f. f ∈ measurability_preserving a b ⇒ f ∈ measurable a b
Proof
    simp[in_measurability_preserving,BIJ_ALT,IN_MEASURABLE]
QED

Theorem measure_preserving_measurability_preserving:
    ∀m0 m1 f. f ∈ measure_preserving m0 m1 ⇒ f ∈ measurability_preserving (measurable_space m0) (measurable_space m1)
Proof
    simp[in_measure_preserving]
QED

Theorem measure_preserving_measurable:
    ∀m0 m1 f. f ∈ measure_preserving m0 m1 ⇒ f ∈ measurable (measurable_space m0) (measurable_space m1)
Proof
    simp[measure_preserving_measurability_preserving,measurability_preserving_measurable]
QED

Definition measurability_contracting_def:
    measurability_contracting a b = {f |
        sigma_algebra a ∧ sigma_algebra b ∧ SURJ f (space a) (space b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}
End

Definition measure_contracting_def:
    measure_contracting m0 m1 = {f |
        f ∈ measurability_contracting (measurable_space m0) (measurable_space m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}
End

Theorem in_measurability_contracting:
    ∀f a b. f ∈ measurability_contracting a b ⇔
        sigma_algebra a ∧ sigma_algebra b ∧ SURJ f (space a) (space b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a
Proof
    simp[measurability_contracting_def]
QED

Theorem in_measure_contracting:
    ∀m0 m1 f. f ∈ measure_contracting m0 m1 ⇔
        f ∈ measurability_contracting (measurable_space m0) (measurable_space m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))
Proof
    simp[measure_contracting_def]
QED

Theorem in_measurability_contracting_alt:
    ∀a b f. f ∈ measurability_contracting a b ⇔ ∃ar br.
        sigma (space a) ar = a ∧ sigma (space b) br = b ∧ subset_class (space a) ar ∧
        subset_class (space b) br ∧ SURJ f (space a) (space b) ∧
        ∀s. s ∈ br ⇒ PREIMAGE f s ∩ space a ∈ ar
Proof
    rw[in_measurability_contracting] >> eq_tac >> strip_tac
    >- (qexistsl_tac [`subsets a`,`subsets b`] >> simp[SIGMA_STABLE,SIGMA_ALGEBRA_SUBSET_CLASS]) >>
    map_every qabbrev_tac [`asp = space a`,`bsp = space b`] >> NTAC 2 $ pop_assum kall_tac >>
    NTAC 2 $ last_x_assum $ SUBST1_TAC o SYM >> NTAC 2 $ irule_at Any SIGMA_ALGEBRA_SIGMA >> simp[] >>
    `sigma_algebra (bsp,{s | s ⊆ bsp ∧ PREIMAGE f s ∩ asp ∈ subsets (sigma asp ar)})` suffices_by (
        rw[sigma_def] >> first_x_assum (fn th => first_x_assum $ C (resolve_then Any assume_tac) th) >>
        fs[] >> pop_assum $ irule o cj 2 >> simp[] >> simp[SUBSET_DEF] >> fs[subset_class_def,SUBSET_DEF]) >>
    simp[SIGMA_ALGEBRA_ALT_SPACE,subset_class_def,FUNSET] >>
    NTAC 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >> rpt CONJ_TAC
    >- (`PREIMAGE f bsp ∩ asp = asp` by (simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[SURJ_DEF]) >>
        pop_assum SUBST1_TAC >> NTAC 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SPACE >> fs[SPACE_SIGMA])
    >- (rw[] >> dxrule_all_then mp_tac SIGMA_ALGEBRA_COMPL >> simp[SPACE_SIGMA] >>
        `PREIMAGE f (bsp DIFF s) ∩ asp = asp DIFF PREIMAGE f s ∩ asp` suffices_by simp[] >>
        rw[EXTENSION] >> eq_tac  >> rw[] >> fs[SURJ_DEF])
    >- (qx_gen_tac `sn` >> rw[] >- (simp[SUBSET_DEF,IN_BIGUNION_IMAGE] >> rw[] >> fs[SUBSET_DEF,SF SFY_ss]) >>
        simp[PREIMAGE_BIGUNION,GSYM BIGUNION_IMAGE_INTER_RIGHT,IMAGE_IMAGE] >>
        irule SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[] >> rw[SUBSET_DEF] >> simp[])
QED

Theorem measurability_contracting_measurable:
    ∀a b f. f ∈ measurability_contracting a b ⇒ f ∈ measurable a b
Proof
    simp[in_measurability_contracting,SURJ_DEF,IN_MEASURABLE,FUNSET]
QED

(* Isomorphism as an Equivalence Relation *)

Theorem isomorphic_refl:
    ∀m. measure_space m ⇒ isomorphic m m
Proof
    rw[isomorphic_def,measure_preserving_def,measurability_preserving_def,space_def,subsets_def] >>
    qexists_tac `I` >> simp[MEASURE_SPACE_SIGMA_ALGEBRA,IMAGE_I,PREIMAGE_I,BIJ_I] >>
    rw[] >> `s ∩ m_space m = s` suffices_by simp[] >> irule SUBSET_INTER1 >>
    simp[MEASURABLE_SETS_SUBSET_SPACE]
QED

Theorem measurability_preserving_LINV:
    ∀f a b. f ∈ measurability_preserving a b ⇒ LINV f (space a) ∈ measurability_preserving b a
Proof
    rpt gen_tac >> simp[in_measurability_preserving,BIJ_LINV_BIJ] >> rw[] >>
    first_x_assum $ drule_then assume_tac >> imp_res_tac SIGMA_ALGEBRA_SUBSET_SPACE >>
    simp[IMAGE_LINV,PREIMAGE_LINV,SF SFY_ss]
QED

Theorem measure_preserving_LINV:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇒ LINV f (m_space m0) ∈ measure_preserving m1 m0
Proof
    rpt gen_tac >> simp[Once in_measure_preserving_alt,Once in_measure_preserving] >> strip_tac >>
    drule_then mp_tac measurability_preserving_LINV >> simp[] >> DISCH_THEN kall_tac >> rw[] >>
    irule EQ_SYM >> irule IRULER >> irule IMAGE_LINV >> qexists_tac `m_space m1` >>
    qspecl_then [`measurable_space m1`,`s`] mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> fs[in_measurability_preserving]
QED

Theorem isomorphic_sym_imp:
    ∀m0 m1. isomorphic m0 m1 ⇒ isomorphic m1 m0
Proof
    rw[isomorphic_def] >> qexists_tac `LINV f (m_space m0)` >> simp[measure_preserving_LINV]
QED

Theorem isomorphic_sym:
    ∀m0 m1. isomorphic m0 m1 ⇔ isomorphic m1 m0
Proof
    rw[] >> eq_tac >> simp[isomorphic_sym_imp]
QED

Theorem measurability_preserving_comp:
    ∀f g a b c. f ∈ measurability_preserving a b ∧ g ∈ measurability_preserving b c ⇒
        g ∘ f ∈ measurability_preserving a c
Proof
    rpt gen_tac >> simp[in_measurability_preserving,BIJ_COMPOSE,SF SFY_ss] >> strip_tac >>
    simp[IMAGE_COMPOSE] >> rw[] >>
    `PREIMAGE (g ∘ f) s ∩ space a = PREIMAGE f (PREIMAGE g s ∩ space b) ∩ space a` suffices_by simp[PREIMAGE_COMP] >>
    simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[BIJ_ALT,FUNSET]
QED

Theorem measure_preserving_comp:
    ∀f g m0 m1 m2. f ∈ measure_preserving m0 m1 ∧ g ∈ measure_preserving m1 m2 ⇒
        g ∘ f ∈ measure_preserving m0 m2
Proof
    rpt gen_tac >> simp[in_measure_preserving] >> strip_tac >>
    drule_all_then mp_tac measurability_preserving_comp >> simp[IMAGE_COMPOSE] >> DISCH_THEN kall_tac >> rw[] >>
    first_x_assum irule >> fs[in_measurability_preserving]
QED

Theorem isomorphic_trans:
    ∀m0 m1 m2. isomorphic m0 m1 ∧ isomorphic m1 m2 ⇒ isomorphic m0 m2
Proof
    rw[isomorphic_def] >> rename [`f ∈ measure_preserving m0 m1`,`g ∈ measure_preserving m1 m2`] >>
    qexists_tac `g ∘ f` >> simp[measure_preserving_comp,SF SFY_ss]
QED

Theorem isomorphic_equiv_on_measure_spaces:
    isomorphic equiv_on measure_space
Proof
    simp[equiv_on_def,IN_APP,isomorphic_refl,Once isomorphic_sym] >> rw[] >>
    dxrule_all_then mp_tac isomorphic_trans >> simp[]
QED

(* isomorphism implying measure space *)

Theorem measure_space_isomorphic:
    ∀m0 m1. measure_space m0 ∧ isomorphic m0 m1 ⇒ measure_space m1
Proof
    rw[] >> rw[measure_space_def,positive_def,countably_additive_def]
    >- (fs[isomorphic_def,in_measure_preserving,measurability_preserving_def])
    >- (fs[isomorphic_def,in_measure_preserving,measurability_preserving_def] >>
        drule_then assume_tac MEASURE_SPACE_EMPTY_MEASURABLE >>
        first_x_assum $ dxrule_then mp_tac >> simp[IMAGE_EMPTY] >>
        DISCH_THEN $ SUBST1_TAC o SYM >> simp[MEASURE_EMPTY])
    >- (fs[isomorphic_def,in_measure_preserving_alt,measurability_preserving_def] >>
        irule MEASURE_POSITIVE >> simp[])
    >- (rename [`IMAGE sn 𝕌(:num)`] >>
        fs[isomorphic_def,in_measure_preserving_alt,measurability_preserving_def] >>
        irule EQ_SYM >> irule EQ_TRANS >>
        qexists_tac `suminf (measure m0 ∘ (λn. PREIMAGE f (sn n) ∩ m_space m0))` >>
        irule_at Any MEASURE_COUNTABLY_ADDITIVE >> fs[FUNSET,o_DEF] >>
        simp[PREIMAGE_BIGUNION,GSYM IMAGE_COMPOSE,o_DEF,BIGUNION_IMAGE_INTER_RIGHT] >>
        rw[] >> first_x_assum $ dxrule_then mp_tac >> simp[DISJOINT_ALT])
QED

Theorem sigma_finite_measure_space_isomorphic:
    ∀m0 m1. sigma_finite_measure_space m0 ∧ isomorphic m0 m1 ⇒ sigma_finite_measure_space m1
Proof
    simp[sigma_finite_measure_space_def,measure_space_isomorphic,SF SFY_ss] >>
    rw[sigma_finite_def] >> rename [`IMAGE sn 𝕌(:num)`] >>
    rfs[isomorphic_def,in_measure_preserving,measurability_preserving_def,FUNSET] >>
    qexists_tac `λn. IMAGE f (sn n)` >> qpat_x_assum `∀s. _ ⇒ _ = _` $ mp_tac o GSYM >>
    simp[] >> DISCH_THEN kall_tac >> drule_then assume_tac $ cj 2 $ iffLR BIJ_DEF >>
    dxrule_then SUBST1_TAC $ GSYM $ iffLR IMAGE_SURJ >>
    drule_then (qspec_then `IMAGE f` $ SUBST1_TAC o SYM) IRULER >>
    simp[IMAGE_BIGUNION,GSYM IMAGE_COMPOSE,o_DEF]
QED

(* pispace measure space *)

Theorem SUBSET_pi_cross:
    ∀n fs gt s t. fs ⊆ gt ∧ s ⊆ t ⇒ pi_cross n fs s ⊆ pi_cross n gt t
Proof
    rw[pi_cross_def,SUBSET_DEF] >> qexistsl_tac [‘f’,‘e’] >> simp[]
QED

Theorem in_m_space_pi_measure_space:
    ∀n mi f i. f ∈ m_space (pi_measure_space n mi) ⇔
        (∀i. i < n ⇒ f i ∈ m_space (mi i)) ∧ ∀i. n ≤ i ⇒ f i = ARB
Proof
    simp[pi_measure_space_def,in_pi_rect]
QED

Theorem in_m_space_pi_measure_space_lt:
    ∀n mi f i. i < n ∧ f ∈ m_space (pi_measure_space n mi) ⇒ f i ∈ m_space (mi i)
Proof
    simp[in_m_space_pi_measure_space]
QED

Theorem in_m_space_pi_measure_space_ge:
    ∀n mi f i. n ≤ i ∧ f ∈ m_space (pi_measure_space n mi) ⇒ f i = ARB
Proof
    simp[in_m_space_pi_measure_space]
QED

Theorem in_m_space_pi_pair_eq:
    ∀n mi f g x y. f ∈ m_space (pi_measure_space n mi) ∧ g ∈ m_space (pi_measure_space n mi) ⇒
        (pi_pair (SUC n) f x = pi_pair (SUC n) g y ⇔ f = g ∧ x = y)
Proof
    rw[pi_pair_def] >> eq_tac >> simp[] >> simp[FUN_EQ_THM] >> strip_tac >> reverse conj_tac
    >- (first_x_assum $ qspec_then ‘n’ mp_tac >> simp[UPDATE_APPLY]) >>
    qx_gen_tac ‘i’ >> first_x_assum $ qspec_then ‘i’ mp_tac >> Cases_on ‘i = n’ >>
    simp[UPDATE_APPLY] >> DISCH_THEN kall_tac >> fs[in_m_space_pi_measure_space]
QED

Theorem sigma_algebra_pi_sigma:
    ∀n sai. (∀i. i < n ⇒ subset_class (space (sai i)) (subsets (sai i))) ⇒ sigma_algebra (pi_sigma n sai)
Proof
    rw[pi_sigma_def] >> irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_pi_rect_sets_imp]
QED

Theorem sigma_algebra_measurable_space_pi_measure_space:
    ∀n mi. (∀i. i < n ⇒ measure_space (mi i)) ⇒
        sigma_algebra (measurable_space (pi_measure_space n mi))
Proof
    rw[measurable_space_pi_measure_space] >> irule sigma_algebra_pi_sigma >>
    fs[measure_space_def,sigma_algebra_def,algebra_def]
QED

Theorem in_measure_preserving_pi_pair:
    ∀n mi. (∀i. i < n ⇒ m_space (mi i) ∈ measurable_sets (mi i)) ∧
        sigma_finite_measure_space (pi_measure_space n mi) ∧ sigma_finite_measure_space (mi n) ⇒
        UNCURRY (pi_pair (SUC n)) ∈
        measure_preserving (pi_measure_space n mi × mi n) (pi_measure_space (SUC n) mi)
Proof
    REVERSE $ rw[in_measure_preserving]
    >- (rename [‘fs ∈ _’] >>
        simp[prod_measure_space_def,prod_measure_def,measure_pi_measure_space,pi_measure_def] >>
        irule IRULER >> simp[FUN_EQ_THM] >> qx_gen_tac ‘e’ >>
        irule pos_fn_integral_cong >> simp[iffLR sigma_finite_measure_space_def,INDICATOR_FN_POS] >>
        qx_gen_tac ‘f’ >> DISCH_TAC >> rw[indicator_fn_def,EXISTS_PROD]
        >- (pop_assum mp_tac >> simp[] >> qexistsl_tac [‘f’,‘e’] >> simp[]) >>
        rename [‘pi_pair (SUC n) f e = pi_pair (SUC n) g d’] >>
        dxrule_at_then Any assume_tac MEASURABLE_SETS_SUBSET_SPACE >>
        rfs[measure_space_prod_measure,SUBSET_DEF] >> pop_assum $ drule_then assume_tac >>
        fs[m_space_prod_measure_space] >> gs[in_m_space_pi_pair_eq,SF SFY_ss]) >>
    fs[sigma_finite_measure_space_def] >> NTAC 2 $ qpat_x_assum ‘sigma_finite _’ kall_tac >>
    ‘BIJ (UNCURRY (pi_pair (SUC n))) (m_space (pi_measure_space n mi × mi n))
      (m_space (pi_measure_space (SUC n) mi))’ by (
        simp[m_space_prod_measure_space,pi_measure_space_def,pi_rect_recur] >>
        simp[BIJ_ALT,EXISTS_UNIQUE_ALT,EXISTS_PROD,FORALL_PROD,FUNSET,in_pi_cross] >> CONJ_TAC
        >- (qx_genl_tac [‘f’,‘e’] >> rw[] >> qexistsl_tac [‘f’,‘e’] >> simp[]) >>
        rw[] >> qexistsl_tac [‘f’,‘e’] >> qx_genl_tac [‘g’,‘d’] >> eq_tac >> strip_tac >> gvs[] >>
        rfs[in_rect_pi_pair_eq,SF SFY_ss]) >>
    ‘∀fs s. pi_cross (SUC n) fs s = IMAGE (UNCURRY (pi_pair (SUC n))) (fs × s)’
        by simp[EXTENSION,EXISTS_PROD,in_pi_cross] >>
    simp[in_measurability_preserving_alt] >>
    qexistsl_tac [‘prod_sets (measurable_sets (pi_measure_space n mi)) (measurable_sets (mi n))’,
        ‘pi_prod_sets (SUC n) (measurable_sets (pi_measure_space n mi)) (measurable_sets (mi n))’] >> rw[]
    >- simp[prod_measure_space_def,prod_sigma_def,SIGMA_REDUCE]
    >- (simp[m_space_pi_measure_space,measurable_sets_pi_measure_space,
            measurable_space_pi_measure_space,o_DEF] >>
        qspecl_then [‘n’,‘measurable_space ∘ mi’] (irule o SRULE [o_DEF]) $ GSYM $ cj 2 pi_sigma_recur >>
        irule pi_rect_in_pi_rect_sets_imp >> rw[])
    >- (rw[subset_class_def,m_space_prod_measure_space] >> irule SUBSET_CROSS >>
        NTAC 2 $ dxrule_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >> rfs[])
    >- (pop_assum kall_tac >> rw[subset_class_def,pi_prod_sets_def] >>
        simp[pi_measure_space_def,pi_rect_recur] >> irule SUBSET_pi_cross >>
        NTAC 2 $ dxrule_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >>
        rfs[m_space_pi_measure_space])
    >- (rename [‘fs × s’] >> simp[pi_prod_sets_def] >> qexistsl_tac [‘fs’,‘s’] >> simp[])
    >- (rename [‘fr ∈ _’] >> gvs[pi_prod_sets_def] >> qexistsl_tac [‘fs’,‘s’] >> simp[] >>
        dxrule_then irule BIJ_PREIMAGE_IMAGE >> simp[m_space_prod_measure_space] >> irule SUBSET_CROSS >>
        NTAC 2 $ dxrule_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >> rfs[])
QED

Theorem sigma_finite_measure_space_pi_measure_space:
    ∀n mi. (∀i. i < n ⇒ sigma_finite_measure_space (mi i)) ⇒ sigma_finite_measure_space (pi_measure_space n mi)
Proof
    NTAC 2 gen_tac >> Induct_on ‘n’ >> rw[]
    >- (simp[pi_measure_space_def,pi_measure_def,pi_rect_recur,pi_sigma_recur] >>
        qspec_then ‘({K ARB},POW {K ARB})’
            (irule o SRULE []) sigma_finite_measure_space_dirac_measure >>
        simp[POW_SIGMA_ALGEBRA]) >>
    ‘isomorphic (pi_measure_space n mi × mi n) (pi_measure_space (SUC n) mi)’ suffices_by (
        DISCH_TAC >> dxrule_at_then Any irule sigma_finite_measure_space_isomorphic >>
        simp[sigma_finite_measure_space_prod_measure]) >>
    fs[]  >> simp[isomorphic_def] >> qexists_tac ‘UNCURRY (pi_pair (SUC n))’ >>
    irule in_measure_preserving_pi_pair >> rw[] >>
    irule MEASURE_SPACE_SPACE >> simp[sigma_finite_measure_space_measure_space]
QED

Theorem measure_space_pi_measure_space:
    ∀n mi. (∀i. i < n ⇒ sigma_finite_measure_space (mi i)) ⇒ measure_space (pi_measure_space n mi)
Proof
    simp[sigma_finite_measure_space_pi_measure_space,iffLR sigma_finite_measure_space_def]
QED

Theorem prob_space_pi_measure_space:
    ∀n mi. (∀i. i < n ⇒ prob_space (mi i)) ⇒ prob_space (pi_measure_space n mi)
Proof
    Induct_on ‘n’ >> rw[] >> simp[prob_space_def] >> irule_at Any measure_space_pi_measure_space >>
    simp[prob_space_sigma_finite_measure_space]
    >- simp[pi_measure_space_def,pi_rect_recur,pi_measure_def,indicator_fn_def] >>
    simp[measure_pi_measure_space,pi_measure_def] >>
    last_x_assum $ qspec_then ‘mi’ assume_tac >> rfs[] >>
    fs[prob_space_def] >> irule EQ_TRANS >> qexists_tac ‘∫⁺ (mi n) (λx. 1)’ >>
    irule_at Any pos_fn_integral_cong >> simp[pos_fn_integral_const] >> CONJ_ASM2_TAC
    >- simp[] >> qx_gen_tac ‘e’ >> rw[] >> irule EQ_TRANS >>
    qexists_tac ‘∫⁺ (pi_measure_space n mi) (λx. 1)’ >> irule_at Any pos_fn_integral_cong >>
    simp[pos_fn_integral_const,INDICATOR_FN_POS] >> qx_gen_tac ‘f’ >> rw[] >>
    simp[indicator_fn_def,pi_pair_in_m_space_pi_measure_space_imp]
QED

(* Misc results *)

Theorem pi_cross_in_measurable_sets_pi_measure_space:
    ∀n mi fs s. (∀i. i < SUC n ⇒ measure_space (mi i)) ∧
        fs ∈ measurable_sets (pi_measure_space n mi) ∧ s ∈ measurable_sets (mi n) ⇒
        pi_cross (SUC n) fs s ∈ measurable_sets (pi_measure_space (SUC n) mi)
Proof
    rw[measurable_sets_pi_measure_space] >>
    qspecl_then [‘n’,‘measurable_space ∘ mi’] (concl_tac o SRULE []) $ cj 2 pi_sigma_recur
    >- (irule pi_rect_in_pi_rect_sets_imp >> simp[MEASURE_SPACE_SPACE]) >>
    pop_assum SUBST1_TAC >> irule IN_SIGMA >> simp[pi_prod_sets_def] >>
    qexistsl_tac [‘fs’,‘s’] >> simp[]
QED

Theorem pi_measure_pi_cross:
    ∀n mi fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mi i)) ∧
        fs ∈ measurable_sets (pi_measure_space n mi) ∧ s ∈ measurable_sets (mi n) ⇒
        pi_measure (SUC n) mi (pi_cross (SUC n) fs s) = pi_measure n mi fs * measure (mi n) s
Proof
    rw[] >> qspecl_then [‘n’,‘mi’] mp_tac in_measure_preserving_pi_pair >>
    qspecl_then [‘n’,‘mi’] assume_tac sigma_finite_measure_space_pi_measure_space >>
    rfs[sigma_finite_measure_space_measure_space,MEASURE_SPACE_SPACE] >>
    simp[in_measure_preserving] >> rw[] >> pop_assum $ qspec_then ‘fs × s’ mp_tac >>
    map_every (qspecl_then [‘pi_measure_space n mi’,‘mi n’,‘fs’,‘s’] mp_tac)
        [prod_measure_cross,MEASURE_SPACE_CROSS] >>
    simp[measure_pi_measure_space] >> NTAC 3 $ DISCH_THEN kall_tac >> irule IRULER >>
    simp[pi_cross_def,IMAGE_DEF,UNCURRY] >> simp[EXTENSION,EXISTS_PROD]
QED

Theorem null_set_pi_crossr:
    ∀n mi fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mi i)) ∧
        fs ∈ measurable_sets (pi_measure_space n mi) ∧ s ∈ null_set (mi n) ⇒
        pi_cross (SUC n) fs s ∈ null_set (pi_measure_space (SUC n) mi)
Proof
    rw[IN_NULL_SET,null_set_def] >- (irule pi_cross_in_measurable_sets_pi_measure_space >> simp[]) >>
    simp[measure_pi_measure_space] >> drule_all_then SUBST1_TAC pi_measure_pi_cross >> simp[]
QED

Theorem null_set_pi_crossl:
    ∀n mi fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mi i)) ∧
        fs ∈ null_set (pi_measure_space n mi) ∧ s ∈ measurable_sets (mi n) ⇒
        pi_cross (SUC n) fs s ∈ null_set (pi_measure_space (SUC n) mi)
Proof
    rw[IN_NULL_SET,null_set_def] >- (irule pi_cross_in_measurable_sets_pi_measure_space >> simp[]) >>
    fs[measure_pi_measure_space] >> drule_all_then SUBST1_TAC pi_measure_pi_cross >> simp[]
QED

Theorem null_set_pi_cross:
    ∀n mi fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mi i)) ∧
        fs ∈ null_set (pi_measure_space n mi) ∧ s ∈ null_set (mi n) ⇒
        pi_cross (SUC n) fs s ∈ null_set (pi_measure_space (SUC n) mi)
Proof
    rw[IN_NULL_SET,null_set_def] >- (irule pi_cross_in_measurable_sets_pi_measure_space >> simp[]) >>
    simp[measure_pi_measure_space] >> drule_all_then SUBST1_TAC pi_measure_pi_cross >> simp[]
QED

Theorem pi_measure_space_space:
    ∀n mi. (∀i. i < n ⇒ measure_space (mi i)) ⇒
        m_space (pi_measure_space n mi) ∈ measurable_sets (pi_measure_space n mi)
Proof
    Induct_on ‘n’ >> rw[pi_measure_space_def] >- simp[pi_rect_recur,pi_sigma_recur,POW_DEF] >>
    simp[pi_sigma_def] >> irule IN_SIGMA >> irule pi_rect_in_pi_rect_sets_imp >>
    simp[MEASURE_SPACE_SPACE]
QED

Theorem pi_measure_space_AE_per_dim:
    ∀n mi P. (∀i. i < n ⇒ sigma_finite_measure_space (mi i)) ∧ (∀i. i < n ⇒ AE x::(mi i). P i x) ⇒
        AE xi::(pi_measure_space n mi). ∀i. i < n ⇒ P i (xi i)
Proof
    Induct_on ‘n’ >> rw[] >- (irule AE_T >> simp[] >> simp[measure_space_pi_measure_space]) >>
    last_x_assum $ qspecl_then [‘mi’,‘P’] assume_tac >> rfs[] >>
    ‘n < SUC n’ by simp[] >> first_x_assum $ dxrule_then assume_tac >>
    fs[AE_ALT] >> rename [‘null_set (pi_measure_space n mn) Npi’,‘null_set (mi n) Nn’] >>
    qexists_tac ‘pi_cross (SUC n) (m_space (pi_measure_space n mi)) Nn ∪
      pi_cross (SUC n) Npi (m_space (mi n))’ >> rw[]
    >- (fs[GSYM IN_NULL_SET] >>
        map_every (irule_at (Pos last)) [NULL_SET_UNION,null_set_pi_crossl,null_set_pi_crossr] >>
        simp[pi_measure_space_space,MEASURE_SPACE_SPACE,measure_space_pi_measure_space]) >>
    fs[SUBSET_DEF] >> qx_gen_tac ‘hi’ >>
    simp[m_space_pi_measure_space_recur,pi_cross_def] >> rw[] >>
    Cases_on ‘n = i’ >> gvs[] >> rename [`SUC n`] >| [DISJ1_TAC,DISJ2_TAC] >>
    qexistsl_tac [‘f’,‘e’] >> simp[] >> first_x_assum irule >> simp[]
    >| [all_tac,qexists_tac ‘i’] >> fs[pi_pair_def,UPDATE_APPLY]
QED

(* change of working space *)

Theorem iso_valid_psf_comp:
    ∀sa sb g s e a. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf sb s e a ⇒ valid_psf sa s (λi. PREIMAGE g (e i) ∩ space sa) a
Proof
    simp[valid_psf_def,measurability_preserving_def]
QED

Theorem epi_valid_psf_comp:
    ∀sa sb g s e a. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_contracting sa sb ∧
        valid_psf sb s e a ⇒ valid_psf sa s (λi. PREIMAGE g (e i) ∩ space sa) a
Proof
    simp[valid_psf_def,measurability_contracting_def]
QED

(*
Theorem iso_psf_comp:
    ∀sa sb g s e a x. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf sb s e a ∧ x ∈ space sa ⇒ psf s e a (g x) = psf s (λi. PREIMAGE g (e i) ∩ space sa) a x
Proof
    rw[psf_def] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >> fs[valid_psf_def] >- (rw[indicator_fn_def]) >>
    DISJ1_TAC >> qx_gen_tac `i` >> DISCH_TAC >> NTAC 2 $ irule_at Any pos_not_neginf >>
    NTAC 2 $ irule_at Any le_mul >> simp[INDICATOR_FN_POS]
QED
*)

Theorem psf_comp:
    ∀sa sb g s e a x. sigma_algebra sa ∧ sigma_algebra sb ∧
        valid_psf sb s e a ∧ x ∈ space sa ⇒ psf s e a (g x) = psf s (λi. PREIMAGE g (e i) ∩ space sa) a x
Proof
    rw[psf_def] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >> fs[valid_psf_def] >- (rw[indicator_fn_def]) >>
    DISJ1_TAC >> qx_gen_tac `i` >> DISCH_TAC >> NTAC 2 $ irule_at Any pos_not_neginf >>
    NTAC 2 $ irule_at Any le_mul >> simp[INDICATOR_FN_POS]
QED

Theorem iso_valid_psf_seq_comp:
    ∀sa sb g si ei ai. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf_seq sb si ei ai ⇒ valid_psf_seq sa si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai
Proof
    rw[valid_psf_seq_def] >- (irule iso_valid_psf_comp >> simp[] >> qexists_tac `sb` >> simp[]) >>
    fs[ext_mono_increasing_def] >> qx_genl_tac [`i`,`j`] >> rw[] >>
    `g x ∈ space sb` by fs[measurability_preserving_def,BIJ_ALT,FUNSET] >>
    NTAC 2 $ first_x_assum $ dxrule_then assume_tac >> pop_assum mp_tac >>
    qmatch_abbrev_tac `_ Σa Σb ⇒ _ Σc Σd` >> `Σc = Σa ∧ Σd = Σb` suffices_by simp[] >>
    UNABBREV_ALL_TAC >> NTAC 2 (irule_at Any $ GSYM psf_comp >> qexists_tac `sb`) >> simp[]
QED

Theorem epi_valid_psf_seq_comp:
    ∀sa sb g si ei ai. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_contracting sa sb ∧
        valid_psf_seq sb si ei ai ⇒ valid_psf_seq sa si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai
Proof
    rw[valid_psf_seq_def] >- (irule epi_valid_psf_comp >> simp[] >> qexists_tac `sb` >> simp[]) >>
    fs[ext_mono_increasing_def] >> qx_genl_tac [`i`,`j`] >> rw[] >>
    `g x ∈ space sb` by fs[measurability_contracting_def,SURJ_DEF] >>
    NTAC 2 $ first_x_assum $ dxrule_then assume_tac >> pop_assum mp_tac >>
    qmatch_abbrev_tac `_ Σa Σb ⇒ _ Σc Σd` >> `Σc = Σa ∧ Σd = Σb` suffices_by simp[] >>
    UNABBREV_ALL_TAC >> NTAC 2 (irule_at Any $ GSYM psf_comp >> qexists_tac `sb`) >> simp[]
QED

(*
Theorem iso_psf_seq_lim_comp:
    ∀sa sb g si ei ai x. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf_seq sb si ei ai ∧ x ∈ space sa ⇒
        psf_seq_lim si ei ai (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai x
Proof
    rw[psf_seq_lim_def] >> fs[valid_psf_seq_def] >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> simp[psf_comp,SF SFY_ss]
QED
*)

Theorem psf_seq_lim_comp:
    ∀sa sb g si ei ai x. sigma_algebra sa ∧ sigma_algebra sb ∧
        valid_psf_seq sb si ei ai ∧ x ∈ space sa ⇒
        psf_seq_lim si ei ai (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai x
Proof
    rw[psf_seq_lim_def] >> fs[valid_psf_seq_def] >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> simp[psf_comp,SF SFY_ss]
QED

Theorem iso_psf_integral_comp:
    ∀m0 m1 g s e a. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_preserving m0 m1 ∧
        valid_psf (measurable_space m1) s e a ⇒
        psf_integral (measure m1) s e a = psf_integral (measure m0) s (λi. PREIMAGE g (e i) ∩ m_space m0) a
Proof
    rw[in_measure_preserving_alt,valid_psf_def,psf_integral_def] >> irule EXTREAL_SUM_IMAGE_EQ >>
    simp[] >> DISJ1_TAC >> rw[] >> irule pos_not_neginf >> irule le_mul >> simp[] >>
    irule MEASURE_POSITIVE >> fs[in_measurability_preserving]
QED

Theorem epi_psf_integral_comp:
    ∀m0 m1 g s e a. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_contracting m0 m1 ∧
        valid_psf (measurable_space m1) s e a ⇒
        psf_integral (measure m1) s e a = psf_integral (measure m0) s (λi. PREIMAGE g (e i) ∩ m_space m0) a
Proof
    rw[in_measure_contracting,valid_psf_def,psf_integral_def] >> irule EXTREAL_SUM_IMAGE_EQ >>
    simp[] >> DISJ1_TAC >> rw[] >> irule pos_not_neginf >> irule le_mul >> simp[] >>
    irule MEASURE_POSITIVE >> fs[in_measurability_contracting]
QED

Theorem iso_pos_fn_integral_comp:
    ∀m0 m1 g f. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_preserving m0 m1 ∧
        f ∈ Borel_measurable (measurable_space m1) ∧ (∀x. x ∈ m_space m1 ⇒ 0 ≤ f x) ⇒ ∫⁺ m1 f = ∫⁺ m0 (f ∘ g)
Proof
    rw[] >> qspecl_then [`measurable_space m1`,`f`] mp_tac pos_fn_sup_psf_seq >> simp[] >> DISCH_TAC >> fs[] >>
    qspecl_then [`m1`,`f`,`si`,`ei`,`ai`] mp_tac pos_fn_psf_integral_convergence >>
    simp[] >> DISCH_THEN kall_tac >> drule_then assume_tac $ cj 1 $ iffLR in_measure_preserving >>
    qspecl_then [`m0`,`f ∘ g`,`si`,`(λi j. PREIMAGE g (ei i j) ∩ m_space m0)`,`ai`]
        mp_tac pos_fn_psf_integral_convergence >> simp[] >>
    qspecl_then [`measurable_space m0`,`measurable_space m1`] mp_tac iso_valid_psf_seq_comp >>
    simp[] >> DISCH_THEN kall_tac >>
    `∀x. x ∈ m_space m0 ⇒ f (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ m_space m0) ai x` by (
        rw[] >> `g x ∈ m_space m1` by fs[measurability_preserving_def,BIJ_ALT,FUNSET] >>
        first_x_assum $ dxrule_then SUBST1_TAC >>
        qspecl_then [`measurable_space m0`,`measurable_space m1`,`g`,`si`,`ei`,`ai`,`x`] mp_tac psf_seq_lim_comp >>
        simp[]) >>
    pop_assum $ simp o single >> DISCH_THEN kall_tac >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> fs[valid_psf_seq_def,iso_psf_integral_comp]
QED

Theorem epi_pos_fn_integral_comp:
    ∀m0 m1 g f. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_contracting m0 m1 ∧
        f ∈ Borel_measurable (measurable_space m1) ∧ (∀x. x ∈ m_space m1 ⇒ 0 ≤ f x) ⇒ ∫⁺ m1 f = ∫⁺ m0 (f ∘ g)
Proof
    rw[] >> qspecl_then [`measurable_space m1`,`f`] mp_tac pos_fn_sup_psf_seq >> simp[] >> DISCH_TAC >> fs[] >>
    qspecl_then [`m1`,`f`,`si`,`ei`,`ai`] mp_tac pos_fn_psf_integral_convergence >>
    simp[] >> DISCH_THEN kall_tac >> drule_then assume_tac $ cj 1 $ iffLR in_measure_contracting >>
    qspecl_then [`m0`,`f ∘ g`,`si`,`(λi j. PREIMAGE g (ei i j) ∩ m_space m0)`,`ai`]
        mp_tac pos_fn_psf_integral_convergence >> simp[] >>
    qspecl_then [`measurable_space m0`,`measurable_space m1`] mp_tac epi_valid_psf_seq_comp >>
    simp[] >> DISCH_THEN kall_tac >>
    `∀x. x ∈ m_space m0 ⇒ f (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ m_space m0) ai x` by (
        rw[] >> `g x ∈ m_space m1` by fs[measurability_contracting_def,SURJ_DEF] >>
        first_x_assum $ dxrule_then SUBST1_TAC >>
        qspecl_then [`measurable_space m0`,`measurable_space m1`,`g`,`si`,`ei`,`ai`,`x`] mp_tac psf_seq_lim_comp >>
        simp[]) >>
    pop_assum $ simp o single >> DISCH_THEN kall_tac >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> fs[valid_psf_seq_def,epi_psf_integral_comp]
QED

(* dimensionality reduction *)

Theorem pi_tonelli:
    ∀n mi ff. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mi i)) ∧
        ff ∈ Borel_measurable (measurable_space (pi_measure_space (SUC n) mi)) ∧
        (∀f. f ∈ m_space (pi_measure_space (SUC n) mi) ⇒ 0 ≤ ff f) ⇒
        (∀e. e ∈ m_space (mi n) ⇒
            (λf. ff (pi_pair (SUC n) f e)) ∈ Borel_measurable (measurable_space (pi_measure_space n mi))) ∧
        (∀f. f ∈ m_space (pi_measure_space n mi) ⇒
            (λe. ff (pi_pair (SUC n) f e)) ∈ Borel_measurable (measurable_space (mi n))) ∧
        (λf. ∫⁺ (mi n) (λe. ff (pi_pair (SUC n) f e))) ∈
            Borel_measurable (measurable_space (pi_measure_space n mi)) ∧
        (λe. ∫⁺ (pi_measure_space n mi) (λf. ff (pi_pair (SUC n) f e))) ∈ Borel_measurable (measurable_space (mi n)) ∧
        ∫⁺ (pi_measure_space (SUC n) mi) ff =
            ∫⁺ (mi n) (λe. ∫⁺ (pi_measure_space n mi) (λf. ff (pi_pair (SUC n) f e))) ∧
        ∫⁺ (pi_measure_space (SUC n) mi) ff =
            ∫⁺ (pi_measure_space n mi) (λf. ∫⁺ (mi n) (λe. ff (pi_pair (SUC n) f e)))
Proof
    rpt gen_tac >> DISCH_TAC >> fs[] >>
    map_every (fn tm => qspecl_then [tm,‘mi’] assume_tac sigma_finite_measure_space_pi_measure_space)
        [‘n’,‘SUC n’] >> rfs[] >>
    ‘sigma_finite_measure_space (pi_measure_space n mi × mi n)’ by simp[sigma_finite_measure_space_prod_measure] >>
    qspecl_then [‘n’,‘mi’] assume_tac in_measure_preserving_pi_pair >>
    rfs[sigma_finite_measure_space_measure_space,MEASURE_SPACE_SPACE] >>
    ‘∫⁺ (pi_measure_space (SUC n) mi) ff =
      ∫⁺ (pi_measure_space n mi × mi n) (ff ∘ UNCURRY (pi_pair (SUC n)))’ by (
        irule iso_pos_fn_integral_comp >> simp[iffLR sigma_finite_measure_space_def]) >>
    pop_assum SUBST1_TAC >>
    qspecl_then [‘pi_measure_space n mi’,‘mi n’,‘ff ∘ UNCURRY (pi_pair (SUC n))’] mp_tac TONELLI_ALT >>
    simp[] >> DISCH_THEN irule >>
    irule_at Any $ INST_TYPE [“:α” |-> “:(num -> α) # α”,“:β” |-> “:(num -> α)”] IN_MEASURABLE_BOREL_COMP >>
    qexistsl_tac [‘UNCURRY (pi_pair (SUC n))’,‘ff’,‘measurable_space (pi_measure_space (SUC n) mi)’] >>
    simp[FORALL_PROD] >> fs[m_space_pi_measure_space_recur,in_pi_cross,PULL_EXISTS] >>
    dxrule measure_preserving_measurable >> simp[m_space_pi_measure_space_recur,sig_alg_prod_measure_space]
QED

Theorem idx_measurable:
    ∀n j sai. j < n ∧ (∀i. i < n ⇒ sigma_algebra (sai i)) ⇒
        C LET j ∈ measurable (pi_sigma n sai) (sai j)
Proof
    rw[] >> simp[IN_MEASURABLE,SIGMA_ALGEBRA_SUBSET_CLASS,sigma_algebra_pi_sigma] >>
    simp[FUNSET,space_pi_sigma,in_pi_rect] >> rw[] >>
    ‘PREIMAGE (C LET j) s ∩ pi_rect n (space ∘ sai) = pi_rect n ((space ∘ sai)⦇j ↦ s⦈)’ suffices_by (
        DISCH_THEN SUBST1_TAC >> simp[pi_sigma_def] >> irule IN_SIGMA >>
        irule pi_rect_in_pi_rect_sets_imp >> rw[] >>
        Cases_on ‘j = i’ >> gs[UPDATE_APPLY,SIGMA_ALGEBRA_SPACE]) >>
    simp[EXTENSION] >> qx_gen_tac ‘f’ >> simp[in_pi_rect,EQ_IMP_THM] >> conj_tac >> strip_tac
    >- (rw[] >> first_x_assum dxrule >> Cases_on ‘j = i’ >> gvs[UPDATE_APPLY]) >>
    first_assum $ dxrule_then $ irule_at Any o SRULE[UPDATE_APPLY] >> rw[] >>
    first_x_assum $ drule_then assume_tac >> Cases_on ‘j = i’ >> gvs[UPDATE_APPLY] >>
    metis_tac[SIGMA_ALGEBRA_IN_SPACE]
QED

Theorem idx_measurable_msp:
    ∀n j mi. j < n ∧ (∀i. i < n ⇒ measure_space (mi i)) ⇒
        C LET j ∈ measurable (measurable_space (pi_measure_space n mi)) (measurable_space (mi j))
Proof
    rw[] >> qspecl_then [‘n’,‘j’,‘measurable_space ∘ mi’] mp_tac idx_measurable >>
    simp[measurable_space_pi_measure_space]
QED

(*
Theorem idx_measurable:
    ∀n m mi. m < n ∧ (∀i. i < n ⇒ measure_space (mi i)) ⇒
        C LET m ∈ measurable (measurable_space (pi_measure_space n mi)) (measurable_space (mi m))
Proof
    
    
    Induct_on ‘n’ >> rw[] >> simp[IN_MEASURABLE,sigma_algebra_measurable_space_pi_measure_space] >>
    CONJ_TAC >- simp[FUNSET,in_m_space_pi_measure_space,pi_pair_def,PULL_EXISTS] >> rw[] >>
    simp[measurable_sets_pi_measure_space,pi_sigma_def] >> irule IN_SIGMA >>
    simp[pi_rect_sets_recur,pi_prod_sets_def] >>
    last_x_assum $ qspecl_then [‘m’,‘mi’] assume_tac >> Cases_on ‘m = n’ >> gvs[]
    >- (qexistsl_tac [‘m_space (pi_measure_space m mi)’,‘s’] >>
        ‘sigma_algebra (measurable_space (pi_measure_space m mi))’
            by simp[sigma_algebra_measurable_space_pi_measure_space] >>
        dxrule_then assume_tac SIGMA_ALGEBRA_SPACE >> fs[] >> simp[EXTENSION] >>
        qx_gen_tac `g` >> simp[pi_m_space_def,pi_cross_def] >> eq_tac >> rw[]
        >| [all_tac,simp[pi_pair_def],all_tac] >> qexistsl_tac [`f`,`e`] >> simp[]
        >- fs[pi_pair_def] >> irule MEASURE_SPACE_IN_MSPACE >> simp[] >> qexists_tac `s` >> simp[])
    >- (fs[measurable_def] >> first_x_assum $ dxrule_then assume_tac >>
        qexistsl_tac [`PREIMAGE (C LET m) s ∩ pi_m_space n mn`,`m_space (mn n)`] >>
        simp[MEASURE_SPACE_SPACE,EXTENSION] >> qx_gen_tac `g` >> simp[pi_m_space_def,pi_cross_def] >>
        eq_tac >> rw[] >| [all_tac,simp[pi_pair_def],all_tac] >> qexistsl_tac [`f`,`e`] >> simp[] >>
        rfs[pi_pair_def])
QED
*)

Theorem pos_fn_integral_pi_dim:
    ∀n mi f j. j < n ∧ (∀i. i < n ⇒ prob_space (mi i)) ∧ (∀x. x ∈ m_space (mi j) ⇒ 0 ≤ f x) ∧
        f ∈ Borel_measurable (measurable_space (mi j)) ⇒
        ∫⁺ (pi_measure_space n mi) (f ∘ C LET j) = ∫⁺ (mi j) f
Proof
    Induct_on ‘n’ >> rw[] >> qmatch_abbrev_tac ‘_ _ ff = _’ >>
    ‘(∀i. i < SUC n ⇒ sigma_finite_measure_space (mi i)) ∧
      ff ∈ Borel_measurable (measurable_space (pi_measure_space (SUC n) mi)) ∧
      (∀f. f ∈ m_space (pi_measure_space (SUC n) mi) ⇒ 0 ≤ ff f)’ by (
        qunabbrev_tac ‘ff’ >> fs[prob_space_sigma_finite_measure_space,prob_space_def] >>
        qspecl_then [‘SUC n’,‘j’,‘mi’] mp_tac idx_measurable_msp >> simp[] >> DISCH_TAC >>
        simp[MEASURABLE_COMP,SF SFY_ss] >> qx_gen_tac ‘g’ >> strip_tac >> first_x_assum irule >>
        fs[IN_MEASURABLE,FUNSET]) >>
    Cases_on ‘j = n’ >> gvs[]
    >- (dxrule_all_then SUBST1_TAC $ cj 5 pi_tonelli >> irule pos_fn_integral_cong >> REVERSE CONJ_ASM1_TAC
        >- fs[prob_space_def] >> qx_gen_tac ‘e’ >> rw[Abbr ‘ff’,pi_pair_def,UPDATE_APPLY] >>
        qspecl_then [‘pi_measure_space j mi’,‘f e’] mp_tac pos_fn_integral_const >> simp[] >>
        ‘prob_space (pi_measure_space j mi)’ suffices_by simp[prob_space_def] >>
        irule prob_space_pi_measure_space >> simp[])
    >- (last_x_assum $ qspecl_then [‘mi’,‘f’,‘j’] mp_tac >> simp[] >> DISCH_THEN $ SUBST1_TAC o SYM >>
        dxrule_all_then SUBST1_TAC $ cj 6 pi_tonelli >> irule pos_fn_integral_cong >> REVERSE CONJ_ASM1_TAC
        >- (csimp[] >> irule_at Any measure_space_pi_measure_space >> simp[prob_space_sigma_finite_measure_space] >>
            qunabbrev_tac ‘ff’ >> rw[] >> first_x_assum irule >> fs[prob_space_def] >>
            qspecl_then [‘n’,‘j’,‘mi’] mp_tac idx_measurable_msp >> simp[IN_MEASURABLE,FUNSET]) >>
        qx_gen_tac ‘g’ >>  rw[Abbr ‘ff’,pi_pair_def,UPDATE_APPLY] >> fs[prob_space_def] >>
        qspecl_then [‘mi n’,‘f (g j)’] mp_tac pos_fn_integral_const >> simp[] >> DISCH_THEN irule >>
        first_x_assum irule >> qspecl_then [‘n’,‘j’,‘mi’] mp_tac idx_measurable_msp >>
        simp[IN_MEASURABLE,FUNSET])
QED

Theorem integral_pi_dim:
    ∀n mi f j. j < n ∧ (∀i. i < n ⇒ prob_space (mi i)) ∧ f ∈ Borel_measurable (measurable_space (mi j)) ⇒
        ∫ (pi_measure_space n mi) (f ∘ C LET j) = ∫ (mi j) f
Proof
    rw[integral_def] >> ‘∀x1:extreal x2 x3 x4. x1 = x3 ∧ x2 = x4 ⇒ x1 - x2 = x3 - x4’ by simp[] >>
    ‘(f ∘ C LET j)⁺ = f⁺ ∘ C LET j ∧ (f ∘ C LET j)⁻ = f⁻ ∘ C LET j’ by simp[o_DEF,fn_plus_def,fn_minus_def] >>
    map_every pop_assum [SUBST1_TAC,SUBST1_TAC,irule] >> NTAC 2 $ irule_at Any pos_fn_integral_pi_dim >>
    simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS]
QED

Theorem integrable_pi_dim:
    ∀n mi f j. j < n ∧ (∀i. i < n ⇒ prob_space (mi i)) ∧ integrable (mi j) f ⇒
        integrable (pi_measure_space n mi) (f ∘ C LET j)
Proof
    rw[] >> fs[integrable_def] >> irule_at Any MEASURABLE_COMP >> qexists_tac ‘measurable_space (mi j)’ >>
    irule_at Any idx_measurable_msp >> simp[prob_space_measure_space] >>
    ‘∀x:extreal y z. x = y ∧ y ≠ z ⇒ x ≠ z’ by simp[] >>
    pop_assum $ NTAC 2 o pop_assum o C (resolve_then Any (irule_at $ Pos last)) >>
    ‘(f ∘ C LET j)⁺ = f⁺ ∘ C LET j ∧ (f ∘ C LET j)⁻ = f⁻ ∘ C LET j’ by simp[o_DEF,fn_plus_def,fn_minus_def] >>
    NTAC 2 $ pop_assum SUBST1_TAC >> NTAC 2 $ irule_at Any pos_fn_integral_pi_dim >>
    simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS]
QED

Theorem pos_fn_integral_pi_sum_dim:
    ∀n mi fi. (∀i. i < n ⇒ prob_space (mi i)) ∧ (∀i x. i < n ∧ x ∈ m_space (mi i) ⇒ 0 ≤ fi i x) ∧
        (∀i. i < n ⇒ (fi i) ∈ Borel_measurable (measurable_space (mi i))) ⇒
        ∫⁺ (pi_measure_space n mi) (λxi. (∑ (λi. fi i (xi i)) (count n))) = ∑ (λi. ∫⁺ (mi i) (fi i)) (count n)
Proof
    rw[] >> irule EQ_TRANS >> qexists_tac ‘∑ (λi. ∫⁺ (pi_measure_space n mi) ((fi i) ∘ C LET i)) (count n)’ >>
    irule_at Any EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
    qspecl_then [‘pi_measure_space n mi’,‘λi. (fi i) ∘ C LET i’,‘count n’] mp_tac pos_fn_integral_sum >>
    simp[] >> DISCH_THEN $ irule_at Any >> irule_at Any measure_space_pi_measure_space >>
    simp[prob_space_sigma_finite_measure_space,GSYM FORALL_IMP_CONJ_THM] >>
    ‘∀i. i < n ⇒ C LET i ∈ measurable (measurable_space (pi_measure_space n mi)) (measurable_space (mi i))’ by (
        rw[] >> irule idx_measurable_msp >> simp[iffLR prob_space_def]) >>
    qx_gen_tac ‘i’ >> DISCH_TAC >> rw[]
    >- (first_x_assum irule >> fs[IN_MEASURABLE,FUNSET])
    >- (irule MEASURABLE_COMP >> qexists_tac ‘measurable_space (mi i)’ >> simp[])
    >- (irule pos_fn_integral_pi_dim >> simp[])
QED

Theorem integral_pi_sum_dim:
    ∀n mi fi. (∀i. i < n ⇒ prob_space (mi i)) ∧ (∀i. i < n ⇒ integrable (mi i) (fi i)) ⇒
        ∫ (pi_measure_space n mi) (λxi. (∑ (λi. fi i (xi i)) (count n))) = ∑ (λi. ∫ (mi i) (fi i)) (count n)
Proof
    rw[] >> irule EQ_TRANS >> qexists_tac ‘∑ (λi. ∫ (pi_measure_space n mi) ((fi i) ∘ C LET i)) (count n)’ >>
    irule_at Any EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
    qspecl_then [‘pi_measure_space n mi’,‘λi. (fi i) ∘ C LET i’,‘count n’] mp_tac integral_sum' >>
    simp[] >> DISCH_THEN $ irule_at Any >> irule_at Any measure_space_pi_measure_space >>
    simp[prob_space_sigma_finite_measure_space,GSYM FORALL_IMP_CONJ_THM] >>
    ‘∀i. i < n ⇒ C LET i ∈ measurable (measurable_space (pi_measure_space n mi)) (measurable_space (mi i))’ by (
        rw[] >> irule idx_measurable_msp >> simp[prob_space_measure_space]) >>
    qx_gen_tac ‘i’ >> DISCH_TAC >> map_every (irule_at Any) [integral_pi_dim,integrable_pi_dim] >>
    simp[integrable_measurable]
QED

Theorem integrable_pi_sum_dim:
    ∀n mi fi. (∀i. i < n ⇒ prob_space (mi i)) ∧ (∀i. i < n ⇒ integrable (mi i) (fi i)) ⇒
        integrable (pi_measure_space n mi) (λxi. (∑ (λi. fi i (xi i)) (count n)))
Proof
    rw[] >>
    qspecl_then [‘pi_measure_space n mi’,‘λi. fi i ∘ C LET i’,‘count n’]
        (irule o SIMP_RULE (srw_ss ()) [LET_THM]) integrable_sum' >>
    simp[prob_space_sigma_finite_measure_space,measure_space_pi_measure_space] >>
    rw[] >> irule integrable_pi_dim >> simp[]
QED

(* convoluted measure finagling *)

Theorem pi_measure_rect:
    ∀n mi E. (∀i. i < n ⇒ sigma_finite_measure_space (mi i)) ∧
        E ∈ (count n) ⟶ measurable_sets ∘ mi ⇒
        pi_measure n mi
          (BIGINTER (IMAGE (λi. PREIMAGE (C LET i) (E i) ∩ m_space (pi_measure_space n mi)) (count n))) =
        ∏ (λi. measure (mi i) (E i)) (count n)
Proof
    Induct_on ‘n’ >> rw[] >- simp[pi_measure_def,indicator_fn_def,EXTREAL_PROD_IMAGE_EMPTY] >>
    Cases_on ‘n = 0’
    >- (simp[COUNT_ONE,EXTREAL_PROD_IMAGE_SING] >>
        qspecl_then [‘0’,‘mi’,‘m_space (pi_measure_space n mi)’,‘E 0’] mp_tac pi_measure_pi_cross >>
        simp[] >> fs[DFUNSET,pi_measure_space_space] >>
        ‘pi_measure 0 mi (m_space (pi_measure_space 0 mi)) = 1’
            by simp[pi_measure_def,indicator_fn_def,in_m_space_pi_measure_space_recur] >>
        pop_assum SUBST1_TAC >> simp[] >> DISCH_THEN $ SUBST1_TAC o SYM >> irule IRULER >>
        simp[ONE,EXTENSION,in_m_space_pi_measure_space_recur,pi_cross_def,pi_pair_def,
            PULL_EXISTS,Excl "REDUCE_CONV (arithmetic reduction)"] >>
        rw[] >> eq_tac >> DISCH_TAC >> fs[] >> qexists_tac ‘e’ >> fs[UPDATE_APPLY] >>
        irule MEASURE_SPACE_IN_MSPACE >> simp[] >> qexists_tac ‘E 0’ >> simp[]) >>
    simp[COUNT_SUC,EXTREAL_PROD_IMAGE_PROPERTY] >>
    first_x_assum $ qspecl_then [‘mi’,‘E’] assume_tac >> rfs[DFUNSET] >>
    pop_assum $ SUBST1_TAC o SYM >> simp[Once mul_comm] >>
    ‘BIGINTER (IMAGE (λi. PREIMAGE (C LET i) (E i) ∩ m_space (pi_measure_space n mi)) (count n)) ∈
      measurable_sets (pi_measure_space n mi)’ by (
        qspecl_then
            [‘pi_measure_space n mi’,‘λi. PREIMAGE (C LET i) (E i) ∩ m_space (pi_measure_space n mi)’,‘count n’]
            mp_tac MEASURE_SPACE_FINITE_INTER >>
        simp[] >> DISCH_THEN irule >> simp[measure_space_pi_measure_space] >> rw[] >>
        drule idx_measurable_msp >> simp[IN_MEASURABLE]) >>
    simp[GSYM pi_measure_pi_cross] >> pop_assum kall_tac >> irule IRULER >>
    simp[EXTENSION,IN_BIGINTER_IMAGE,in_m_space_pi_measure_space_recur,pi_cross_def,pi_pair_def,PULL_EXISTS] >>
    qx_gen_tac ‘xi’ >> eq_tac >> DISCH_TAC >> gvs[UPDATE_APPLY] >- metis_tac[] >>
    first_x_assum (fn th => map_every (fn n => assume_tac $ cj n th) [1,2]) >>
    pop_assum $ qspec_then `0` assume_tac >> rfs[] >>
    NTAC 2 (qexistsl_tac [‘f’,‘e’] >>  simp[] >>
        irule_at Any MEASURE_SPACE_IN_MSPACE >> simp[] >> qexists_tac ‘E n’ >> rw[])
QED

Theorem pi_prob_rect:
    ∀n mi E N. (∀i. i < n ⇒ prob_space (mi i)) ∧ E ∈ N ⟶ measurable_sets ∘ mi ∧ N ⊆ count n ∧ N ≠ ∅ ⇒
        pi_measure n mi (BIGINTER (IMAGE (λi. PREIMAGE (C LET i) (E i) ∩ m_space (pi_measure_space n mi)) N)) =
        ∏ (λi. measure (mi i) (E i)) N
Proof
    rw[] >> qabbrev_tac ‘EP = (λi. if i ∈ N then E i else m_space (mi i))’ >>
    qspecl_then [‘n’,‘mi’,‘EP’] assume_tac pi_measure_rect >>
    ‘∀x1:extreal x2 x3 x4. x2 = x3 ∧ x1 = x2 ∧ x3 = x4 ⇒ x1 = x4’ by simp[] >>
    pop_assum $ pop_assum o C (resolve_then (Pos hd) irule) >>
    irule_at Any EXTREAL_PROD_IMAGE_EQ_INTER >> simp[prob_space_sigma_finite_measure_space] >>
    drule_at_then Any (irule_at Any) SUBSET_FINITE_I >> fs[SUBSET_DEF,DFUNSET] >>
    irule_at Any IRULER >> reverse $ rw[]
    >- (rw[Abbr ‘EP’] >> irule MEASURE_SPACE_SPACE >> simp[prob_space_measure_space])
    >- (first_x_assum drule >> simp[])
    >- fs[Abbr ‘EP’,prob_space_def]
    >- simp[Abbr ‘EP’] >>
    simp[Once EXTENSION,IN_BIGINTER_IMAGE] >> qx_gen_tac ‘xi’ >> simp[Abbr ‘EP’] >>
    REVERSE eq_tac >> DISCH_TAC >> qx_gen_tac ‘i’ >> DISCH_TAC
    >- (NTAC 2 $ first_x_assum $ drule_then assume_tac >> rfs[]) >>
    fs[GSYM MEMBER_NOT_EMPTY] >> first_assum $ drule_then assume_tac o cj 2 >>
    rw[] >> simp[in_m_space_pi_measure_space_lt,SF SFY_ss]
QED

Theorem pi_prob_dim:
    ∀n mi s j. j < n ∧ (∀i. i < n ⇒ prob_space (mi i)) ∧ s ∈ measurable_sets (mi j) ⇒
        pi_measure n mi (PREIMAGE (C LET j) s ∩ m_space (pi_measure_space n mi)) = measure (mi j) s
Proof
    rw[] >> qspecl_then [‘n’,‘mi’,‘K s’,‘{j}’] mp_tac pi_prob_rect >>
    simp[EXTREAL_PROD_IMAGE_SING,DFUNSET]
QED

Theorem pi_measure_space_dim_indep_vars:
    ∀n mi X A. (∀i. i < n ⇒ prob_space (mi i)) ∧ (∀i. i < n ⇒ random_variable (X i) (mi i) (A i)) ⇒
        indep_vars (pi_measure_space n mi) (λi. X i ∘ C LET i) A (count n)
Proof
    rw[indep_vars_def,DFUNSET,indep_events_def] >> simp[SF PROB_ss] >>
    qabbrev_tac ‘PreX = (λi. PREIMAGE (X i) (E i) ∩ m_space (mi i))’ >>
    qspecl_then [‘n’,‘mi’,‘PreX’,‘N’] assume_tac pi_prob_rect >>
    ‘∀x1:extreal x2 x3 x4. x2 = x3 ∧ x1 = x2 ∧ x3 = x4 ⇒ x1 = x4’ by simp[] >>
    pop_assum $ pop_assum o C (resolve_then (Pos hd) irule) >> simp[measure_pi_measure_space] >>
    map_every (irule_at Any) [EXTREAL_PROD_IMAGE_EQ,IRULER,IRULER] >> rw[]
    >- (simp[Abbr ‘PreX’] >> irule IMAGE_CONG >> rw[] >>
        irule PREIMAGE_o_INTER >>
        gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[in_m_space_pi_measure_space_lt])
    >- (simp[Abbr ‘PreX’] >> rename [‘i ∈ N’] >>
        ‘IMAGE (C LET i) (m_space (pi_measure_space n mi)) ⊆ m_space (mi i)’ by (
            gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[in_m_space_pi_measure_space_lt]) >>
        qspecl_then [‘m_space (pi_measure_space n mi)’,‘m_space (mi i)’,‘C LET i’,‘X i’,‘E i’]
            mp_tac PREIMAGE_o_INTER >>
        simp[] >> DISCH_THEN kall_tac >> irule $ GSYM pi_prob_dim >>
        fs[SUBSET_DEF,random_variable_def,IN_MEASURABLE,SF PROB_ss])
    >- (rw[Abbr ‘PreX’,DFUNSET] >> fs[SUBSET_DEF,random_variable_def,IN_MEASURABLE,SF PROB_ss])
QED

(* Infinite Measure Spaces *)

Definition inf_pi_rect_def:
    inf_pi_rect si = UNIV --> si
End

Theorem in_inf_pi_rect:
    ∀si f. f ∈ inf_pi_rect si ⇔ ∀i. f i ∈ si i
Proof
    simp[IN_APP,inf_pi_rect_def]
QED

Definition inf_pi_rect_sets_def:
    inf_pi_rect_sets = IMAGE inf_pi_rect ∘ inf_pi_rect
End

Definition inf_pi_sigma_def:
    inf_pi_sigma sai = sigma (inf_pi_rect (space ∘ sai)) (inf_pi_rect_sets (subsets ∘ sai))
End

Theorem SUBSET_inf_pi_rect:
    ∀si ti. (∀i. si i ⊆ ti i) ⇒ inf_pi_rect si ⊆ inf_pi_rect ti
Proof
    simp[SUBSET_DEF,in_inf_pi_rect]
QED

Theorem subset_class_inf_pi_rect_sets:
    ∀sai. (∀i. subset_class (space (sai i)) (subsets (sai i))) ⇒
       subset_class (inf_pi_rect (space ∘ sai)) (inf_pi_rect_sets (subsets ∘ sai))
Proof
    rw[subset_class_def,inf_pi_rect_sets_def] >> rename [‘inf_pi_rect si’] >>
    irule SUBSET_inf_pi_rect >> gs[in_inf_pi_rect]
QED

Theorem sigma_algebra_inf_pi_sigma:
    ∀sai. (∀i. subset_class (space (sai i)) (subsets (sai i))) ⇒
       sigma_algebra (inf_pi_sigma sai)
Proof
    rw[inf_pi_sigma_def] >> irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_inf_pi_rect_sets]
QED

(* Omnidimensional Cyclinders *)

Definition J_cylinders_def:
    J_cylinders J = {s | ∀x y. (∀i. i ∈ J ⇒ x i = y i) ⇒ (x ∈ s ⇔ y ∈ s)}
End

Definition bounded_J_cylinders_def:
    bounded_J_cylinders sj J =
        {s ∩ inf_pi_rect sj | ∀x y. (∀i. i ∈ J ⇒ x i = y i) ⇒ (x ∈ s ⇔ y ∈ s)}
End

Definition set_cylinder_def:
    set_cylinder (n:num) f s = {y | ∃x. x ∈ s ∧ ∀i. i < n ⇒ y (f i) = x i}
End

Definition bounded_set_cylinder_def:
    bounded_set_cylinder sj (n:num) f s = {y | y ∈ UNIV --> sj ∧ ∃x. x ∈ s ∧ ∀i. i < n ⇒ y (f i) = x i}
End

Theorem J_cylinders_alt_imp:
    ∀J. J_cylinders J = {s | ∀x y. (∀i. i ∈ J ⇒ x i = y i) ∧ x ∈ s ⇒ y ∈ s}
Proof
    simp[J_cylinders_def,EXTENSION] >> metis_tac[]
QED

Theorem bounded_J_cylinders_alt_imp:
    ∀sj J. bounded_J_cylinders sj J =
        {s ∩ inf_pi_rect sj | ∀x y. (∀i. i ∈ J ⇒ x i = y i) ∧ x ∈ s ⇒ y ∈ s}
Proof
    simp[bounded_J_cylinders_def,Once EXTENSION] >> rpt gen_tac >> eq_tac >> disch_tac >>
    gvs[] >> qexists_tac ‘s’ >> metis_tac[]
QED

Theorem bounded_J_cylinders_alt:
    ∀sj J. bounded_J_cylinders sj J = IMAGE (λs. s ∩ inf_pi_rect sj) (J_cylinders J)
Proof
    simp[Once EXTENSION,IN_IMAGE,J_cylinders_def,bounded_J_cylinders_def]
QED

Theorem bounded_set_cylinder_alt:
    ∀sj n f s. bounded_set_cylinder sj n f s = set_cylinder n f s ∩ inf_pi_rect sj
Proof
    rw[EXTENSION,set_cylinder_def,bounded_set_cylinder_def,inf_pi_rect_def] >> metis_tac[]
QED

Theorem bounded_J_cylinders_alt_res_imp:
    ∀sj J. bounded_J_cylinders sj J =
        {r | ∃s. s ∩ inf_pi_rect sj = r ∧
          ∀x y. x ∈ inf_pi_rect sj ∧ y ∈ inf_pi_rect sj ∧ (∀i. i ∈ J ⇒ x i = y i) ∧ x ∈ s ⇒ y ∈ s}
Proof
    simp[bounded_J_cylinders_alt_imp,Once EXTENSION] >> rpt gen_tac >> eq_tac >> disch_tac >>
    gvs[] >- (qexists_tac ‘s’ >> metis_tac[]) >>
    qexists_tac ‘{x | ∃z. z ∈ s ∧ z ∈ inf_pi_rect sj ∧ ∀i. i ∈ J ⇒ x i = z i}’ >>
    rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]
QED

Theorem set_cylinder_J_cylinder:
    ∀n f s. set_cylinder n f s ∈ J_cylinders (IMAGE f (count n))
Proof
    rw[J_cylinders_def,set_cylinder_def] >> metis_tac[]
QED

Theorem bounded_set_cylinder_bounded_J_cylinder:
    ∀sj n f s. bounded_set_cylinder sj n f s ∈ bounded_J_cylinders sj (IMAGE f (count n))
Proof
    rw[bounded_J_cylinders_def,Excl "IN_IMAGE"] >> irule_at Any bounded_set_cylinder_alt >>
    simp[SIMP_RULE (srw_ss()) [J_cylinders_def,Excl "IN_IMAGE"] set_cylinder_J_cylinder]
QED

Theorem space_rect_cyl_inj_empty_dim:
    ∀sj n f s. (∃j. sj j = ∅) ⇒ bounded_set_cylinder sj n f s = ∅
Proof
    rw[EXTENSION,bounded_set_cylinder_def,DFUNSET] >> metis_tac[]
QED

Theorem J_cylinders_SUBSET:
    ∀Js Jt. Js ⊆ Jt ⇒ J_cylinders Js ⊆ J_cylinders Jt
Proof
    rw[SUBSET_DEF,J_cylinders_def]
QED

Theorem J_cylinders_INTER:
    ∀Js Jt. J_cylinders Js ∩ J_cylinders Jt = J_cylinders (Js ∩ Jt)
Proof
    rw[EXTENSION,EQ_IMP_THM] >| [fs[J_cylinders_alt_imp],fs[J_cylinders_def],fs[J_cylinders_def]] >>
    rpt gen_tac >> rename [‘_ ∧ x ∈ s ⇒ y ∈ s’] >> rw[] >>
    last_x_assum irule >> qexists_tac ‘λi. if i ∈ Js then y i else x i’ >> simp[] >>
    last_x_assum irule >> first_x_assum $ irule_at Any >> rw[]
QED

Theorem IN_J_cylinders_INTER:
    ∀s t Js Jt. s ∈ J_cylinders Js ∧ t ∈ J_cylinders Jt ⇒ s ∩ t ∈ J_cylinders (Js ∪ Jt)
Proof
    rw[J_cylinders_alt_imp] >> metis_tac[]
QED

Theorem bounded_J_cylinders_INTER:
    ∀sj Js Jt. bounded_J_cylinders sj Js ∩ bounded_J_cylinders sj Jt = bounded_J_cylinders sj (Js ∩ Jt)
Proof
    rw[] >> irule SUBSET_ANTISYM >> reverse conj_tac
    >- simp[bounded_J_cylinders_alt,GSYM J_cylinders_INTER,IMAGE_INTER] >>
    rw[bounded_J_cylinders_alt_res_imp,SUBSET_DEF,J_cylinders_alt_imp] >>
    rename [‘s ∩ inf_pi_rect sj = t ∩ inf_pi_rect sj’] >> qexists_tac ‘s’ >> rw[] >>
    ‘(∀z. z ∈ inf_pi_rect sj ∧ z ∈ s ⇒ z ∈ t) ∧ (∀z. z ∈ inf_pi_rect sj ∧ z ∈ t ⇒ z ∈ s)’
        by (fs[EXTENSION] >> metis_tac[]) >>
    ‘(λi. if i ∈ Js then y i else x i) ∈ t ∩ inf_pi_rect sj’ by (simp[] >>
        last_x_assum $ irule_at Any >> last_assum $ irule_at Any >> gvs[in_inf_pi_rect] >> rw[]) >>
    fs[] >> first_x_assum $ drule_all_then assume_tac >>
    last_x_assum $ irule_at Any >> simp[PULL_EXISTS] >> first_x_assum $ irule_at Any >> rw[]
QED

Theorem J_cylinder_set_cylinder:
    ∀J r. FINITE J ∧ r ∈ J_cylinders J ⇒
        ∃n f s. INJ f (count n) UNIV ∧ J = IMAGE f (count n) ∧
            r = set_cylinder n f s
Proof
    rw[] >> drule_all_then strip_assume_tac FINITE_BIJ_COUNT >> rename[‘BIJ f (count n)’] >>
    drule_then strip_assume_tac BIJ_INV >>
    qexistsl_tac [‘n’,‘f’,‘{x | (λj. if j ∈ J then x (g j) else ARB) ∈ r}’] >>
    simp[BIJ_IMAGE] >> irule_at Any INJ_SUBSET >> irule_at Any $ cj 1 $ iffLR BIJ_DEF >>
    first_assum $ irule_at Any >> gs[EXTENSION,set_cylinder_def,J_cylinders_alt_imp] >>
    qx_gen_tac ‘y’ >> eq_tac >> rw[]
    >| [qexists_tac ‘y ∘ f’ >> simp[],all_tac] >>
    NTAC 2 $ last_x_assum $ irule_at Any >> rw[] >>
    ‘g i < n’ by fs[BIJ_ALT,FUNSET,IN_COUNT] >>
    first_x_assum $ drule_then assume_tac >> pop_assum $ SUBST1_TAC o SYM >>
    AP_TERM_TAC >> simp[]
QED

Theorem bounded_J_cylinder_bounded_set_cylinder:
    ∀sj J r. FINITE J ∧ r ∈ bounded_J_cylinders sj J ⇒
        ∃n f s. INJ f (count n) UNIV ∧ J = IMAGE f (count n) ∧
            r = bounded_set_cylinder sj n f s
Proof
    rw[bounded_J_cylinders_alt,bounded_set_cylinder_alt,IN_IMAGE] >> rename [‘r ∈ J_cylinders J’] >>
    drule_all_then strip_assume_tac J_cylinder_set_cylinder >>
    qexistsl_tac [‘n’,‘f’,‘s’] >> simp[]
QED

Theorem bounded_set_cylinder_dim_INTER:
    ∀sj m n f g s t. bounded_set_cylinder sj n g t = bounded_set_cylinder sj m f s ⇒
        ∃l h r. INJ h (count l) UNIV ∧ IMAGE f (count m) ∩ IMAGE g (count n) = IMAGE h (count l) ∧
            bounded_set_cylinder sj m f s = bounded_set_cylinder sj l h r ∧
            bounded_set_cylinder sj n g t = bounded_set_cylinder sj l h r
Proof
    rw[] >>
    map_every (fn thm => qspecl_then thm assume_tac bounded_set_cylinder_bounded_J_cylinder)
        [[‘sj’,‘m’,‘f’,‘s’],[‘sj’,‘n’,‘g’,‘t’]] >>
    gvs[] >>
    dxrule_all_then assume_tac $ iffLR $ SRULE [Once EXTENSION] bounded_J_cylinders_INTER >>
    ‘FINITE (IMAGE g (count n) ∩ IMAGE f (count m))’ by simp[INTER_FINITE,FINITE_COUNT] >>
    drule_all_then assume_tac bounded_J_cylinder_bounded_set_cylinder >> metis_tac[INTER_COMM]
QED

Theorem bounded_set_cylinder_dim_SUBSET:
    ∀sj m n f g s t. bounded_set_cylinder sj n g t = bounded_set_cylinder sj m f s ∧
        INJ f (count m) UNIV ∧ INJ g (count n) UNIV ∧ IMAGE f (count m) ⊆ IMAGE g (count n) ⇒
        ∃h hf hg r. INJ h (count n) UNIV ∧
            hf PERMUTES (count m) ∧ hg PERMUTES (count n) ∧
            (∀i. i < m ⇒ f i = h (hf i)) ∧ (∀i. i < n ⇒ g i = h (hg i)) ∧
            IMAGE f (count m) = IMAGE h (count m) ∧ IMAGE g (count n) = IMAGE h (count n) ∧
            bounded_set_cylinder sj m f s = bounded_set_cylinder sj m h r ∧
            bounded_set_cylinder sj n g t = bounded_set_cylinder sj n h r
Proof
    rw[] >> drule_all_then assume_tac INJ_COUNT_SUBSET_LE >>
    ‘BIJ f (count m) (IMAGE f (count m)) ∧ BIJ g (count n) (IMAGE g (count n))’
        by simp[INJ_IMAGE_BIJ,SF SFY_ss] >>
    qspecl_then [‘{i | m ≤ i ∧ i < n}’,‘IMAGE g (count n) DIFF IMAGE f (count m)’] concl_tac FINITE_CARD_BIJ
    >- (‘{i | m ≤ i ∧ i < n} = count n DIFF count m’ by simp[EXTENSION] >>
        pop_assum SUBST1_TAC >> NTAC 2 $ irule_at Any FINITE_DIFF >>
        dxrule_then assume_tac COUNT_MONO >> simp[IMAGE_FINITE,SUBSET_INTER2] >>
        resolve_then Any (NTAC 2 o dxrule_then assume_tac) (cj 1 $ iffLR BIJ_DEF) INJ_CARD_IMAGE >> gs[]) >>
    gs[] >> rename [‘BIJ cf _ _’] >>
    map_every qabbrev_tac [‘ign = IMAGE g (count n)’,‘ifm = IMAGE f (count m)’] >>
    qspec_then ‘f’ assume_tac BIJ_INV >> pop_assum $ drule_then assume_tac >> fs[] >> rename [‘BIJ fi’] >>
    qspec_then ‘cf’ assume_tac BIJ_INV >> pop_assum $ drule_then assume_tac >> fs[] >> rename [‘BIJ cfi’] >>
    map_every qabbrev_tac [‘h = (λi. if i < m then f i else cf i)’,
        ‘hg = (λj. if j ∈ ifm then fi j else cfi j) ∘ g’,
        ‘r = {x | ∃y. y ∈ s ∧ ∀i. i < m ⇒ y i = x i}’] >>
    qexistsl_tac [‘h’,‘I’,‘hg’,‘r’] >> simp[BIJ_I] >> rpt conj_asm1_tac
    >- (rpt $ qpat_x_assum ‘INJ _ _ _’ kall_tac >> rpt $ qpat_x_assum ‘∀x. _’ kall_tac >>
        simp[INJ_DEF,Abbr ‘h’] >> qx_genl_tac [‘i’,‘j’] >> rw[]
        >- (rpt $ dxrule_then assume_tac $ cj 1 $ iffLR BIJ_DEF >> fs[INJ_DEF])
        >- (gvs[NOT_LESS,BIJ_ALT,FUNSET] >> metis_tac[])
        >- (gvs[NOT_LESS,BIJ_ALT,FUNSET] >> metis_tac[])
        >- (rpt $ dxrule_then assume_tac $ cj 1 $ iffLR BIJ_DEF >> fs[INJ_DEF]))
    >- (irule FINITE_SURJ_BIJ >> simp[SURJ_DEF] >> conj_tac
        >- (qx_gen_tac ‘i’ >> reverse $ rw[Abbr ‘hg’] >- fs[BIJ_ALT,FUNSET] >>
            irule LESS_LESS_EQ_TRANS >> qexists_tac ‘m’ >> fs[BIJ_ALT,FUNSET]) >>
        qspec_then ‘g’ assume_tac BIJ_INV >> pop_assum $ drule_then assume_tac >> fs[] >> rename [‘BIJ gi’] >>
        qx_gen_tac ‘j’ >> rw[Abbr ‘hg’] >> Cases_on ‘j < m’ >> fs[BIJ_ALT,FUNSET,SUBSET_DEF]
        >- (qexists_tac ‘gi (f j)’ >> simp[])
        >- (fs[NOT_LESS] >> qexists_tac ‘gi (cf j)’ >> simp[]))
    >- (simp[Abbr ‘h’])
    >- (simp[Abbr ‘h’,Abbr ‘hg’] >> qx_gen_tac ‘i’ >> disch_tac >>
        Cases_on ‘g i ∈ ifm’ >> simp[]
        >- (‘fi (g i) < m’ by fs[BIJ_ALT,FUNSET] >> simp[]) >>
        ‘g i ∈ ign’ by fs[BIJ_ALT,FUNSET] >> ‘¬(cfi (g i) < m)’ suffices_by simp[] >>
        fs[NOT_LESS,BIJ_ALT,FUNSET])
    >- (simp[Abbr ‘ifm’] >> irule IMAGE_CONG >> simp[])
    >- (simp[Abbr ‘ign’] >>
        qspecl_then [‘h’,‘hg’,‘count n’] mp_tac $
            INST_TYPE [“:α” |-> “:num”,“:β” |-> “:α”,“:γ” |-> “:num”] IMAGE_IMAGE >>
        ‘IMAGE hg (count n) = count n’ by fs[BIJ_DEF,IMAGE_SURJ] >>
        pop_assum SUBST1_TAC >> disch_then SUBST1_TAC >>
        irule IMAGE_CONG >> simp[])
    >- (simp[bounded_set_cylinder_def,Abbr ‘r’,EXTENSION] >>
        qx_gen_tac ‘z’ >> rw[EQ_IMP_THM] >- NTAC 2 (qexists_tac ‘x’ >> simp[]) >>
        first_x_assum $ irule_at Any >> simp[])
    >- (simp[bounded_set_cylinder_def,Abbr ‘r’,EXTENSION] >>
        qx_gen_tac ‘z’ >> rw[EQ_IMP_THM] >>
        qexists_tac ‘λi. if i < m then y i else z (h i)’ >> rw[] >>
        first_x_assum $ irule_at Any >> simp[])
QED

Theorem bounded_set_cylinder_dim_le:
    ∀sj m n f s. m ≤ n ⇒ bounded_set_cylinder sj n f s ⊆ bounded_set_cylinder sj m f s
Proof
    rw[] >> simp[SUBSET_DEF,bounded_set_cylinder_def] >> qx_gen_tac ‘z’ >> rw[] >>
    first_x_assum $ irule_at Any >> simp[]
QED

Theorem bounded_set_cylinder_dim_range:
    ∀sj l m n f s. m ≤ l ∧ l ≤ n ∧ bounded_set_cylinder sj n f s = bounded_set_cylinder sj m f s ⇒
        bounded_set_cylinder sj l f s = bounded_set_cylinder sj m f s
Proof
    metis_tac[bounded_set_cylinder_dim_le,SUBSET_ANTISYM]
QED

Definition measurable_cylinders_def:
    measurable_cylinders saj = BIGUNION (IMAGE (bounded_J_cylinders (space ∘ saj)) FINITE) ∩
        subsets (inf_pi_sigma saj)
End

Theorem subset_class_measurable_cylinders:
    ∀saj. subset_class (inf_pi_rect (space ∘ saj)) (measurable_cylinders saj)
Proof
    rw[subset_class_def,measurable_cylinders_def,IN_BIGUNION_IMAGE,bounded_J_cylinders_def] >>
    simp[INTER_SUBSET]
QED

Definition cylinder_sigma_def:
    cylinder_sigma saj = sigma (inf_pi_rect (space ∘ saj)) (measurable_cylinders saj)
End

Theorem sigma_algebra_cyclinder_sigma:
    ∀saj. sigma_algebra (cylinder_sigma saj)
Proof
    rw[cylinder_sigma_def] >> irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_measurable_cylinders]
QED

Definition set_cyl_premeasure_def:
    set_cyl_premeasure mi n s =
        pi_measure n mi (bounded_set_cylinder (λi. if i < n then m_space (mi i) else {ARB}) n I s)
End

(*
Theorem set_cyl_premeasure_unique_dim_cong:
    ∀pj m n f g s t. n = m ∧ (∀i. i < m ⇒ g i = f i) ∧
        IMAGE (λx i. if i < m then x i else ARB) t = IMAGE (λx i. if i < m then x i else ARB) s ⇒
        set_cyl_premeasure pj n g t = set_cyl_premeasure pj m f s
Proof
    cheat
QED
*)

Theorem set_cyl_premeasure_unique_dim_perm:
    ∀pj n f g h s t. h PERMUTES (count n) ∧ (∀i. i < n ⇒ g i = f (h i)) ∧
        bounded_set_cylinder (m_space ∘ pj) n g t = bounded_set_cylinder (m_space ∘ pj) n f s ⇒
        set_cyl_premeasure (pj ∘ g) n t = set_cyl_premeasure (pj ∘ f) n s
Proof
    cheat
QED


Theorem set_cyl_premeasure_unique_dim_count_SUC:
    ∀pj n f s. (∀j. prob_space (pj j)) ∧ INJ f (count (SUC n)) UNIV ∧
        bounded_set_cylinder (m_space ∘ pj) (SUC n) f s = bounded_set_cylinder (m_space ∘ pj) n f s ⇒
        set_cyl_premeasure (pj ∘ f) (SUC n) s = set_cyl_premeasure (pj ∘ f) n s
Proof
    rw[set_cyl_premeasure_def] >> qmatch_abbrev_tac ‘pi_measure _ mi r = _ _ _ t’ >>
    simp[pi_measure_def] >>
    ‘t ∈ measurable_sets (pi_measure_space n mi)’ by cheat >>
    ‘measure_space (pi_measure_space n mi)’ by (simp[Abbr ‘mi’] >>
        irule measure_space_pi_measure_space >> rw[prob_space_sigma_finite_measure_space]) >>
    drule_all_then (SUBST1_TAC o SYM o SRULE[measure_pi_measure_space]) pos_fn_integral_indicator >>
    ‘prob_space (mi n)’ by simp[Abbr ‘mi’] >> pop_assum $ assume_tac o SRULE [prob_space_def] >>
    ‘0 ≤ ∫⁺ (pi_measure_space n mi) (𝟙 t)’ by (
        irule pos_fn_integral_pos >> simp[INDICATOR_FN_POS]) >>
    qabbrev_tac ‘c = ∫⁺ (pi_measure_space n mi) (𝟙 t)’ >>
    qspecl_then [‘mi n’,‘c’] mp_tac pos_fn_integral_const >> fs[] >>
    disch_then $ SUBST1_TAC o SYM >> irule pos_fn_integral_cong >> csimp[] >>
    qx_gen_tac ‘e’ >> rw[Abbr ‘c’] >> irule pos_fn_integral_cong >>
    csimp[INDICATOR_FN_POS] >> qx_gen_tac ‘h’ >>
    ‘∃ej. ∀j. ej j ∈ m_space (pj j)’ by (simp[GSYM SKOLEM_THM] >>
        qx_gen_tac ‘j’ >> simp[MEMBER_NOT_EMPTY] >> CCONTR_TAC >>
        fs[] >> last_x_assum $ qspec_then ‘j’ assume_tac >>
        gs[prob_space_def,MEASURE_EMPTY]) >>
    ‘BIJ f (count (SUC n)) (IMAGE f (count (SUC n)))’ by (
        irule INJ_IMAGE_BIJ >> qexists_tac ‘UNIV’ >> simp[]) >>
    dxrule_then strip_assume_tac BIJ_INV >> rename [‘BIJ fi _ _’] >>
    rw[indicator_fn_eq,EQ_IMP_THM]
    >- (‘(λj. if j ∈ IMAGE f (count (SUC n)) then pi_pair (SUC n) h e (fi j) else ej j) ∈
          bounded_set_cylinder (m_space ∘ pj) (SUC n) f s’ by (pop_assum mp_tac >>
            simp[Abbr ‘r’,bounded_set_cylinder_def,DFUNSET,pi_pair_def] >> rw[]
            >- (ntac 2 $ pop_assum kall_tac >> rw[] >> rename [‘i < SUC n’] >>
                fs[] >> first_x_assum $ qspec_then ‘i’ mp_tac >> simp[]) >>
            first_x_assum $ irule_at Any >> qx_gen_tac ‘i’ >> rw[] >>
            fs[] >> first_x_assum $ qspec_then ‘i’ mp_tac >> simp[]) >>
        last_x_assum $ SUBST_ALL_TAC >> pop_assum mp_tac >>
        simp[Abbr ‘t’,bounded_set_cylinder_def,DFUNSET,pi_pair_def] >> rw[]
        >- (ntac 2 $ pop_assum kall_tac >> rw[]
            >- (drule_all in_m_space_pi_measure_space_lt >> simp[Abbr ‘mi’])
            >- (fs[NOT_LESS] >> drule_all in_m_space_pi_measure_space_ge >> simp[Abbr ‘mi’])) >>
        first_x_assum $ irule_at Any >> qx_gen_tac ‘i’ >> rw[] >>
        first_x_assum $ drule >> fs[UPDATE_APPLY] >>
        ‘∃x. f i = f x ∧ x < SUC n’ suffices_by simp[] >> qexists_tac ‘i’ >> simp[])
    >- (‘(λj. if j ∈ IMAGE f (count (SUC n)) then pi_pair (SUC n) h e (fi j) else ej j) ∈
          bounded_set_cylinder (m_space ∘ pj) n f s’ by (pop_assum mp_tac >>
            simp[Abbr ‘t’,bounded_set_cylinder_def,DFUNSET,pi_pair_def] >> rw[]
            >- (ntac 2 $ pop_assum kall_tac >> rw[] >> fs[Abbr ‘mi’] >>
                rename [‘i < SUC n’] >> Cases_on ‘i = n’ >> fs[UPDATE_APPLY] >>
                first_x_assum $ qspec_then ‘i’ mp_tac >> simp[]) >>
            first_x_assum $ irule_at Any >> qx_gen_tac ‘i’ >> rw[] >>
            fs[UPDATE_APPLY] >> first_x_assum $ qspec_then ‘i’ mp_tac >> simp[]) >>
        last_x_assum $ SUBST_ALL_TAC o SYM >> pop_assum mp_tac >>
        simp[Abbr ‘r’,bounded_set_cylinder_def,DFUNSET,pi_pair_def] >> rw[]
        >- (ntac 2 $ pop_assum kall_tac >> ‘i < n ∨ i = n ∨ n < i’ by simp[] >> fs[UPDATE_APPLY,Abbr ‘mi’]
            >- (drule_all in_m_space_pi_measure_space_lt >> simp[])
            >- (drule_at Any in_m_space_pi_measure_space_ge >> simp[])) >>
        first_x_assum $ irule_at Any >> qx_gen_tac ‘i’ >> rw[] >>
        first_x_assum $ drule >> fs[] >>
        ‘∃x. f i = f x ∧ x < SUC n’ suffices_by simp[] >> qexists_tac ‘i’ >> simp[])
QED

Theorem set_cyl_premeasure_unique_dim_count_le:
    ∀pj m n f s. (∀j. prob_space (pj j)) ∧ m ≤ n ∧ INJ f (count n) UNIV ∧
        bounded_set_cylinder (m_space ∘ pj) n f s = bounded_set_cylinder (m_space ∘ pj) m f s ⇒
        set_cyl_premeasure (pj ∘ f) n s = set_cyl_premeasure (pj ∘ f) m s
Proof
    NTAC 3 gen_tac >> Induct_on ‘n - m’ >- (rw[] >> ‘m = n’ by simp[] >> gvs[]) >>
    rw[] >> rename [‘SUC l = _’] >> ‘l = n - SUC m’ by simp[] >>
    last_x_assum $ dxrule_then assume_tac >> pop_assum $ qspecl_then [‘f’,‘s’] assume_tac >>
    rfs[] >> irule EQ_TRANS >> pop_assum $ irule_at Any >>
    irule_at Any set_cyl_premeasure_unique_dim_count_SUC >> csimp[EQ_SYM] >>
    conj_tac >- (fs[INJ_DEF]) >> irule $ GSYM bounded_set_cylinder_dim_range >>
    simp[] >> qexists_tac ‘n’ >> simp[]
QED

Theorem set_cyl_premeasure_unique_dim_subset:
    ∀pj m n f g s t. (∀j. prob_space (pj j)) ∧ INJ f (count m) UNIV ∧ INJ g (count n) UNIV ∧
        IMAGE f (count m) ⊆ IMAGE g (count n) ∧
        bounded_set_cylinder (m_space ∘ pj) n g t = bounded_set_cylinder (m_space ∘ pj) m f s ⇒
        set_cyl_premeasure (pj ∘ g) n t = set_cyl_premeasure (pj ∘ f) m s
Proof
    rw[] >> drule_all_then assume_tac INJ_COUNT_SUBSET_LE >>
    drule_then (drule_then assume_tac) bounded_set_cylinder_dim_SUBSET >> gvs[] >>
    chain_irule_at [
        (Any,EQ_TRANS,[‘set_cyl_premeasure (pj ∘ h) m r’],[]),
        (Any,EQ_TRANS,[‘set_cyl_premeasure (pj ∘ h) n r’],[]),
        (Pos last,EQ_SYM,[],[]),
        (Any,set_cyl_premeasure_unique_dim_perm,[‘hf’],[]),
        (Any,set_cyl_premeasure_unique_dim_perm,[‘hg’],[]),
        (Any,set_cyl_premeasure_unique_dim_count_le,[],[])]
QED

Theorem set_cyl_premeasure_unique:
    ∀pj m n f g s t. (∀j. prob_space (pj j)) ∧ INJ f (count m) UNIV ∧ INJ g (count n) UNIV ∧
        bounded_set_cylinder (m_space ∘ pj) n g t = bounded_set_cylinder (m_space ∘ pj) m f s ⇒
        set_cyl_premeasure (pj ∘ g) n t = set_cyl_premeasure (pj ∘ f) m s
Proof
    rw[] >> drule_then assume_tac bounded_set_cylinder_dim_INTER >> gvs[] >>
    irule EQ_TRANS >> qexists_tac ‘set_cyl_premeasure (pj ∘ h) l r’ >>
    irule_at (Pos last) EQ_SYM >> ntac 2 $ irule_at Any set_cyl_premeasure_unique_dim_subset >>
    qpat_x_assum ‘_ ∩ _ = _’ $ SUBST1_TAC o SYM >> simp[]
QED

Theorem cyl_premeasure_spec[local]:
    ∃mu. ∀pj n f s. (∀j. prob_space (pj j)) ∧ INJ f (count n) UNIV ⇒
        mu pj (bounded_set_cylinder (m_space ∘ pj) n f s) = set_cyl_premeasure (pj ∘ f) n s
Proof
    ‘∃mu. ∀pj cyl n g t. (∀j. prob_space (pj j)) ∧ INJ g (count n) UNIV ∧
        cyl = bounded_set_cylinder (m_space ∘ pj) n g t ⇒
        mu pj cyl = set_cyl_premeasure (pj ∘ g) n t’ suffices_by simp[] >>
    simp[GSYM SKOLEM_THM,Once $ GSYM AND_IMP_INTRO] >> rw[RIGHT_FORALL_IMP_THM,RIGHT_EXISTS_IMP_THM] >>
    reverse $ Cases_on ‘∃m f s. INJ f (count m) UNIV ∧ cyl = bounded_set_cylinder (m_space ∘ pj) m f s’
    >- metis_tac[] >> fs[] >> qexists_tac ‘set_cyl_premeasure (pj ∘ f) m s’ >> rw[] >>
    irule set_cyl_premeasure_unique >> simp[]
QED

val cyl_premeasure_def = new_specification ("cyl_premeasure_def", ["cyl_premeasure"], cyl_premeasure_spec);

val _ = export_theory();
