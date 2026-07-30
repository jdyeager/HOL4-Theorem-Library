open HolKernel Parse boolLib bossLib;
open pred_setTheory;
open pairTheory;
open sigma_algebraTheory;

open ex_machina;
open trivialTheory;
open trivialSimps;

val _ = new_theory "natsa";

val _ = augment_srw_ss [TRIVIAL_ss];

Definition natsa_def:
    natsa = (𝕌(:num), POW 𝕌(:num))
End

Theorem SPACE_NATSA:
    space natsa = 𝕌(:num)
Proof
    simp[natsa_def]
QED

Theorem SUBSETS_NATSA:
    subsets natsa = POW 𝕌(:num)
Proof
    simp[natsa_def]
QED

Theorem IN_SPACE_NATSA[simp]:
    ∀n. n ∈ space natsa
Proof
    simp[SPACE_NATSA]
QED

Theorem IN_SUBSETS_NATSA[simp]:
    ∀s. s ∈ subsets natsa
Proof
    simp[SUBSETS_NATSA,GSYM UNIV_FUN_TO_BOOL]
QED

Theorem SUBSET_SUBSETS_NATSA[simp]:
    ∀c. c ⊆ subsets natsa
Proof
    simp[SUBSET_DEF]
QED

Theorem SIGMA_ALGEBRA_NATSA:
    sigma_algebra natsa
Proof
    simp[natsa_def,POW_SIGMA_ALGEBRA]
QED

Theorem MEASURABLE_NATSA:
    ∀a f. (∀x. f x ∈ space a) ⇒ f ∈ measurable natsa a
Proof
    simp[measurable_def,FUNSET]
QED

Theorem MEASURABLE_NATSA_REAL_BOREL:
    ∀f. f ∈ measurable natsa borel
Proof
    rw[] >> irule MEASURABLE_NATSA >> simp[real_borelTheory.space_borel]
QED

Theorem MEASURABLE_NATSA_EXTREAL_BOREL:
    ∀f. f ∈ measurable natsa Borel
Proof
    rw[] >> irule MEASURABLE_NATSA >> simp[borelTheory.SPACE_BOREL]
QED

(* Eliminating natsa (and countable sigalgs generally) *)

Theorem IN_MEASURABLE_PROD_COUNTABLE_ELIM:
    ∀a b c. sigma_algebra a ∧ sigma_algebra b ∧ sigma_algebra c ∧
        countable (space a) ∧ (∀x. x ∈ space a ⇒ {x} ∈ subsets a) ⇒
        ∀f. f ∈ measurable (a × b) c ⇔ ∀x. x ∈ space a ⇒ (λy. f (x,y)) ∈ measurable b c
Proof
    rw[EQ_IMP_THM] >- metis_tac[IN_MEASURABLE_FROM_PROD_SIGMA] >>
    gs[measurable_def,FUNSET] >> conj_tac
    >- (rw[IN_SPACE_PROD_SIGMA] >> metis_tac[PAIR]) >>
    pop_assum $ assume_tac o SRULE [AND_IMP_INTRO,PULL_FORALL] o cj 2 >>
    rw[] >> first_x_assum $ drule_at_then Any assume_tac >>
    qmatch_goalsub_abbrev_tac ‘t ∈ _’ >> qabbrev_tac ‘xs = IMAGE FST t’ >>
    ‘t = BIGUNION (IMAGE (λx. {x} × (PREIMAGE (λy. f (x,y)) s ∩ space b)) xs)’ by (
        simp[Once EXTENSION,Abbr ‘xs’,Abbr ‘t’,
            EXISTS_PROD,PULL_EXISTS,FORALL_PROD,IN_SPACE_PROD_SIGMA] >>
        metis_tac[]) >>
    pop_assum SUBST1_TAC >> irule SIGMA_ALGEBRA_COUNTABLE_UNION >>
    simp[Abbr ‘xs’,SIGMA_ALGEBRA_PROD_SIGMA_WEAK] >>
    irule_at Any image_countable >> irule_at Any subset_countable >>
    first_assum $ irule_at Any >>
    simp[Abbr ‘t’,SUBSET_DEF,IN_IMAGE,PULL_EXISTS,IN_SPACE_PROD_SIGMA,FORALL_PROD] >>
    qx_genl_tac [‘x’,‘y’] >> rw[prod_sigma_def] >> irule IN_SIGMA >>
    simp[IN_PROD_SETS] >> irule_at Any EQ_REFL >> simp[]
QED

Theorem IN_MEASURABLE_PROD_NATSA_ELIM:
    ∀a b. sigma_algebra a ∧ sigma_algebra b ⇒
        ∀f. f ∈ measurable (natsa × a) b ⇔ ∀n. (λx. f (n,x)) ∈ measurable a b
Proof
    rw[] >> qspecl_then [‘natsa’,‘a’,‘b’] assume_tac IN_MEASURABLE_PROD_COUNTABLE_ELIM >>
    gs[SIGMA_ALGEBRA_NATSA]
QED

(* Measurable functions to natsa *)
(* g on cuontable fn mbl α -> natsa: summation, producting, power *)

(*
Theorem IN_NATSA_MEASURABLE_COUNTABLE_AGGREGATE:
    ∀a b ns fn g h. sigma_algebra a ∧ sigma_algebra b ∧ countable ns ∧
        (∀n. n ∈ ns ⇒ fn n ∈ measurable a b)
        (∀x. x ∈ space a ⇒ h x = g (C f x) ns) ⇒
Proof
QED
*)

val _ = export_theory();
