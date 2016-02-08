Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop path finset.


Set Implicit Arguments.
Unset Strict Implicit.

Section Finer.

  Variable T : finType.
  Implicit Type P : {set {set T}}.

  Definition is_finer P1 P2 :=
    [forall (s1 | s1 \in P1), [exists (s2 | s2 \in P2),  s1 \subset s2 ]].

  Lemma is_finerP P1 P2 :
    reflect
      (forall s1,  s1 \in P1 -> exists s2,  s2 \in P2 /\ s1 \subset s2)
      (is_finer P1 P2).
  Proof.
    rewrite /is_finer;  apply (iffP idP).
    - move/forall_inP => H s1 /H{H} /exists_inP [] s2 H1 H2.
      by exists s2.
    - move=> H; apply/forall_inP => s1 /H{H} [] s2 [] H1 H2.
      apply/exists_inP; by exists s2.
  Qed.

  Lemma is_finer_refl : reflexive is_finer.
  Proof. move=> p; apply/is_finerP => s1 H1; by exists s1. Qed.

  Lemma is_finer_trans : transitive is_finer.
  Proof.
    move=> P2 P1 p3 /is_finerP H12 /is_finerP H23.
    apply/is_finerP => s1 /H12{H12} [] s2 [] /H23{H23} [] s3 [] Hs3 H23 H12.
    exists s3; split; first exact: Hs3.
    exact: (subset_trans H12 H23).
  Qed.

End Finer.



Section Restriction.

  Variable T : finType.

  Implicit Type P : {set {set T}}.
  Implicit Types A B S : {set T}.

  Definition rest P S : {set {set T}} := [set B :&: S | B in P] :\ set0.

  Lemma cover_rest P S : cover (rest P S) = cover P :&: S.
  Proof.
    rewrite /cover/rest; apply/setP => x; apply/idP/idP; rewrite !inE.
    - move=> /bigcupP [] A; rewrite !inE => /andP [] HBn0 /imsetP [] B HB HA.
      subst A; rewrite inE => /andP [] HxB HxS.
      rewrite HxS andbT; apply/bigcupP; by exists B.
    - move=> /andP [] /bigcupP [] B HB HxB HxS.
      apply/bigcupP; exists (B :&: S); rewrite !inE; last by rewrite HxB HxS.
      apply/andP; split.
      + apply/set0Pn; exists x; by rewrite inE HxB HxS.
      + apply/imsetP; by exists B.
  Qed.

  Lemma trivIset_rest P S : trivIset P -> trivIset (rest P S).
  Proof.
    move=> /trivIsetP Htriv; apply/trivIsetP => A B; rewrite !inE.
    move=> /andP [] HA /imsetP [] Ap HAp HAtmp; subst A.
    move=> /andP [] HB /imsetP [] Bp HBp HBtmp; subst B.
    apply contraR; rewrite -setI_eq0 => /set0Pn [] x.
    rewrite !inE => /and3P [] /andP [] HxAp HxS HxBp _.
    have /contraR := Htriv Ap Bp HAp HBp; rewrite -setI_eq0 => H.
    suff /H/eqP -> : Ap :&: Bp != set0 by [].
    by apply/set0Pn; exists x; rewrite inE HxAp HxBp.
  Qed.

  Lemma partition_rest P A B :
    A \subset B -> partition P B -> partition (rest P A) A.
  Proof.
    move=> Hsub /and3P [] /eqP Hcov Htriv Hnon0.
    apply/and3P; split.
    - rewrite cover_rest Hcov; by apply/eqP/setIidPr.
    - exact: trivIset_rest.
    - by rewrite/rest !inE eq_refl.
  Qed.

  Lemma pblock0 P x : x \notin cover P -> pblock P x = set0.
  Proof.
    move=> Hx; rewrite /pblock.
    case: pickP => /= [A /andP[PA Ax]| //].
    exfalso; move: Hx; rewrite /cover => /bigcupP; apply.
    by exists A.
  Qed.

  Lemma pblock_rest P S x :
    trivIset P -> x \in S -> pblock (rest P S) x = pblock P x :&: S.
  Proof.
    move=> Htriv HxS.
    case: (boolP (x \in cover P :&: S)); rewrite inE HxS andbT => Hcov.
    - apply def_pblock; first exact: trivIset_rest.
      + rewrite /rest !inE; apply/andP; split.
        * apply/set0Pn; exists x; by rewrite inE HxS andbT mem_pblock.
        * apply/imsetP; exists (pblock P x) => //; exact: pblock_mem.
      + by rewrite inE HxS andbT mem_pblock.
    - rewrite (pblock0 Hcov) set0I.
      apply pblock0; by rewrite cover_rest inE negb_and Hcov.
  Qed.

  Lemma rest_pblock_def P A B :
    A \subset B -> partition P B -> rest P A = [set pblock P x :&: A | x in A].
  Proof.
    move=> Hsub HP.
    apply/setP => S; rewrite !inE.
    case: (altP (S =P set0)) => /= [-> | HSn0].
    - apply esym; apply negbTE; apply (introN idP) => /imsetP [] x Hx.
      move=> /setP/(_ x); rewrite !inE Hx mem_pblock.
      move: HP => /and3P [] /eqP -> _ _.
      by move: Hsub => /subsetP ->.
    - apply/idP/idP => /imsetP [].
      + move=> U HU HS; subst S; apply/imsetP.
        move: HSn0 => /set0Pn [] x; rewrite inE => /andP [] HxU HxA.
        exists x; first exact HxA.
        by move: HP => /and3P [] _ /def_pblock/(_ HU HxU) ->.
      + move=> x Hx HS; subst S; apply/imsetP.
        exists (pblock P x); last by [].
        apply pblock_mem.
        move: HP => /and3P [] /eqP -> _ _.
        by move: Hsub => /subsetP ->.
  Qed.

End Restriction.


Section Defs.

  Variable T : finType.

  Structure setpart : predArgType :=
    SetPart {setpartval :> {set {set T}}; _ : partition setpartval setT}.
  Canonical tash_subType := Eval hnf in [subType for setpartval].
  Definition setpart_eqMixin := Eval hnf in [eqMixin of setpart by <:].
  Canonical setpart_eqType := Eval hnf in EqType setpart setpart_eqMixin.
  Definition setpart_choiceMixin := Eval hnf in [choiceMixin of setpart by <:].
  Canonical setpart_choiceType := Eval hnf in ChoiceType setpart setpart_choiceMixin.
  Definition setpart_countMixin := Eval hnf in [countMixin of setpart by <:].
  Canonical setpart_countType := Eval hnf in CountType setpart setpart_countMixin.
  Canonical setpart_subCountType := Eval hnf in [subCountType of setpart].
  Definition setpart_finMixin := Eval hnf in [finMixin of setpart by <:].
  Canonical setpart_finType := Eval hnf in FinType setpart setpart_finMixin.
  Canonical setpart_subFinType := Eval hnf in [subFinType of setpart].


  Implicit Type P : setpart.

  Lemma setpartP P : partition P setT.
  Proof. by case: P. Qed.

  Lemma setpart_cover P x : x \in cover P.
  Proof.
    have := setpartP P => /and3P [] /eqP -> _ _.
    by rewrite inE.
  Qed.

  Lemma setpart_inter P S1 S2 x :
    S1 \in P -> S2 \in P -> x \in S1 -> x \in S2 -> S1 = S2.
  Proof.
    move=> HS1 HS2 Hx1 Hx2; apply/eqP.
    have:= setpartP P => /and3P [] _ /trivIsetP/(_ _ _ HS1 HS2)/contraR Htmp _.
    move: Htmp; apply; apply/(introN idP); rewrite -setI_eq0 => /eqP/setP/(_ x).
    by rewrite in_set0 in_setI Hx1 Hx2 /=.
  Qed.

  Lemma is_finer_setpart_subset P1 P2 :
    is_finer P1 P2 -> is_finer P2 P1 -> P1 \subset P2.
  Proof.
    move: P1 P2 => [] P1 HP1 [] P2 HP2 /=.
    move=> /is_finerP H12 /is_finerP H21.
    apply/subsetP => s1 Hs1.
    move/(_ s1 Hs1) : H12 => [] s2 [] Hs2 Hs12.
    move/(_ s2 Hs2) : H21 => [] s1' [] Hs1' Hs21.
    suff H' : s1 = s1'.
      subst s1'; rewrite (_ : s1 = s2) //.
      by apply/eqP; rewrite eqEsubset Hs12 Hs21.
    apply/eqP.
    have {Hs12 Hs21 s2 Hs2 P2 HP2} := subset_trans Hs12 Hs21.
    apply contraLR => Hdiff.
    move: HP1 => /and3P [] _ /trivIsetP /(_ _ _ Hs1 Hs1' Hdiff) Hdisj Hnon0.
    have /set0Pn : s1 != set0 by move: Hnon0; apply contra => /eqP <-.
    move=> [] x Hx; apply (introN idP) => /subsetP/(_ _ Hx) Hx'.
    move: Hdisj; rewrite -setI_eq0 => /eqP/setP/(_ x).
    by rewrite in_set0 in_setI Hx Hx' /=.
  Qed.

  Lemma is_finer_setpart_anti P1 P2 :
    is_finer P1 P2 -> is_finer P2 P1 -> P1 = P2.
  Proof.
    move=> H12 H21; apply/eqP; rewrite eqE /=; rewrite eqEsubset.
    apply/andP; split; exact: is_finer_setpart_subset.
  Qed.

  Lemma trivpartP : partition [set [set x] | x in T] [set: T].
  Proof.
    apply/and3P; split.
    - apply/eqP/setP => x; rewrite inE /cover.
      apply/bigcupP; exists [set x]; last by rewrite in_set1.
      apply/imsetP; by exists x.
    - apply/trivIsetP => A B /imsetP [] a _ -> /imsetP [] b _ -> {A B} Hab.
      rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE.
      apply negbTE; move: Hab; by apply contra => /andP [] /eqP <- /eqP ->.
    - apply/(introN idP) => /imsetP [] x _ /setP/(_ x).
      by rewrite !inE eq_refl.
  Qed.

  Definition trivpart := SetPart trivpartP.

  Lemma is_finer_triv P : is_finer trivpart P.
  Proof.
    apply/is_finerP => s /imsetP [] x _ -> {s}.
    have:= setpart_cover P x; rewrite /cover => /bigcupP [] S HS Hx.
    exists S; split; first by [].
    by apply/subsetP => y; rewrite !inE => /eqP ->.
  Qed.

  Lemma fullpartP :
    partition (if #|T| == 0 then set0 else [set [set: T]]) [set: T].
  Proof.
    apply/and3P; split.
    - apply/eqP/setP => x; rewrite inE /cover.
      case: (altP (#|T| =P 0)) => HT.
      + exfalso; move: HT => /eqP; rewrite -cardsT cards_eq0.
        move/eqP/setP/(_ x); by rewrite !inE.
      + by rewrite big_set1 inE.
    - apply/trivIsetP => A B.
      case: (altP (#|T| =P 0)) => HT; first by rewrite inE.
      rewrite !in_set1 => /eqP -> /eqP ->.
      by rewrite eq_refl.
    - case: (altP (#|T| =P 0)); first by rewrite inE.
      by rewrite in_set1 -cardsT cards_eq0 eq_sym.
  Qed.

  Definition fullpart := SetPart fullpartP.

  Lemma is_finer_full P : is_finer P fullpart.
  Proof.
    rewrite /fullpart; apply/is_finerP => s HS.
    exists [set: T]; split => //=.
    case: (altP (#|T| =P 0)) => HT.
    - exfalso; have:= setpartP P => /and3P [] _ _ Hn0.
      move: HT; rewrite -cardsT => /eqP; rewrite cards_eq0 => /eqP H0.
      suff Heq0 : s = set0 by move: Hn0; rewrite -Heq0 HS.
      have:= subsetT s; by rewrite H0 subset0 => /eqP.
    - by rewrite in_set1.
    Qed.

End Defs.



Section Card0. (* Partition of the empty set *)

Variable T : finType.
Hypothesis HcardT : #|T| = 0.

Lemma set_card0 : [set: T] = set0.
Proof.
  have H := card0_eq HcardT.
  apply/setP => x; exfalso; by have:= H x; rewrite !inE.
Qed.

Lemma subset_card0 (S : {set T}) : S = set0.
Proof.
  have H := card0_eq HcardT.
  apply/setP => x; exfalso; by have:= H x; rewrite !inE.
Qed.

Lemma part_card0_eq_set0 P : partition P [set: T] -> P = set0.
Proof.
  move=> /and3P [] _ _ Hn0.
  apply/setP => S; rewrite inE (subset_card0 S).
  exact: negbTE.
Qed.

Lemma part_card0 : partition set0 [set: T].
Proof.
  apply/and3P; split.
  - by rewrite /cover big_set0 set_card0.
  - by rewrite /trivIset /cover !big_set0 cards0.
  - by rewrite in_set0.
Qed.

Let Part0 := SetPart part_card0.

Lemma setpart0_eq_set0 (P : setpart T) : P = Part0.
Proof.
  case: P => P HP; apply/eqP;
  by rewrite eqE /= (part_card0_eq_set0 HP).
Qed.

Lemma enum_setpart0 : enum (setpart T) = [:: Part0 ].
Proof.
  move Hl : (enum _) => l.
  case: l Hl => [|P0 [|P1 l]] Hl.
  - exfalso.
    have:= mem_enum (setpart T) Part0.
    by rewrite Hl inE in_nil.
  - by rewrite (setpart0_eq_set0 P0).
  - exfalso.
    rewrite (setpart0_eq_set0 P0) (setpart0_eq_set0 P1) in Hl.
    have:= enum_uniq (setpart T); by rewrite Hl /= inE eq_refl /=.
Qed.

End Card0.



Section Card1. (* Partition of a singleton *)

Variable T : finType.
Hypothesis HcardT : #|T| = 1.

Lemma subset_card1E (S : {set T}) : (S == set0) || (S == setT).
Proof.
  case: (altP (S =P set0)) => [-> |]//= /set0Pn [] x Hx.
  rewrite eqEcard subsetT /= cardsT HcardT card_gt0.
  apply/set0Pn; by exists x.
Qed.

Lemma subset_card1 (S : {set T}) : (S = set0) \/ (S = setT).
Proof.
  have:= subset_card1E S => /orP [] /eqP ->.
  by left. by right.
Qed.

Lemma part_card1_eq P : partition P [set: T] -> P = [set setT].
Proof.
  have : #|T| > 0 by rewrite HcardT.
  move=> /card_gt0P [] x Hx.
  move=> /and3P [] H1 _ Hn0.
  apply/setP => S; rewrite inE.
  case: (subset_card1 S) => [-> | HS].
  - move: Hn0 => /negbTE ->.
    apply esym; apply/negbTE/(introN idP) => /eqP/setP/(_ x).
    by rewrite !inE.
  - rewrite {S}HS eq_refl.
    move: H1; rewrite /cover.
    case: (altP (P =P set0)) => [-> |]/=.
    + rewrite big_set0 !inE => /eqP/setP/(_ x).
      by rewrite !inE.
    + move/set0Pn => [] S.
      have:= subset_card1 S => [[]] ->.
      * by move: Hn0 => /negbTE ->.
      * by move=> ->.
Qed.

Lemma part_card1 : partition [set [set: T]] [set: T].
Proof.
  apply/and3P; split.
  - by rewrite /cover big_set1.
  - by rewrite /trivIset /cover !big_set1.
  - rewrite in_set1.
    have : #|T| > 0 by rewrite HcardT.
    move=> /card_gt0P [] x Hx.
    apply/(introN idP) => /eqP/setP/(_ x).
    by rewrite !inE.
Qed.

Let Part1 := SetPart part_card1.

Lemma setpart1_eq_set1 (P : setpart T) : P = Part1.
Proof.
  case: P => P HP; apply/eqP;
  by rewrite eqE /= (part_card1_eq HP).
Qed.

Lemma enum_setpart1 : enum (setpart T) = [:: Part1 ].
Proof.
  move Hl : (enum _) => l.
  case: l Hl => [|P0 [|P1 l]] Hl.
  - exfalso.
    have:= mem_enum (setpart T) Part1.
    by rewrite Hl inE in_nil.
  - by rewrite (setpart1_eq_set1 P0).
  - exfalso.
    rewrite (setpart1_eq_set1 P0) (setpart1_eq_set1 P1) in Hl.
    have:= enum_uniq (setpart T); by rewrite Hl /= inE eq_refl /=.
Qed.

End Card1.


Section Card.

Variable T : finType.

Definition inj_finer_setpart x0 (P : setpart T) (S : {set T}) :=
  pblock P (odflt x0 [pick x in S]).

  Lemma inj_finer_setpart_non0 x0 (P : setpart T) (S : {set T}) :
    (inj_finer_setpart x0 P S) != set0.
  Proof.
    rewrite /inj_finer_setpart.
    set x := (odflt _ _).
    have Hbl:= pblock_mem (setpart_cover P x).
    have:= setpartP P => /and3P [] _ _.
    by apply contra => /eqP <-.
  Qed.

  Lemma inj_finer_setpartP x0 (P1 P2 : setpart T) (S : {set T}) :
    is_finer P1 P2 -> S \in P2 -> (inj_finer_setpart x0 P1 S) \subset S.
  Proof.
    move/is_finerP => Hfin HS.
    rewrite /inj_finer_setpart.
    case: pickP => [/= x Hx | Habs].
    - have:= pblock_mem (setpart_cover P1 x).
      move=> /Hfin {Hfin} [] S2 [] HS2 Hsubs.
      suff -> : S = S2 by [].
      have:= setpart_cover P1 x.
      rewrite -mem_pblock => /(subsetP Hsubs) Hx2.
      exact: (@setpart_inter _ P2 _ _ x).
    - exfalso.
      have {Habs} HS0 : S = set0 by apply/setP => x; rewrite Habs inE.
      have:= setpartP P2 => /and3P [] _ _.
      by rewrite -HS0 HS.
  Qed.

  Lemma is_finer_inj x0 (P1 P2 : setpart T) :
    is_finer P1 P2 -> {in P2 &, injective (inj_finer_setpart x0 P1)}.
  Proof.
    move=> H S1 S2 HS1 HS2 Heq.
    have:= inj_finer_setpart_non0 x0 P1 S1 => /set0Pn [] x Hx.
    have := inj_finer_setpartP x0 H HS1 => /subsetP/(_ _ Hx) Hx1.
    rewrite {}Heq in Hx.
    have:= inj_finer_setpartP x0 H HS2 => /subsetP/(_ _ Hx) {Hx} Hx2.
    exact: (@setpart_inter _ P2 _ _ x).
  Qed.

  Lemma is_finer_card (P1 P2 : setpart T) :
    is_finer P1 P2 -> #|P1| >= #|P2|.
  Proof.
    move Hn : #|T| => n.
    case: n Hn P1 P2 => [|n] Hn P1 P2.
    - by rewrite (setpart0_eq_set0 Hn P1) (setpart0_eq_set0 Hn P2) /= cards0.
    - have : #|T| > 0 by rewrite Hn.
      move=> /card_gt0P [] x Hx.
      move=> /(is_finer_inj (x0 := x))/card_in_imset <-.
      apply subset_leqif_cards; apply/subsetP => S /imsetP [] S2 HS2 ->.
      rewrite /inj_finer_setpart; apply pblock_mem.
      exact: setpart_cover.
  Qed.

  Lemma setpart_card (p : setpart T) : #|p| <= #|T|.
  Proof.
    have:= is_finer_card (is_finer_triv p).
    by rewrite card_imset; last exact: set1_inj.
  Qed.

  Lemma is_finer_card_eq (P1 P2 : setpart T) :
    is_finer P1 P2 -> #|P1| = #|P2| -> P1 = P2.
  Proof.
    move Hn : #|T| => n.
    case: n Hn P1 P2 => [|n] Hn P1 P2.
    - by rewrite (setpart0_eq_set0 Hn P1) (setpart0_eq_set0 Hn P2) /= cards0.
    - have : #|T| > 0 by rewrite Hn.
      move=> /card_gt0P [] x Hx.
      move=> /(is_finer_inj (x0 := x))/card_in_imset <-.
      admit.
      (* apply subset_leqif_cards; apply/subsetP => S /imsetP [] S2 HS2 ->.
      rewrite /inj_finer_setpart; apply pblock_mem.
      exact: setpart_cover. *)
  Qed.

  Lemma is_finer_card_final (P1 P2 : setpart T) :
    is_finer P1 P2 -> (#|P2| <= #|P1| ?= iff (P1 == P2)).
  Proof.
    move=> H; rewrite /leqif -pair_andP; split; first exact: is_finer_card.
    apply/idP/idP; last by move/eqP ->.
    by move/eqP/esym/(is_finer_card_eq H) ->.
  Qed.

End Card.



Require Import ordtype.

Section RefineOrder.

Variable T : finType.

Fact is_finer_porder : PartOrder.axiom (fun P1 P2 : setpart T => is_finer P1 P2).
Proof.
  split.
  - move=> p; exact: is_finer_refl.
  - move=> P q /andP []; exact: is_finer_setpart_anti.
  - move=> P q r; exact: is_finer_trans.
Qed.

Definition setpart_pordMixin := PartOrder.Mixin is_finer_porder.
Canonical setpart_pordType := Eval hnf in POrdType (setpart T) setpart_pordMixin.

End RefineOrder.


