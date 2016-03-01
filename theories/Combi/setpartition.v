Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop path finset.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Finer.

  Variable T : finType.
  Implicit Type P : {set {set T}}.

  Definition is_finer P1 P2 :=
    [forall (s1 | s1 \in P1), [exists (s2 | s2 \in P2),  s1 \subset s2 ]].

  Lemma is_finerP P1 P2 :
    reflect
      (forall s1, s1 \in P1 -> exists2 s2, s2 \in P2 & s1 \subset s2)
      (is_finer P1 P2).
  Proof.
    apply (iffP forall_inP) => H s1 /H{H}.
    - by move/exists_inP => [s2 H1 H2]; exists s2.
    - by move=> [s2 H1 H2]; apply/exists_inP; exists s2.
  Qed.

  Lemma is_finer_refl : reflexive is_finer.
  Proof. by move=> p; apply/is_finerP => [s1 H1]; exists s1. Qed.

  Lemma is_finer_trans : transitive is_finer.
  Proof.
    move=> P2 P1 p3 /is_finerP H12 /is_finerP H23.
    apply/is_finerP => s1 /H12{H12} [] s2 /H23{H23} [] s3 Hs3 H23 H12.
    exists s3; first exact: Hs3.
    exact: (subset_trans H12 H23).
  Qed.

  Lemma is_finer_setUl P1 P2 P :
    is_finer P1 P -> is_finer P2 P -> is_finer (P1 :|: P2) P.
  Proof.
    move=> /is_finerP H1 /is_finerP H2; apply/is_finerP => S.
    by rewrite inE => /orP [/H1 | /H2].
  Qed.

End Finer.

Hint Resolve is_finer_refl.

Section Restriction.

  Variable T : finType.

  Implicit Type P : {set {set T}}.
  Implicit Types A B S : {set T}.

  Definition rest P S : {set {set T}} := [set B :&: S | B in P] :\ set0.

  Lemma cover_rest P S : cover (rest P S) = cover P :&: S.
  Proof.
    rewrite /cover/rest; apply/setP => x; apply/idP/idP; rewrite !inE.
    - move/bigcupP => [A]; rewrite !inE => /andP [HBn0 /imsetP [B HB HA]].
      subst A; rewrite inE => /andP [HxB HxS].
      by rewrite HxS andbT; apply/bigcupP; exists B.
    - move/andP => [/bigcupP [B HB HxB] HxS].
      apply/bigcupP; exists (B :&: S); rewrite !inE; last by rewrite HxB HxS.
      apply/andP; split.
      + by apply/set0Pn; exists x; rewrite inE HxB HxS.
      + by apply/imsetP; exists B.
  Qed.

  Lemma trivIset_rest P S : trivIset P -> trivIset (rest P S).
  Proof.
    move=> /trivIsetP Htriv; apply/trivIsetP => A B; rewrite !inE.
    move/andP => [HA /imsetP [Ap HAp HAtmp]]; subst A.
    move/andP => [HB /imsetP [Bp HBp HBtmp]]; subst B.
    apply contraR; rewrite -setI_eq0 => /set0Pn [x].
    rewrite !inE => /and3P [/andP [HxAp HxS] HxBp _].
    have /contraR := Htriv Ap Bp HAp HBp; rewrite -setI_eq0 => H.
    suff /H/eqP -> : Ap :&: Bp != set0 by [].
    by apply/set0Pn; exists x; rewrite inE HxAp HxBp.
  Qed.

  Lemma partition_rest P A B :
    A \subset B -> partition P B -> partition (rest P A) A.
  Proof.
    move=> Hsub /and3P [/eqP Hcov Htriv Hnon0].
    apply/and3P; split.
    - by rewrite cover_rest Hcov; apply/eqP/setIidPr.
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
      move: HP => /and3P [/eqP-> _ _].
      by move: Hsub => /subsetP ->.
    - apply/idP/idP => /imsetP [].
      + move=> U HU HS; subst S; apply/imsetP.
        move: HSn0 => /set0Pn [] x; rewrite inE => /andP [] HxU HxA.
        exists x; first exact HxA.
        by move: HP => /and3P [] _ /def_pblock/(_ HU HxU) ->.
      + move=> x Hx HS; subst S; apply/imsetP.
        exists (pblock P x); last by [].
        apply pblock_mem.
        move: HP => /and3P [/eqP-> _ _].
        by move: Hsub => /subsetP ->.
  Qed.

End Restriction.


Section Defs.

  Variable T : finType.
  Variable C : {set T}.

  Structure setpart : predArgType :=
    SetPart {setpartval :> {set {set T}}; _ : partition setpartval C}.
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

  Lemma setpartP P : partition P C.
  Proof. by case: P. Qed.

  Lemma setpart_cover P : cover P = C.
  Proof. by have:= setpartP P => /and3P [/eqP -> _]. Qed.

  Lemma setpart_inter P S1 S2 x :
    S1 \in P -> S2 \in P -> x \in S1 -> x \in S2 -> S1 = S2.
  Proof.
    move=> HS1 HS2 Hx1 Hx2; apply/eqP.
    have:= setpartP P => /and3P [_ /trivIsetP/(_ _ _ HS1 HS2)/contraR Htmp _].
    move: Htmp; apply; apply/(introN idP); rewrite -setI_eq0 => /eqP/setP/(_ x).
    by rewrite in_set0 in_setI Hx1 Hx2 /=.
  Qed.

  Lemma is_finer_setpart_subset P1 P2 :
    is_finer P1 P2 -> is_finer P2 P1 -> P1 \subset P2.
  Proof.
    move: P1 P2 => [P1 HP1] [P2 HP2] /=.
    move=> /is_finerP H12 /is_finerP H21.
    apply/subsetP => s1 Hs1.
    move/(_ s1 Hs1) : H12 => [s2 Hs2 Hs12].
    move/(_ s2 Hs2) : H21 => [s1' Hs1' Hs21].
    suff H' : s1 = s1'.
      subst s1'; rewrite (_ : s1 = s2) //.
      by apply/eqP; rewrite eqEsubset Hs12 Hs21.
    apply/eqP.
    have {Hs12 Hs21 s2 Hs2 P2 HP2} := subset_trans Hs12 Hs21.
    apply contraLR => Hdiff.
    move: HP1 => /and3P [_ /trivIsetP/(_ _ _ Hs1 Hs1' Hdiff) Hdisj Hnon0].
    have /set0Pn : s1 != set0 by move: Hnon0; apply contra => /eqP <-.
    move=> [x Hx]; apply (introN idP) => /subsetP/(_ _ Hx) Hx'.
    move: Hdisj; rewrite -setI_eq0 => /eqP/setP/(_ x).
    by rewrite in_set0 in_setI Hx Hx' /=.
  Qed.

  Lemma is_finer_setpart_anti P1 P2 :
    is_finer P1 P2 -> is_finer P2 P1 -> P1 = P2.
  Proof.
    move=> H12 H21; apply/eqP; rewrite eqE /=; rewrite eqEsubset.
    apply/andP; split; exact: is_finer_setpart_subset.
  Qed.

  Lemma trivpartP : partition [set [set x] | x in C] C.
  Proof.
    apply/and3P; split.
    - apply/eqP/setP => x; rewrite /cover.
      apply/idP/idP.
      + move=> /bigcupP [B /imsetP [y Hy] ->].
        by rewrite in_set1 => /eqP->.
      + move=> Hx; apply/bigcupP; exists [set x]; last by rewrite in_set1.
        apply/imsetP; by exists x.
    - apply/trivIsetP => A B /imsetP [a _ ->] /imsetP [b _ ->] {A B} Hab.
      rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE.
      apply negbTE; move: Hab; by apply contra => /andP [/eqP<- /eqP->].
    - apply/(introN idP) => /imsetP [x _ /setP/(_ x)].
      by rewrite !inE eq_refl.
  Qed.

  Definition trivpart := SetPart trivpartP.

  Lemma is_finer_triv P : is_finer trivpart P.
  Proof.
    apply/is_finerP => s /imsetP [x Hx -> {s}].
    move: Hx; rewrite -(setpart_cover P) /cover => /bigcupP [S HS HxS].
    exists S; first by [].
    by apply/subsetP => y; rewrite !inE => /eqP ->.
  Qed.

End Defs.

Section Card0. (* Partition of the empty set *)

  Variable T : finType.

  Lemma part_card0_eq_set0 (P : {set {set T}}) : partition P set0 -> P = set0.
  Proof.
    move=> /and3P [/eqP]; rewrite /cover => Hcov _ Hn0.
    apply/eqP; rewrite -subset0; apply/subsetP => S HS; exfalso.
    have: S \subset \bigcup_(B in P) B by apply (bigcup_max S).
    rewrite Hcov subset0 => /eqP HS0.
    by move: Hn0; rewrite -HS0 HS.
  Qed.

  Lemma part_card0 : partition set0 (@set0 T).
  Proof.
    apply/and3P; split.
    - by rewrite /cover big_set0.
    - by rewrite /trivIset /cover !big_set0 cards0.
    - by rewrite in_set0.
  Qed.

  Let Part0 := SetPart part_card0.

  Lemma setpart0_eq_set0 (P : setpart set0) : P = Part0.
  Proof.
    case: P => P HP; apply/eqP;
    by rewrite eqE /= (part_card0_eq_set0 HP).
  Qed.

  Lemma enum_setpart0 : enum (setpart set0) = [:: Part0 ].
  Proof.
    move Hl : (enum _) => l.
    case: l Hl => [|P0 [|P1 l]] Hl.
    - exfalso.
      have:= mem_enum (setpart set0) Part0.
      by rewrite Hl inE in_nil.
    - by rewrite (setpart0_eq_set0 P0).
    - exfalso.
      rewrite (setpart0_eq_set0 P0) (setpart0_eq_set0 P1) in Hl.
      have:= enum_uniq (setpart (@set0 T)); by rewrite Hl /= inE eq_refl /=.
  Qed.

End Card0.


Section Card1. (* Partition of a singleton *)

  Variable T : finType.
  Variable C : {set T}.
  Hypothesis HcardC : #|C| = 1.

  Lemma subset_card1E (S : {set T}) :
    S \subset C -> (S == set0) || (S == C).
  Proof.
    move: HcardC => /eqP/cards1P [x HC]; subst C.
    by rewrite subset1 orbC.
  Qed.

  Lemma subset_card1 (S : {set T}) : S \subset C -> (S = set0) \/ (S = C).
  Proof. by move=> /subset_card1E /orP [] /eqP->; [left | right]. Qed.

  Lemma in_part_card1 (P : {set {set T}}) S :
    partition P C -> S \in P -> S = C.
  Proof.
    move: HcardC => /eqP/cards1P [x HC]; subst C.
    move=> /and3P [H1 _ Hn0] HS.
    apply/eqP; rewrite eqEsubset.
    have: S \subset \bigcup_(B in P) B by apply (bigcup_max S).
    move: H1; rewrite /cover => /eqP-> HSx.
    rewrite HSx /=.
    apply/subsetP => y; rewrite inE => /eqP Hy; subst y.
    have: S != set0 by move: Hn0; apply contra => /eqP <-.
    move/set0Pn => [y Hy].
    suff: y = x by move <-.
    move: HSx => /subsetP/(_ y Hy).
    by rewrite inE => /eqP.
  Qed.

  Lemma part_card1_eq (P : {set {set T}}) : partition P C -> P = [set C].
  Proof.
    move=> Hpart.
    have Hin := in_part_card1 Hpart.
    move: Hpart => /and3P [H1 _ Hn0].
    apply/setP => S; rewrite inE.
    apply/idP/idP => [/Hin -> // | /eqP HS].
    subst S.
    have: P != set0.
      move: H1; apply contraL => /eqP ->.
      by rewrite /cover big_set0 eq_sym -card_gt0 HcardC.
    move/set0Pn => [S HS].
    by rewrite -(Hin S HS).
  Qed.

  Lemma part_card1 : partition [set C] C.
  Proof.
    apply/and3P; split.
    - by rewrite /cover big_set1.
    - by rewrite /trivIset /cover !big_set1.
    - by rewrite in_set1 eq_sym -card_gt0 HcardC.
  Qed.

  Let Part1 := SetPart part_card1.

  Lemma setpart1_eq_set1 P : P = Part1.
  Proof.
    case: P => P HP; apply/eqP;
    by rewrite eqE /= (part_card1_eq HP).
  Qed.

  Lemma enum_setpart1 : enum (setpart C) = [:: Part1 ].
  Proof.
    move Hl : (enum _) => l.
    case: l Hl => [|P0 [|P1 l]] Hl.
    - exfalso.
      have:= mem_enum (setpart C) Part1.
        by rewrite Hl inE in_nil.
    - by rewrite (setpart1_eq_set1 P0).
    - exfalso.
      rewrite (setpart1_eq_set1 P0) (setpart1_eq_set1 P1) in Hl.
      have:= enum_uniq (setpart C); by rewrite Hl /= inE eq_refl /=.
  Qed.

End Card1.

Section Full.

  Variable T : finType.
  Variable C : {set T}.

  Lemma fullpartP :
    partition (if #|C| == 0 then set0 else [set C]) C.
  Proof.
    apply/and3P; split.
    - apply/eqP/setP => x; rewrite /cover.
      case: (altP (#|C| =P 0)) => HT.
      + by rewrite big_set0 (cards0_eq HT).
      + by rewrite big_set1.
    - apply/trivIsetP => A B.
      case: (altP (#|C| =P 0)) => HT; first by rewrite inE.
      rewrite !in_set1 => /eqP -> /eqP ->.
      by rewrite eq_refl.
    - case: (altP (#|C| =P 0)); first by rewrite inE.
      rewrite in_set1; apply contra => /eqP <-.
      by rewrite cards0.
  Qed.

  Definition fullpart := SetPart fullpartP.

  Lemma is_finer_full (P : setpart C) : is_finer P fullpart.
  Proof.
    rewrite /fullpart; apply/is_finerP => S HS /=.
    case: (altP (#|C| =P 0)) => [/cards0_eq HC | HC].
    - exfalso; subst C; have:= setpart0_eq_set0 P.
      move=> /eqP; rewrite eqE /= => /eqP HP.
      by move: HS; rewrite HP inE.
    - exists C; first by rewrite in_set1.
      apply/subsetP => x Hx.
      have:= setpartP P => /and3P [/eqP{3}<- _ _].
      rewrite /cover; apply/bigcupP; by exists S.
    Qed.

End Full.


Section FinerCard.

  Variable T : finType.
  Variable C : {set T}.

  Implicit Type P : setpart C.
  Implicit Type S : {set T}.

  Section DefInjToFiner.

    Variable c0 : T.
    Hypothesis Hc0 : c0 \in C.

    Definition inj_to_finer P S := pblock P (odflt c0 [pick x in S]).

    Lemma inj_to_finer_non0 P S : S \subset C -> inj_to_finer P S != set0.
    Proof.
      rewrite /inj_to_finer => HS.
      case: pickP => [/= x Hx | Hx] /=.
      - apply/set0Pn; exists x.
        rewrite mem_pblock setpart_cover.
        by move: HS => /subsetP ->.
      - apply/set0Pn; exists c0.
        by rewrite mem_pblock setpart_cover.
    Qed.

    Lemma inj_to_finerP P1 P2 S :
      is_finer P1 P2 -> S \in P2 -> inj_to_finer P1 S \subset S.
    Proof.
      move/is_finerP => Hfin HS.
      rewrite /inj_to_finer.
      case: pickP => [/= x Hx | Habs].
      - have: S \subset \bigcup_(B in P2) B by apply (bigcup_max S).
        move=> /subsetP/(_ _ Hx).
        rewrite -/(cover P2) (cover_partition (setpartP P2)) => HxC.
        have:= HxC; rewrite -{1}(cover_partition (setpartP P1)) => /pblock_mem.
        move=> /Hfin {Hfin} [S2 HS2] Hsubs.
        suff -> : S = S2 by [].
        move: HxC; rewrite -(setpart_cover P1) -mem_pblock => /(subsetP Hsubs) Hx2.
        exact: (@setpart_inter _ _ P2 _ _ x).
      - exfalso.
        have {Habs} HS0 : S = set0 by apply/setP => x; rewrite Habs inE.
        have:= setpartP P2 => /and3P [_ _].
        by rewrite -HS0 HS.
    Qed.

    Lemma inj_to_finer_subset P1 P2 :
      is_finer P1 P2 -> [set inj_to_finer P1 x | x in P2] \subset P1.
    Proof.
      move=> Hfin; apply/subsetP => S /imsetP [S2 HS2 ->].
      rewrite /inj_to_finer; apply pblock_mem.
      rewrite setpart_cover.
      case: pickP => /= [x Hx | //].
      have: S2 \subset \bigcup_(B in P2) B by apply (bigcup_max S2).
      move=> /subsetP/(_ _ Hx).
      by rewrite -/(cover P2) (cover_partition (setpartP P2)).
    Qed.

    Lemma is_finer_inj P1 P2 :
      is_finer P1 P2 -> {in P2 &, injective (inj_to_finer P1)}.
    Proof.
      move=> H S1 S2 HS1 HS2 Heq.
      have: S1 \subset C.
        rewrite -(cover_partition (setpartP P2)) /cover.
        exact: (bigcup_max S1).
      move/(inj_to_finer_non0 P1) => /set0Pn [x Hx].
      have:= inj_to_finerP H HS1 => /subsetP/(_ _ Hx) Hx1.
      rewrite {}Heq in Hx.
      have:= inj_to_finerP H HS2 => /subsetP/(_ _ Hx) {Hx} Hx2.
      exact: (@setpart_inter _ _ P2 _ _ x).
    Qed.

    End DefInjToFiner.

  Lemma is_finer_card_gt P1 P2 : is_finer P1 P2 -> #|P1| >= #|P2|.
  Proof.
    move=> Hfin.
    case: (set_0Vmem C) => [HC| [c0 Hc0]].
    subst C; by rewrite (setpart0_eq_set0 P1) (setpart0_eq_set0 P2).
    have:= is_finer_inj Hc0 Hfin => /card_in_imset <-.
    apply subset_leqif_cards;
    exact: inj_to_finer_subset.
  Qed.

  Lemma setpart_card P : #|P| <= #|C|.
  Proof.
    have:= is_finer_card_gt (is_finer_triv P).
    by rewrite card_imset; last exact: set1_inj.
  Qed.

  Lemma is_finer_card_eq P1 P2 : is_finer P1 P2 -> #|P1| = #|P2| -> P1 = P2.
  Proof.
    case: (set_0Vmem C) P1 P2 => [-> | [c0 Hc0]] P1 P2 Hfin Hcard.
      by rewrite (setpart0_eq_set0 P1) (setpart0_eq_set0 P2).
    have Hinj : [set inj_to_finer c0 P1 x | x in P2] = P1.
    apply/eqP; rewrite eqEcard.
    have:= is_finer_inj Hc0 Hfin => /card_in_imset; rewrite -Hcard => ->.
      rewrite leqnn andbT.
      exact: inj_to_finer_subset.
    have /leqif_sum : forall S, S \in P2 ->
       #|inj_to_finer c0 P1 S| <= #|S| ?=
          iff (#|inj_to_finer c0 P1 S| == #|S|).
      move=> S HS; split; last by [].
      apply subset_leqif_cards; exact: (inj_to_finerP _ Hfin).
    have:= setpartP P2 => /and3P [/eqP Hcov2 HtrivP2 _].
    move: HtrivP2; rewrite /trivIset => /eqP ->.
    rewrite Hcov2.
    rewrite -(big_imset (fun x : {set T} => #|x|) (is_finer_inj Hc0 Hfin)) /=.
    rewrite Hinj.
    have:= setpartP P1 => /and3P [/eqP Hcov1 HtrivP1 _].
      move: HtrivP1; rewrite /trivIset => /eqP ->.
      rewrite Hcov1 => [] [] _; rewrite eq_refl => /esym/forall_inP Hall.
      have {Hall} Hall S : S \in P2 -> inj_to_finer c0 P1 S = S.
      move=> Hin.
      apply/setP/(subset_cardP (eqP (Hall _ Hin))).
      exact: (inj_to_finerP _ Hfin).
    apply/eqP; rewrite eqE /=; rewrite -{}Hinj.
    apply/eqP/setP => S; apply/idP/idP.
    - move=> /imsetP [U HU -> {S}].
      by rewrite (Hall _ HU).
    - move=> Hin.
      apply/imsetP; exists S; first exact Hin.
      apply esym; exact: Hall.
  Qed.

  Lemma is_finer_card (P1 P2 : setpart C) :
    is_finer P1 P2 -> (#|P2| <= #|P1| ?= iff (P1 == P2)).
  Proof.
    move=> H; rewrite /leqif -pair_andP; split; first exact: is_finer_card_gt.
    apply/idP/idP; last by move/eqP ->.
    by move/eqP/esym/(is_finer_card_eq H) ->.
  Qed.

End FinerCard.



Section GreatestLowerBound.

  Variable T : finType.
  Variable C : {set T}.

  Implicit Type P : setpart C.
  Implicit Type S : {set T}.

  Definition glb P1 P2 := [set S1 :&: S2 | S1 in P1, S2 in P2] :\ set0.

  Lemma glbP P1 P2 : partition (glb P1 P2) C.
  Proof.
    rewrite /glb; apply/and3P; split.
    - rewrite /cover; apply/eqP/setP => x.
      apply/idP/idP => [/bigcupP [S] | HC].
      + rewrite !inE => /andP [_ /imset2P [S1 S2 HS1 _ HStmp]].
        subst S; rewrite inE => /andP [Hx1 _].
        rewrite -(setpart_cover P1); apply/bigcupP; by exists S1.
      + have:= HC; rewrite -{1}(setpart_cover P1) => /bigcupP [S1 HS1 Hx1].
        move:  HC; rewrite -{1}(setpart_cover P2) => /bigcupP [S2 HS2 Hx2].
        apply/bigcupP; exists (S1 :&: S2); rewrite !inE ?Hx1 ?Hx2 //.
        apply/andP; split; first by apply/set0Pn; exists x; rewrite inE Hx1 Hx2.
        apply/imset2P; by exists S1 S2.
    - apply/trivIsetP => U V; rewrite !inE.
      move=> /andP [HU1n0 /imset2P [U1 U2 HU1 HU2 HU]]; subst U.
      move=> /andP [HV1n0 /imset2P [V1 V2 HV1 HV2 HV]]; subst V.
      apply contraR; rewrite -setI_eq0 => /set0Pn [x].
      rewrite !inE => /andP [/andP [xU1 xU2] /andP [xV1 xV2]].
      rewrite (_ : U1 = V1); last exact: (setpart_inter HU1 HV1 xU1 xV1).
      rewrite (_ : U2 = V2); last exact: (setpart_inter HU2 HV2 xU2 xV2).
      exact: eq_refl.
    - by rewrite !inE eq_refl.
  Qed.

  Definition glb_setpart P1 P2 := SetPart (glbP P1 P2).

  Lemma glb_setpartC P1 P2 : glb_setpart P1 P2 = glb_setpart P2 P1.
  Proof.
    apply/eqP; rewrite eqE /=; rewrite /glb.
    have tmp (P Q : setpart C) :
      [set U :&: V | U in P, V in Q] \subset
                                     [set V :&: U | V in Q, U in P].
      apply/subsetP => x /imset2P [U V HU HV -> {x}].
      apply/imset2P; exists V U => //.
      by rewrite setIC.
    set A := (X in X :\ _); set B := (X in _ == X :\ _).
    suff -> : A = B by [].
    apply/eqP; by rewrite eqEsubset !tmp.
  Qed.

  Lemma is_finer_glbl P1 P2 : is_finer (glb_setpart P1 P2) P1.
  Proof.
    apply/is_finerP => S.
    rewrite !inE => /andP [_ /imset2P [S1 S2 H1 H2 -> {S}]].
    exists S1; first by [].
    exact: subsetIl.
  Qed.

  Lemma is_finer_glbr P1 P2 : is_finer (glb_setpart P1 P2) P2.
  Proof. rewrite glb_setpartC; exact: is_finer_glbl. Qed.

  Lemma glb_setpartP P1 P2 P :
    is_finer P P1 -> is_finer P P2 -> is_finer P (glb_setpart P1 P2).
  Proof.
    move=> /is_finerP Hfin1 /is_finerP Hfin2.
    apply/is_finerP => S HS.
    move/(_ _ HS): Hfin1 => [U1 H1 HU1].
    move/(_ _ HS): Hfin2 => [U2 H2 HU2].
    exists (U1 :&: U2).
    - rewrite !inE; apply/andP; split.
      + apply/set0Pn.
        have:= setpartP P => /and3P [_ _ Hn0].
        have: S != set0 by move: Hn0; apply contra => /eqP <-.
        move/set0Pn => [x Hx].
        exists x; rewrite inE.
        move: HU1 => /subsetP -> //=.
        by move: HU2 => /subsetP ->.
      + by apply/imset2P; exists U1 U2.
    - by rewrite subsetI HU1 HU2.
  Qed.

End GreatestLowerBound.


Section TrivIsetClosure.

  Variable T : finType.

  Implicit Types (A B : {set T}) (AB : {set T} * {set T}) (P : {set {set T}}).

  Let set00 : {set T} * {set T} := (set0, set0).
  Definition inIset P AB :=
    [&& (AB.1 \in P), (AB.2 \in P), (AB.1 != AB.2) & (AB.1 :&: AB.2 != set0)].

  Lemma inIset_ex P : exists AB, ~~ trivIset P ==> inIset P AB.
  Proof.
    suff: ~~ trivIset P -> [exists AB, inIset P AB].
      by case: (trivIset _)/boolP => /= _; [exists set00|move/(_ erefl)/existsP].
    apply contraR; rewrite negb_exists_in => /forallP hdis.
    apply/trivIsetP => A B HA HB AB_neq; have := hdis (A,B).
    by rewrite HA HB AB_neq /= setI_eq0 negbK.
  Qed.

  Lemma inIset_exC P : { AB | ~~ trivIset P ==> inIset P AB }.
  Proof. exact : sigW (inIset_ex _). Qed.

  Definition gen_Iset P := if trivIset P then set00 else projT1 (inIset_exC P).

  Lemma gen_IsetP P : ~~ trivIset P -> inIset P (gen_Iset P).
  Proof.
      rewrite /gen_Iset.
      by case: ifP => // /negbT tsn _; case: inIset_exC => x; rewrite tsn.
  Qed.

  Section Replace_byU.

    Variable P : {set {set T}}.
    Variables A B : {set T}.
    Hypothesis HinI : inIset P (A, B).

    Lemma cardsP : 1 < #|P|.
    Proof.
      case/and4P: HinI => /= ha hb ab_neq ?.
      by rewrite (cardsD1 A) (cardsD1 B) !inE eq_sym ab_neq ha hb.
    Qed.

    Definition replace_byU := (A :|: B) |: P :\: [set A; B].

    Lemma card_replace_byU_lt : #|replace_byU| < #|P|.
    Proof.
      case/and4P: HinI => /= HA HB ab_neq ?.
      rewrite cardsU1 cardsDS ?cards2 ?ab_neq; last first.
        by apply/subsetP=> x; rewrite !inE; case/orP=> /eqP->.
      rewrite (leq_ltn_trans (leq_add (leq_b1 _) (leqnn _))) //.
      rewrite addnBA ?cardsP // subn2 -subn1 -{2}[#|P|]subn0.
      by rewrite ltn_sub2l // (ltn_trans (@erefl _ (0 < 1))) ?cardsP.
    Qed.

    Lemma cover_replace_byU : cover (replace_byU) = cover P.
    Proof.
      move: HinI => /and4P [/= HA HB _ _].
      rewrite /cover/replace_byU.
      rewrite bigcup_setU big_set1.
      apply/setP => x; rewrite !inE.
      case: (boolP (x \in A)) => HxA /=.
        apply esym; apply/bigcupP; by exists A.
      case: (boolP (x \in B)) => HxB /=.
        apply esym; apply/bigcupP; by exists B.
      apply/idP/idP => /bigcupP [S].
      - rewrite !inE negb_or => /andP [_ HS] Hx.
        apply/bigcupP; by exists S.
      - move=> HS Hx; apply/bigcupP; exists S; last exact Hx.
        rewrite !inE HS andbT.
        have /negbTE -> : S != A.
          by move: HxA; apply contra => /eqP <-.
        have /negbTE -> : S != B.
          by move: HxB; apply contra => /eqP <-.
        by [].
    Qed.

    Lemma is_finer_replace_byU : is_finer P replace_byU.
    Proof.
      apply/is_finerP => S HS.
      rewrite /replace_byU.
      case: (altP (S =P A)) => [HA | /negbTE HA].
        subst S; exists (A :|: B); first by rewrite !inE eq_refl.
        exact: subsetUl.
      case: (altP (S =P B)) => [HB | /negbTE HB].
        subst S; exists (A :|: B); first by rewrite !inE eq_refl.
        exact: subsetUr.
      exists S; last by [].
      by rewrite !inE HA HB HS /= orbT.
    Qed.

    Lemma trivIset_is_finer_replace_byU Q :
      trivIset Q -> is_finer P Q -> is_finer replace_byU Q.
    Proof.
      move: HinI => /and4P/= [ HA HB Hneq Hn0].
      rewrite /replace_byU => /trivIsetP Htriv /is_finerP Hfin.
      apply/is_finerP => S; rewrite !inE => /orP [/eqP -> |].
      - case: (Hfin _ HA) => U HU HAU.
        case: (Hfin _ HB) => V HV HBV.
        have HUV : U = V.
          apply/eqP; apply (contraR (Htriv _ _ HU HV)).
          rewrite -setI_eq0; apply/set0Pn.
          move: Hn0 => /set0Pn [x]; rewrite inE => /andP [HxA HxB].
          exists x; rewrite inE.
          by move: HAU HBV => /subsetP -> // /subsetP ->.
        subst V; exists U; first exact: HU.
        rewrite -(setUid U); exact: setUSS.
      - rewrite negb_or => /andP [/andP [HSA HSB] /Hfin [U HUQ HSU]].
        by exists U.
    Qed.

  End Replace_byU.


  Definition UIset P :=
    if trivIset P then P
    else let: (A, B) := gen_Iset P in replace_byU P A B.

  Lemma UIset_triv P : trivIset P -> UIset P = P.
  Proof. by rewrite /UIset; case: ifP. Qed.

  Lemma IUset_card_lt P : ~~ trivIset P -> #|UIset P| < #|P|.
  Proof.
    move=> htriv; rewrite /UIset/gen_Iset.
    case: inIset_exC => -[A B]; rewrite !htriv /= (negbTE htriv) /=.
    exact: card_replace_byU_lt.
  Qed.

  Fixpoint lubs_rec P n :=
    if n is n'.+1 then
      if trivIset P then P
      else lubs_rec (UIset P) n'
    else P.
  Definition lubs P := lubs_rec P #|P|.

  Lemma trivIset_lubs_rec P n : n >= #|P| -> trivIset (lubs_rec P n).
  Proof.
    elim: n P => [| n IHn] P //=.
      rewrite leqn0 cards_eq0 => /eqP ->.
      by rewrite /trivIset /cover !big_set0 cards0.
    case: (boolP (trivIset P)) => [// | /IUset_card_lt/leq_trans H/H{H}].
    rewrite ltnS; exact: IHn.
  Qed.
  Lemma trivIset_lubs P : trivIset (lubs P).
  Proof. exact: trivIset_lubs_rec. Qed.

  Lemma set0_notin_lubs P : set0 \notin P -> set0 \notin (lubs P).
  Proof.
    apply contra.
    rewrite /lubs; elim: #|P| {1 3}P => [// | n IHn] {P} P /=.
    case: (boolP (trivIset P)) => [// | Hntriv /IHn {IHn}].
    have:= gen_IsetP Hntriv.
    rewrite /UIset; move: Hntriv => /negbTE ->.
    case: (gen_Iset P) => A B /and4P/= [HA HB Hneq HAB].
    rewrite /replace_byU !inE => /orP [].
    - by rewrite eq_sym setU_eq0 => /andP [/eqP<-].
    - by rewrite negb_or => /andP [].
  Qed.

  Lemma cover_lubs P : cover (lubs P) = cover P.
  Proof.
    rewrite /lubs; elim: #|P| {1 3}P => [// | n IHn] {P} P /=.
    case: (boolP (trivIset P)) => [// | Hntriv].
    rewrite IHn.
    have:= gen_IsetP Hntriv.
    rewrite /UIset; move: Hntriv => /negbTE ->.
    case: (gen_Iset P) => A B.
    exact: cover_replace_byU.
  Qed.

  Lemma is_finer_lubs P : is_finer P (lubs P).
  Proof.
    rewrite /lubs; elim: #|P| {1 2}P => [| n IHn] {P} P /=.
      exact: is_finer_refl.
    case: (boolP (trivIset P)) => [_ | /negbTE Htriv]; first exact: is_finer_refl.
    apply: (is_finer_trans _ (IHn _)).
    rewrite /UIset Htriv; case: (gen_Iset P) => A B.
    exact: is_finer_replace_byU.
  Qed.

  Lemma trivIset_is_finer_lubs P Q :
    trivIset Q -> is_finer P Q -> is_finer (lubs P) Q.
  Proof.
    move=> HtrivQ.
    rewrite /lubs; elim: #|P| {1 2}P => [// | n IHn] {P} P /=.
    case: (boolP (trivIset P)) => [// | HntrivP].
    have:= gen_IsetP HntrivP.
    rewrite /UIset; move: HntrivP => /negbTE ->.
    case: (gen_Iset P) => A B /trivIset_is_finer_replace_byU/(_ _ HtrivQ).
    move=> H/H{H}; exact: IHn.
  Qed.

End TrivIsetClosure.


Section LeastUpperBound.

  Variable T : finType.
  Variable C : {set T}.

  Implicit Type P : setpart C.
  Implicit Type S : {set T}.

  Definition lub P1 P2 := lubs (P1 :|: P2).

  Lemma lubP P1 P2 : partition (lub P1 P2) C.
  Proof.
    rewrite /lub; apply/and3P; split.
    - by rewrite cover_lubs /cover bigcup_setU -!/(cover _) !setpart_cover setUid.
    - exact: trivIset_lubs.
    - apply set0_notin_lubs; rewrite inE negb_or.
      have:= setpartP P1 => /and3P [_ _ ->] /=.
      by have:= setpartP P2 => /and3P [].
  Qed.

  Definition lub_setpart P1 P2 := SetPart (lubP P1 P2).

  Lemma lub_setpartC P1 P2 : lub_setpart P1 P2 = lub_setpart P2 P1.
  Proof. by apply/eqP; rewrite eqE /= /lub setUC. Qed.

  Lemma is_finer_lubl P1 P2 : is_finer P1 (lub_setpart P1 P2).
  Proof.
    rewrite /= /lub.
    apply: (is_finer_trans _ (is_finer_lubs _)).
    apply/is_finerP => S HS.
    by exists S; first by rewrite inE HS.
  Qed.

  Lemma is_finer_lubr P1 P2 : is_finer P2 (lub_setpart P1 P2).
  Proof. rewrite lub_setpartC; exact: is_finer_lubl. Qed.

  Lemma lub_setpartP P1 P2 P :
    is_finer P1 P -> is_finer P2 P -> is_finer (lub_setpart P1 P2) P.
  Proof.
    rewrite /= /lub => H1 H2.
    apply trivIset_is_finer_lubs.
    - by have:= setpartP P => /and3P [].
    - exact: is_finer_setUl.
  Qed.

End LeastUpperBound.



Require Import ordtype.

Section RefineOrder.

Variable T : finType.
Variable C : {set T}.

Fact is_finer_porder : PartOrder.axiom (fun P1 P2 : setpart C => is_finer P1 P2).
Proof.
  split.
  - move=> p; exact: is_finer_refl.
  - move=> P q /andP []; exact: is_finer_setpart_anti.
  - move=> P q r; exact: is_finer_trans.
Qed.

Definition setpart_pordMixin := PartOrder.Mixin is_finer_porder.
Canonical setpart_pordType := Eval hnf in POrdType (setpart C) setpart_pordMixin.

End RefineOrder.
