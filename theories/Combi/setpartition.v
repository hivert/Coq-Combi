Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop path finset.


Set Implicit Arguments.
Unset Strict Implicit.


Section Defs.

  Variable n : nat.

  Definition is_finer (p1 p2 : {set {set 'I_n}}) :=
    [forall (s1 | s1 \in p1), [exists (s2 | s2 \in p2),  s1 \subset s2 ]].

  Lemma is_finerP (p1 p2 : {set {set 'I_n}}) :
    reflect
      (forall s1,  s1 \in p1 -> exists s2,  s2 \in p2 /\ s1 \subset s2)
      (is_finer p1 p2).
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
    move=> p2 p1 p3 /is_finerP H12 /is_finerP H23.
    apply/is_finerP => s1 /H12{H12} [] s2 [] /H23{H23} [] s3 [] Hs3 H23 H12.
    exists s3; split; first exact: Hs3.
    exact: (subset_trans H12 H23).
  Qed.

  Structure setpartn : predArgType :=
    SetPartN {setpartnval :> {set {set 'I_n}}; _ : partition setpartnval setT}.
  Canonical tash_subType := Eval hnf in [subType for setpartnval].
  Definition setpartn_eqMixin := Eval hnf in [eqMixin of setpartn by <:].
  Canonical setpartn_eqType := Eval hnf in EqType setpartn setpartn_eqMixin.
  Definition setpartn_choiceMixin := Eval hnf in [choiceMixin of setpartn by <:].
  Canonical setpartn_choiceType := Eval hnf in ChoiceType setpartn setpartn_choiceMixin.
  Definition setpartn_countMixin := Eval hnf in [countMixin of setpartn by <:].
  Canonical setpartn_countType := Eval hnf in CountType setpartn setpartn_countMixin.
  Canonical setpartn_subCountType := Eval hnf in [subCountType of setpartn].
  Definition setpartn_finMixin := Eval hnf in [finMixin of setpartn by <:].
  Canonical setpartn_finType := Eval hnf in FinType setpartn setpartn_finMixin.
  Canonical setpartn_subFinType := Eval hnf in [subFinType of setpartn].

  Lemma setpartnP (p : setpartn) : partition p setT.
  Proof. by case: p. Qed.

  Lemma setpartn_cover (p : setpartn) x : x \in cover p.
  Proof.
    have := setpartnP p => /and3P [] /eqP -> _ _.
    by rewrite inE.
  Qed.

  Lemma setpartn_inter (p : setpartn) S1 S2 x :
    S1 \in p -> S2 \in p -> x \in S1 -> x \in S2 -> S1 = S2.
  Proof.
    move=> HS1 HS2 Hx1 Hx2; apply/eqP.
    have:= setpartnP p => /and3P [] _ /trivIsetP/(_ _ _ HS1 HS2)/contraR Htmp _.
    move: Htmp; apply; apply/(introN idP); rewrite -setI_eq0 => /eqP/setP/(_ x).
    by rewrite in_set0 in_setI Hx1 Hx2 /=.
  Qed.

  Lemma is_finer_setpart_subset (p1 p2 : setpartn) :
    is_finer p1 p2 -> is_finer p2 p1 -> p1 \subset p2.
  Proof.
    move: p1 p2 => [] p1 Hp1 [] p2 Hp2 /=.
    move=> /is_finerP H12 /is_finerP H21.
    apply/subsetP => s1 Hs1.
    move/(_ s1 Hs1) : H12 => [] s2 [] Hs2 Hs12.
    move/(_ s2 Hs2) : H21 => [] s1' [] Hs1' Hs21.
    suff H' : s1 = s1'.
      subst s1'; rewrite (_ : s1 = s2) //.
      by apply/eqP; rewrite eqEsubset Hs12 Hs21.
    apply/eqP.
    have {Hs12 Hs21 s2 Hs2 p2 Hp2} := subset_trans Hs12 Hs21.
    apply contraLR => Hdiff.
    move: Hp1 => /and3P [] _ /trivIsetP /(_ _ _ Hs1 Hs1' Hdiff) Hdisj Hnon0.
    have /set0Pn : s1 != set0 by move: Hnon0; apply contra => /eqP <-.
    move=> [] x Hx; apply (introN idP) => /subsetP/(_ _ Hx) Hx'.
    move: Hdisj; rewrite -setI_eq0 => /eqP/setP/(_ x).
    by rewrite in_set0 in_setI Hx Hx' /=.
  Qed.

  Lemma is_finer_setpart_anti (p1 p2 : setpartn) :
    is_finer p1 p2 -> is_finer p2 p1 -> p1 = p2.
  Proof.
    move=> H12 H21; apply/eqP; rewrite eqE /=; rewrite eqEsubset.
    apply/andP; split; exact: is_finer_setpart_subset.
  Qed.

End Defs.


(* Partition of the empty set *)

Lemma set_ordinal0 : [set: 'I_0] = set0.
Proof. apply/setP => [[x Hx]]; exfalso; by move: Hx; rewrite ltn0. Qed.

Lemma subset_ordinal0 (p : {set 'I_0}) : p = set0.
Proof. apply/setP => [[x Hx]]; exfalso; by move: Hx; rewrite ltn0. Qed.

Lemma part_ordinal0_eq_set0 p : (partition p) [set: 'I_0] -> p = set0.
Proof.
  move=> /and3P [] _ _ Hn0.
  apply/setP => S; rewrite inE (subset_ordinal0 S).
  exact: negbTE.
Qed.

Lemma part_ordinal0 : partition set0 [set: 'I_0].
Proof.
  apply/and3P; split.
  - by rewrite /cover big_set0 set_ordinal0.
  - by rewrite /trivIset /cover !big_set0 cards0.
  - by rewrite in_set0.
Qed.

Let Part0 := SetPartN part_ordinal0.

Lemma setpartn0_eq_set0 (p : setpartn 0) : p = Part0.
Proof.
  case: p => p Hp; apply/eqP;
  by rewrite eqE /= (part_ordinal0_eq_set0 Hp).
Qed.

Lemma enum_setpartn0 : enum (setpartn 0) = [:: Part0 ].
Proof.
  move Hl : (enum _) => l.
  case: l Hl => [|p0 [|p1 l]] Hl.
  - exfalso.
    have:= mem_enum (setpartn 0) Part0.
    by rewrite Hl inE in_nil.
  - by rewrite (setpartn0_eq_set0 p0).
  - exfalso.
    rewrite (setpartn0_eq_set0 p0) (setpartn0_eq_set0 p1) in Hl.
    have:= enum_uniq (setpartn 0); by rewrite Hl /= inE eq_refl /=.
Qed.


Lemma mem_ordinal1 (x : 'I_1) : x = ord0.
Proof. by apply/eqP; case: x => [[| x]]//=. Qed.

Lemma set_ordinal1 : [set: 'I_1] = [set ord0].
Proof. apply/setP => x; by rewrite !inE (mem_ordinal1 x) eq_refl. Qed.

Lemma subset_ordinal1E (S : {set 'I_1}) : (S == set0) || (S == setT).
Proof.
  case: (altP (S =P set0)) => [-> |]//= /set0Pn [] x.
  rewrite (mem_ordinal1 x) => {x} H0; apply/eqP/setP => x.
  by rewrite !inE (mem_ordinal1 x) H0.
Qed.

Lemma subset_ordinal1 (S : {set 'I_1}) : (S = set0) \/ (S = setT).
Proof.
  have:= subset_ordinal1E S => /orP [] /eqP ->.
  by left. by right.
Qed.

Lemma part_ordinal1_eq p : (partition p) [set: 'I_1] -> p = [set setT].
Proof.
  move=> /and3P [] H1 _ Hn0.
  apply/setP => S; rewrite inE.
  case: (subset_ordinal1 S) => [-> | HS].
  - move: Hn0 => /negbTE ->.
    apply esym; apply/negbTE/(introN idP) => /eqP/setP/(_ ord0).
    by rewrite !inE.
  - rewrite {S}HS eq_refl.
    move: H1; rewrite /cover set_ordinal1 => /eqP/setP/(_ ord0).
    rewrite inE eq_refl.
    case: (altP (p =P set0)) => [-> |]/=.
    + by rewrite big_set0 !inE.
    + move/set0Pn => [] S.
      have:= subset_ordinal1 S => [[]] ->.
      * by move: Hn0 => /negbTE ->.
      * by rewrite set_ordinal1 => ->.
Qed.

Lemma part_ordinal1 : partition [set [set: 'I_1]] [set: 'I_1].
Proof.
  apply/and3P; split.
  - by rewrite /cover big_set1.
  - by rewrite /trivIset /cover !big_set1.
  - rewrite in_set1.
    apply/(introN idP) => /eqP/setP/(_ ord0).
    by rewrite set_ordinal1 !inE eq_refl.
Qed.

Let Part1 := SetPartN part_ordinal1.

Lemma setpartn1_eq_set1 (p : setpartn 1) : p = Part1.
Proof.
  case: p => p Hp; apply/eqP;
  by rewrite eqE /= (part_ordinal1_eq Hp).
Qed.

Lemma enum_setpartn1 : enum (setpartn 1) = [:: Part1 ].
Proof.
  move Hl : (enum _) => l.
  case: l Hl => [|p0 [|p1 l]] Hl.
  - exfalso.
    have:= mem_enum (setpartn 1) Part1.
    by rewrite Hl inE in_nil.
  - by rewrite (setpartn1_eq_set1 p0).
  - exfalso.
    rewrite (setpartn1_eq_set1 p0) (setpartn1_eq_set1 p1) in Hl.
    have:= enum_uniq (setpartn 1); by rewrite Hl /= inE eq_refl /=.
Qed.


Require Import ordtype.

Section RefineOrder.

Variable n : nat.

Fact is_finer_porder : PartOrder.axiom (fun p1 p2 : setpartn n => is_finer p1 p2).
Proof.
  split.
  - move=> p; exact: is_finer_refl.
  - move=> p q /andP []; exact: is_finer_setpart_anti.
  - move=> p q r; exact: is_finer_trans.
Qed.

Definition setpartn_pordMixin := PartOrder.Mixin is_finer_porder.
Canonical setpartn_pordType := Eval hnf in POrdType (setpartn n) setpartn_pordMixin.

End RefineOrder.


Section Card.

  Variable n : nat.

  Definition inj_finer_setpart x0 (p : setpartn n) (S : {set 'I_n}) :=
    pblock p (odflt x0 [pick x in S]).

  Lemma inj_finer_setpart_non0 x0 (p : setpartn n) (S : {set 'I_n}) :
    (inj_finer_setpart x0 p S) != set0.
  Proof.
    rewrite /inj_finer_setpart.
    set x := (odflt _ _).
    have Hbl:= pblock_mem (setpartn_cover p x).
    have:= setpartnP p => /and3P [] _ _.
    by apply contra => /eqP <-.
  Qed.

  Lemma inj_finer_setpartP x0 (p1 p2 : setpartn n) (S : {set 'I_n}) :
    is_finer p1 p2 -> S \in p2 -> (inj_finer_setpart x0 p1 S) \subset S.
  Proof.
    move/is_finerP => Hfin HS.
    rewrite /inj_finer_setpart.
    case: pickP => [/= x Hx | Habs].
    - have:= pblock_mem (setpartn_cover p1 x).
      move=> /Hfin {Hfin} [] S2 [] HS2 Hsubs.
      suff -> : S = S2 by [].
      have:= setpartn_cover p1 x.
      rewrite -mem_pblock => /(subsetP Hsubs) Hx2.
      exact: (@setpartn_inter _ p2 _ _ x).
    - exfalso.
      have {Habs} HS0 : S = set0 by apply/setP => x; rewrite Habs inE.
      have:= setpartnP p2 => /and3P [] _ _.
      by rewrite -HS0 HS.
  Qed.

  Lemma is_finer_inj x0 (p1 p2 : setpartn n) :
    is_finer p1 p2 -> {in p2 &, injective (inj_finer_setpart x0 p1)}.
  Proof.
    move=> H S1 S2 HS1 HS2 Heq.
    have:= inj_finer_setpart_non0 x0 p1 S1 => /set0Pn [] x Hx.
    have := inj_finer_setpartP x0 H HS1 => /subsetP/(_ _ Hx) Hx1.
    rewrite {}Heq in Hx.
    have:= inj_finer_setpartP x0 H HS2 => /subsetP/(_ _ Hx) {Hx} Hx2.
    exact: (@setpartn_inter _ p2 _ _ x).
  Qed.

End Card.

Lemma is_finer_card n (p1 p2 : setpartn n) : is_finer p1 p2 -> #|p1| >= #|p2|.
Proof.
  case: n p1 p2 => [|n] p1 p2.
  - by rewrite (setpartn0_eq_set0 p1) (setpartn0_eq_set0 p2) /= cards0.
  - move=> /(is_finer_inj (x0 := ord0))/card_in_imset <-.
    apply subset_leqif_cards; apply/subsetP => S /imsetP [] S2 HS2 ->.
    rewrite /inj_finer_setpart; apply pblock_mem.
    exact: setpartn_cover.
Qed.



