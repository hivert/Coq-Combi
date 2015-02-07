(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop.

Require Import tools.

Set Implicit Arguments.
Unset Strict Implicit.


Lemma sum_count_mem (T : finType) (P : pred T) l :
   \sum_(i | P i) (count_mem i) l = count P l.
Proof.
  rewrite -size_filter -(eq_filter (mem_enum P)).
  rewrite -big_filter filter_index_enum.
  have := enum_uniq P.
  elim: (enum P) => [_ | p1 p IHp].
    rewrite big_nil (eq_filter (a2 := pred0)); first by rewrite filter_pred0.
    move=> i /=; by apply in_nil.
  rewrite big_cons => /= /andP [] Hp1 /IHp{IHp} ->.
  rewrite size_filter.
  rewrite (eq_count (a1 := mem (p1 :: p)) (a2 := predU (pred1 p1) (mem p))); first last.
    move => i /=; by rewrite in_cons.
  rewrite -[RHS]addn0.
  have /eq_count Hi : predI (pred1 p1) (mem p) =1 pred0.
    move=> i /=; apply (introF idP) => /andP [] /eqP -> Hp1'.
    by rewrite Hp1' in Hp1.
  have := Hi l; rewrite count_pred0 => <-.
  by rewrite count_predUI size_filter.
Qed.


Section SubtypeSeq.

Variable T : countType.
Variable P : pred T.
Variable TP : subCountType P.
(* Variable subT : subType P.
Let TP := sub_choiceType subT. *)

Fixpoint subType_seq l {struct l} :=
  match l as l1 return all P l1 -> seq TP with
    | [::]     => fun _ : true = true => [::]
    | l0 :: ll => fun Hall =>
                    match elimTF andP Hall with
                      | conj H0 Hl => (Sub l0 H0) :: (subType_seq ll Hl)
                    end
  end.


Variable lst : seq T.
Hypothesis HallP : all P lst.

Lemma subType_seqP : map val (subType_seq HallP) = lst.
Proof.
  elim: lst HallP => [//= | l0 l IHl] /=.
  case/andP => /= H0 Hall0; by rewrite IHl SubK.
Qed.

Section SubCount.

Hypothesis Hcount : forall x : T, P x -> count_mem x lst = 1.

Lemma finite_subP : Finite.axiom (subType_seq HallP).
Proof.
  move=> xP; rewrite (eq_count (a2 := (pred1 (val xP)) \o val)).
  - rewrite -count_map subType_seqP Hcount //=; by apply valP.
  - move=> i; apply/(sameP idP); apply(iffP idP) => /eqP H; apply /eqP.
    + by apply val_inj.
    + by rewrite H.
Qed.

Definition sub_finMixin := Eval hnf in FinMixin finite_subP.
Definition sub_finType := Eval hnf in FinType TP sub_finMixin.
Definition sub_subFinType := Eval hnf in [subFinType of sub_finType].

Lemma enum_subP : map val (enum sub_finType) = lst.
Proof. by rewrite enumT unlock /= subType_seqP. Qed.

End SubCount.



Section SubUndup.

Hypothesis HPin : forall x : T, P x -> x \in lst.

Lemma finite_sub_undupP :
  Finite.axiom (undup (subType_seq HallP)).
Proof.
  rewrite /Finite.axiom => x.
  rewrite count_uniq_mem; last by apply undup_uniq.
  rewrite mem_undup.
  have := HPin (valP x); by rewrite -{1}subType_seqP (mem_map val_inj) => ->.
Qed.

Definition sub_undup_finMixin := Eval hnf in FinMixin finite_sub_undupP.
Definition sub_undup_finType := Eval hnf in FinType TP sub_undup_finMixin.
Definition sub_undup_subFinType := Eval hnf in [subFinType of sub_undup_finType].

Lemma enum_sub_undupP : map val (enum sub_undup_finType) = undup lst.
Proof.
  rewrite enumT unlock /= -{2}subType_seqP.
  elim: lst HallP => [//= | l0 l IHl] /=.
  case/andP => /= H0 Hall0.
  rewrite mem_map; last by apply val_inj.
  case: (Sub l0 H0 \in subType_seq Hall0); by rewrite /= IHl.
Qed.

End SubUndup.

End SubtypeSeq.


Section SubtypesDisjointUnion.

Variable T : countType.
Variable TI : countType.
Variable FI : T -> TI.
Variable P : pred T.
Variable Pi : TI -> pred T.
Variable PI : pred TI.

Variable TPI : subFinType PI.
Variable TPi : forall i : TPI, subFinType (Pi (val i)).

Hypothesis HPTi : forall i : TPI, (predI P (pred1 (val i) \o FI)) =1 (Pi (val i)).
Hypothesis Hpart : forall x : T, P x -> PI (FI x).

Definition enum_union := flatten [seq map val (enum (TPi i)) | i <- enum TPI].

Lemma all_unionP : all P enum_union.
Proof.
  rewrite /enum_union.
  apply/allP => x /flatten_mapP [] i /mapP [] ifin Hi -> {i} /mapP [] xfin Hx -> {x}.
  have /= := valP xfin; by rewrite -HPTi /= => /andP [].
Qed.

Lemma count_unionP x : P x -> count_mem x enum_union = 1.
Proof.
  move=> HPx; have:= HPx; rewrite /enum_union => /Hpart H.
  rewrite count_flatten -2!map_comp; set ci := (X in map X _).
  set ix := @Sub TI PI TPI (FI x) H.
  have {ci} /eq_map -> : ci =1 (pred_of_simpl (pred1 ix)).
    rewrite /ci {ci} => i /=.
    case: (altP (i =P ix)) => [-> {i} | Hneq].
    - rewrite count_map /=.
      have Hix : Pi (val ix) x by rewrite -HPTi /= SubK HPx eq_refl.
      pose xPI := @Sub T _ (TPi ix) x Hix.
      rewrite (eq_count (a2 := pred1 xPI)); first last.
        move=> y /=.
        apply/(sameP idP); apply(iffP idP) => /eqP HH; apply /eqP.
        + by rewrite HH SubK.
        + apply val_inj; by rewrite HH SubK.
      rewrite enumT /=; by apply (@enumP (TPi ix)).
    - apply/count_memPn; move: Hneq; apply contra.
      move=> /mapP [] xfin _ Hx.
      apply/eqP; apply val_inj; rewrite SubK.
      have /= := valP xfin; by rewrite -HPTi Hx=> /andP [] _ /eqP ->.
  rewrite sumn_count /=.
  by apply (@enumP TPI).
Qed.

Variable TP : subCountType P.

Let union_enum := subType_seq TP all_unionP.

Lemma subType_unionP : map val union_enum = enum_union.
Proof. by apply subType_seqP. Qed.

Lemma finite_unionP : Finite.axiom union_enum.
Proof. apply finite_subP => x; by apply count_unionP. Qed.

Definition union_finMixin := Eval hnf in FinMixin finite_unionP.
Definition union_finType := Eval hnf in FinType TP union_finMixin.
Definition union_subFinType := Eval hnf in [subFinType of union_finType].

Lemma enum_union_finTypeE :
  map val (enum union_finType) = enum_union.
Proof. by rewrite enumT unlock subType_seqP. Qed.

End SubtypesDisjointUnion.