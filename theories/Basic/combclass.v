(** * Combi.Basic.combclass : Fintypes for Combinatorics *)
(******************************************************************************)
(*     Copyright (C) 2014 2015 Florent Hivert <florent.hivert@lri.fr>         *)
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
(** The goal of this file is to define various way to easily build finite
subtype of a countable type knowing a lists of its elements. We provide four
ways, three from a list (see [sub_subFinType], [sub_uniq_subFinType] and
[sub_undup_subFinType] below) and one by taking the disjoint union of already
constructed subfintypes (see [union_subFinType] below].  *)

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop tools.

Set Implicit Arguments.
Unset Strict Implicit.

(** A missing lemma: fintypes in bijection have the same cardinality          *)

(** TODO : Contribute to SSReflect/fintype.v                                  *)
Section BijCard.

Variables U V : finType.
Variable f : U -> V.

Lemma bij_card : bijective f -> #|U| = #|V|.
Proof.
  move=> [] g Hfg Hgf.
  apply anti_leq; apply/andP; split.
  - rewrite -(card_codom (can_inj Hfg)); exact: max_card.
  - rewrite -(card_codom (can_inj Hgf)); exact: max_card.
Qed.

End BijCard.

(** Summing [count_mem] in a [finType] *)
Lemma sum_count_mem (T : finType) (P : pred T) l :
   \sum_(i | P i) (count_mem i) l = count P l.
Proof.
  rewrite -size_filter -(eq_filter (mem_enum P)).
  rewrite -big_filter filter_index_enum.
  elim: (enum P) (enum_uniq P) => [_ | p1 p IHp].
    rewrite big_nil (eq_filter (a2 := pred0)); first by rewrite filter_pred0.
    move=> i /=; exact: in_nil.
  rewrite big_cons => /= /andP [] Hp1 /IHp{IHp} ->.
  rewrite size_filter.
  rewrite (eq_count (a1 := mem (p1 :: p)) (a2 := predU (pred1 p1) (mem p))); first last.
    move => i /=; by rewrite in_cons.
  rewrite -[RHS]addn0.
  have /eq_count/(_ l) : predI (pred1 p1) (mem p) =1 pred0.
    move=> i /=; apply (introF idP) => /andP [] /eqP -> Hp1'.
    by rewrite Hp1' in Hp1.
  rewrite count_pred0 => <-.
  by rewrite count_predUI size_filter.
Qed.

(** * Building subtype from a sequence

Here is how to construct a fintype from a list: we are given
- a type [T] which is a [countType]
- a type [TP] which is [subCountType] of [T] for a predicate [P].
- a list [lst] of element from [T] whose element veryfies the predicate [P].

We define three possible ways to provide [TP] with a [subFinType] structure:
- [sub_subFinType] which suppose that any element verifying [P] appears only
  once in [lst];
- [sub_uniq_subFinType] which suppose that any element verifying [P] appears in
  [lst] and that [lst] is duplicate free ([uniq]);
- [sub_undup_subFinType] which suppose that any element verifying [P] appears in
  [lst] and remove the duplicate elements.
*)

Section SubtypeSeq.

Variable T : countType.
Variable P : pred T.
Variable TP : subCountType P.

Fixpoint subType_seq l {struct l} :=
  match l as l1 return all P l1 -> seq TP with
    | [::]     => fun _ : true = true => [::]
    | l0 :: ll => fun Hall =>
                    match elimTF andP Hall with
                      | conj H0 Hl => (Sub l0 H0) :: (subType_seq ll Hl)
                    end
  end.


Variable lst : seq T.

(** ** Method 1 - Each element appears only once *)
Section SubCount.

Hypothesis HallP : all P lst.
Hypothesis Hcount : forall x : T, P x -> count_mem x lst = 1.

Lemma subType_seqP : map val (subType_seq HallP) = lst.
Proof.
  elim: lst HallP => [| l0 l IHl] //=.
  case/andP => /= H0 Hall0; by rewrite IHl SubK.
Qed.

Lemma sub_enumE : lst =i P.
Proof.
  move=> i.
  apply/idP/idP; rewrite !unfold_in.
  - by move=> /(allP HallP).
  - move=> /Hcount => H; apply/count_memPn; by rewrite H.
Qed.

Lemma finite_subP : Finite.axiom (subType_seq HallP).
Proof.
  move=> xP; rewrite (eq_count (a2 := (pred1 (val xP)) \o val)).
  - rewrite -count_map subType_seqP Hcount //=; exact: valP.
  - move=> i; apply/idP/idP=> /eqP H; apply/eqP; by [rewrite H | apply val_inj].
Qed.

Definition sub_finMixin := Eval hnf in FinMixin finite_subP.
Definition sub_finType := Eval hnf in FinType TP sub_finMixin.
Definition sub_subFinType := Eval hnf in [subFinType of sub_finType].

Lemma enum_subE : map val (enum sub_finType) = lst.
Proof. by rewrite enumT unlock /= subType_seqP. Qed.

Lemma card_subE : #|sub_finType| = size lst.
Proof. by rewrite cardE -(size_map val) /= enum_subE. Qed.

End SubCount.


(** ** Method 2 - Each element appears and the lists is uniq *)
Section SubUniq.

Hypothesis Huniq : uniq lst.
Hypothesis HE : lst =i P.

Lemma Hallp : all P lst.
Proof. apply/allP => x; by rewrite HE. Qed.

Lemma Hcount x : P x -> count_mem x lst = 1.
Proof.
  have:= HE x; rewrite !unfold_in => <-.
  by rewrite (count_uniq_mem _ Huniq) unfold_in => ->.
Qed.

Definition sub_uniq_finMixin := Eval hnf in sub_finMixin Hallp Hcount.
Definition sub_uniq_finType := Eval hnf in FinType TP sub_uniq_finMixin.
Definition sub_uniq_subFinType := Eval hnf in [subFinType of sub_uniq_finType].

Lemma enum_sub_uniqE : map val (enum sub_uniq_finType) = lst.
Proof. by rewrite enumT unlock /= subType_seqP. Qed.

Lemma card_sub_uniqE : #|sub_uniq_finType| = size lst.
Proof. by rewrite cardE -(size_map val) /= enum_subE. Qed.

End SubUniq.


(** ** Method 3 - Each element appears, we remove the duplicates *)
Section SubUndup.

Hypothesis HallP : all P lst.
Hypothesis HPin : forall x : T, P x -> x \in lst.

Lemma finite_sub_undupP :
  Finite.axiom (undup (subType_seq HallP)).
Proof.
  move=> x; rewrite count_uniq_mem; last exact: undup_uniq.
  rewrite mem_undup.
  have:= HPin (valP x); by rewrite -{1}subType_seqP (mem_map val_inj) => ->.
Qed.

Definition sub_undup_finMixin := Eval hnf in FinMixin finite_sub_undupP.
Definition sub_undup_finType := Eval hnf in FinType TP sub_undup_finMixin.
Definition sub_undup_subFinType := Eval hnf in [subFinType of sub_undup_finType].

Lemma enum_sub_undupE : map val (enum sub_undup_finType) = undup lst.
Proof.
  rewrite enumT unlock /= -{2}subType_seqP.
  elim: lst HallP => [//= | l0 l IHl] /=.
  case/andP=> /= H0 Hall0.
  rewrite mem_map; last exact: val_inj.
  case: (Sub l0 H0 \in subType_seq Hall0); by rewrite /= IHl.
Qed.

End SubUndup.

End SubtypeSeq.


(** * Finite subtype obtained as a finite the dijoint union of finite subtypes

Here is how to construct a union of disjoint finite subtype of a countable
type. More precisely, we want to define a type for

    <<U := Union_(i : TI | Pi i) TPi i>>

For the constructed type[U], we need the following data:
- a type [T] which is a [countType].
- a type [TP] which is [subCountType] of [T] for a predicate [P].
The index type must be also finite, it should be given by
- a type [TI] which is a [countType].
- a type [TPI] which is [subCountType] of [TI] for a predicate [PI].
For all index [i : TPI], there must be a finite type, given by
- a type [TPi i] which is a [subFinType (Pi (val i))] for a predicate [Pi i].
Finally the sets <<{ { x | Pi i } | PI i }>> should define a partition
of <<{ x | P x }>>. This is ensured by providing
- a map [FI : T -> TI] which recover the index of an element [x] of [T].
Together with the two following requirements:
- for all index [i : TPi] and [x : T], the statement [Pi i x] must be
  equivalent to [P x && i == FI x].
- forall [x : T], such that [P x] the assertion [PI (FI x)] must holds.
From all these data [union_subFinType] is a [subFinType] of [T] for the
predicate [P] that is a [subFinType] structure for [TP].

See [stpn_subFinType] and [yamn_subFinType] for example of usage.
*)
Section SubtypesDisjointUnion.

Variable T : countType.
Variable P : pred T.
Variable TP : subCountType P.

Variable TI : countType.
Variable PI : pred TI.
Variable TPI : subFinType PI.

Variable Pi : TI -> pred T.
Variable TPi : forall i : TPI, subFinType (Pi (val i)).

Variable FI : T -> TI.
Hypothesis HPTi : forall i : TPI, (predI P (pred1 (val i) \o FI)) =1 (Pi (val i)).
Hypothesis Hpart : forall x : T, P x -> PI (FI x).

Definition enum_union := flatten [seq map val (enum (TPi i)) | i <- enum TPI].

Lemma all_unionP : all P enum_union.
Proof.
  rewrite /enum_union.
  apply/allP => x /flatten_mapP [] i /mapP [] ifin Hi -> {i} /mapP [] xfin Hx -> {x}.
  have:= valP xfin; by rewrite -HPTi /= => /andP [].
Qed.

Lemma count_unionP x : P x -> count_mem x enum_union = 1.
Proof.
  move=> HPx; have:= HPx; rewrite /enum_union => /Hpart H.
  rewrite count_flatten -2!map_comp.
  pose ix := @Sub TI PI TPI (FI x) H.
  rewrite (eq_map (f2 := fun i => i == ix : nat)); first last.
    move=> i /=.
    case: (altP (i =P ix)) => [-> {i} | Hneq].
    - rewrite count_map /=.
      have Hix : Pi (val ix) x by rewrite -HPTi /= SubK HPx eq_refl.
      pose xPI := @Sub T _ (TPi ix) x Hix.
      rewrite (eq_count (a2 := pred1 xPI)); first last.
        move=> y /=; apply/idP/idP => /eqP HH; apply /eqP.
        + apply val_inj; by rewrite HH SubK.
        + by rewrite HH SubK.
      rewrite enumT /=; exact: (@enumP (TPi ix)).
    - apply/count_memPn; move: Hneq; apply contra => /mapP [] xfin _ Hx.
      apply/eqP; apply val_inj; rewrite SubK.
      have:= valP xfin; by rewrite /= -HPTi Hx=> /andP [] _ /eqP ->.
  rewrite sumn_count /=; exact: (@enumP TPI).
Qed.

Let union_enum := subType_seq TP all_unionP.

Lemma subType_unionE : map val union_enum = enum_union.
Proof. exact: subType_seqP. Qed.

Lemma finite_unionP : Finite.axiom union_enum.
Proof. apply finite_subP => x; exact: count_unionP. Qed.

Definition union_finMixin := Eval hnf in FinMixin finite_unionP.
Definition union_finType := Eval hnf in FinType TP union_finMixin.
Definition union_subFinType := Eval hnf in [subFinType of union_finType].

Lemma enum_unionE :
  map val (enum union_finType) = enum_union.
Proof. by rewrite enumT unlock subType_seqP. Qed.

Lemma card_unionE : #|union_finType| = \sum_(i : TPI) #|TPi i|.
Proof.
  rewrite cardE -(size_map val) /= enum_unionE.
  rewrite /enum_union size_flatten /shape -map_comp.
  rewrite (eq_map (f2 := fun i => #|TPi i|)); first last.
    move=> i /=; by rewrite size_map cardE.
  rewrite /index_enum -enumT.
  elim: (enum TPI) => [| i0 I IHI] /=; first by rewrite big_nil.
  by rewrite big_cons IHI.
Qed.

End SubtypesDisjointUnion.
