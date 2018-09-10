(** * Combi.Combi.permuted : Listing the Permutations of a tuple or seq *)

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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import tuple bigop path div finset binomial.
From mathcomp Require Import perm fingroup action gproduct.

Require Import tools combclass sorted partition composition multinomial.
Require Import permcomp cycles.

(** * The list of the permuted tuple of a given tuple

The main goal is to show that, given a sequence [s] over an [eqType] there
are only finitely many sequences [s'] which are a permutation of [s] (that is
[perm_eq s s']) and to show that the number is a multinomial coefficient.

- [permuted_tuple t] == a sequence of tuples containing (with duplicates) all
             tuple [t'] such that [perm_eq t t']
- [permuted_seq s] == a sequence of seqs containing (with duplicates) all seqs
             [s'] such that [perm_eq s s']
- [permuted t] == sigma typle for tuple [t'] such that [perm_eq t t'].  this
             is canonically a [fintype], provided the type of the elements of
             [t] is a [countType].

- [permutedact t s] == the [n] tuple [t] permuted by the permutation [s]
- [permuted_action] == the corresponding action of the symmetric group ['S_n]

The main result is the cardinality of the set of permuted of a tuple expressed
as a multinomial [card_permuted_multinomial].
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Section Permuted.

Variable T : eqType.

Section SizeN.

Variable n : nat.

Definition permuted_tuple (t : n.-tuple T) :=
  [seq [tuple tnth t (aperm i p) | i < n] | p : 'S_n ].

Lemma size_permuted_tuple (t : n.-tuple T) : size (permuted_tuple t) = n`!.
Proof using. rewrite /permuted_tuple size_map -cardE; exact: card_Sn. Qed.

Lemma perm_eq_permuted_tuple (s : seq T) (H : size s == n) :
  forall s1, perm_eq s s1 ->
             s1 \in [seq tval t | t <- permuted_tuple (Tuple H)].
Proof using.
set t := Tuple H; have Ht : perm_eq s t by [].
move=> s1 Hss1; rewrite perm_eq_sym in Hss1.
have:= perm_eq_trans Hss1 Ht => /tuple_perm_eqP [p Hs1].
apply/mapP; set t1 := (X in _ = tval X) in Hs1; exists t1; last exact Hs1.
rewrite /permuted_tuple; apply/mapP.
by exists p; first by rewrite mem_enum.
Qed.

Lemma mem_enum_permuted (s t : n.-tuple T) :
  perm_eq s t -> t \in permuted_tuple s.
Proof using.
rewrite perm_eq_sym => /tuple_perm_eqP [perm Hperm].
apply/mapP; exists perm; first by rewrite mem_enum.
by apply val_inj; rewrite /= Hperm.
Qed.

Lemma all_permuted (s : n.-tuple T) :
  all (fun x : n.-tuple T => perm_eq s x) (permuted_tuple s).
Proof using.
apply/allP => t /mapP [/= perm _] ->{t}.
by rewrite perm_eq_sym; apply/tuple_perm_eqP; exists perm.
Qed.

End SizeN.

Definition permuted_seq s :=
  [seq tval t | t <- permuted_tuple (Tuple (eq_refl (size s)))].

Lemma size_permuted_seq s : size (permuted_seq s) = (size s)`!.
Proof using. by rewrite /permuted_seq size_map size_permuted_tuple. Qed.

Lemma eq_seqE s s1 : perm_eq s s1 -> s1 \in permuted_seq s.
Proof using. exact: perm_eq_permuted_tuple. Qed.

End Permuted.


Section FinType.

Variable T : countType.
Variable n : nat.
Variable w : n.-tuple T.

Structure permuted : predArgType :=
  Permuted { tpval :> n.-tuple T; _ : perm_eq w tpval }.

Canonical permuted_subType := Eval hnf in [subType for tpval].
Definition permuted_eqMixin := Eval hnf in [eqMixin of permuted by <:].
Canonical permuted_eqType := Eval hnf in EqType permuted permuted_eqMixin.
Definition permuted_choiceMixin :=
  Eval hnf in [choiceMixin of permuted by <:].
Canonical permuted_choiceType :=
  Eval hnf in ChoiceType permuted permuted_choiceMixin.
Definition permuted_countMixin :=
  Eval hnf in [countMixin of permuted by <:].
Canonical permuted_countType :=
  Eval hnf in CountType permuted permuted_countMixin.
Canonical permuted_subCountType :=
  Eval hnf in [subCountType of permuted].

Let type := sub_undup_finType permuted_subCountType
                              (all_permuted w) (mem_enum_permuted (s := w)).
Canonical permuted_finType := [finType of permuted for type].
Canonical permuted_subFinType := Eval hnf in [subFinType of permuted].

Lemma permutedP (p : permuted) : perm_eq w p.
Proof using. by case: p. Qed.

End FinType.

Hint Resolve permutedP.


Import GroupScope.

(** * Action of ['S_n] on permuted for and [n.-tuple T].

There is no use defining an action on general tuple because most of the lemmas
on actions assume that the type acted upon is a [finType]. We could require
that the underlying type is a [fintype] so that the set of tuple is a
[fintype] too, but the use we have in mind is [T = nat] allowing to deal with
the action on monomials. Instead of that, we decide to act only on the sigma
type [permuted].

*)


Section ActOnTuple.

Variables (T : countType) (n : nat) (w : n.-tuple T).
Implicit Type (t : permuted w).

Local Notation wp := (Permuted (perm_eq_refl w)).

Lemma permutedact_subproof t (s : 'S_n) :
  perm_eq w [tuple tnth t (s^-1 i) | i < n].
Proof using.
apply: (perm_eq_trans (permutedP t)).
by rewrite /= perm_eq_sym; apply/tuple_perm_eqP; exists s^-1.
Qed.
Definition permutedact t s := Permuted (permutedact_subproof t s).

Local Notation "t # s" := (permutedact t s)
  (at level 40, left associativity, format "t # s").

Lemma permutedact_is_action : is_action [set: 'S_n] permutedact.
Proof using.
split => /= [s t1 t2 Heq | t s1 s2 _ _].
- apply val_inj; apply eq_from_tnth => i.
  move: Heq => /(congr1 (fun t => tnth t (s i))).
  by rewrite !tnth_mktuple permK.
- apply val_inj; apply eq_from_tnth => /= i.
  by rewrite !tnth_mktuple invMg permM.
Qed.
Canonical permuted_action := Action permutedact_is_action.
Local Notation pact := permuted_action.

Lemma permuted_action_trans :
  [transitive [set: 'S_n], on [set: permuted w] | pact].
Proof using.
apply/imsetP; exists (Permuted (perm_eq_refl w)); first by [].
apply/setP => /= t; rewrite !inE; apply/esym/orbitP => /=.
have:= permutedP t => /tuple_perm_eqP [s /val_inj Hs].
exists s; first by rewrite inE.
apply val_inj => /=; apply eq_from_tnth => /= i.
by rewrite {1}Hs !tnth_mktuple permKV.
Qed.

Lemma stab_tuple_prod :
  'C[wp | pact] =
  (\prod_(x : seq_sub w) 'C(~:[set i | tnth w i == val x] | 'P))%G.
Proof using.
have Htriv : trivIset [set [set i | tnth w i == val x] | x : seq_sub w].
  apply/trivIsetP => /= X Y.
  move=> /imsetP [/= [x Hx _ /= ->{X}]].
  move=> /imsetP [/= [y Hy _ /= ->{Y}]] Hneq.
  rewrite -setI_eq0; apply/eqP/setP => /= i.
  rewrite !inE; apply (introF idP) => /andP [/eqP ->] /eqP Hxy.
  by move: Hneq; rewrite Hxy eq_refl.
apply/eqP; rewrite bigprodGE eqEsubset; apply/andP; split.
- apply/subsetP => /= s.
  move/astabP/(_ wp); rewrite inE eq_refl => /(_ isT) Ht.
  rewrite -(perm_decE (s := s) Htriv); first last.
  + apply/astabP => /= CS /imsetP [/= x _ ->{CS}].
    apply/astab1P; rewrite astab1_set.
    rewrite !inE /=; apply/subsetP => j.
    rewrite !inE => /eqP <-.
    by rewrite -{1}[w]/(val wp) -Ht tnth_mktuple permK.
  + apply/subsetP => /= i _; apply/bigcupP => /=.
    exists [set i0 | tnth w i0 == tnth w i]; last by rewrite inE.
    by apply/imsetP => /=; exists (SeqSub (mem_tnth i w)) => //=.
  apply group_prod => /= u /imsetP [/= X].
  move=> /imsetP [x Hx ->{X} ->{u}]; apply/mem_gen.
  apply/bigcupP; exists x => //.
  rewrite perm_onE !inE; exact: restr_perm_on.
- rewrite gen_subG; apply/subsetP => /= s /bigcupP [/= x _] Hs.
  rewrite !inE /=; apply/subsetP => j; rewrite !inE => /eqP ->{j}.
  apply/eqP/val_inj/eq_from_tnth => /= i.
  rewrite tnth_mktuple.
  case: (boolP (tnth w i == val x)) => Hl0.
  + move: Hs; rewrite perm_onE inE => /im_perm_on/setP/(_ i).
    rewrite !inE Hl0 => /imsetP [/= j].
    rewrite inE => /eqP H {1}->.
    by rewrite (eqP Hl0) permK.
  + move: Hs => /groupVr; rewrite /= perm_onE inE => /out_perm -> //.
    by rewrite inE.
Qed.

Lemma stab_tuple_dprod :
  'C[wp | pact] =
  \big[dprod/1]_(x : seq_sub w) 'C(~:[set i | tnth w i == val x] | 'P).
Proof using.
rewrite stab_tuple_prod; apply/esym/eqP/bigdprodYP => x /= _.
rewrite !perm_onE.
apply/subsetP => /= s; rewrite !inE negb_and negbK => Ht /=.
have {Ht} : s \in 'C(~:[set i | tnth w i != val x] | 'P).
  move: Ht; rewrite bigprodGE => /gen_prodgP [u [/= f Hf ->{s}]].
  apply group_prod => j _; move/(_ j): Hf => /bigcupP [k Hk] /=.
  rewrite !perm_onE !inE /perm_on => /subset_trans; apply.
  by apply/subsetP => C; rewrite !inE => /eqP ->.
rewrite perm_onE inE => on_neqi; apply/andP; split.
- case: (altP (s =P 1)) => //=; apply contra => on_eqi.
  apply/eqP/permP => /= i; rewrite perm1.
  case: (boolP (tnth w i == val x)) => [HC | /negbTE HC].
  + by rewrite (out_perm on_neqi) // !inE HC.
  + by rewrite (out_perm on_eqi) // !inE HC.
- apply/centP => /= u; move: on_neqi.
  rewrite inE !support_perm_on -[support u \subset _]setCS => on_neqi on_eqi.
  apply support_disjointC; rewrite disjoints_subset.
  apply: (subset_trans on_neqi); apply: (subset_trans _ on_eqi).
  by apply/subsetP => X; rewrite !inE.
Qed.

Close Scope group_scope.

Lemma card_stab_tuple :
  #|('C[wp | pact])%G| = \prod_(x : seq_sub w) (count_mem (val x) w)`!.
Proof using.
rewrite -(bigdprod_card (esym stab_tuple_dprod)).
apply eq_bigr => [[i _]] _ /=.
rewrite card_astab_perm; congr (_)`!.
rewrite -map_tnth_enum.
rewrite cardE /enum_mem size_filter /= count_map count_filter.
by apply eq_count => X; rewrite !inE andbC.
Qed.

Lemma card_permuted_prod :
  #|[set: permuted w]| * \prod_(x : seq_sub w) (count_mem (val x) w)`! = n`!.
Proof using.
rewrite -card_Sn -card_stab_tuple.
rewrite -(atransPin (subxx _) permuted_action_trans (x := wp)) ?inE //.
by rewrite -cardsT /= -(card_orbit_in_stab pact wp (subxx _)) /= setTI.
Qed.

Lemma dvdn_card_permuted :
  \prod_(x : seq_sub w) (count_mem (val x) w)`! %| n`!.
Proof using.
by apply/dvdnP; exists #|[set: permuted w]|; rewrite card_permuted_prod.
Qed.

Lemma card_permuted_seq_sub :
  #|[set: permuted w]| = n`! %/ \prod_(x : seq_sub w) (count_mem (val x) w)`!.
Proof using.
rewrite -card_permuted_prod mulnK //.
by apply prodn_gt0 => i; apply: fact_gt0.
Qed.

Lemma card_permuted :
  #|[set: permuted w]| = n`! %/ \prod_(x <- undup w) (count_mem x w)`!.
Proof using. by rewrite card_permuted_seq_sub -big_seq_sub. Qed.

Lemma size_count_mem_undup (s : seq T) :
  size s = \sum_(j <- undup s) count_mem j s.
Proof using.
have -> : size s = \sum_(i <- s) 1.
  by elim: s => [|s0 s /= ->] /=; rewrite ?big_nil // big_cons add1n.
rewrite -big_undup_iterop_count /=; apply eq_bigr => i _.
rewrite Monoid.iteropE /=.
by elim: (count_mem i s) => {i} //= i ->.
Qed.

Theorem card_permuted_multinomial :
  #|[set: permuted w]| = 'C[[seq count_mem x w | x <- undup w]].
Proof using.
rewrite card_permuted multinomial_factd big_map; congr (_`! %/ _).
by rewrite -sumnE  -{1}(size_tuple w) big_map size_count_mem_undup.
Qed.

End ActOnTuple.
