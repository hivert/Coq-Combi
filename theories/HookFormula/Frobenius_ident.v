(** * Combi.hook.Frobenius_ident : Frobenius identity *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * A proof of Frobenius identity:

The goal of this file is to prove the following identities:
[[
Frobenius_ident n :
    n`! = \sum_(p : 'P_n) (n`! %/ (hook_length_prod p))^2.
]]
and
[[
Theorem Frobenius_ident_rat n :
    1 / (n`!)%:Q = \sum_(p : 'P_n) 1 / (hook_length_prod p)%:Q ^+ 2.
]]

TODO: The following proof is unnecessarily complicated, involving the
construction of several [finType]. This should be simplified.
 ******)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype choice ssrnat seq
        ssrint div rat fintype bigop path ssralg ssrnum.
(* Import bigop before ssralg/ssrnum to get correct printing of \sum \prod*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import ordtype tools combclass partition tableau Schensted std stdtab.
Require Import hook.


Section Identity.

Definition is_stdtab_pair_of_shape sh p :=
  (is_stdtab_of_shape sh p.1) && (is_stdtab_of_shape sh p.2).
Definition is_stdtab_pair_of_n n p :=
  [&& (is_stdtab_of_n n p.1), (is_stdtab_of_n n p.2) & (shape p.1 == shape p.2)].

Variable n : nat.

Section Shape.

Variable sh : 'P_n.

Definition stpsh : predArgType := ((stdtabsh sh) * (stdtabsh sh))%type.
Definition seq_of_stpsh (p : stpsh) := let: (p1, p2) := p in (val p1, val p2).
Definition stpsh_of_seq p : is_stdtab_pair_of_shape sh p -> stpsh.
Proof.
by move=> /andP [] /(@StdtabSh sh) p1 /(@StdtabSh sh) p2; apply: (p1, p2).
Defined.

Lemma stpshP (p : stpsh) : is_stdtab_pair_of_shape sh (seq_of_stpsh p).
Proof using.
rewrite /is_stdtab_pair_of_shape.
case: p => [p1 p2] /=.
by rewrite !stdtabshP !shape_stdtabsh !eq_refl.
Qed.

Lemma seq_of_stpshK p : (stpsh_of_seq (stpshP p)) = p.
Proof using.
apply/eqP; rewrite /stpsh_of_seq /eq_op /=.
apply/andP; split; case: p => [[p1 H1] [p2 H2]] /=; apply /eqP => /=.
- by case: (elimTF _ _) => /= H _; apply: val_inj.
- by case: (elimTF _ _) => /= _ H; apply: val_inj.
Qed.

Lemma stpsh_of_seqK p (Hp : is_stdtab_pair_of_shape sh p) :
  seq_of_stpsh (@stpsh_of_seq p Hp) = p.
Proof using.
rewrite /stpsh_of_seq /=.
case: (elimTF _ _) => /= _ _.
by case: p {Hp}.
Qed.

Lemma stpsh_val_rect :
  forall F : stpsh -> Type,
    (forall p Px, F (@stpsh_of_seq p Px)) ->
    forall u : stpsh, F u.
Proof using. by move=> F H p; rewrite -(seq_of_stpshK p); apply: H. Qed.

Canonical stpsh_subType :=
  SubType _ seq_of_stpsh stpsh_of_seq stpsh_val_rect stpsh_of_seqK.
Definition stpsh_subCountType := Eval hnf in [subCountType of stpsh_subType].
(* We can't write simply
Canonical stpsh_finType := [finType of stpsh].
Canonical stpsh_subFinType := Eval hnf in [subFinType of stpsh_finType].
because there is a discrepancy on the mixin fot the choiceType *)

Lemma enum_stpshP : Finite.axiom (T:=stpsh_subCountType) (enum stpsh).
Proof using.
rewrite /Finite.axiom => [[p1 p2]].
rewrite enumT /= -(@enumP _ (p1, p2)).
by apply eq_count => [[x1 x2]] /=.
Qed.

Definition stpsh_finMixin := Eval hnf in FinMixin enum_stpshP.
Definition stpsh_finType := Eval hnf in FinType stpsh_subCountType stpsh_finMixin.
Definition stpsh_subFinType := Eval hnf in [subFinType of stpsh_finType].

Lemma card_stpsh : #|{:stpsh_subFinType}| = #|{:stdtabsh sh}|^2.
Proof using.
by rewrite -mulnn -card_prod !cardE enumT unlock /=.
Qed.

End Shape.


Lemma stpn_PredEq (ev : intpartn n) :
  predI (is_stdtab_pair_of_n n) (pred1 (val ev) \o shape \o (fun x => x.1)) =1
  is_stdtab_pair_of_shape ev.
Proof using.
move=> [p1 p2] /=; rewrite /is_stdtab_pair_of_n /is_stdtab_pair_of_shape /=.
case: (altP (shape p1 =P ev)) => [Hsh1|]; last by rewrite !andbF /=.
rewrite [shape p1 == _]eq_sym Hsh1 !andbT.
case: (altP (shape p2 =P ev)) => [Hsh2|]; last by rewrite ?andbF /=.
by rewrite !andbT /size_tab Hsh1 Hsh2 intpartn_sumn eq_refl !andbT.
Qed.

Lemma stpn_partition_shape tabp :
  is_stdtab_pair_of_n n tabp -> is_part_of_n n ((shape \o (fun x => x.1)) tabp).
Proof using.
rewrite /is_stdtab_pair_of_n; move: tabp => [p1 p2] /= /andP [].
rewrite /size_tab => /andP [] /andP [] H _ -> _ /=.
exact: (is_part_sht H).
Qed.

Structure stpn : Set :=
  STPN {stpnval :> seq (seq nat) * seq (seq nat);
        _ : is_stdtab_pair_of_n n stpnval }.
Canonical stpn_subType := Eval hnf in [subType for stpnval].
Definition stpn_eqMixin := Eval hnf in [eqMixin of stpn by <:].
Canonical stpn_eqType := Eval hnf in EqType stpn stpn_eqMixin.
Definition stpn_choiceMixin := Eval hnf in [choiceMixin of stpn by <:].
Canonical stpn_choiceType := Eval hnf in ChoiceType stpn stpn_choiceMixin.
Definition stpn_countMixin := Eval hnf in [countMixin of stpn by <:].
Canonical stpn_countType := Eval hnf in CountType stpn stpn_countMixin.
Canonical stpn_subCountType := Eval hnf in [subCountType of stpn].

Definition stpn_unionType :=
  union_finType
    stpn_subCountType
    (Pi := fun sh : seq nat => is_stdtab_pair_of_shape sh)
    (fun p : 'P_n => (stpsh_subFinType p))
    stpn_PredEq stpn_partition_shape.
Canonical stpn_finType := Eval hnf in [finType of stpn for stpn_unionType].
Canonical stpn_subFinType := Eval hnf in [subFinType of stpn].

Lemma card_stpn : #|{:stpn}| = \sum_(p : 'P_n) (n`! %/ (hook_length_prod p))^2.
Proof using.
rewrite card_unionE.
rewrite (eq_bigr (fun sh : 'P_n => #|{:stdtabsh sh}|^2)); first last.
  by move=> i _; rewrite card_stpsh.
apply eq_bigr => sh _.
by rewrite HookLengthFormula intpartn_sumn.
Qed.

Lemma RSstdmapP (s : stdwordn n) : is_stdtab_pair_of_n n (RStabmap s).
Proof using.
have:= RStabmap_spec s; have:= RStabmapE s.
rewrite /is_stdtab_pair_of_n /is_RStabpair /=.
move H : (RStabmap s) => [p q] /= HRS /and3P [] Hp Hq /eqP Hsh.
rewrite /size_tab -Hsh Hq eq_refl /= !andbT.
rewrite HRS RSstdE stdwordnP /=.
by rewrite -/(size_tab _) size_RS size_sdtn eq_refl !andbT.
Qed.
Definition RSstd (s : stdwordn n) : stpn := STPN (RSstdmapP s).

Lemma rspair_stpnP (p : stpn) : is_RStabpair (val p).
Proof using.
rewrite /is_RStabpair; case: p => [[p q]] /=.
by rewrite /is_stdtab_pair_of_n /= =>
  /and3P [] /andP [] /andP [] -> _ _ /andP [] -> _ ->.
Qed.
Definition rspair_stpn (p : stpn) : (rstabpair [inhOrdType of nat]) :=
  RSTabPair (rspair_stpnP p).
Lemma RSstdmap_invP (p : stpn) : is_std_of_n n (RStabinv (rspair_stpn p)).
Proof using.
have /= := RStabinvK (rspair_stpn p).
rewrite /RStab /= => /(congr1 (@val _ _ _)) => /= Hp.
rewrite /is_std_of_n /=; apply/andP; split.
- rewrite -RSstdE -RStabmapE {}Hp.
  by case: p => [[p q]]; rewrite /is_stdtab_pair_of_n /= => /andP [] /andP [].
- rewrite -size_RS -RStabmapE {}Hp.
  by case: p => [[p q]]; rewrite /is_stdtab_pair_of_n /= => /andP [] /andP [].
Qed.
Definition RSstdinv (p : stpn) : stdwordn n := StdWordN (RSstdmap_invP p).

Lemma RSstdinvK : cancel RSstdinv RSstd.
Proof using.
move=> pq; have:= RStabinvK (rspair_stpn pq).
rewrite /RStab /= => /(congr1 (@val _ _ _)) => /= Hpq.
move: pq Hpq => [[p q]] Hpq; rewrite /RSstd /RSstdinv /= => H.
exact: val_inj.
Qed.
Lemma RSstdK : cancel RSstd RSstdinv.
Proof using.
move=> s /=; apply val_inj; rewrite /= -(RStabK s).
by congr (RStabinv _); apply: val_inj.
Qed.
Lemma bijRSstd : bijective RSstd.
Proof using. by exists RSstdinv; [exact: RSstdK | exact: RSstdinvK]. Qed.

Theorem Frobenius_ident : n`! = \sum_(p : 'P_n) (n`! %/ (hook_length_prod p))^2.
Proof using.
by rewrite -{1}card_stdwordn -card_stpn; apply: bij_card bijRSstd.
Qed.

Open Scope ring_scope.

Import GRing.Theory.
Import Num.Theory.

Theorem Frobenius_ident_rat :
  1 / (n`!)%:Q = \sum_(p : 'P_n) 1 / (hook_length_prod p)%:Q ^+ 2.
Proof using.
rewrite -[RHS]mulr1.
have Hfn0 : n`!%:Q != 0 by rewrite intr_eq0 eqz_nat -lt0n fact_gt0.
rewrite -{5}(@divff _ ((n`!%:Q) ^+ 2)); last by rewrite sqrf_eq0.
rewrite mulrA mulr_suml.
rewrite (eq_bigr (fun p : 'P_n => ((n`! %/ (hook_length_prod p)) ^ 2)%N%:Q)); first last.
  move=> p _; rewrite PoszM intrM.
  have -> : (n`! %/ hook_length_prod p)%:Q = (n`!)%:Q / (hook_length_prod p)%:Q.
    rewrite -[LHS]mulr1 -{2}(@divff _ (hook_length_prod p)%:Q); first last.
      by rewrite intr_eq0 eqz_nat /=; apply: (hook_length_prod_non0 p).
    rewrite !mulrA -intrM -PoszM.
    have:= hook_length_prod_div p.
    by rewrite intpartn_sumn dvdn_eq => /eqP ->.
  by rewrite -expr2 expr_div_n mulrC mul1r.
rewrite -!(big_morph intr (@intrD _) (id2 := 0)) //=.
rewrite -!(big_morph Posz PoszD (id2 := 0%N)) //=.
rewrite -Frobenius_ident expr2.
by rewrite invfM mulrA divff.
Qed.

End Identity.
