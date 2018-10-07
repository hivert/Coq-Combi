(** * Combi.MPoly.homogsym : Homogenous Symmetric Polynomials *)
(******************************************************************************)
(*      Copyright (C) 2016-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * The Space of Homogeneous Symmetric Polynomials

In this file we study the vector space of homogeneous symmetric polynomials.
The main goal is to construct its classical basis and Cauchy's scalar product.

- [f \is d.-homsym] == f is a homogenerous of degree d symmetric polynomial.
- [f \is [in R[n], d.-homsym]] == idem specifying the ring and number of
                     variables.
- [{homsym R[n, d]}] == the space of homogenerous of degree [d] symmetric
                     polynomials in [n] variables over [R].
- [p *h q]        == the product of two homogeneous symmetric polynomial as a
                     homogeneous symmetric polynomials.

The classical bases:

- ['he[la]]       == the elementary hom. sym. poly. associated to [la]
- ['hh[la]]       == the complete   hom. sym. poly. associated to [la]
- ['hp[la]]       == the power sum  hom. sym. poly. associated to [la]
- ['hm[la]]       == the monomial   hom. sym. poly. associated to [la]
- ['hs[la]]       == the Schur      hom. sym. poly. associated to [la]

- [in_homsym d p] == if [p] is a polynomial [{mpoly R[n]}] which is both
                     symmetric and homogeneous of degree [d], return it as a
                     [{sympol R[n, d]}]. It is canonically linear.

- ['he]           == the elementary hom. sym. basis
- ['hh]           == the complete   hom. sym. basis
- ['hp]           == the power sum  hom. sym. basis
- ['hm]           == the monomial   hom. sym. basis
- ['hs]           == the Schur      hom. sym. basis


Changing the base ring and the number of variables:

- [intpart_of_mon m] == if [m] is the monomial [x_1^{i_1}x_2^{i_2}...x_n^{i_n}]
                     returns the integer partition [n^{i_n}...2^{i_2}1^{i_1}]
- [intpartn_of_mon H] == the same as an [intpart_of_mon d] where [H] is a proof of
                     [mnmwgt m = d]

- [map_homsym mor f] == change the base ring of the hom. sym. poly [f] using
                     the ring morphism [mor]. This is canonically additive.
- [cnvarhomsym n f] == change the number of variables of the hom. sym. poly
                     [f] by sending elementary to elementary. This is
                     canonically linear.

The scalar product:

- ['[ u | v ]]    == the scalar product of hom. sym. poly., only defined over
                     the field [algC].
- ['[ u | v ] _(n, d)] == the scalar product of hom. sym. poly. specifying
                     the number of variable and degree.

The main results are [symbm_basis], [symbe_basis], [symbs_basis],
[symbh_basis], [symbp_basis] which asserts that they are all bases (if the
characteristic of the base ring is zero for [symbp_basis]), and the definition
of the scalar product.
 *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset bigop ssrint ssralg path.
From mathcomp Require Import perm fingroup matrix vector zmodp.
From mathcomp Require ssrnum.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab.
Require Import antisym Schur_mpoly Schur_altdef sympoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Reserved Notation "{ 'homsym' T [ n , d ] }"
  (at level 0, T, n, d at level 2, format "{ 'homsym'  T [ n ,  d ] }").
Reserved Notation "'[ p | q ]" 
  (at level 2, format "'[hv' ''[' p  | '/ '  q ] ']'").
Reserved Notation "'[ p | q ] _( R , n )"
  (at level 2, format "'[hv' ''[' p  | '/ '  q ] ']' '_(' R ,  n )").


Definition ishomogsym1 {n} {R : ringType} (d : nat) :
  qualifier 0 {sympoly R[n]} := [qualify p | sympol p \is d.-homog].

Module SymPolyHomogKey.
Fact homogsym1_key {n} {R : ringType} d : pred_key (@ishomogsym1 n R d).
Proof. by []. Qed.
Definition homogsym1_keyed {n R} d := KeyedQualifier (@homogsym1_key n R d).
End SymPolyHomogKey.
Canonical SymPolyHomogKey.homogsym1_keyed.

Notation "d .-homsym" := (@ishomogsym1 _ _ d)
  (at level 1, format "d .-homsym") : form_scope.
Notation "[ 'in' R [ n ] , d .-homsym ]" := (@ishomogsym1 n R d)
  (at level 0, R, n at level 2, d at level 0,
     format "[ 'in'  R [ n ] ,  d .-homsym ]") : form_scope.

(** ** Homogeneous symmetric polynomials *)
Section DefType.

Variable n : nat.
Variable R : ringType.
Variable d : nat.

Implicit Types p q : {sympoly R[n]}.

Lemma homsymE p : (p \is d.-homsym) = (sympol p \is d.-homog).
Proof. by []. Qed.

Lemma symdhom_submod_closed : submod_closed [in R[n], d.-homsym].
Proof.
split => [|a p q Hp Hq]; rewrite !homsymE.
- exact: dhomog0.
- by apply rpredD => //; apply rpredZ.
Qed.
Canonical symdhom_addPred    := AddrPred   symdhom_submod_closed.
Canonical symdhom_oppPred    := OpprPred   symdhom_submod_closed.
Canonical symdhom_zmodPred   := ZmodPred   symdhom_submod_closed.
Canonical symdhom_submodPred := SubmodPred symdhom_submod_closed.

Hypothesis Hvar : (d <= n.+1)%N.

Record homogsym : predArgType :=
  HomogSym {homsym :> {sympoly R[n]}; _ : homsym \is d.-homsym }.

Canonical  homogsym_subType := Eval hnf in [subType for @homsym].
Definition homogsym_eqMixin := Eval hnf in [eqMixin of homogsym by <:].
Canonical  homogsym_eqType  := Eval hnf in EqType homogsym homogsym_eqMixin.

Definition homogsym_choiceMixin := [choiceMixin of homogsym by <:].
Canonical  homogsym_choiceType  :=
  Eval hnf in ChoiceType homogsym homogsym_choiceMixin.

Definition homogsym_of of phant R := homogsym.

Identity Coercion type_homsym_of : homogsym_of >-> homogsym.

Lemma homsym_inj : injective homsym. Proof. exact: val_inj. Qed.

End DefType.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with homogsym_of.
Bind Scope ring_scope with homogsym.
Arguments homogsym n%N R%R.
Arguments homsym_inj n%N R%R d%N.


Notation "{ 'homsym' T [ n , d ] }" := (homogsym_of n d (Phant T)).

Section HomogSymLModType.

Variable n : nat.
Variable R : ringType.
Variable d : nat.

Definition homogsym_zmodMixin := [zmodMixin of {homsym R[n, d]} by <:].
Canonical  homogsym_zmodType  :=
  Eval hnf in ZmodType {homsym R[n, d]} homogsym_zmodMixin.
Canonical  homogsymen_zmodType  :=
  Eval hnf in ZmodType (homogsym n R d) homogsym_zmodMixin.

Definition homogsym_lmodMixin := [lmodMixin of {homsym R[n, d]} by <:].
Canonical  homogsym_lmodType  :=
  Eval hnf in LmodType R {homsym R[n, d]} homogsym_lmodMixin.
Canonical  homogsymen_lmodType :=
  Eval hnf in LmodType R (homogsym n R d) homogsym_lmodMixin.

Lemma homsym_is_linear :
  linear (@homsym n R d : {homsym R[n, d]} -> {sympoly R[n]}).
Proof. by []. Qed.
Canonical homsym_additive   := Additive   homsym_is_linear.
Canonical homsym_linear     := AddLinear  homsym_is_linear.

Lemma homsym_is_dhomog (x : {homsym R[n, d]}) : sympol x \is d.-homog.
Proof. by case: x. Qed.

(*
Coercion dhomog_of_homogsym (p : {homsym R[n, d]}) :=
  DHomog (homsym_is_dhomog p).

Lemma dhomog_of_sym_is_linear : linear (@homsym n R d).
Proof. by []. Qed.
Canonical dhomog_of_sym_additive := Additive  dhomog_of_sym_is_linear.
Canonical dhomog_of_sym_linear   := AddLinear dhomog_of_sym_is_linear.
 *)

End HomogSymLModType.

Import GRing.Theory.
Local Open Scope ring_scope.


(** ** Products of homogeneous symmetric polynomials *)
Section HomogSymProd.

Variable n : nat.
Variable R : comRingType.
Variable c d : nat.

Lemma homsymprod_subproof (p : {homsym R[n, c]}) (q : {homsym R[n, d]}) :
  homsym p * homsym q \is (c + d).-homsym.
Proof. by apply: dhomogM => /=; apply: homsym_is_dhomog. Qed.
Canonical homsymprod p q : {homsym R[n, c + d]} :=
  HomogSym (homsymprod_subproof p q).
Definition homsymprodr_head k p q := let: tt := k in homsymprod q p.

Notation homsymprodr := (homsymprodr_head tt).
Local Notation "p *h q" := (homsymprod p q)
                             (at level 20, format "p  *h  q").

Lemma homsymprod_is_linear p : linear (homsymprod p).
Proof.
by move=> a /= u v; apply val_inj; rewrite /= mulrDr -scalerAr.
Qed.
Canonical homsymprod_additive p := Additive (homsymprod_is_linear p).
Canonical homsymprod_linear p := Linear (homsymprod_is_linear p).

Lemma homsymprodrE p q : homsymprodr p q = q *h p. Proof. by []. Qed.
Lemma homsymprodr_is_linear p : linear (homsymprodr p).
Proof.
by move=> a /= u v; apply val_inj; rewrite /= mulrDl -scalerAl.
Qed.
Canonical homsymprodr_additive p := Additive (homsymprodr_is_linear p).
Canonical homsymprodr_linear p := Linear (homsymprodr_is_linear p).


Lemma homsymprod0r p : p *h 0 = 0. Proof. exact: raddf0. Qed.
Lemma homsymprodBr p q1 q2 : p *h (q1 - q2) = p *h q1 - p *h q2.
Proof. exact: raddfB. Qed.
Lemma homsymprodNr p q : p *h (- q) = - p *h q.
Proof. exact: raddfN. Qed.
Lemma homsymprodDr p q1 q2 : p *h (q1 + q2) = p *h q1 + p *h q2.
Proof. exact: raddfD. Qed.
Lemma homsymprodMnr p q m : p *h (q *+ m) = (p *h q) *+ m.
Proof. exact: raddfMn. Qed.
Lemma homsymprod_sumr p I r (P : pred I) (q : I -> {homsym R[n, d]}) :
  p *h (\sum_(i <- r | P i) q i) = \sum_(i <- r | P i) p *h q i.
Proof. exact: raddf_sum. Qed.
Lemma homsymprodZr a p q : p *h (a *: q) = a *: (p *h q).
Proof. by rewrite linearZ. Qed.

Lemma homsymprod0l p : 0 *h p = 0.
Proof. by rewrite -homsymprodrE linear0. Qed.
Lemma homsymprodNl p q : (- q) *h p = - q *h p.
Proof. by rewrite -!homsymprodrE linearN. Qed.
Lemma homsymprodDl p q1 q2 : (q1 + q2) *h p = q1 *h p + q2 *h p.
Proof. by rewrite -!homsymprodrE linearD. Qed.
Lemma homsymprodBl p q1 q2 : (q1 - q2) *h p = q1 *h p - q2 *h p.
Proof. by rewrite -!homsymprodrE linearB. Qed.
Lemma homsymprodMnl p q m : (q *+ m) *h p = q *h p *+ m.
Proof. by rewrite -!homsymprodrE linearMn. Qed.
Lemma homsymprod_suml p I r (P : pred I) (q : I -> {homsym R[n, c]}) :
  (\sum_(i <- r | P i) q i) *h p = \sum_(i <- r | P i) q i *h p.
Proof. by rewrite -!homsymprodrE linear_sum. Qed.
Lemma homsymprodZl p a q : (a *: q) *h p = a *: q *h p.
Proof. by rewrite -!homsymprodrE linearZ. Qed.

End HomogSymProd.

Notation homsymprodr := (homsymprodr_head tt).
Notation "p *h q" := (homsymprod p q)
                       (at level 20, format "p  *h  q").

(** ** Homogeneous symmetric polynomials as a vector space *)
Section Vector.

Variable n0 : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.

Variable d : nat.
Local Notation SF := {sympoly R[n]}.
Implicit Type (la : 'P_d).

Definition homsymm la : {homsym R[n, d]} := HomogSym (symm_homog n R la).
Definition homsyme la : {homsym R[n, d]} := HomogSym (prod_syme_homog n R la).
Definition homsymh la : {homsym R[n, d]} := HomogSym (prod_symh_homog n R la).
Definition homsymp la : {homsym R[n, d]} := HomogSym (prod_symp_homog n R la).
Definition homsyms la : {homsym R[n, d]} := HomogSym (syms_homog n0 R la).

Lemma homsymmE (f : {homsym R[n, d]}) :
  f = \sum_(l : 'P_d) f@_(mpart l) *: homsymm l.
Proof.
by apply val_inj; rewrite /= {1}(homog_symmE (homsym_is_dhomog f)) !linear_sum.
Qed.

Lemma homogsym_vecaxiom :
  Vector.axiom #|[set p : 'P_d | size p <= n]| {homsym R[n, d]}.
Proof.
pose b := [set p : 'P_d | size p <= n].
pose t := enum_tuple (pred_of_set b).
have sztntht k : size (tnth t k) <= n.
  by have := mem_tnth k t; rewrite /t mem_enum inE.
exists (fun p : {homsym R[n, d]} => \row_(i < #|b|) p@_(mpart (tnth t i))).
  by move=> c p q; apply/matrixP=> i j; rewrite !mxE /= mcoeffD mcoeffZ.
exists (fun r : 'rV[R]_(#|b|) => \sum_(i < #|b|) (r 0 i) *: (homsymm (tnth t i))).
- move=> p; rewrite [RHS]homsymmE.
  rewrite (bigID (mem b)) /= [X in _ + X]big1 ?addr0 => [|la]; first last.
    rewrite inE => /negbTE H .
    by apply val_inj; apply val_inj; rewrite /= /symm H scaler0.
  rewrite [RHS](eq_bigl (fun la => la \in b)); first last.
    by move=> i /=; rewrite inE.
  rewrite [RHS]big_enum /= -[enum _]/(tval t).
  rewrite big_tuple; apply eq_bigr => i _; congr (_ *: _).
  by rewrite mxE.
- move=> r /=; apply/matrixP=> i j.
  rewrite mxE !raddf_sum ord1 /= (bigD1 j) //=.
  rewrite !linearZ /= mcoeff_symm ?sztntht //.
  rewrite perm_eq_refl mulr1 big1 ?addr0 //.
  move=> k Hkj.
  rewrite !linearZ /= mcoeff_symm ?sztntht //.
  suff : ~~(perm_eq (mpart (n := n) (tnth t k)) (mpart (n := n) (tnth t j))).
    by move /negbTE ->; rewrite mulr0.
  move: Hkj; apply contra => /perm_eq_partm/(congr1 val)/eqP.
  rewrite /= !mpartK // !(tnth_nth (rowpartn d)) /t /= => H.
  apply/eqP/val_inj/eqP => /=.
  by rewrite -(nth_uniq (rowpartn d) _ _ (enum_uniq (pred_of_set b))) // -cardE.
Qed.
Definition homogsym_vectMixin := VectMixin homogsym_vecaxiom.
Canonical homogsym_vectType :=
  Eval hnf in VectType R {homsym R[n, d]} homogsym_vectMixin.

End Vector.

Notation "''he[' k ]" := (homsyme _ _ k)
                              (at level 8, k at level 2, format "''he[' k ]").
Notation "''hh[' k ]" := (homsymh _ _ k)
                              (at level 8, k at level 2, format "''hh[' k ]").
Notation "''hp[' k ]" := (homsymp _ _ k)
                              (at level 8, k at level 2, format "''hp[' k ]").
Notation "''hm[' k ]" := (homsymm _ _ k)
                              (at level 8, k at level 2, format "''hm[' k ]").
Notation "''hs[' k ]" := (homsyms _ _ k)
                              (at level 8, k at level 2, format "''hs[' k ]").


Section InHomSym.

Variable n0 d : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.
Local Notation Pol := {mpoly R[n]}.
Local Notation HSF := {homsym R[n, d]}.

Local Notation "''pi_' d" :=
  (pihomog [measure of mdeg] d) (at level 5, format "''pi_' d").

(** TODO: Contribute to Pierre-Yves's multinomials *)
Lemma msym_pihomog nv s (p : {mpoly R[nv]}) :
  msym s ('pi_d p) = 'pi_d (msym s p).
Proof.
rewrite (mpolyE p) ![_ (\sum_(m <- msupp p) _)]linear_sum /=.
rewrite [msym s _]linear_sum linear_sum /=.
apply eq_bigr => m _; rewrite !linearZ /=; congr (_ *: _).
rewrite msymX !pihomogX /=.
have -> : mdeg [multinom m ((s^-1)%g i) | i < nv] = mdeg m.
  rewrite /mdeg; apply eq_big_perm.
  by apply/tuple_perm_eqP; exists (s^-1)%g.
by case: (mdeg m == d); rewrite ?msym0 ?msymX.
Qed.

Lemma pihomog_sym nv (p : {mpoly R[nv]}) :
  p \is symmetric -> 'pi_d p \is symmetric.
Proof. by move=> /issymP Hp; apply/issymP => s; rewrite msym_pihomog Hp. Qed.

Definition in_homsym (p : Pol) : HSF :=
  \sum_(la : 'P_d) p@_(mpart la) *: 'hm[la].

Lemma in_homsym_is_linear : linear in_homsym.
Proof.
rewrite /in_homsym => a u v.
rewrite linear_sum /= -big_split /=; apply eq_bigr => la _.
by rewrite scalerA -scalerDl mcoeffD mcoeffZ.
Qed.
Canonical in_homsym_additive := Additive  in_homsym_is_linear.
Canonical in_homsym_linear   := AddLinear in_homsym_is_linear.

Lemma in_homsymE (p : {homsym R[n, d]}) : in_homsym p = p.
Proof. by rewrite {2}(homsymmE p). Qed.

End InHomSym.


(** * The classical bases of homogeneous symmetric polynomials *)
Section HomSymField.

Variable n0 d : nat.
Local Notation n := (n0.+1).
Variable R : fieldType.
Local Notation "''pi_' d" :=
  (pihomog [measure of mdeg] d) (at level 5, format "''pi_' d").
Local Notation HSF := {homsym R[n, d]}.


Local Notation Basis := (#|{:'P_d}|.-tuple HSF).
Definition symbe : Basis := [tuple of [seq 'he[la] | la : 'P_d]].
Definition symbh : Basis := [tuple of [seq 'hh[la] | la : 'P_d]].
Definition symbm : Basis := [tuple of [seq 'hm[la] | la : 'P_d]].
Definition symbs : Basis := [tuple of [seq 'hs[la] | la : 'P_d]].
Definition symbp : Basis := [tuple of [seq 'hp[la] | la : 'P_d]].

Hypothesis Hd : (d <= n)%N.

Lemma basis_homsym : [set p : 'P_d | (size p <= n)%N] =i {:'P_d}.
Proof using Hd.
move=> la.
rewrite !inE; apply: (leq_trans _ Hd).
by rewrite -[X in (_ <= X)%N](intpartn_sumn la); apply: size_part.
Qed.

Lemma dim_homsym :
  \dim (fullv (vT := [vectType R of HSF])) = #|{:'P_d}|.
Proof using Hd.
by rewrite dimvf /Vector.dim /=; apply eq_card; apply basis_homsym.
Qed.

Lemma free_symbm : free symbm.
Proof using Hd.
apply/freeP => co.
rewrite (reindex _ (onW_bij _ (@enum_rank_bij _))) /=.
rewrite (eq_bigr (fun la : 'P_d => (co (enum_rank la)) *: 'hm[la])); first last.
  move=> la _; rewrite (nth_map (rowpartn _)) /= -?cardE ?ltn_ord //.
  by rewrite -?enum_val_nth enum_rankK.
move => /(congr1 val).
rewrite /= linear_sum /= => /symm_unique0 H i.
rewrite -(enum_valK i); apply H.
apply: (leq_trans _ Hd).
rewrite -[X in (_ <= X)%N](intpartn_sumn (enum_val i)).
exact: size_part.
Qed.

Lemma symbm_basis : basis_of fullv symbm.
Proof using Hd.
by rewrite basisEfree free_symbm subvf size_map size_tuple /= dim_homsym.
Qed.

Lemma symbs_basis : basis_of fullv symbs.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbm_basis).
apply/span_subvP => s /mapP [/= la]; rewrite !mem_enum => _ ->{s}.
have -> : 'hm[la] = \sum_(mu : 'P_d) 'K^-1(la, mu) *: 'hs[mu] :> HSF.
  by apply val_inj; rewrite /= (symm_syms _ _ la) !linear_sum.
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.

Theorem mcoeff_symbs (la : 'P_d) f :
  coord symbs (enum_rank la) f =
  (alternpol 'X_[rho n] * sympol (homsym f))@_(mpart la + rho n).
Proof.
have /coord_span -> : f \in span symbs.
  by rewrite (span_basis symbs_basis) memvf.
rewrite !coord_sum_free ?(basis_free symbs_basis) //.
rewrite (reindex _ (onW_bij _ (@enum_rank_bij _))) /=.
rewrite !linear_sum /= mulr_sumr linear_sum /= (bigD1 la) //=.
rewrite (nth_map (rowpartn d)) -?cardE ?ltn_ord // nth_enum_rank.
rewrite -scalerAr linearZ /=.
have Hszp (nu : 'P_d) : size nu <= n.
  by apply: (leq_trans _ Hd); rewrite -{2}(intpartn_sumn nu) size_part.
rewrite mcoeff_alt_SchurE // eq_refl mulr1 big1 ?addr0 // => mu /negbTE Hmula.
rewrite (nth_map (rowpartn d)) -?cardE ?ltn_ord // nth_enum_rank.
rewrite -scalerAr linearZ /=.
by rewrite mcoeff_alt_SchurE // Hmula mulr0.
Qed.

Local Notation E := [tuple mesym n R i.+1 | i < n].

Definition intpart_of_mon m : seq nat :=
  rev (flatten [tuple nseq (m i) i.+1 | i < n]).

Lemma intpart_of_monP m : mnmwgt m = d -> is_part_of_n d (intpart_of_mon m).
Proof using.
rewrite /mnmwgt => H.
rewrite /= is_part_sortedE; apply/and3P; split.
- rewrite /intpart_of_mon sumn_rev sumn_flatten -[X in _ == X]H.
  rewrite -sumnE big_map big_tuple.
  apply/eqP/eq_bigr => /= i _.
  by rewrite -sumnE tnth_mktuple big_nseq iter_addn_0 mulnC.
- rewrite /intpart_of_mon /= rev_sorted.
  apply/(sorted.sortedP 0%N) => //=; first exact: leq_trans.
  move=> i j; rewrite !nth_flatten.
  rewrite size_flatten.
  have -> : shape [seq nseq (m i0) i0.+1 | i0 : 'I_n] = m.
    rewrite /shape -map_comp (tuple_map_ord m) /=.
    apply eq_map => k /=.
    by rewrite size_nseq.
  move=> /andP [Hij Hjm]; have Him := leq_ltn_trans Hij Hjm.
  have:= reshape_indexP Hjm; have:= reshape_offsetP Hjm.
  have:= reshape_indexP Him; have:= reshape_offsetP Him.
  rewrite size_tuple => Hc1 Hr1 Hc2 Hr2.
  do 2 (rewrite (nth_map ord0); last by rewrite size_enum_ord).
  rewrite !(mnm_nth 0) !nth_nseq !nth_enum_ord //= {Hr1 Hr2}.
  rewrite {}Hc1 {}Hc2 ltnS; move: Hij.
  by rewrite (reshape_leq m) => /orP [/ltnW | /andP [/eqP ->]].
- rewrite /intpart_of_mon; rewrite mem_rev; apply/flatten_mapP => /= [[s _]].
  by move=> /nseqP [].
Qed.
Canonical intpartn_of_mon m (H : mnmwgt m = d) := IntPartN (intpart_of_monP H).

Local Lemma Esym : (forall i : 'I_n, E`_i \is symmetric).
Proof using.
move=> i; rewrite (nth_map i) ?size_tuple //.
by rewrite -tnth_nth tnth_ord_tuple mesym_sym.
Qed.

Lemma comp_symbe m (H : mnmwgt m = d) :
  'X_[m] \mPo E = 'he[intpartn_of_mon H].
Proof using.
rewrite comp_mpolyX /= /prod_gen /intpartn_of_mon /intpart_of_mon /=.
rewrite rmorph_prod /= -[RHS](eq_big_perm _ (perm_eq_rev _)) /=.
rewrite big_flatten /= big_map /=.
rewrite /index_enum -!enumT /=; apply eq_bigr => i _.
rewrite big_nseq tnth_mktuple.
by rewrite -big_const_ord prodr_const cardT -cardE card_ord.
Qed.

Lemma in_homsym_comp_symbe m (H : mnmwgt m = d) :
  in_homsym d ('X_[m] \mPo E) = 'he[intpartn_of_mon H].
Proof using. by rewrite comp_symbe in_homsymE. Qed.

Lemma symbe_basis : basis_of fullv symbe.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
apply/subvP => /= p _; rewrite span_def big_map.
have:= sym_fundamental_homog (sympol_is_symmetric p) (homsym_is_dhomog p).
move=> [t [Hp /dhomogP Hhomt]].
have {Hp} -> : p = \sum_(m <- msupp t) t@_m *: in_homsym d ('X_[m] \mPo E).
  apply val_inj; apply val_inj; rewrite /= -{1}Hp {1}(mpolyE t) {Hp}.
  rewrite !linear_sum /=; apply eq_big_seq => m /Hhomt /= Hm.
  rewrite !linearZ /=; congr (_ *: _).
  by rewrite in_homsym_comp_symbe /= comp_symbe /=.
rewrite big_seq; apply memv_suml => m Hm; apply memvZ.
rewrite (in_homsym_comp_symbe (Hhomt m Hm)).
move: (intpartn_of_mon _) => {m Hm} la.
rewrite (bigD1_seq la) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
apply memv_add; first exact: memv_line.
exact: mem0v.
Qed.

Lemma symbh_basis : basis_of fullv symbh.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbe_basis).
apply/span_subvP => s /mapP [/= la]; rewrite !mem_enum => _ ->{s}.
have -> : 'he[la] = \sum_(mu : 'P_d)
           coeff_prodgen
             (fun d (la : 'P_d) => (-1)^+(d - size la) * (perm_partn la)%:R)
             la mu *: 'hh[mu] :> HSF.
  by apply val_inj; rewrite /= linear_sum /= (prod_prodgen (syme_to_symh n0 R)).
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.

Lemma symbp_basis : [char R] =i pred0 -> basis_of fullv symbp.
Proof using Hd.
move=> Hchar.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbh_basis).
apply/span_subvP => s /mapP [/= la]; rewrite !mem_enum => _ ->{s}.
pose co := fun (n : nat) (l : 'P_n) => (permcent.zcard l)%:R^-1 : R.
have -> : 'hh[la] = \sum_(mu : 'P_d)
                     coeff_prodgen co la mu *: 'hp[mu] :> HSF.
  apply val_inj; rewrite /= linear_sum /=.
  by rewrite (prod_prodgen (fun n => symh_to_symp n0 n Hchar)).
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.

End HomSymField.

From mathcomp Require Import ssrnum rat algC.
Import GRing.Theory Num.Theory.
Require Import permcent.

Local Lemma char0_rat : [char rat] =i pred0.
Proof. exact: Num.Theory.char_num. Qed.
Local Lemma char0_algC : [char algC] =i pred0.
Proof. exact: Num.Theory.char_num. Qed.
Hint Resolve char0_algC char0_rat.

Notation "''he'" := (symbe _ _ _) (at level 8, format "''he'").
Notation "''hh'" := (symbh _ _ _) (at level 8, format "''hh'").
Notation "''hp'" := (symbp _ _ _) (at level 8, format "''hp'").
Notation "''hm'" := (symbm _ _ _) (at level 8, format "''hm'").
Notation "''hs'" := (symbs _ _ _) (at level 8, format "''hs'").


(** ** Changing the base field *)
Section ChangeField.

Variable R S : fieldType.
Variable mor : {rmorphism R -> S}.

Variable n0 d : nat.
Local Notation n := (n0.+1).
Local Notation HSFR := {homsym R[n, d]}.
Local Notation HSFS := {homsym S[n, d]}.

Lemma map_sympoly_d_homog (f : HSFR) : map_sympoly mor f \is d.-homsym.
Proof.
rewrite homsymE /=; apply/dhomogP => /= m.
rewrite mcoeff_msupp mcoeff_map_mpoly => Hm.
have {Hm} : f@_m != 0.
  move: Hm; apply contra => /eqP ->.
  by apply/eqP; apply: (rmorph0 mor).
rewrite -mcoeff_msupp => Hm.
by have /dhomogP/(_ _ Hm) := homsym_is_dhomog f.
Qed.
Definition map_homsym (f : HSFR) : HSFS := HomogSym (map_sympoly_d_homog f).

Lemma map_homsym_is_additive : additive map_homsym.
Proof.
by move=> /= p q; apply val_inj; rewrite /= rmorphB.
Qed.
Canonical map_homsym_additive := Additive map_homsym_is_additive.

Lemma scale_map_homsym (r : R) (p : HSFR) :
  map_homsym (r *: p) = (mor r) *: (map_homsym p).
Proof. by apply val_inj; rewrite /= scale_map_sympoly. Qed.

Lemma map_homsymm la : map_homsym 'hm[la] = 'hm[la].
Proof. by apply val_inj; rewrite /= map_symm. Qed.
Lemma map_homsyme la : map_homsym 'he[la] = 'he[la].
Proof. by apply val_inj; rewrite /= map_syme_prod. Qed.
Lemma map_homsymh la : map_homsym 'hh[la] = 'hh[la].
Proof. by apply val_inj; rewrite /= map_symh_prod. Qed.
Lemma map_homsymp la : map_homsym 'hp[la] = 'hp[la].
Proof. by apply val_inj; rewrite /= map_symp_prod. Qed.
Lemma map_homsyms la : map_homsym 'hs[la] = 'hs[la].
Proof. by apply val_inj; rewrite /= map_syms. Qed.

Lemma map_homsymbm : map_tuple map_homsym 'hm = 'hm.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsymm. Qed.
Lemma map_homsymbe : map_tuple map_homsym 'he = 'he.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsyme. Qed.
Lemma map_homsymbh : map_tuple map_homsym 'hh = 'hh.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsymh. Qed.
Lemma map_homsymbp : map_tuple map_homsym 'hp = 'hp.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsymp. Qed.
Lemma map_homsymbs : map_tuple map_homsym 'hs = 'hs.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsyms. Qed.

End ChangeField.


(** ** Changing the number of variables *)
Section ChangeNVar.

Variable R : comRingType.
Variable m0 n0 : nat.
Local Notation m := m0.+1.
Local Notation n := n0.+1.
Variable d : nat.
Hypothesis Hd : (d <= m)%N || (n0 < m)%N.

Lemma cnvarhomsym_subproof (p : {homsym R[m, d]}) :
  (cnvarsym n0 p) \is d.-homsym.
Proof using.
case: p => [p] /=; rewrite unfold_in /= => Hp; rewrite unfold_in.
rewrite /cnvarsym /=; apply/mwmwgt_homogP.
have [f [Hf Hfhom]] := sym_fundamental_homog (sympol_is_symmetric p) Hp.
rewrite /sympolyf; case: (sym_fundamental _) => [g []] /=.
by rewrite -Hf => H _; rewrite (msym_fundamental_un H).
Qed.
Definition cnvarhomsym (p : {homsym R[m, d]}) : {homsym R[n, d]} :=
  HomogSym (cnvarhomsym_subproof p).
Lemma cnvarhomsym_is_linear : linear cnvarhomsym.
Proof. by move=> a f g; apply val_inj; rewrite /= !linearD !linearZ /=. Qed.
Canonical cnvarhomsym_additive   := Additive  cnvarhomsym_is_linear.
Canonical cnvarhomsym_linear     := AddLinear cnvarhomsym_is_linear.

Lemma cnvarhomsyme la : cnvarhomsym 'he[la] = 'he[la].
Proof using Hd. by apply val_inj; rewrite /= -/'e[_] cnvar_prodsyme. Qed.
Lemma cnvarhomsymh la : cnvarhomsym 'hh[la] = 'hh[la].
Proof using Hd. by apply val_inj; rewrite /= -/'h[_] cnvar_prodsymh. Qed.
Lemma cnvarhomsymp la : cnvarhomsym 'hp[la] = 'hp[la].
Proof using Hd. by apply val_inj; rewrite /= -/'p[_] cnvar_prodsymp. Qed.
Lemma cnvarhomsymm la : cnvarhomsym 'hm[la] = 'hm[la].
Proof using Hd. by apply val_inj; rewrite /= cnvar_symm. Qed.
Lemma cnvarhomsyms la : cnvarhomsym 'hs[la] = 'hs[la].
Proof using Hd. by apply val_inj; rewrite /= cnvar_syms. Qed.

End ChangeNVar.


(** * The scalar product *)
Section ScalarProduct.

Variable n0 d : nat.
Local Notation n := (n0.+1).
Local Notation algCF := [numFieldType of algC].
Local Notation HSF := {homsym algC[n, d]}.

Definition homsymdot (p q : HSF) : algC :=
  \sum_(i < #|{:'P_d}|) (zcard (enum_val i))%:R *
  (coord 'hp i p) * (coord 'hp i q)^*.
Definition homsymdotr_head k p q := let: tt := k in homsymdot q p.

Notation homsymdotr := (homsymdotr_head tt).
Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.

Lemma homsymdotE p q :
  '[ p | q ] =
  \sum_(la : 'P_d) (zcard la)%:R *
    (coord 'hp (enum_rank la) p) * (coord 'hp (enum_rank la) q)^*.
Proof.
rewrite /homsymdot [RHS](reindex _ (onW_bij _ (@enum_val_bij _))) /=.
by apply/eq_bigr => i _; rewrite enum_valK.
Qed.
Lemma homsymdotrE p q : homsymdotr p q = '[q | p]. Proof. by []. Qed.

Lemma homsymdotr_is_linear p :
  linear (homsymdotr p : HSF -> algC^o).
Proof.
move=> a u v.
rewrite linear_sum -big_split; apply: eq_bigr => x _ /=.
rewrite linearD linearZ /= mulrDr mulrDl !mulrA; congr (_ + _).
by rewrite [_ * a]mulrC -!mulrA.
Qed.
Canonical homsymdotr_additive p := Additive (homsymdotr_is_linear p).
Canonical homsymdotr_linear p := Linear (homsymdotr_is_linear p).


Lemma homsymdot0l p : '[0 | p] = 0.
Proof. by rewrite -homsymdotrE linear0. Qed.
Lemma homsymdotNl p q : '[- q | p] = - '[q | p].
Proof. by rewrite -!homsymdotrE linearN. Qed.
Lemma homsymdotDl p q1 q2 : '[q1 + q2 | p] = '[q1 | p] + '[q2 | p].
Proof. by rewrite -!homsymdotrE linearD. Qed.
Lemma homsymdotBl p q1 q2 : '[q1 - q2 | p] = '[q1 | p] - '[q2 | p].
Proof. by rewrite -!homsymdotrE linearB. Qed.
Lemma homsymdotMnl p q n : '[q *+ n | p] = '[q | p] *+ n.
Proof. by rewrite -!homsymdotrE linearMn. Qed.
Lemma homsymdot_suml p I r (P : pred I) (q : I -> HSF) :
  '[\sum_(i <- r | P i) q i | p] = \sum_(i <- r | P i) '[q i | p].
Proof. by rewrite -!homsymdotrE linear_sum. Qed.
Lemma homsymdotZl p a q : '[a *: q | p] = a * '[q | p].
Proof. by rewrite -!homsymdotrE linearZ. Qed.

Lemma homsymdotC p q : '[p | q] = ('[q | p])^*.
Proof.
rewrite /homsymdot rmorph_sum /=.
apply: eq_bigr=> x _; rewrite !rmorphM conjCK -!mulrA.
have /geC0_conj -> : 0 <= ((zcard (enum_val x))%:R : algC).
  by rewrite -nnegrE ?nnegrE ?ler01 ?ler0n ?oner_neq0.
by congr (_ * _); rewrite mulrC.
Qed.

Lemma homsymdotBr p q1 q2 : '[p | q1 - q2] = '[p | q1] - '[p | q2].
Proof. by rewrite !(homsymdotC p) -rmorphB homsymdotBl. Qed.
Canonical homsymdot_additive p := Additive (homsymdotBr p).

Lemma homsymdot0r p : '[p | 0] = 0. Proof. exact: raddf0. Qed.
Lemma homsymdotNr p q : '[p | - q] = - '[p | q].
Proof. exact: raddfN. Qed.
Lemma homsymdotDr p q1 q2 : '[p | q1 + q2] = '[p | q1] + '[p | q2].
Proof. exact: raddfD. Qed.
Lemma homsymdotMnr p q n : '[p | q *+ n] = '[p | q] *+ n.
Proof. exact: raddfMn. Qed.
Lemma homsymdot_sumr p I r (P : pred I) (q : I -> HSF) :
  '[p | \sum_(i <- r | P i) q i] = \sum_(i <- r | P i) '[p | q i].
Proof. exact: raddf_sum. Qed.
Lemma homsymdotZr a p q : '[p | a *: q] = a^* * '[p | q].
Proof. by rewrite !(homsymdotC p) homsymdotZl rmorphM. Qed.

Lemma symbpE la : 'hp[la] = ('hp)`_(enum_rank la) :> HSF.
Proof. by rewrite /symbp tupleE /= (nth_map la) ?nth_enum_rank // -cardE. Qed.
Lemma coord_symbp (Hd : (d <= n)%N) la mu :
  coord (vT := [vectType algC of HSF]) 'hp (enum_rank mu) 'hp[la] = (la == mu)%:R.
Proof.
rewrite !symbpE !(coord_free _ _ (basis_free (symbp_basis _ _))) //.
by rewrite !(inj_eq enum_rank_inj).
Qed.

Lemma homsymdotp (Hd : (d <= n)%N) la mu :
  '[ 'hp[la] | 'hp[mu] ] = (zcard la)%:R * (la == mu)%:R.
Proof.
rewrite homsymdotE (bigD1 mu) //= big1 ?addr0 => [| nu /negbTE Hneq].
- rewrite !(coord_symbp Hd) eq_refl /= conjC1 mulr1.
  by case: eqP => [-> //| _]; rewrite !mulr0.
- by rewrite !(coord_symbp Hd) [mu == nu]eq_sym Hneq conjC0 mulr0.
Qed.

End ScalarProduct.

Notation homsymdotr := (homsymdotr_head tt).
Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.
Notation "''[' u | v ] _( n , d )" :=
  (@homsymdot n d u v) (only parsing) : ring_scope.
