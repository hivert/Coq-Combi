(******************************************************************************)
(*       Copyright (C) 2015 Florent Hivert <florent.hivert@lri.fr>            *)
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
Require Import bigop ssralg poly polydiv generic_quotient ring_quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(* Axiomatisation of formal power series as inverse limit of trucated         *)
(*   polynomials.                                                             *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'series' T }" (at level 0, format "{ 'series'  T }").

Import GRing.Theory.

Open Scope ring_scope.

Section TruncPol.

Variable R : fieldType.

Import Pdiv.Ring.

Lemma mod1Xn n : 1 %% 'X^n.+1 = 1 :> {poly R}.
Proof. by rewrite modp_small // size_polyXn size_polyC oner_eq0. Qed.

Lemma modp_mn m n (f : {poly R}) : m >= n -> (f %% 'X^m) %% 'X^n = f %% 'X^n.
Proof.
  move=> H; rewrite {2}(divp_eq f 'X^m) modp_add.
  suff -> : (_ * 'X^m) %% 'X^n = 0 by rewrite add0r.
  move=> F g; by rewrite -(subnK H) exprD mulrA modp_mull.
Qed.

Section Defs.

Variable n : nat.

Structure truncType : predArgType :=
  Trunc { pol :> {poly R}; _ : size pol <= n.+1 }.

Canonical trunc_subType := Eval hnf in [subType for pol].
Definition trunc_eqMixin := Eval hnf in [eqMixin of truncType by <:].
Canonical trunc_eqType := Eval hnf in EqType truncType trunc_eqMixin.
Definition trunc_choiceMixin := Eval hnf in [choiceMixin of truncType by <:].
Canonical trunc_choiceType := Eval hnf in ChoiceType truncType trunc_choiceMixin.

Lemma truncP (p : {poly R}) : size (p %% 'X^n.+1) <= n.+1.
Proof.
  rewrite -ltnS -(size_polyXn R n.+1).
  apply: ltn_modpN0; by rewrite -size_poly_gt0 size_polyXn.
Qed.
Definition trunc (p : {poly R}) := Trunc (truncP p).

Lemma truncK : cancel pol trunc.
Proof.
  rewrite /trunc => [[p Hp]]; apply val_inj => /=.
  apply: modp_small; by rewrite size_polyXn ltnS.
Qed.
Lemma trunc_polE p : pol (trunc p) = p %% 'X^n.+1.
Proof. by []. Qed.

Lemma truncE (p : truncType) : p %% 'X^n.+1 = p.
Proof. apply val_inj; by rewrite -{2}[p]truncK /=. Qed.

Definition add_trunc := [fun a b => trunc (pol a + pol b)].

Lemma add_truncA : associative add_trunc.
Proof. move=> a b c /=; apply val_inj; by rewrite /= !modp_add !modp_mod addrA. Qed.

Lemma add_truncC : commutative add_trunc.
Proof. move=> a b /=; apply val_inj; by rewrite addrC. Qed.

Lemma add_trunc0 : left_id (trunc 0) add_trunc.
Proof. move=> a /=; apply val_inj; by rewrite /= mod0p add0r truncE. Qed.

Lemma add_truncN : left_inverse (trunc 0) (fun a => trunc (- pol a)) add_trunc.
Proof.
  move=> a /=; apply val_inj.
  by rewrite /= modp_add modp_mod -modp_add addNr mod0p .
Qed.

Definition trunc_zmodMixin := ZmodMixin add_truncA add_truncC add_trunc0 add_truncN.
Canonical trunc_zmodType := Eval hnf in ZmodType truncType trunc_zmodMixin.

Definition mul_trunc := [fun a b => trunc (pol a * pol b)].

Lemma mul_truncA : associative mul_trunc.
Proof.
  move=> a b c /=; apply val_inj.
  by rewrite /= [(_ %% _) * _]mulrC !modp_mul [pol c * _]mulrC mulrA.
Qed.

Lemma mul_trunc1 : left_id (trunc 1) mul_trunc.
Proof. move=> a /=; apply val_inj; by rewrite /= mulrC modp_mul mulr1 truncE. Qed.

Lemma mul_truncDl : left_distributive mul_trunc +%R.
Proof.
  move=> a b c /=; apply val_inj.
  by rewrite /= mulrC modp_mul mulrC -!modp_add modp_mod mulrDl.
Qed.

Lemma trunc10 : (trunc 1) != 0.
Proof.
  apply (introN idP) => /eqP H.
  have := eq_refl (pol (trunc 1)); rewrite {2}H.
  by rewrite trunc_polE /= mod0p mod1Xn oner_eq0.
Qed.

Lemma mul_truncC : commutative mul_trunc.
Proof. move=> a b /=; apply val_inj; by rewrite /= mulrC. Qed.

Definition trunc_ringMixin :=
  Eval hnf in ComRingMixin mul_truncA mul_truncC mul_trunc1 mul_truncDl trunc10.
Canonical trunc_ringType := Eval hnf in RingType truncType trunc_ringMixin.
Canonical trunc_comRingType := Eval hnf in ComRingType truncType mul_truncC.

Definition scale_trunc a := [fun p => trunc (a *: pol p)].

Lemma scale_truncA a b v : scale_trunc a (scale_trunc b v) = scale_trunc (a * b) v.
Proof. apply val_inj; by rewrite /= -modp_scalel modp_mod scalerA. Qed.

Lemma scale_trunc1r : left_id 1 scale_trunc.
Proof. move=> a /=; apply val_inj; by rewrite /= scale1r truncE. Qed.

Lemma scale_truncDr : right_distributive scale_trunc +%R.
Proof.
  move=> a x y /=; apply val_inj.
  by rewrite /= -modp_scalel -modp_add !modp_mod scalerDr.
Qed.

Lemma scale_truncDl a : {morph scale_trunc^~ a : x y / x + y >-> x + y}.
Proof.
  move=> x y /=; apply val_inj.
  by rewrite /= -modp_add modp_mod -scalerDl.
Qed.

Definition trunc_lmodMixin :=
  Eval hnf in LmodMixin scale_truncA scale_trunc1r scale_truncDr scale_truncDl.
Canonical trunc_lmodType := Eval hnf in LmodType R truncType trunc_lmodMixin.

Lemma scale_truncAl k (x y : truncType) : k *: (x * y) = (k *: x) * y.
Proof.
  apply val_inj; rewrite /=. rewrite -modp_scalel modp_mod.
  by rewrite [(_ %% _) * y]mulrC modp_mul [X in _ = (X) %% _]mulrC scalerAl.
Qed.

Canonical trunc_lalgType := LalgType R truncType scale_truncAl.
Canonical trunc_commAlgType := CommAlgType R truncType.

Canonical trunc_quotType := QuotType truncType (QuotClass truncK).

Definition eq_trunc (p q : {poly R}) := (p %% 'X^n.+1) == (q %% 'X^n.+1).

Lemma pi_truncTypeE x : \pi_(truncType)%qT x = trunc x.
Proof. by rewrite unlock /= /pi_phant /=. Qed.

Lemma eq_truncP : {mono \pi_(truncType)%qT : x y / eq_trunc x y >-> x == y}.
Proof. move=> x y /=; by rewrite !pi_truncTypeE. Qed.

Definition trunc_eqQuotMixin :
  eq_quot_mixin_of eq_trunc (QuotClass truncK) trunc_eqMixin := eq_truncP.
Canonical trunc_eqQuotType :=
  Eval hnf in EqQuotType eq_trunc trunc_quotType trunc_eqQuotMixin.

Lemma pi_trunc0 : \pi_(truncType)%qT 0 = 0.
Proof. by rewrite pi_truncTypeE. Qed.

Lemma pi_trunc_opp : {morph \pi_(truncType)%qT : x / (@GRing.opp _) x >-> - x}.
Proof. move=> x /=; apply val_inj; by rewrite !pi_truncTypeE /= !modp_opp modp_mod. Qed.

Lemma pi_trunc_add :   {morph \pi_(truncType)%qT : x y / (@GRing.add _) x y >-> x + y}.
Proof. move=> x y /=; apply val_inj; by rewrite !pi_truncTypeE /= !modp_add !modp_mod. Qed.

Definition trunc_zmodQuotMixin :=
  Eval hnf in ZmodQuotMixin trunc_eqQuotType pi_trunc0 pi_trunc_opp pi_trunc_add.
Canonical truc_zmodQuotType := Eval hnf in ZmodQuotType _ _ _ truncType trunc_zmodQuotMixin.

Lemma pi_trunc1 : \pi_(truncType)%qT 1 = 1.
Proof. by rewrite pi_truncTypeE. Qed.

Lemma pi_trunc_mul : {morph \pi_(truncType)%qT : x y / (@GRing.mul _) x y >-> x * y}.
Proof.
  move=> x y /=; apply val_inj.
  by rewrite !pi_truncTypeE /= modp_mul [_ %% _ * _]mulrC modp_mul mulrC.
Qed.

Definition trunc_ringQuotMixin :=
  Eval hnf in RingQuotMixin trunc_eqQuotType pi_trunc1 pi_trunc_mul.
Canonical trunc_ringQuotType := Eval hnf in RingQuotType _ _ truncType trunc_ringQuotMixin.

(* Invert f0 + 'X * f *)

Fixpoint invmodXn n (f0 : R) (f : {poly R}) :=
  if n is n'.+1 then
    (f0^-1)%:P * (1 - (invmodXn n' f0 f) * 'X * f)
  else (f0^-1)%:P.

Lemma invmodXnP m f0 (f : {poly R}) :
  f0 != 0 -> ((f0%:P + 'X * f) * (invmodXn m f0 f)) %% 'X^m.+1 = 1.
Proof.
  elim: m => [| m IHm] /= Hf0.
    rewrite mulrDl modp_add -mulrA modp_mulr addr0.
    by rewrite -polyC_mul (divff Hf0) mod1Xn.
  have {IHm} := IHm Hf0.
  move : (invmodXn _ _ _) => g Hrec.
  have := divp_eq ((f0%:P + 'X * f) * g) 'X^m.+1.
  rewrite Hrec; move : (_ %/ _ : {poly R}) => Q {Hrec} Hrec.
  rewrite mulrA [X in (X * _)]mulrC -[(f0^-1)%:P * _ * _]mulrA.
  rewrite mulrDr mulrN -mulrA mulrA Hrec.
  rewrite !mulrDl opprD !mulr1 mul1r -addrA.
  rewrite ['X * f + _]addrC -[_ - _ + _]addrA addNr addr0.
  rewrite -mulrA ['X^_ * _]mulrA ['X^_ * _]mulrC -exprS ['X^_ * _]mulrC.
  rewrite mulrDr modp_add -polyC_mul (mulVf Hf0).
  by rewrite mulrA -mulNr mulrA -mulNr modp_mull addr0 mod1Xn.
Qed.

Definition trunc_unit := [pred p : truncType | p`_0 != 0].
Definition trunc_inv (f : truncType) :=
  if trunc_unit f then trunc (invmodXn n f`_0 (Poly (behead f))) else f.

Lemma trunc_invP (f : truncType) : f`_0 != 0 -> f * (trunc_inv f) = 1.
Proof.
  move=> Hf0.
  rewrite /trunc_inv /= Hf0 -{1}[f]reprK /= -pi_truncTypeE -pi_trunc_mul pi_truncTypeE.
  rewrite unlock /= /repr_of /=.
  move: Hf0; rewrite -{2}[pol f]polyseqK /=.
  case Hf : (polyseq f) => [| f0 ff] /=; first by rewrite eq_refl.
  move=> Hf0; rewrite cons_poly_def addrC [ _* 'X]mulrC.
  apply val_inj; by rewrite /= (invmodXnP n (Poly ff) Hf0) mod1Xn.
Qed.

Lemma trinvP : {in trunc_unit, left_inverse 1 trunc_inv *%R}.
Proof. move=> x; rewrite unfold_in => /trunc_invP; by rewrite mulrC. Qed.

Lemma mul1inv x y : y * x = 1 -> trunc_unit x.
Proof.
  rewrite -{1}[x]reprK -{1}[y]reprK -pi_trunc_mul pi_truncTypeE.
  rewrite unlock /= /repr_of /=.
  rewrite -{1}[pol x]polyseqK /=.
  case Hf : (polyseq x) => [| f0 ff] /=.
    rewrite mulr0 -pi_truncTypeE pi_trunc0 => /esym/eqP.
    by rewrite oner_eq0.
  move=> H; apply (introN idP) => /eqP Hf0.
  have := erefl (pol 1); rewrite -{1}H Hf0 {H Hf0}.
  rewrite -pi_truncTypeE pi_trunc_mul /= !pi_truncTypeE mod1Xn.
  rewrite /trunc /= modp_mul mulrC modp_mul cons_poly_def addr0 mulrC mulrA => Habs.
  have := divp_eq (pol y * Poly ff * 'X) 'X^n.+1.
  rewrite Habs {Habs}; move: (_ %/ _  : {poly R}) => Q Habs.
  have := erefl ((pol y * Poly ff * 'X) %% 'X); rewrite {2}Habs.
  rewrite modp_mull modp_add exprS mulrC -mulrA modp_mulr add0r (mod1Xn 0) => /esym/eqP.
  by rewrite oner_eq0.
Qed.

Lemma trinvCP : {in [predC trunc_unit], trunc_inv =1 id}.
Proof. rewrite /trunc_inv => f /=; by rewrite unfold_in /= unfold_in /= => /negbTE ->. Qed.

Definition trunc_unitRingMixin :=
  Eval hnf in ComUnitRingMixin trinvP mul1inv trinvCP.
Canonical trunc_unitRingType := Eval hnf in UnitRingType truncType trunc_unitRingMixin.
Canonical trunc_comUnitRingType := [comUnitRingType of truncType].
Canonical trunc_unitAlgType := Eval hnf in [unitAlgType R of truncType].

End Defs.

Section Morph.

Local Open Scope ring_scope.

Lemma trunc_lrmorphism m : lrmorphism (trunc m).
Proof.
  repeat split.
  - move=> f g; apply val_inj; by rewrite /= !modp_add !modp_opp !modp_mod.
  - move=> f g; apply val_inj; rewrite /= !modp_mul.
    by rewrite [(f %% _ )* g]mulrC modp_mul mulrC.
  - move=> a x; apply val_inj; rewrite /=.
    by rewrite -modp_scalel !modp_mod.
Qed.

Canonical truncm m := LRMorphism (trunc_lrmorphism m).

Variable n m : nat.
Hypothesis Hmn : m >= n.

Definition truncmn (x : truncType m) : truncType n := truncm n x.

Lemma truncmn_lrmorphism : lrmorphism truncmn.
Proof.
  repeat split.
  - move=> f g; apply val_inj; by rewrite /= !modp_add !modp_opp !modp_mod !modp_mn.
  - move=> f g; apply val_inj; rewrite /= !modp_mul modp_mn; last by rewrite ltnS.
    by rewrite [(f %% _ )* g]mulrC modp_mul mulrC.
  - apply val_inj; by rewrite /= modp_mn; last by rewrite ltnS.
  - move=> a x; apply val_inj; rewrite /=.
    by rewrite -modp_scalel !modp_mod !modp_mn.
Qed.

Canonical trmn := LRMorphism truncmn_lrmorphism.

End Morph.

Lemma truncmn_trans m n p :
  n >= p -> (@truncmn p n) \o (@truncmn n m) =1 @truncmn p m.
Proof.
  move=> Hpn x /=; apply val_inj.
  by rewrite /= modp_mn; last by rewrite ltnS.
Qed.

End TruncPol.

Require Import invlim.

Delimit Scope powser_scope with PS.

Definition trans (R : fieldType) := fun (i j : nat_dir) (Hij : i <= j) => (trmn R Hij).
Definition powser R := {invlim nat_dir | (trans R)}.

Local Arguments proj _ _ _ i%nat_scope s%invlim_scope.

Notation "{ 'series' T }" := (powser T).

Section PowserConstr.

Variable R : fieldType.

Local Open Scope nat_scope.
Local Open Scope ring_scope.


Implicit Type f g : {series R}.


Lemma proj_coeff0 f n : (proj n f)`_0 = (proj 0 f)`_0.
Proof.
  have Hn : 0 <= n by []; rewrite -(projP _ Hn) /=.
  rewrite -{2}[pol (proj n f)]polyseqK /=.
  case Hf : (polyseq _) => [| f0 ff] /=.
    by rewrite mod0p polyseq0.
  rewrite cons_poly_def addrC [_ * 'X]mulrC.
  rewrite modp_add modp_mulr addr0 modp_small; first last.
    rewrite size_polyC size_polyX; by case: eqP.
  rewrite polyseqC; by case: eqP => /=.
Qed.


Definition unitps := [pred f : {series R} | proj 0 f != 0].

Lemma unitpsP (n : nat) f : reflect (proj n f \is a GRing.unit) (unitps f).
Proof.
  apply (iffP idP) => /=.
  - move=> H0; rewrite inE; move: H0; apply contra => /eqP.
    rewrite proj_coeff0 => H0; apply/eqP; apply val_inj; rewrite /= mod0p.
    have Hsz : size (proj 0 f) <= 1 by case: (proj _ f).
    by rewrite (size1_polyC Hsz) H0.
  - move/mulVr => H; have Hn : 0 <= n by [].
    have := erefl (trmn R Hn 1); rewrite -{1}H {H}.
    rewrite !(rmorphismMP (trmn R Hn)) /= -(projP _ Hn) => H.
    apply (introN idP) => /eqP Habs.
    move: H; rewrite Habs mulr0 => /esym/eqP.
    by rewrite oner_eq0.
Qed.

Lemma invps_compat f : compatible (trans R) (fun n => (proj n f)^-1).
Proof.
  move=> m n Hmn; case: (boolP (unitps f)) => H0.
  - by rewrite (rmorphV (trmn R Hmn) (unitpsP _ _ H0)) -(projP _ Hmn).
  - move: H0 => /unitpsP H0.
    rewrite !invr_out.
    + by rewrite -(projP _ Hmn).
    + apply (introN idP); apply H0.
    + apply (introN idP); apply H0.
Qed.
Definition invps f := CSeq (invps_compat f).

Local Open Scope invlim_scope.
Notation "f ^-1" := (invps f) : invlim_scope.
Notation "f / g" := (f * (invps g)) : invlim_scope.


Lemma invpsE f n : proj n f^-1 = ((proj n f)^-1)%R.
Proof. rewrite /invps; by rewrite projE. Qed.

Lemma mulpsVr f : unitps f -> f^-1 * f == 1.
Proof.
  move=> /unitpsP Hf; rewrite -eq_projE => n.
  by rewrite mulcsE onecsE invpsE mulVr; last exact: Hf.
Qed.

Lemma mulpsrV f : unitps f -> f * f^-1 == 1.
Proof.
  move=> /unitpsP Hf; rewrite -eq_projE => n.
  by rewrite mulcsE onecsE invpsE mulrV; last exact: Hf.
Qed.

Lemma invpsCP f : ~~ unitps f -> f^-1 == f.
Proof.
  move=> /unitpsP H; rewrite -eq_projE => n.
  rewrite invpsE invr_out //; apply (introN idP); by apply H.
Qed.

Lemma mulps1inv x y : y * x == 1 -> unitps x.
Proof.
  rewrite -eq_projE => H; apply /(unitpsP 0); apply/unitrPr.
  exists (proj 0 y); rewrite mulrC.
  by rewrite -mulcsE H onecsE.
Qed.

Lemma pol_compat (p : {poly R}) : compatible (trans R) ((truncm R)^~ p).
Proof. move=> i j Hij; apply val_inj; by rewrite /= modp_mn. Qed.

Definition polps := induced pol_compat.
Coercion ps_of_pol := fun (p : {poly R}) => polps p : ({series R}).

Let geom : {series R} := 1 / ( 1 - (polps 'X)).

End PowserConstr.

Notation "f ^-1" := (invps f) : invlim_scope.
Notation "f / g" := (f * (invps g)) : invlim_scope.

(*
Definition truncsys := forall n, truncType R n.
Definition compatible (f : truncsys) := forall m n (H : m >= n), (trmn R H) (f m) = f n.

CoInductive powser := PowSer { cseq :> truncsys; _ : compatible cseq }.
Bind Scope powser_scope with powser.

Lemma powserP (x : powser) : compatible x.
Proof. by case: x. Qed.

Definition neq_powser (x y : powser) : Prop := exists n, (cseq x) n != (cseq y) n.
Notation "!=%PS" := neq_powser : powser_scope.
Notation "x != y" := (neq_powser x  y) : powser_scope.
Definition eq_powser x y := (~ (x != y)%PS).
Notation "x == y" := (eq_powser x y) : powser_scope.

Local Open Scope nat_scope.
Local Open Scope powser_scope.
Local Open Scope ring_scope.

Lemma eq_powserE x y : (forall n, (cseq x) n = (cseq y) n) <-> (x == y)%PS.
Proof.
  rewrite /eq_powser; split.
  - move=> Heq [] n; by rewrite Heq eq_refl.
  - move=> H n; case: (altP (cseq x n =P cseq y n)) => // Habs.
    exfalso; apply H; by exists n.
Qed.

Lemma eq_powser_refl x : x == x.
Proof. by rewrite -eq_powserE. Qed.
Hint Resolve eq_powser_refl.

Lemma neq_powser_sym x y : x != y -> y != x.
Proof. move=> [] n H; exists n; by rewrite eq_sym. Qed.

Lemma eq_powser_sym x y : x == y -> y == x.
Proof. by move=> eq_xy /neq_powser_sym. Qed.

Lemma eq_powser_trans x y z : x == y -> y == z -> x == z.
Proof. rewrite -!eq_powserE => Hxy Hyz n; by rewrite Hxy Hyz. Qed.
*)
Section PowserCheat.

Variable R : fieldType.

Definition truncsys := forall n, truncType R n.
Definition compatible (f : truncsys) := forall m n (H : m >= n), (trmn R H) (f m) = f n.

(* I'm cheating here assuming that PowerSeries equality is decidable *)
Variable powser : choiceType.

Variable truncpsc : powser -> truncsys.
Hypothesis truncpsc_compat : forall f, compatible (truncpsc f).
Hypothesis eq_truncpsc :
  forall (f g : powser), (forall n, truncpsc f n = truncpsc g n) -> f = g.
Variable limtrunc : forall (f : truncsys), compatible f -> powser.
Hypothesis limtruncE :
  forall (f : truncsys) (Hf : compatible f) n, truncpsc (limtrunc Hf) n = f n.

Lemma addpsc_compat f g : compatible (fun n => truncpsc f n + truncpsc g n).
Proof. move=> m n Hmn; by rewrite rmorphD /= !truncpsc_compat. Qed.
Definition addpsc f g := limtrunc (addpsc_compat f g).
Lemma addpscE f g n : truncpsc (addpsc f g) n = truncpsc f n + truncpsc g n.
Proof. rewrite /addpsc; by rewrite limtruncE. Qed.

Lemma addpscA : associative addpsc.
Proof. move => f g h; apply eq_truncpsc => n; by rewrite !addpscE addrA. Qed.
Lemma addpscC : commutative addpsc.
Proof. move => f g; apply eq_truncpsc => n; by rewrite !addpscE addrC. Qed.

Lemma powser0_compat : compatible (fun n => 0).
Proof. move=> m n Hmn; by rewrite rmorph0. Qed.
Definition powser0 := limtrunc powser0_compat.
Lemma powser0E n : truncpsc powser0 n = 0.
Proof. rewrite /powser0; by rewrite limtruncE. Qed.

Lemma add0psc : left_id (powser0) addpsc.
Proof. move=> a /=; apply eq_truncpsc => n; by rewrite addpscE limtruncE add0r. Qed.

Lemma opppsc_compat f : compatible (fun n => - truncpsc f n).
Proof. move=> m n Hmn; by rewrite rmorphN /= truncpsc_compat. Qed.
Definition opppsc f := limtrunc (opppsc_compat f).
Lemma opppscE f n : truncpsc (opppsc f) n = - truncpsc f n.
Proof. rewrite /opppsc; by rewrite limtruncE. Qed.

Lemma addNpsc : left_inverse powser0 opppsc addpsc.
Proof. move=> f; apply eq_truncpsc => n; by rewrite addpscE limtruncE powser0E addNr. Qed.

Definition powser_zmodMixin := ZmodMixin addpscA addpscC add0psc addNpsc.
Canonical powser_zmodType := Eval hnf in ZmodType powser powser_zmodMixin.

Lemma mulpsc_compat f g : compatible (fun n => truncpsc f n * truncpsc g n).
Proof. move=> m n Hmn; by rewrite rmorphM /= !truncpsc_compat. Qed.
Definition mulpsc f g := limtrunc (mulpsc_compat f g).
Lemma mulpscE f g n : truncpsc (mulpsc f g) n = truncpsc f n * truncpsc g n.
Proof. rewrite /mulpsc; by rewrite limtruncE. Qed.

Lemma mulpscA : associative mulpsc.
Proof. move => f g h; apply eq_truncpsc => n; by rewrite !mulpscE mulrA. Qed.
Lemma mulpscC : commutative mulpsc.
Proof. move => f g; apply eq_truncpsc => n; by rewrite !mulpscE mulrC. Qed.

Lemma powser1_compat : compatible (fun n => 1).
Proof. move=> m n Hmn; by rewrite rmorph1. Qed.
Definition powser1 := limtrunc powser1_compat.
Lemma powser1E n : truncpsc powser1 n = 1.
Proof. rewrite /powser1; by rewrite limtruncE. Qed.

Lemma mul1psc : left_id powser1 mulpsc.
Proof. move=> a /=; apply eq_truncpsc => n; by rewrite mulpscE limtruncE mul1r. Qed.

Lemma powser10 : powser1 != powser0.
Proof.
  have := oner_neq0 (trunc_ringType R 0).
  apply contra => /eqP Heq.
  have := erefl (truncpsc powser1 0%N); by rewrite {2}Heq powser0E powser1E => ->.
Qed.

Lemma mulpscDl : left_distributive mulpsc +%R.
Proof.
  move=> a b c /=; apply eq_truncpsc => n; by rewrite mulpscE! limtruncE mulrDl. Qed.

Definition powser_ringMixin :=
  ComRingMixin mulpscA mulpscC mul1psc mulpscDl powser10.
Canonical powser_ringType := Eval hnf in RingType powser powser_ringMixin.
Canonical powser_comRingType := Eval hnf in ComRingType powser mulpscC.

Lemma truncpsc_coeff0 f n : (truncpsc f n)`_0 = (truncpsc f 0%N)`_0.
Proof.
  have Hn : 0 <= n by []; rewrite -(truncpsc_compat f Hn) /=.
  rewrite -{2}[pol (truncpsc f n)]polyseqK /=.
  case Hf : (polyseq _) => [| f0 ff] /=.
    by rewrite mod0p polyseq0.
  rewrite cons_poly_def addrC [ _* 'X]mulrC.
  rewrite modp_add modp_mulr addr0 modp_small; first last.
    rewrite size_polyC size_polyX; by case: eqP.
  rewrite polyseqC; by case: eqP => /=.
Qed.

Definition unitpsc := [pred f : powser | truncpsc f 0%N != 0].

Lemma unitpscP n f : reflect (truncpsc f n \is a GRing.unit) (unitpsc f).
Proof.
  apply (iffP idP) => /=.
  - move=> H0; rewrite inE; move: H0; apply contra => /eqP.
    rewrite truncpsc_coeff0 => H0; apply/eqP; apply val_inj; rewrite /= mod0p.
    have Hsz : size (truncpsc f 0%N) <= 1 by case: truncpsc.
    by rewrite (size1_polyC Hsz) H0.
  - move/mulVr => H; have Hn : 0 <= n by [].
    have := erefl (trmn R Hn 1); rewrite -{1}H {H}.
    rewrite !(rmorphismMP (trmn R Hn)) /= (truncpsc_compat _ Hn) => H.
    apply (introN idP) => /eqP Habs.
    move: H; rewrite Habs mulr0 => /esym/eqP.
    by rewrite oner_eq0.
Qed.

Lemma invpsc_compat f : compatible (fun n => (truncpsc f n)^-1).
Proof.
  move=> m n Hmn; case: (boolP (unitpsc f)) => H0.
  - by rewrite (rmorphV (trmn R Hmn) (unitpscP _ _ H0)) /= truncpsc_compat.
  - move: H0 => /unitpscP H0.
    rewrite !invr_out.
    + by rewrite truncpsc_compat.
    + apply (introN idP); apply H0.
    + apply (introN idP); apply H0.
Qed.
Definition invpsc f := limtrunc (invpsc_compat f).
Lemma invpscE f n : truncpsc (invpsc f) n = (truncpsc f n)^-1.
Proof. rewrite /invpsc; by rewrite limtruncE. Qed.

Lemma invpscP : {in unitpsc, left_inverse 1 invpsc *%R}.
Proof.
  move=> f /unitpscP Hf; apply eq_truncpsc => n.
  by rewrite mulpscE powser1E limtruncE mulVr; last exact: Hf.
Qed.

Lemma invpscCP : {in [predC unitpsc], invpsc =1 id}.
Proof.
  move=> f; rewrite unfold_in /= => /unitpscP H; apply eq_truncpsc => n.
  rewrite invpscE invr_out //; apply (introN idP); by apply H.
Qed.

Lemma mulpsc1inv x y : mulpsc y x = 1 -> unitpsc x.
Proof.
  move=> H; apply /(unitpscP 0); apply/unitrPr.
  exists (truncpsc y 0%N); rewrite mulrC.
  by rewrite -mulpscE H powser1E.
Qed.

Definition powser_unitRingMixin :=
  Eval hnf in ComUnitRingMixin invpscP mulpsc1inv invpscCP.
Canonical powser_unitRingType := Eval hnf in UnitRingType powser powser_unitRingMixin.
Canonical powser_comUnitRingType := [comUnitRingType of powser].

End PowserCheat.

(*

Let PX_pred n := [pred p : {poly R} | 'X^n.+1 %| p].

Fact PX_key n : pred_key (PX_pred n). Proof. by []. Qed.
Canonical PX n := KeyedPred (PX_key n).

Lemma PX0 n : 0 \in PX n.
Proof. apply/dvdpP; exists 0; by rewrite mul0r. Qed.

Lemma inclPXleq n m : n >= m -> {subset (PX n) <= (PX m)}.
Proof.
  move=> H p; rewrite !inE.
  move/dvdpP => [a] -> /=; apply/dvdpP; exists (a * 'X^(n.+1 - m.+1)).
  by rewrite -mulrA -exprD subnK.
Qed.

Lemma inclPXn n : {subset (PX n.+1) <= (PX n)}.
Proof. by apply inclPXleq. Qed.

Lemma divXnE n (p : {poly R}) : p %% 'X^n = Poly (take n p).
Proof.
  
Lemma PXP n (p : {poly R}) : reflect (forall i, i <= n -> p`_i = 0) (p \in PX n).
Proof.
  apply (iffP idP).
  - rewrite inE => /dvdpP [] a -> i Hi; by rewrite coefMXn ltnS Hi.
  - move=> H; case: (altP (p =P 0)) => [->| H0]; first exact: PX0.
    apply/dvdpP; exists (divPoly (drop n p)).
    apply val_inj => /=; rewrite polyseqMXn.
    - rewrite -cat_nseq /=.

Lemma opprclosedPX n : oppr_closed (PX n).
Proof.
  
Qed.

Lemma idealr_closed_nontrivial R S : @idealr_closed R S -> nontrivial_ideal S.
Proof. by case=> S0 S1 hS; split => // a x xS; rewrite -[_ * _]addr0 hS. Qed.

Lemma idealr_closedB R S : @idealr_closed R S -> zmod_closed S.
Proof. by case=> S0 _ hS; split=> // x y xS yS; rewrite -mulN1r addrC hS. Qed.

Lemma closedPX n : idealr_closed (PX n).
Proof.
  split => [|| a b c Hb Hc]; rewrite ?inE.
  - exact: PX0.
  - apply (introN idP); by rewrite dvdp1 size_polyXn.
  - apply dvdp_add; last exact Hc.
    exact: dvdp_mull.
Qed.

Import DefaultKeying GRing.DefaultPred.
Canonical addrPX n := AddrPred (closedPX n).
Canonical zmodPX n := ZmodPred (k := addrPX n) (closedPX n).
Definition oXn n := Idealr (PX n) (closedPX n).
Definition PolyTr n := {ideal_quot (PX n)}.


Lemma subXn n m p q :
  n >= m -> p == q %[mod_ideal (PX n)] -> p == q %[mod_ideal (PX m)].
Proof. move=> H; rewrite -!Quotient.idealrBE /=; by apply: inclPXleq. Qed.


*)
