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

Import GRing.Theory.

Section TruncPol.

Variable R : fieldType.
Local Open Scope ring_scope.

Import Pdiv.Ring.

Lemma mod1Xn n : 1 %% 'X^n.+1 = 1 :> {poly R}.
Proof. by rewrite modp_small // size_polyXn size_polyC oner_eq0. Qed.

Lemma truncmn m n (f : {poly R}) : m >= n -> (f %% 'X^m) %% 'X^n = f %% 'X^n.
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
  ComRingMixin mul_truncA mul_truncC mul_trunc1 mul_truncDl trunc10.
Canonical trunc_ringType := Eval hnf in RingType truncType trunc_ringMixin.
Canonical trunc_comRingType := Eval hnf in ComRingType truncType mul_truncC.

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

End Defs.

Section Morph.

Variable m n : nat.
Hypothesis Hmn : m >= n.
Local Open Scope ring_scope.

Definition mormn (x : truncType m) : truncType n := trunc n x.


Lemma mormn_add : additive mormn.
Proof. move=> f g; apply val_inj; by rewrite /= !modp_add !modp_opp !modp_mod !truncmn. Qed.

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

(*
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
*)

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



Section InvLim.

Variable R : ringType.
Local Open Scope ring_scope.

Variable sys : nat -> algType R.
Variable mors : forall n : nat, {lrmorphism (sys n.+1) -> (sys n)}.

Definition compat (s : forall n, sys n) := forall n, (mors n) (s n.+1) == s n.

Structure cseqType : predArgType := CSeq {cseq :> forall n, sys n; _ : compat cseq}.

Lemma cseqP (s : cseqType) n : (mors n) (s n.+1) = s n.
Proof. case: s => [s comp] /=; apply/eqP; exact: comp. Qed.

(* Unfortunately the following relation is undecidable for general cseq *)
Definition eqcseq (f g : cseqType) : Prop := forall n, f n = g n.

Notation "f =c g " := (eqcseq f g) (at level 70, no associativity).

Lemma cseq_refl f : f =c f.
Proof. by []. Qed.

Lemma cseq_sym f g : f =c g -> g =c f.
Proof. move=> H n; by rewrite H. Qed.

Lemma cseq_trans f g h : f =c g -> g =c h -> f =c h.
Proof. move=> Hfg Hgh n; by rewrite Hfg Hgh. Qed.

Lemma compat_zero : compat (fun n => 0).
Proof. rewrite /compat => n; by rewrite rmorph0. Qed.
Definition c0 := CSeq _ compat_zero.

Lemma compat_one : compat (fun n => 1).
Proof. rewrite /compat => n; by rewrite rmorph1. Qed.
Definition c1 := CSeq _ compat_one.

Lemma compat_addc (f g : cseqType) : compat (fun n => f n + g n).
Proof. rewrite /compat => n; by rewrite rmorphD /= !cseqP. Qed.
Definition addc f g := CSeq _ (compat_addc f g).

Lemma compat_oppc (f : cseqType) : compat (fun n => - f n).
Proof. rewrite /compat => n; by rewrite rmorphN /= !cseqP. Qed.
Definition oppc f := CSeq _ (compat_oppc f).

Lemma compat_mulc (f g : cseqType) : compat (fun n => f n * g n).
Proof. rewrite /compat => n; by rewrite rmorphM /= !cseqP. Qed.
Definition mulc f g := CSeq _ (compat_mulc f g).

Notation "f +c g " := (addc f g) (at level 50).

(* Z-Module theory *)
Lemma addcA f g h : (f +c g) +c h =c f +c (g +c h).
Proof. move=> n /=; by rewrite addrA. Qed.

Lemma addcC f g : f +c g =c g +c f.
Proof. move=> n /=; by rewrite addrC. Qed.

Lemma add0c f : c0 +c f =c f.
Proof. move=> n /=; by rewrite add0r. Qed.

Lemma addc0 f : f +c c0 =c f.
Proof. move=> n /=; by rewrite addr0. Qed.

Lemma addcN f : f +c (oppc f) =c c0.
Proof. move=> n /=; by rewrite addrN. Qed.

Lemma addNc f : (oppc f) +c f =c c0.
Proof. move=> n /=; by rewrite addNr. Qed.

(* Ring theory *)

Notation "f *c g " := (mulc f g) (at level 30).

Lemma eqcseq01 : ~(c0 =c c1).
Proof.
  move=> H. have := oner_neq0 (sys 0%N).
  have /= -> := (H 0%N); by rewrite eq_refl.
Qed.

Lemma mulcA f g h : (f *c g) *c h =c f *c (g *c h).
Proof. move=> n /=; by rewrite mulrA. Qed.

Lemma mul1c f : c1 *c f =c f.
Proof. move=> n /=; by rewrite mul1r. Qed.

Lemma mulc1 f : f *c c1 =c f.
Proof. move=> n /=; by rewrite mulr1. Qed.

Lemma mulcDl f g h : (f +c g) *c h =c (f *c h) +c (g *c h).
Proof. by move=> n /=; rewrite mulrDl. Qed.

Lemma mulcDr f g h : f *c (g +c h) =c (f *c g) +c (f *c h).
Proof. by move=> n /=; rewrite mulrDr. Qed.

End InvLim.

Section ComInvLim.

Variable R : comRingType.
Local Open Scope ring_scope.

Variable sys : nat -> calgType R.
Variable mors : forall n : nat, {lrmorphism (sys n.+1) -> (sys n)}.

Lemma mulcC f g : f *c g =c g *c f.
Proof. move=> n /=; by rewrite mulrC. Qed.


  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul *%R;
  _ : right_distributive mul *%R;
  _ : one != 0


