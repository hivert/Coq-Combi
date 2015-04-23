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
Require Import path finset finfun fingraph tuple bigop ssrint ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope invlim_scope with ILim.

Definition directed (T : eqType) (r : rel T) := forall i j : T, { k | r i k & r j k }.

Inductive dirposet := DirPoset
  {
    carrier : eqType;
    posleq :> rel carrier;
    _ : reflexive posleq;
    _ : antisymmetric posleq;
    _ : transitive posleq;
    _ : directed posleq
  }.

Definition eqtype_of_dirposet (P : dirposet) : eqType := carrier P.
Coercion eqtype_of_dirposet : dirposet >-> eqType.

Lemma dp_refl (P : dirposet) : reflexive P.
Proof. by case: P. Qed.
Lemma dp_sym (P : dirposet) : antisymmetric P.
Proof. by case: P. Qed.
Lemma dp_trans (P : dirposet) : transitive P.
Proof. by case: P. Qed.
Lemma dp_dir (P : dirposet) : directed P.
Proof. by case: P. Qed.


Lemma leq_dir : directed leq.
Proof. move=> i j; exists (maxn i j). by apply leq_maxl. by apply leq_maxr. Qed.

Canonical nat_dir := DirPoset leqnn anti_leq leq_trans leq_dir.
Definition dir_of_nat (i : nat) : nat_dir := i.
Coercion dir_of_nat : nat >-> Equality.sort.

Lemma nat_dirE i j : nat_dir i j <-> i <= j.
Proof. by []. Qed.



Section Defs.

Variable Index : dirposet.
Variable sys : Index -> eqType.
Definition trans_eqType := forall i j : Index, Index i j -> (sys j) -> (sys i).
Variable mors : trans_eqType.

(* The following hypothesis is not used anywhere *)
Hypothesis Hcomp :
  forall i j k  (Hij : Index i j) (Hjk L : Index j k),
    (mors Hij) \o (mors Hjk) =1 (mors (dp_trans Hij Hjk)).

Definition sysseq := forall n, sys n.
Definition compatible (f : sysseq) :=
  forall (i j : Index) (Hij : Index i j), mors Hij (f j) = f i.

Record cseq_type : predArgType := CSeq {cseq : sysseq; _ : compatible cseq}.

Definition cseq_of of phant Index := cseq_type.
Identity Coercion type_cseq_of : cseq_of >-> cseq_type.

Definition proj (i : Index) (s : cseq_type) : sys i := cseq s i.

Lemma cseqP (s : cseq_type) : compatible (fun i => proj i s).
Proof. by case s. Qed.

Lemma projE s (H : compatible s) i : proj i (CSeq H) = s i.
Proof. by []. Qed.

Lemma projP s i j (Hij : Index i j) : mors Hij (proj j s) = (proj i s).
Proof. by rewrite cseqP. Qed.

End Defs.

Notation "{ 'invlim' I '|' M }" := (cseq_of M (Phant I))
  (at level 0, format "{ 'invlim' I '|' M }") : type_scope.

Section EqType.

Variable Index : dirposet.
Variable sys : Index -> eqType.
Variable mors : trans_eqType sys.

Let cseqType := {invlim Index | mors}.

Definition neq_invlim (x y : cseqType) : Prop := exists n, (cseq x) n != (cseq y) n.
Notation "!=%ILim" := neq_invlim : invlim_scope.
Notation "x != y" := (neq_invlim x  y) : invlim_scope.
Definition eq_invlim x y := (~ (x != y)%ILim).
Notation "x == y" := (eq_invlim x y) : invlim_scope.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope invlim_scope.

Lemma eq_invlimE x y : (forall n, cseq x n = cseq y n) <-> (x == y)%ILim.
Proof.
  rewrite /eq_invlim; split.
  - move=> Heq [] n; by rewrite Heq eq_refl.
  - move=> H n; case: (altP (cseq x n =P cseq y n)) => // Habs.
    exfalso; apply H; by exists n.
Qed.

Lemma eq_projE x y : (forall n, proj n x = proj n y) <-> (x == y)%ILim.
Proof. exact: eq_invlimE. Qed.

Lemma eq_invlim_refl x : x == x.
Proof. by rewrite -eq_invlimE. Qed.
Hint Resolve eq_invlim_refl.

Lemma neq_invlim_sym x y : x != y -> y != x.
Proof. move=> [] n H; exists n; by rewrite eq_sym. Qed.

Lemma eq_invlim_sym x y : x == y -> y == x.
Proof. by move=> eq_xy /neq_invlim_sym. Qed.

Lemma eq_invlim_trans x y z : x == y -> y == z -> x == z.
Proof. rewrite -!eq_invlimE => Hxy Hyz n; by rewrite Hxy Hyz. Qed.

Variable E : eqType.
Variable phi : forall n, E -> sys n.
Hypothesis Hphi : forall e : E, compatible mors (phi^~ e).

(* Universal property *)
Definition induced e := CSeq (Hphi e).
Lemma inducedE n e : proj n (induced e) = phi n e.
Proof. by []. Qed.

End EqType.

Bind Scope invlim_scope with cseq.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope invlim_scope.

Notation "!=%ILim" := neq_invlim : invlim_scope.
Notation "x != y" := (neq_invlim x  y) : invlim_scope.
Notation "x == y" := (eq_invlim x y) : invlim_scope.

Import GRing.Theory.



Section ZmodType.

Variable Index : dirposet.
Variable sys : Index -> zmodType.
Definition trans_additive :=
  forall i j : Index, Index i j -> {additive (sys j) -> (sys i)}.
Variable mors : trans_additive.

Let cseqType := {invlim Index | mors}.


Implicit Type f g : cseqType.

Lemma zerocs_compat : compatible mors (fun n => 0).
Proof. move=> m n Hmn; by rewrite /= raddf0. Qed.
Definition zerocs : cseqType := CSeq zerocs_compat.
Notation "0" := zerocs : invlim_scope.
Lemma zerocsE n : proj n 0 = 0%R.
Proof. by []. Qed.


Lemma addcs_compat f g : compatible mors (fun n => cseq f n + cseq g n).
Proof. move=> m n Hmn; by rewrite /= raddfD !(@cseqP _ _ mors). Qed.
Definition addcs f g : cseqType := CSeq (addcs_compat f g).
Notation "x + y" := (addcs x y) : invlim_scope.
Lemma addcsE n : {morph (proj n) : x y / x + y >-> (x + y)%R}.
Proof. by []. Qed.

Lemma oppcs_compat f : compatible mors (fun n => - cseq f n).
Proof. move=> m n Hmn; by rewrite /= raddfN !(@cseqP _ _ mors). Qed.
Definition oppcs f : cseqType := CSeq (oppcs_compat f).
Notation "- x" := (oppcs x) : invlim_scope.
Notation "x - y" := (x + -y) : invlim_scope.
Lemma oppcsE n : {morph (proj n) : x / - x >-> (- x)%R}.
Proof. by []. Qed.
Lemma oppcsB n : {morph (proj n) : x y / x - y >-> (x - y)%R}.
Proof. by []. Qed.

Lemma addcsC f g : f + g == g + f.
Proof. apply eq_projE => d; by rewrite /= addrC. Qed.
Lemma addcsA f g h : f + (g + h) == (f + g) + h.
Proof. apply eq_projE => d; by rewrite /= addrA. Qed.

Lemma add0cs f : 0 + f == f.
Proof. apply eq_projE => d; by rewrite /= add0r. Qed.
Lemma addcs0 f : f + 0 == f.
Proof. apply eq_projE => d; by rewrite /= addr0. Qed.

Lemma addcsN f : f + (- f) == 0.
Proof. apply eq_projE => d; by rewrite /= addrN. Qed.

Lemma addNcs f : (- f) + f == zerocs.
Proof. apply eq_projE => d; by rewrite /= addNr. Qed.

(* Universal property *)
Variable E : zmodType.
Variable phi : forall n, {additive E -> sys n}.
Hypothesis Hphi : forall e : E, compatible mors (phi^~ e).
Let induced : E -> cseqType := induced Hphi.

Lemma inducedD x y : induced (x + y) == induced x + induced y.
Proof. apply eq_projE => d; by rewrite /= raddfD. Qed.
Lemma inducedN x : induced (- x) == - induced x.
Proof. apply eq_projE => d; by rewrite /= raddfN. Qed.
Lemma induced0 : induced 0 == 0.
Proof. apply eq_projE => d; by rewrite /= raddf0. Qed.

End ZmodType.

Notation "x + y" := (addcs x y) : invlim_scope.
Notation "- x" := (oppcs x) : invlim_scope.
Notation "x - y" := (x + (- y)) : invlim_scope.
Notation "0" := (@zerocs _ _ _) : invlim_scope.

Section Ring.

Variable Index : dirposet.
Variable sys : Index -> ringType.
Definition trans_rmorphism :=
  forall i j : Index, Index i j -> {rmorphism (sys j) -> (sys i)}.
Variable mors : trans_rmorphism.

Let cseqType := {invlim Index | mors}.


Implicit Type f g : cseqType.

Lemma onecs_compat : compatible mors (fun n => 1).
Proof. move=> m n Hmn; by rewrite /= rmorph1. Qed.
Definition onecs : cseqType := CSeq onecs_compat.
Notation "1" := onecs : invlim_scope.
Lemma onecsE n : proj n 1 = 1%R.
Proof. by []. Qed.

Lemma mulcs_compat f g : compatible mors (fun n => cseq f n * cseq g n).
Proof. move=> m n Hmn; by rewrite /= rmorphismMP !(@cseqP _ _ mors). Qed.
Definition mulcs f g : cseqType := CSeq (mulcs_compat f g).
Notation "x * y" := (mulcs x y) : invlim_scope.
Lemma mulcsE n : {morph (proj n) : x y / x * y >-> (x * y)%R}.
Proof. by []. Qed.

Lemma mulpsA f g h : f * (g * h) == (f * g) * h.
Proof. apply eq_projE => d; by rewrite /= mulrA. Qed.

Lemma mul1ps f : 1 * f == f.
Proof. apply eq_projE => d; by rewrite /= mul1r. Qed.
Lemma mulps1 f : f * 1 == f.
Proof. apply eq_projE => d; by rewrite /= mulr1. Qed.

Lemma mul_addpsr f g h : f * (g + h) == (f * g) + (f * h).
Proof. apply eq_projE => d; by rewrite /= mulrDr. Qed.

Lemma mul_addpsl f g h : (g + h) * f == (g * f) + (h * f).
Proof. apply eq_projE => d; by rewrite /= mulrDl. Qed.

Lemma eqcs01 : Index -> 1 != 0.
Proof.  move=> i; exists i; rewrite /=; exact: oner_neq0. Qed.

(* Universal property *)
Variable E : ringType.
Variable phi : forall n, {rmorphism E -> sys n}.
Hypothesis Hphi : forall e : E, compatible mors (phi^~ e).
Let induced : E -> cseqType := induced Hphi.

Lemma inducedM x y : induced (x * y) == induced x * induced y.
Proof. apply eq_projE => d; by rewrite /= rmorphM. Qed.
Lemma induced1 : induced 1 == 1.
Proof. apply eq_projE => d; by rewrite /= rmorph1. Qed.

End Ring.

Notation "x * y" := (mulcs x y) : invlim_scope.
Notation "1" := (@onecs _ _ _): invlim_scope.

Section CommRing.

Variable Index : dirposet.
Variable sys : Index -> comRingType.
Variable mors : trans_rmorphism sys.

Let cseqType := {invlim Index | mors}.

Implicit Type f g : cseqType.

Lemma mulpsC f g : f * g == g * f.
Proof. apply eq_projE => d; by rewrite /= mulrC. Qed.

End CommRing.


Section Unit.

Variable R : unitRingType.

Variable Index : dirposet.
Variable sys : Index -> unitRingType.
Variable mors : trans_rmorphism sys.

Let cseqType := {invlim Index | mors}.

Implicit Type f g : cseqType.

Definition prounit f := forall n, (proj n f) \is a GRing.unit.
Lemma inv_compat f : prounit f -> compatible mors (fun n => (proj n f)^-1).
Proof.
  move=> Hinv m n Hmn.
  rewrite /= rmorphV; last exact: Hinv.
  by rewrite !(@cseqP _ _ mors).
Qed.
Definition invcs f (Hf : prounit f) : cseqType := CSeq (inv_compat Hf).
Lemma invcsE n f (Hf : prounit f) : proj n (invcs Hf) = (proj n f)^-1.
Proof. by []. Qed.

(* Universal property *)
Variable E : unitRingType.
Variable phi : forall n, {rmorphism E -> sys n}.
Hypothesis Hphi : forall e : E, compatible mors (phi^~ e).
Let induced : E -> cseqType := induced Hphi.

Lemma induced_prounit e : e \is a GRing.unit -> prounit (induced e).
Proof. move=> He n; rewrite inducedE; exact: rmorph_unit. Qed.
Lemma induced_invcs e (He : e \is a GRing.unit) :
  invcs (induced_prounit He) == induced (e^-1).
Proof. apply eq_projE => d; by rewrite /= rmorphV. Qed.

End Unit.


Section Linear.

Variable R : comRingType.

Variable Index : dirposet.
Variable sys : Index -> lmodType R.
Definition trans_linear :=
  forall i j : Index, Index i j -> {linear (sys j) -> (sys i)}.
Variable mors : trans_linear.

Let cseqType := {invlim Index | mors}.

Implicit Type f g : cseqType.

Lemma scale_compat a f : compatible mors (fun n =>  a *: (cseq f n)).
Proof. move=> m n Hmn; by rewrite /= linearZ_LR !(@cseqP _ _ mors). Qed.
Definition scalecs a f : cseqType := CSeq (scale_compat a f).
Notation "a *: y" := (scalecs a y) : invlim_scope.
Lemma scalecsE n a : {morph (proj n) : x y / a *: y >-> (a *: y)%R}.
Proof. by []. Qed.

(* Universal property *)
Variable E : lmodType R.
Variable phi : forall n, {linear E -> sys n}.
Hypothesis Hphi : forall e : E, compatible mors (phi^~ e).

Let induced : E -> cseqType := induced Hphi.

Lemma inducedZ a x : induced (a *: x) == a *: induced x.
Proof. apply eq_projE => d; by rewrite /= linearZ_LR. Qed.

End Linear.

Notation "a *: y" := (scalecs a y) : invlim_scope.

(*
Import GRing.Theory.

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


*)
