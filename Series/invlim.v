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


