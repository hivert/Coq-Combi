(** * Combi.Basic.latticetype : Lattice Types *)
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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice fintype seq.
Require Import tools ordtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(******************************************************************************)

Section Spec.

CoInductive meet_spec (T : pordType) (x y b : T) : Prop :=
| MeetSpec :
    b <= x -> b <= y -> (forall z, z <= x -> z <= y -> z <= b) -> meet_spec x y b.

CoInductive join_spec (T : pordType) (x y b : T) : Prop :=
| JoinSpec :
    b >= x -> b >= y -> (forall z, z >= x -> z >= y -> z >= b) -> join_spec x y b.

Variable T : pordType.
Implicit Type x y : T.

Lemma meet_spec_uniq x y b1 b2 :
  meet_spec x y b1 -> meet_spec x y b2 -> b1 = b2.
Proof.
  move=> [Hb1x Hb1y Hb1] [Hb2x Hb2y Hb2].
  by apply anti_leqX; rewrite Hb1 // Hb2.
Qed.

Lemma meet_join_spec x y b :
  @join_spec (dual_pordType T) x y b <-> @meet_spec T x y b.
Proof. by split=> [] [Hx Hy H]; constructor; rewrite ?dual_leqX. Qed.

Lemma join_meet_spec x y b :
  @meet_spec (dual_pordType T) x y b <-> @join_spec T x y b.
Proof. by split=> [] [Hx Hy H]; constructor; rewrite ?dual_leqX. Qed.

End Spec.


Module Semilattice.

Definition axiom (T : pordType) (meet : T -> T -> T) :=
  forall x y : T, meet_spec x y (meet x y).

Section ClassDef.

Record mixin_of (T : pordType) :=
  Mixin { meet : T -> T -> T; _ : @axiom T meet }.

Record class_of (T : Type) := Class {
  base : PartOrder.class_of T;
  mixin : mixin_of (PartOrder.Pack base T)
}.
Local Coercion base : class_of >->  PartOrder.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T0 _ _ := cT in T0.
Notation xclass := (class : class_of xT).

Definition pack (b : PartOrder.class_of T) (m : mixin_of (PartOrder.Pack b T))
           (bT : pordType)
           (_ : phant_id (PartOrder.class bT) b)
           (m0 : mixin_of bT)
           (_ : phant_id m m0) := Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition pordType := @PartOrder.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> PartOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion pordType : type >-> PartOrder.type.
Canonical pordType.
Notation semilatticeType := type.
Notation semilatticeMixin := mixin_of.
Notation SemilatticeType T m := (@pack T _ m _ id _ id).
Notation "[ 'semilatticeType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'semilatticeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'semilatticeType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'semilatticeType'  'of'  T ]") : form_scope.

End Exports.

End Semilattice.
Export Semilattice.Exports.

Definition meet (T : semilatticeType) : T -> T -> T :=
  Semilattice.meet (Semilattice.mixin (Semilattice.class T)).

Section SemilatticeTheory.

Variable T : semilatticeType.
Implicit Type x y : T.

Lemma meetP x y : meet_spec x y (meet x y).
Proof. by case: T x y => sort [] /= base /= []. Qed.

Lemma meet_uniq x y b : meet_spec x y b -> meet x y = b.
Proof. move/meet_spec_uniq => H. apply: esym; apply: H; exact: meetP. Qed.

Lemma meetC x y : meet x y = meet y x.
Proof.
  have [Hy Hx Hb] := meetP y x.
  apply: meet_uniq; constructor => // b H1 H2; exact: Hb.
Qed.

Lemma ge_meetL x y : meet x y <= x.
Proof. by have [] := meetP x y. Qed.

Lemma ge_meetR x y : meet x y <= y.
Proof. rewrite meetC; exact: ge_meetL. Qed.

Lemma meet_le x y z : z <= x -> z <= y -> z <= meet x y.
Proof. have [_ _] := meetP x y; apply. Qed.

Lemma meet_leE x y : (x <= y) = (meet x y == x).
Proof.
  apply/idP/idP => [H | /eqP <-].
  - by apply/eqP/meet_uniq; constructor.
  - exact: ge_meetR.
Qed.

Lemma meet_monotonic x1 y1 x2 y2 :
  x1 <= x2 -> y1 <= y2 -> meet x1 y1 <= meet x2 y2.
Proof.
  move=> H1 H2; apply: meet_le.
  - exact: (leqX_trans (ge_meetL _ _)).
  - exact: (leqX_trans (ge_meetR _ _)).
Qed.

Lemma meetA x y z : meet (meet x y) z = meet x (meet y z).
Proof.
  apply meet_uniq; constructor.
  - by apply: meet_monotonic; last exact: ge_meetL.
  - exact: (leqX_trans (ge_meetR _ _) (ge_meetR _ _)).
  - move=> b Hb_xy Hbz; apply: meet_le.
    + exact: (leqX_trans Hb_xy (ge_meetL _ _)).
    + apply: (meet_le _ Hbz).
      exact: (leqX_trans Hb_xy (ge_meetR _ _)).
Qed.

Lemma meetId x : meet x x = x.
Proof. by apply: meet_uniq; constructor. Qed.

End SemilatticeTheory.


(*

Lemma lubP x y : @meet_spec (dual_pordType T) x y (lub x y).
Proof. by case: T x y => sort [] /= base /= []. Qed.

Lemma le_lub x y : x <= lub x y.
Proof. by have [] := lubP x y. Qed.

Lemma lubE x y : lub x y = @meet (dual_pordType T) x y.
Proof. by case: T x y => sort [] /= base /= []. Qed.
*)
