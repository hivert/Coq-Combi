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

Lemma iota_gtn n k : [seq x <- iota 0 n | gtn k x] = iota 0 (minn n k).
Proof.
  rewrite /minn; case ltnP => Hn.
  + rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT.
    move=> i; rewrite mem_iota add0n /= => Hi.
    by rewrite (ltn_trans Hi Hn).
  + rewrite -{1}[k]addn0; move: (0) => i.
    elim: k i n Hn => [//= | k IHk] i n Hn.
    * rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
      move=> j; by rewrite mem_iota leqNgt add0n => /andP [] /negbTE ->.
    * have:= ltn_predK Hn => H; rewrite -H in Hn.
      have:= IHk i.+1 _ Hn => /= <-.
      by rewrite -{1}H /= -{1}[i]add0n ltn_add2r /= addSnnS.
Qed.

Lemma iota_leq n k : [seq x <- iota 0 n | k <= x] = iota k (n - k).
Proof.
  rewrite -{1 2}[k]add0n; move: (0)%N => i.
  elim: n i k => [| n IHn] i k //=.
  rewrite /= -{2}[i]addn0 leq_add2l.
  case: leqP.
  - rewrite leqn0 => /eqP ->; rewrite addn0 subn0 /=.
    rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT.
    move=> j; by rewrite mem_iota /= => /andP [] /ltnW ->.
  - case: k => [//= | k _].
    rewrite subSS -addSnnS; exact: IHn.
Qed.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.

Delimit Scope series_scope with S.
Open Scope ring_scope.

Reserved Notation "{ 'pow' T }" (at level 0, format "{ 'pow'  T }").

Section Defs.

Variable R : comRingType.

Definition PowSer := nat -> R.

Definition zerops : PowSer := [fun _ => 0].
Definition oneps : PowSer := [fun d => if d is 0%N then 1 else 0].
Definition xps : PowSer := [fun d => if d is 1%N then 1 else 0].

Definition addps (f g : PowSer) : PowSer := fun d => f d + g d.
Definition oppps (f : PowSer) : PowSer := fun d => - f d.
Definition mulps (f g : PowSer) : PowSer :=
  fun d => \sum_(0 <= i < d.+1) (f i) * (g (d - i)%N).
Definition mulRps r (g : PowSer) : PowSer := [fun d => r * g d].

Notation "0" := (zerops) : series_scope.
Notation "1" := (oneps) : series_scope.
Notation "x + y" := (addps x y) : series_scope.
Notation "x * y" := (mulps x y) : series_scope.
Notation "- x" := (oppps x) : series_scope.
Notation "x *+ y" := (mulRps x y) : series_scope.

Open Scope series_scope.

Lemma addpsC f g : f + g =1 g + f.
Proof. rewrite /addps => d; by rewrite addrC. Qed.

Lemma addpsA f g h : f + (g + h) =1 (f + g) + h.
Proof. rewrite /addps => d; by rewrite addrA. Qed.

Lemma add0ps f : 0 + f =1 f.
Proof. rewrite /addps/= => d; by rewrite add0r. Qed.
Lemma addps0 f : f + 0 =1 f.
Proof. rewrite /addps/= => d; by rewrite addr0. Qed.

Lemma addpsN f : f + (- f) =1 0.
Proof. rewrite /addps/oppps/= => d; by rewrite addrN. Qed.
Lemma addNps f : (- f) + f =1 zerops.
Proof. rewrite /addps/oppps/= => d; by rewrite addNr. Qed.

Lemma mulpsC f g : f * g =1 g * f.
Proof.
  rewrite /mulps => d; rewrite !big_mkord.
  rewrite (reindex (@rev_ord _)) /=; last by apply onW_bij; apply inv_bij; apply rev_ordK.
  apply eq_bigr => i _.
  rewrite mulrC subSS subKn //.
  rewrite -ltnS; exact: ltn_ord.
Qed.

Lemma mul1ps f : 1 * f =1 f.
Proof.
  rewrite /mulps/= => d.
  rewrite (@eq_big_nat _ _ _ 0 d.+1 _
                       (fun i => if pred1 0%N i then f d else 0%R)); first last.
    move=> i _; rewrite /oneps /=.
    case: i => [|i] /=; first by rewrite subn0 mul1r.
    by rewrite mul0r.
  rewrite -big_mkcond -big_filter filter_pred1_uniq.
  - by rewrite /= big_cons big_nil addr0.
  - rewrite /index_iota; exact: iota_uniq.
  - by rewrite /index_iota subn0 /= in_cons eq_refl.
Qed.
Lemma mulps1 f : f * 1 =1 f.
Proof. by move=> d; rewrite mulpsC mul1ps. Qed.

Lemma mulpsA f g h : f * (g * h) =1 (f * g) * h.
Proof.
  rewrite /mulps => d.
  rewrite [RHS](eq_bigr (fun i =>
                      (\sum_(0 <= i0 < i.+1) f i0 * g (i - i0)%N * h (d - i)%N)));
    last by move=> i _; rewrite mulr_suml; apply eq_bigr.
  rewrite [RHS](@eq_big_nat _ _ _ 0 d.+1 _ (fun i =>
      \sum_(0 <= i0 < d.+1 | i0 <= i) f i0 * g (i - i0)%N * h (d - i)%N)); first last.
    move=> i /andP [] _ Hi; rewrite -[RHS]big_filter; apply congr_big => //.
    rewrite /index_iota !subn0.
    rewrite (eq_filter (a2 := gtn i.+1)); last by move=> j /=; rewrite ltnS.
    rewrite iota_gtn /minn ltnS.
    move: Hi; by rewrite ltnNge => /negbTE ->.
  rewrite (exchange_big_dep_nat predT) //=.
  rewrite [RHS](eq_bigr (fun j =>
                           f j * \sum_(0 <= i < d.+1 | j <= i) g (i - j)%N * h (d - i)%N))%R;
    last by move=> i _; rewrite mulr_sumr; apply eq_bigr => j _; rewrite mulrA.
  apply eq_big_nat => i /andP [] _; rewrite ltnS => Hi; congr (_ * _)%R.
  rewrite -[RHS]big_filter iota_leq subn0.
  rewrite -{3}[i]addn0 iota_addl big_map (subSn Hi).
  apply eq_big_nat => j /andP [] _ Hj.
  by rewrite addKn subnDA.
Qed.

Lemma mul_addpsr f g h : f * (g + h) =1 (f * g) + (f * h).
Proof.
  rewrite /mulps /addps => d; rewrite -big_split /=.
  apply eq_bigr => j _; by rewrite mulrDr.
Qed.

Lemma mul_addpsl f g h : (g + h) * f =1 (g * f) + (h * f).
Proof.
  rewrite /mulps /addps => d; rewrite -big_split /=.
  apply eq_bigr => j _; by rewrite mulrDl.
Qed.

Lemma mul_scal a b f g : (a *+ f) * (b *+ g) =1 (a * b) *+ (f * g).
Proof.
  rewrite /mulps/mulRps => d /=.
  rewrite mulr_sumr; apply eq_bigr => i _.
  by rewrite !mulrA -[(a * f i * b)%R]mulrA [(f i * b)%R]mulrC mulrA.
Qed.

End Defs.

Notation "0" := (zerops) : series_scope.
Notation "1" := (oneps) : series_scope.
Notation "x + y" := (addps x y) : series_scope.
Notation "x * y" := (mulps x y) : series_scope.
Notation "- x" := (oppps x) : series_scope.
Notation "x *+ y" := (mulRps x y) : series_scope.

Notation "{ 'pow' R }" := (PowSer R).


Section Valuation.

Variable R : comRingType.

Definition geqval (f : {pow R}) n := (forall i, i < n -> f i == 0).


CoInductive val (f : {pow R}) n :=
  Valuation: f n != 0 -> (forall i, i < n -> f i == 0) -> val f n.

Lemma val_uniq f m n : val f m -> val f n -> m = n.
Proof.
  suff Tmp i j : val f i -> val f j -> i <= j.
    by move=> Hm Hn; apply anti_leq; apply/andP; split; apply Tmp.
  move=> [] Hi Hlti [] Hj Hltj; rewrite leqNgt.
  exact: (contra (Hlti j) Hj).
Qed.

End Valuation.
(*
Section Streams.

Variable R : comRingType.

CoInductive stream := Cons: R -> stream -> stream.

CoFixpoint stream_of_fun (f : PowSer R) :=
  Cons (f 0%N) (stream_of_fun (fun d => f d.+1)).

Lemma stream_eq f g : f =1 g <-> stream_of_fun f = stream_of_fun g.
Proof.
  split.
  - move=> H; rewrite /=.
*)
