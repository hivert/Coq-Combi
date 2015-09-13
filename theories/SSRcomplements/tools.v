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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop.

Set Implicit Arguments.
Unset Strict Implicit.

(******************************************************************************)
(** * A bunch of lemmas about seqs which are missing in SSReflect             *)
(*                                                                            *)
(** TODO: these probably should be contributed to SSReflect itself            *)
(******************************************************************************)

(* Some automatization *)
Lemma nth_nil i : nth 0 [::] i = 0.
Proof. by rewrite nth_default. Qed.
Hint Resolve nth_nil.

Lemma ieqi1F i : (i == i.+1) = false.
Proof. apply: negbTE; by elim i. Qed.

Lemma bad_if_leq i j : i <= j -> (if i < j then i else j) = i.
Proof. move=> Hi; case (ltnP i j) => //= Hj; apply/eqP; by rewrite eqn_leq Hi Hj. Qed.

Section RCons.

  Variable (T : eqType).
  Implicit Type s w : seq T.
  Implicit Type a b : T.

  Lemma flatten_rcons s t : flatten (rcons t s) = flatten t ++ s.
  Proof.
    elim: t => [//= | t0 t IHt /=]; first by rewrite cats0.
    by rewrite IHt catA.
  Qed.

  Lemma cons_head_behead x s : (s != [::]) -> head x s :: behead s = s.
  Proof. by case s. Qed.

  Lemma belast_behead_rcons x l s :
    belast (head x (rcons s l)) (behead (rcons s l)) = s.
  Proof. case: s => [//= | s0 s]; by rewrite rcons_cons /= belast_rcons. Qed.

  Lemma last_behead_rcons x l s :
    last (head x (rcons s l)) (behead (rcons s l)) = l.
  Proof. case: s => [//= | s0 s]; by rewrite rcons_cons /= last_rcons. Qed.

  Lemma head_any s a b : s != [::] -> head a s = head b s.
  Proof. by elim: s. Qed.

  Lemma nth_any s a b i : i < size s -> nth a s i = nth b s i.
  Proof. elim: s i => //= s0 s IHs [//=|i] Hsize /=. by apply: IHs. Qed.

  Lemma rcons_set_nth a s l : set_nth a s (size s) l = rcons s l.
  Proof. elim: s => [//=| l0 s IHs]. by rewrite rcons_cons -IHs /=. Qed.

  Lemma set_nth_non_nil d s n y : set_nth d s n y != [::].
  Proof. elim: s => [|s0 s]; by case n. Qed.

  Lemma set_nth_rcons x0 s x n y :
    set_nth x0 (rcons s x) n y =
    if n < size s then rcons (set_nth x0 s n y) x
    else if n == size s then rcons s y else (rcons s x) ++ ncons (n - size s).-1 x0 [:: y].
  Proof.
    elim: s n => [//= | s0 s IHs] n.
    + case eqP => [-> //= |]; by case: n => [| []].
    + rewrite rcons_cons /=; case: n => [//= | n] /=.
      have {IHs} := (IHs n). rewrite eqSS -[n.+1 < (size s).+1]/(n < (size s)).
      by case (ltngtP n (size s)) => _ <-.
  Qed.

  Lemma rconsK a u v : rcons u a = rcons v a -> u = v.
  Proof.
    elim: u v => [| u0 u IHu]; case=> [|v0 v] //= [].
    + move=> _; by case v.
    + move=> _; by case u.
    + by move=> -> /IHu ->.
  Qed.

  Lemma nth_set_nth_expand a b l i c j :
    (size l <= j < i) -> nth a (set_nth b l i c) j = b.
  Proof.
    elim: l i j => [/= | l0 l IHl].
    - elim => [//= | i' Hi] /=.
      case => [//= | j /=]; by rewrite nth_ncons /leq subSS => ->.
    - elim => [//= | i' Hi] j /=; first by rewrite ltn0 andbF.
      case: j Hi => [//= | j /=] Hi /andP [] H1 H2.
      apply: IHl; by move: H1 H2; rewrite !/leq !subSS => -> ->.
  Qed.

  Lemma nth_set_nth_any a b l i c j :
    nth a (set_nth b l i c) j =
    if j == i then c else
      if j < size l then nth a l j else
        if j <= i then b else a.
  Proof.
    case eqP => [<- | /eqP Hneq].
    - have Hj : j < size (set_nth b l j c) by rewrite size_set_nth; apply: leq_maxl.
      by rewrite (nth_any a b Hj) nth_set_nth /= eq_refl.
    - case (ltnP j (size l)) => Hjsz.
      + have Hj : j < size (set_nth b l i c)
          by rewrite size_set_nth; apply: (leq_trans Hjsz); apply: leq_maxr.
        by rewrite (nth_any a b Hj) nth_set_nth /= (negbTE Hneq) (nth_any a b Hjsz).
      + case (leqP j i) => Hij.
        * apply: nth_set_nth_expand; by rewrite Hjsz /= ltn_neqAle Hneq Hij.
        * rewrite nth_default; first by [].
          rewrite size_set_nth /maxn; by case (ltnP i.+1 (size l)).
  Qed.

  Lemma cons_in_map_cons a b s w :
    forall l : seq (seq T), a :: s \in [seq b :: s1 | s1 <- l] -> a == b.
  Proof.
    elim=> [//=| l0 l H]; rewrite map_cons in_cons; move/orP => []; last by exact H.
    by move=> /eqP [] ->.
  Qed.

  Lemma count_flatten (s : seq (seq T)) P :
    count P (flatten s) = sumn [seq count P x | x <- s].
  Proof. elim: s => [//= | s0 s IHs /=]. by rewrite count_cat IHs. Qed.

  Lemma rcons_nilF s l : ((rcons s l) == [::]) = false.
  Proof. case eqP=>//= H; have:= eq_refl (size (rcons s l)). by rewrite {2}H size_rcons. Qed.

  Lemma count_mem_rcons w l i : count_mem i (rcons w l) = count_mem i w + (l == i).
  Proof. by rewrite -count_rev rev_rcons /= count_rev addnC. Qed.

  Lemma sumn_count s P :
    sumn [seq nat_of_bool (P i) | i <- s] = count P s.
  Proof. by elim: s => //= s0 s /= ->. Qed.

End RCons.

Lemma map_flatten (T1 T2 : eqType) (f : T1 -> T2) s :
  map f (flatten s) = flatten (map (map f) s).
Proof. elim: s => [//= | s0 s /= <-]; by apply map_cat. Qed.

Lemma filter_flatten (T : eqType) (s : seq (seq T)) (P : pred T) :
  filter P (flatten s) = flatten [seq filter P i | i <- s].
Proof. elim: s => [//= | s0 s /= <-]; exact: filter_cat. Qed.

Lemma sumn_flatten s :
  sumn (flatten s) = sumn (map sumn s).
Proof. elim: s => [//= | s0 s /= <-]; by apply sumn_cat. Qed.

Lemma sumn_rev s : sumn (rev s) = sumn s.
Proof.
  elim: s => [//= | s0 s /= <-].
  by rewrite rev_cons -cats1 sumn_cat /= addn0 addnC.
Qed.

Lemma nth_shape T (s : seq (seq T)) i : nth 0 (shape s) i = size (nth [::] s i).
Proof.
  rewrite /shape; case: (ltnP i (size s)) => Hi; first exact: nth_map.
  by rewrite !nth_default // size_map.
Qed.

Lemma shape_rev T (s : seq (seq T)) : shape (rev s) = rev (shape s).
Proof. rewrite /shape; elim: s => [//= | s0 s IHs] /=; by rewrite map_rev. Qed.

Lemma eq_from_flatten_shape (T : eqType) (u v : seq (seq T)) :
  (u = v) <-> ((flatten u = flatten v) /\ (shape u = shape v)).
Proof.
  split; first by move ->.
  move=> [] Hflat Hshape.
  by rewrite -(flattenK u) -(flattenK v) Hflat Hshape.
Qed.

Lemma sumn_iota a b x :
  a <= x < a + b -> sumn [seq ((i == x) : nat) | i <- iota a b] = 1.
Proof.
  elim: b a => [/=| b IHb] a.
    rewrite addn0 => /andP [] /leq_ltn_trans H/H{H}.
    by rewrite ltnn.
  have:= IHb a.+1 => /= {IHb} IHb.
  case (ltnP a x) => H1 /andP [] H2 H3.
  + rewrite IHb; first by rewrite (ltn_eqF H1).
    by rewrite H1 addSnnS.
  + rewrite eqn_leq H1 H2 /= {H2 H3 IHb}.
    apply/eqP; rewrite eqSS; apply/eqP.
    elim: b a H1 => [//= | b IHb] a Ha /=.
    rewrite IHb; first by rewrite gtn_eqF; last by rewrite ltnS.
    by rewrite leqW.
Qed.

Lemma sumn_map_condE (T : Type) (s : seq T) (f : T -> nat) (P : pred T) :
  \sum_(i <- s | P i) f i = sumn [seq f i | i <- s & P i].
Proof.
  elim: s => [//= | s0 s IHs] /=; first by rewrite big_nil.
  rewrite big_cons IHs.
  by case: (P s0).
Qed.

Lemma sumn_mapE (T : Type) (s : seq T) (f : T -> nat) :
  \sum_(i <- s) f i = sumn [seq f i | i <- s].
Proof. by rewrite sumn_map_condE filter_predT. Qed.

Lemma sumnE s : \sum_(i <- s) i = sumn s.
Proof. by rewrite sumn_mapE map_id. Qed.

Lemma perm_sumn l1 l2 : perm_eq l1 l2 -> sumn l1 = sumn l2.
Proof. rewrite -!sumnE; by apply eq_big_perm. Qed.

Lemma sumn_take r s : sumn (take r s) = \sum_(0 <= i < r) nth 0 s i.
Proof.
  elim: r s => [|r IHr] s /=.
    by rewrite take0 /index_iota /= big_nil.
  case: s => [| s0 s] /=.
    rewrite {IHr} (eq_bigr (fun _ => 0)) //.
    rewrite big_const_nat subn0.
    by elim: r.
  rewrite IHr /index_iota !subn0 /= big_cons /=.
  congr (_ + _); rewrite -add1n iota_addl big_map.
  exact: eq_bigr.
Qed.

Lemma sum_iota_sumnE l n :
  size l <= n -> \sum_(0 <= i < n) nth 0 l i = sumn l.
Proof. by rewrite -sumn_take => /take_oversize ->. Qed.

Lemma take_rev (T : eqType) (l : seq T) i : take i (rev l) = rev (drop (size l - i) l).
Proof.
  elim: i l => [| i IHi] l.
    by rewrite take0 subn0 drop_size.
  case/lastP: l => [//= | l' ln].
  rewrite rev_rcons /= IHi -rev_rcons.
  congr (rev _).
  rewrite size_rcons subSS.
  rewrite -(cats1 l') drop_cat.
  case: ltnP; first by rewrite cats1.
  move=> /drop_oversize -> /=.
  suff -> : size l' - i - size l' = 0 by [].
  by rewrite subnAC subnn sub0n.
Qed.

Lemma drop_rev (T : eqType) (l : seq T) i : drop i (rev l) = rev (take (size l - i) l).
Proof.
  elim: i l => [| i IHi] l.
    by rewrite drop0 subn0 take_size.
  case/lastP: l => [//= | l' ln].
  rewrite rev_rcons /= IHi; congr (rev _).
  rewrite size_rcons subSS -cats1 take_cat.
  case: ltnP => //= /take_oversize ->.
  suff -> : size l' - i - size l' = 0 by rewrite cats0.
  by rewrite subnAC subnn sub0n.
Qed.

Lemma drop_drop (T : eqType) (s : seq T) n1 n2 :
  drop n1 (drop n2 s) = drop (n1 + n2) s.
Proof.
  elim: s n1 n2 => [| s0 s IHs] //=.
  case=> [//= | n1] n2; first by rewrite drop0 add0n.
  rewrite addSn; case: n2 => [//=| n2]; first by rewrite addn0.
  by rewrite -addSnnS.
Qed.

Lemma rev_flatten (T : eqType) (l : seq (seq T)) :
  rev (flatten l) = flatten (rev (map rev l)).
Proof.
  elim: l => [| l0 l IHl] //=.
  by rewrite rev_cons flatten_rcons -IHl rev_cat.
Qed.

Lemma rev_reshape (T : eqType) s (l : seq T) :
  size l = sumn s -> rev (map rev (reshape (rev s) (rev l))) = reshape s l.
Proof.
  move=> H; apply eq_from_flatten_shape; split.
  - rewrite reshapeKr; last by rewrite H.
    rewrite -rev_flatten reshapeKr; first by rewrite revK.
    by rewrite size_rev H sumn_rev.
  - rewrite shape_rev /shape -map_comp.
    rewrite (eq_map (f2 := size)); last by move=> v; rewrite /= size_rev.
    rewrite -/(shape _) reshapeKl; last by rewrite size_rev sumn_rev H.
    rewrite -/(shape _) reshapeKl; last by rewrite H.
    by rewrite revK.
Qed.

Lemma nth_reshape (T : eqType) s (l : seq T) n :
  nth [::] (reshape s l) n = take (nth 0 s n) (drop (sumn (take n s)) l).
Proof.
  elim: n s l => [| n IHn] [| s0 s] l; rewrite ?take0 ?drop0 //=.
  rewrite addnC -drop_drop; exact: IHn.
Qed.

Lemma map_reshape (T1 T2 : Type) (f : T1 -> T2) sh (s : seq T1) :
  map (map f) (reshape sh s) = reshape sh (map f s).
Proof. elim: sh s => [//= | sh0 sh IHsh] /= s;  by rewrite map_take IHsh map_drop. Qed.

Lemma size_reshape (T : Type) sh (s : seq T) : size (reshape sh s) = size sh.
Proof. elim: sh s => [//= | s0 sh IHsh] /= s; by rewrite IHsh. Qed.

Lemma reshape_rcons (T : Type) (s : seq T) sh sn :
  sumn sh + sn = size s ->
  reshape (rcons sh sn) s = rcons (reshape sh (take (sumn sh) s)) (drop (sumn sh) s).
Proof.
  elim: sh s => [//= | s0 sh IHsh] /= s.
    rewrite add0n => Hsz.
    by rewrite drop0 take_oversize; last by rewrite Hsz.
  move=> Hsize.
  have Hs0 : (if s0 < size s then s0 else size s) = s0.
    by rewrite bad_if_leq; last by rewrite -Hsize -addnA; apply leq_addr.
  have -> : take (s0 + sumn sh) s = take s0 s ++ take (sumn sh) (drop s0 s).
    rewrite -{1 3}[s](cat_take_drop s0) drop_cat take_cat size_take.
    by rewrite Hs0 ltnNge leq_addr /= addKn ltnn subnn drop0.
  rewrite take_cat size_take Hs0 ltnn subnn take0 cats0.
  rewrite drop_cat size_take Hs0 ltnn subnn drop0.
  have -> : drop (s0 + sumn sh) s = drop (sumn sh) (drop s0 s).
    rewrite -[s](cat_take_drop s0) !drop_cat size_take.
    by rewrite Hs0 ltnNge leq_addr /= addKn ltnn subnn drop0.
  by rewrite -IHsh; last by rewrite size_drop -Hsize -addnA addKn.
Qed.


Fixpoint reshape_coord sh i :=
  if sh is s0 :: s then
    if i < s0 then (0, i)
    else let (r, c) := reshape_coord s (i - s0) in (r.+1, c)
  else (0, i).

Definition flatten_coord sh r c := (\sum_(0 <= j < r) nth 0 sh j) + c.

Lemma flatten_coordP sh r c :
  c < nth 0 sh r -> flatten_coord sh r c < sumn sh.
Proof.
  case: (ltnP r (size sh)) => Hr; last by rewrite (nth_default _ Hr).
  rewrite -(sum_iota_sumnE (n := size sh)) // => Hc.
  rewrite (big_cat_nat _ _ _ _ (ltnW Hr)) //= ltn_add2l.
  rewrite (big_ltn Hr); exact: ltn_addr.
Qed.

Lemma reshape_coordP sh i :
  i < sumn sh -> let (r, c) := (reshape_coord sh i) in r < size sh /\ c < nth 0 sh r.
Proof.
  elim: sh i => [| s0 s IHs] i //= Hi.
  case: (ltnP i s0) => His0 //=.
  have {IHs} := IHs (i - s0); case: (reshape_coord s (i - s0)) => r c /=.
  rewrite ltnS; apply.
  by rewrite -(subSn His0) leq_subLR.
Qed.

Lemma reshape_coordK sh i :
  let (r, c) := reshape_coord sh i in flatten_coord sh r c = i.
Proof.
  rewrite /flatten_coord.
  elim: sh i => [| s0 s IHs] i //=; first by rewrite /index_iota /= big_nil.
  case: (ltnP i s0) => His0 //=; first by rewrite /index_iota /= big_nil.
  have {IHs} := IHs (i - s0); case: (reshape_coord s (i - s0)) => r c.
  rewrite big_nat_recl //= -addnA => ->.
  exact: subnKC.
Qed.

Lemma flatten_coordK sh r c :
  c < nth 0 sh r -> reshape_coord sh (flatten_coord sh r c) = (r, c).
Proof.
  rewrite /flatten_coord.
  elim: r c sh => [| r IHr] /= c [//= | s0 s] /=.
    by rewrite /index_iota subn0 /= big_nil add0n => ->.
  have -> : \sum_(0 <= j < r.+1) nth 0 (s0 :: s) j = s0 + \sum_(0 <= j < r) nth 0 s j.
    by rewrite big_nat_recl //=.
  rewrite [X in if X then _ else _]ltnNge -addnA leq_addr /=.
  by rewrite addKn => /IHr ->.
Qed.

Lemma iota_ltn a b : b <= a -> [seq i <- iota 0 a | i < b] = iota 0 b.
Proof.
  move=> Hab.
  rewrite -(subnKC Hab) iota_add add0n filter_cat.
  rewrite -[RHS]cats0; congr (_ ++ _).
  - rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
    move=> i /=; by rewrite mem_iota add0n => /andP [] _ ->.
  - rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 //.
    move=> i /=. rewrite mem_iota (subnKC Hab) => /andP [].
    by rewrite leqNgt => /negbTE.
Qed.

Lemma iota_geq a b : [seq i <- iota 0 a | b <= i] = iota b (a - b).
Proof.
  elim: a => [//=| n IHn].
  rewrite -addn1 iota_add add0n /= filter_cat IHn {IHn} /=.
  case: leqP => Hb.
  - by rewrite addn1 (subSn Hb) -addn1 iota_add /= subnKC.
  - rewrite addn1 cats0.
    have := Hb; rewrite /leq => /eqP ->.
    by have := ltnW Hb; rewrite /leq => /eqP ->.
Qed.

Lemma nth_flatten T (x : T) tab i :
  nth x (flatten tab) i = let (r, c) := (reshape_coord (shape tab) i) in
                          nth x (nth [::] tab r) c.
Proof.
  elim: tab i => [| t0 t IHt] //= i.
  rewrite nth_cat; case: ltnP => //= Hi.
  rewrite IHt {IHt}; by case: (reshape_coord (shape t) (i - size t0)) => r c.
Qed.

Section BigInterv.

Variable R : Type.
Variable idx : R.
Variable op : Monoid.law idx.

Lemma big_nat_widen0 a b c F :
  b <= c -> \big[op/idx]_(a <= i < b) F i = \big[op/idx]_(0 <= i < c | a <= i < b) F i.
Proof.
  move=> Hbc.
  rewrite {1}/index_iota -iota_geq -{1}(subn0 b) big_filter -/(index_iota 0 b).
  by rewrite (big_nat_widen _ _ _ _ _ Hbc).
Qed.

End BigInterv.

Lemma sum_nth_rev s a b :
   \sum_(a <= i < b) nth 0 (rev s) i = \sum_(size s - b <= i < size s - a) nth 0 s i.
Proof.
  have sum0 u v : size s <= u -> \sum_(u <= i < v) nth 0 (rev s) i = 0.
    move=> Hu; rewrite big_seq_cond [LHS](eq_bigr (fun i => 0)); first last.
      move=> i; rewrite mem_iota => /andP [] /andP [] Hai _ _.
      rewrite nth_default // size_rev; exact: leq_trans Hu Hai.
    by rewrite -big_seq_cond -/(index_iota _ _) /= sum_nat_const_nat muln0.
  wlog Hbs: b / b <= (size s).
    move=> Hwlog; case: (leqP b (size s)) => [| /ltnW Hbs]; first exact: Hwlog.
    have:= Hwlog (size s) (leqnn (size s)).
    have:= Hbs; rewrite subnn {1}/leq => /eqP -> <-.
    case: (ltnP a (size s)) => Has.
    - by rewrite (big_cat_nat _ _ _ (ltnW Has) Hbs) /= (sum0 _ _ (leqnn (size s))) addn0.
    - rewrite {2}/index_iota; have:= Has; rewrite /leq => /eqP -> /=.
      by rewrite (sum0 _ _ Has) big_nil.
  case: (ltnP a b) => Hab; first last.
  - rewrite /index_iota; have:= Hab; rewrite /leq => /eqP -> /=.
    have := leq_sub2l (size s) Hab; rewrite /leq => /eqP -> /=.
    by rewrite !big_nil.
  - rewrite (big_nat_widen0 _ _ _ Hbs) big_nat_rev /= add0n.
    rewrite big_seq_cond [LHS](eq_bigr (fun i => nth 0 s i)); first last.
      move=> i /and3P []; rewrite mem_iota add0n subn0 => /andP [] _ Hi Hi1 Hi2.
      rewrite nth_rev; last exact (leq_trans Hi2 Hbs).
      congr nth; by rewrite subnS subKn.
    rewrite (eq_bigl (fun i => size s - b <= i < size s - a)); first last.
      move=> i /=; rewrite mem_iota add0n subn0 leq0n /=.
        rewrite leq_subLR addnC -leq_subLR ltn_subRL addnC -ltn_subRL [RHS]andbC.
        case: (size s) => [//= | n]; rewrite subSS ltnS.
        case: (leqP i n) => [Hn | /=]; first by rewrite (subSn Hn) ltnS.
        rewrite {1}/leq => /eqP ->.
        by rewrite ltn0.
    rewrite -big_nat_widen0 //; exact: leq_subr.
Qed.

Lemma incr_nth_inj sh : injective (incr_nth sh).
Proof.
  move=> i j Hsh.
  case (altP (i =P j)) => [//= | /negbTE Hdiff].
  have:= eq_refl (nth 0 (incr_nth sh i) j).
  by rewrite {2}Hsh !nth_incr_nth eq_refl Hdiff eqn_add2r.
Qed.

Lemma incr_nthC (s : seq nat) i j :
  incr_nth (incr_nth s i) j = incr_nth (incr_nth s j) i.
Proof.
  apply (eq_from_nth (x0 := 0)).
  - rewrite !size_incr_nth.
    case (ltnP i (size s)) => Hi.
    + case (ltnP j (size s)) => Hj; first by rewrite Hi.
      by rewrite ltnS (ltnW (leq_trans Hi Hj)).
    + case (ltnP j (size s)) => Hj.
      * by rewrite ltnS (ltnW (leq_trans Hj Hi)) ltnNge Hi.
      * rewrite !ltnS; case: (ltngtP i j) => Hij; last by rewrite Hij.
        - by rewrite (ltnW Hij) leqNgt Hij.
        - by rewrite (ltnW Hij) leqNgt Hij.
  - move=> k Hk; by rewrite !nth_incr_nth !addnA [(_ == _) + _]addnC.
Qed.

Lemma filter_perm_eq (T : eqType) (u v : seq T) P :
  perm_eq u v -> perm_eq (filter P u) (filter P v).
Proof.
  move=> /perm_eqP Hcount.
  apply/perm_eqP => Q; rewrite !count_filter.
  by apply Hcount.
Qed.

Lemma all_perm_eq (T : eqType) (u v : seq T) P : perm_eq u v -> all P u -> all P v.
Proof.
  move=> /perm_eq_mem Hperm /allP Hall; apply/allP => x.
  by rewrite -Hperm => /Hall.
Qed.

Lemma flatten_seq1 (T : eqType) (s : seq T) : flatten [seq [:: x] | x <- s] = s.
Proof. by elim: s => [//= | s0 s /= ->]. Qed.
