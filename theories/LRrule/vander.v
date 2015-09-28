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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun tuple bigop ssralg ssrint.
Require Import fingroup perm zmodp binomial poly matrix.
Require Import ssrcomplements poset freeg mpoly.
Require Import tools ordtype sorted partition skewtab Schur therule.
Require Import sym_group antisym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Definition intpartn_cast m n (eq_mn : m = n) p :=
  let: erefl in _ = n := eq_mn return intpartn n in p.

Lemma intpartn_castE m n (eq_mn : m = n) p : val (intpartn_cast eq_mn p) = val p.
Proof. subst m; by case: p. Qed.



Section Alternant.

Variable n : nat.
Variable R : comRingType.


Definition alternpol f : {mpoly R[n]} := \sum_(s : 'S_n) (-1) ^+ s *: msym s f.
Definition rho := [multinom (n - 1 - i)%N | i < n].
Definition mpart (s : seq nat) := [multinom (nth 0 s i)%N | i < n].


Local Notation "''e_' k" := (@mesym _ _ k) (at level 8, k at level 2, format "''e_' k").
Local Notation "''a_' k" := (alternpol 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Lemma alt_anti m : 'a_m \is antisym.
Proof.
  apply/isantisymP => S.
  rewrite /alternpol.
  rewrite (big_morph (msym S) (@msymD _ _ _) (@msym0 _ _ _)).
  rewrite scaler_sumr.
  rewrite [RHS](reindex_inj (mulIg S)); apply: eq_big => //= s _.
  rewrite msymZ -msymMm scalerA; congr (_ *: _).
  by rewrite odd_permM signr_addb [X in (_  = _ * X)]mulrC signrMK.
Qed.

Lemma rho_iota : rho = rev (iota 0 n) :> seq nat.
Proof.
  apply (eq_from_nth (x0 := 0%N)).
    by rewrite size_tuple size_rev size_iota.
  move=> i; rewrite size_tuple => Hi.
  rewrite /= nth_rev size_iota //.
  rewrite (eq_map (f2 := (fun i => (n - 1 - i)%N) \o (@val _ _ _))) //.
  rewrite map_comp val_enum_ord (nth_map 0%N); last by rewrite size_iota.
  rewrite !nth_iota //.
    rewrite ?add0n subn1; by case: n Hi.
  case: n Hi => [// | m] _.
  rewrite subSS ltnS; exact: leq_subr.
Qed.

Lemma rho_uniq : uniq rho.
Proof.
  suff : perm_eq rho (iota 0 n).
    move/perm_eq_uniq ->; exact: iota_uniq.
  rewrite rho_iota perm_eq_sym.
  exact: perm_eq_rev.
Qed.

Lemma alt_uniq_non0 (m : 'X_{1..n}) : uniq m -> 'a_m != 0.
Proof.
  move=> Huniq.
  suff : mcoeff m 'a_m == 1.
    apply contraL => /eqP ->; rewrite mcoeff0 eq_sym.
    exact: oner_neq0.
  rewrite /alternpol (reindex_inj invg_inj) /=.
  rewrite raddf_sum /= (bigID (pred1 1%g)) /=.
  rewrite big_pred1_eq odd_permV odd_perm1 expr0 scale1r invg1 msym1m.
  rewrite mcoeffX eq_refl /=.
  rewrite (eq_bigr (fun _ => 0)); first by rewrite big1_eq addr0.
  move=> s Hs; rewrite mcoeffZ msymX mcoeffX invgK.
  suff : [multinom m (s i) | i < n] != m.
    move=> /negbTE -> /=; by rewrite mulr0.
  move: Hs; apply contra => /eqP; rewrite mnmP => Heq.
  apply/eqP; rewrite -permP => i; rewrite perm1; apply val_inj => /=.
  have /eqP := Heq i; rewrite !mnmE !(mnm_nth 0%N).
  rewrite nth_uniq; last exact: Huniq.
  - by move=> /eqP ->.
  - rewrite size_tuple; exact: ltn_ord.
  - rewrite size_tuple; exact: ltn_ord.
Qed.

Lemma altrho_non0 : 'a_rho != 0.
Proof. exact: alt_uniq_non0 (rho_uniq). Qed.

Lemma alterpol_alternate (m : 'X_{1..n}) (i j : 'I_n) :
  i != j -> m i = m j -> 'a_m = 0.
Proof.
  move=> H Heq.
  pose t := tperm i j.
  have oddMt s: (t * s)%g = ~~ s :> bool by rewrite odd_permM odd_tperm H.
  rewrite [alternpol _](bigID (@odd_perm _)) /=.
  apply: canLR (subrK _) _; rewrite add0r -sumrN.
  rewrite (reindex_inj (mulgI t)); apply: eq_big => //= s.
  rewrite oddMt => /negPf ->; rewrite scaleN1r scale1r; congr (- _).
  rewrite msymMm.
  suff -> : msym t 'X_[m] = ('X_[m] : {mpoly R[n]}) by [].
  rewrite msymX; congr mpolyX.
  rewrite mnmP => k /=.
  rewrite !mnmE /= tpermV.
  case: (tpermP i j k) => Hk //; by rewrite Hk Heq.
Qed.

Lemma alt_add1_0 (m : 'X_{1..n}) i :
  (nth 0%N m i).+1 = nth 0%N m i.+1 -> 'a_(m + rho) = 0.
Proof.
  move=> Heq.
  have Hi1n : i.+1 < n.
    rewrite ltnNge; apply (introN idP) => Hi.
    move: Heq; by rewrite [RHS]nth_default // size_tuple.
  have Hi : i < n by rewrite ltnW.
  pose i0 := Ordinal Hi; pose i1 := Ordinal Hi1n.
  have /alterpol_alternate : i0 != i1.
    apply (introN idP) => /eqP H.
    have := erefl (val i0); rewrite {2}H /= => /eqP.
    by rewrite ieqi1F.
  apply.
  rewrite !mnmDE !mnmE !(mnm_nth 0%N) -Heq -(mnm_nth 0%N m i0).
  rewrite addSn -addnS subn1 /= subnS prednK //.
  have -> : (n.-1 - i = n - i.+1)%N.
    case: n Hi1n Hi {i0 i1} => [//= | n' _] /=.
    by rewrite subSS.
  by rewrite subn_gt0.
Qed.


Lemma alt_elementary (m : 'X_{1..n}) k :
  'a_(m + rho) * 'e_k = \sum_(h : {set 'I_n} | #|h| == k) 'a_(m + mesym1 h + rho).
Proof.
  rewrite /alternpol exchange_big /=.
  rewrite mulr_suml; apply eq_bigr => s _.
  rewrite -(issymP _ (mesym_sym n R k) s) mesymE.
  rewrite (raddf_sum (msym_additive _ _)) /=.
  rewrite mulr_sumr; apply eq_bigr => h _.
  rewrite -scalerAl -msymM -mpolyXD.
  by rewrite -!addmA [(mesym1 h + rho)%MM]addmC.
Qed.



Local Open Scope nat_scope.

Section HasIncr.

Variables (d k : nat) (P1 : intpartn d) (h : {set 'I_n}).

Definition hasincr :=
  has (fun i => (nth 0 (mpart P1 + mesym1 h)%MM i).+1 ==
                 nth 0 (mpart P1 + mesym1 h)%MM i.+1) (iota 0 n.-1).

Lemma hasincr0 : hasincr -> 'a_(mpart P1 + mesym1 h + rho) = 0%R.
Proof. move=> /hasP [] i _ /eqP; exact: alt_add1_0. Qed.

Fixpoint rem_trail0 s :=
  if s is s0 :: s' then
    if (rem_trail0 s') is t1 :: t' then s0 :: t1 :: t'
    else if s0 == 0 then [::] else [:: s0]
  else [::].

Lemma size_rem_trail0 s : size (rem_trail0 s) <= size s.
Proof.
  elim: s => [//= | s0 s]/=.
  case: (rem_trail0 s) => [/= _ | //=].
  by case: eqP.
Qed.

Lemma nth_rem_trail0 s i : nth 0 (rem_trail0 s) i = nth 0 s i.
Proof.
  elim: s i => [//= | s0 s]/=.
  case: (rem_trail0 s) => [/= | t1 t'] IHs i.
  - case (altP (s0 =P 0)) => [-> |_].
    * by case: i => [//= | i]; first by rewrite /= -IHs.
    * case: i => [//= | i] /=; exact: IHs.
  - case: i => [//= | i] /=; exact: IHs.
Qed.

Lemma sumn_rem_trail0 s : sumn (rem_trail0 s) = sumn s.
Proof.
  elim: s => [//= | s0 s] /=.
  case: (rem_trail0 s) => [/= <- | t1 t' <- //=].
  case: (altP (s0 =P 0%N)) => [-> | _] /=; by rewrite ?addn0.
Qed.

Lemma is_part_rem_trail0 s : sorted geq s -> is_part (rem_trail0 s).
Proof.
  case: s => [//= | s0 s]; rewrite [sorted _ _]/=.
  elim: s s0 => [| s1 s IHs] s0 /=; first by case: s0.
  move=> /andP [] H01 /IHs /=.
  case: (rem_trail0 s) => [_ | t0 t] /=; last by rewrite H01.
  case: (altP (s1 =P 0)) => [_ | Hs1].
  - case (altP (s0 =P 0)) => [// | Hs0] /=.
    by rewrite lt0n Hs0.
  - by rewrite /= H01 lt0n Hs1.
Qed.

Lemma not_hasincr_part :
  size P1 <= n -> ~~ hasincr ->
  is_part_of_n (d + #|h|) (rem_trail0 ((mpart P1) + mesym1 h)%MM).
Proof.
  move=> Hsz /hasPn H.
  rewrite /mpart.
  apply/andP; split.
  - rewrite sumn_rem_trail0.
    rewrite -(@sum_iota_sumnE _ n); last by rewrite size_map size_enum_ord.
    rewrite big_mkord.
    rewrite (eq_bigr (fun i : 'I_n => nth 0 P1 i + (mesym1 h) i)%N); first last.
      move=> i _.
      have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      rewrite nth_ord_enum /= (mnm_nth 0) /=.
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      by rewrite nth_ord_enum.
    rewrite big_split /=; apply/eqP; congr (_ + _)%N.
    + rewrite -{2}(intpartn_sumn P1).
      by rewrite -(sum_iota_sumnE Hsz) big_mkord.
    + rewrite -mdeg_mesym1 /mdeg.
      rewrite -map_tnth_enum big_map /index_enum enumT.
      apply eq_bigr => i _.
      by rewrite mnm_tnth.
  - apply is_part_rem_trail0.
    apply/(sorted1P 0) => i.
    rewrite size_map size_enum_ord => Hi1.
    have Hi : i < n by exact: (ltn_trans _ Hi1).
    have {H} /H : i \in iota 0 n.-1.
      rewrite mem_iota add0n.
      by case: n Hi1 {Hsz H Hi} => [//= | n'] /=; rewrite ltnS.
    rewrite /mpart.
    have H0 : 0 < n by apply: (leq_ltn_trans _ Hi1).
    rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
    rewrite !nth_enum_ord //.
    set bi := (_ \in h); set bi1 := (_ \in h).
    have:= is_partP _ (intpartnP P1) => [] [] _ H.
    have {H} := H i; move: (i.+1) => j /= H1.
    case: bi bi1 => [] [] /=; rewrite ?addn1 ?addn0 => H2.
    - by rewrite ltnS.
    - exact: (leq_trans H1).
    - by rewrite ltn_neqAle -eqSS eq_sym H2 H1.
    - exact: H1.
Qed.

Let add_mpart_mesym :=
  if [&& size P1 <= n, #|h| == k & ~~ hasincr] then (rem_trail0 ((mpart P1) + mesym1 h)%MM)
  else rowpart (d + k) (* unused *).
Lemma add_mpart_mesymP : is_part_of_n (d + k) add_mpart_mesym.
Proof.
  rewrite /add_mpart_mesym.
  case: (boolP [&& _, _ & _]) => [/and3P [] H1 /eqP <- H3| _].
  + exact: not_hasincr_part.
  + exact: rowpartnP.
Qed.
Definition add_mesym : intpartn (d + k) := IntPartN add_mpart_mesymP.

Lemma add_mesymE :
  size P1 <= n -> #|h| == k -> ~~ hasincr ->
  mpart add_mesym = (mpart P1 + mesym1 h)%MM.
Proof.
  rewrite /add_mesym /add_mpart_mesym => Hsz /= /eqP <- Hincr.
  rewrite /mpart Hincr Hsz eq_refl /=.
  set S := (map _ _).
  rewrite mnmP => i.
  rewrite mnmE nth_rem_trail0.
  have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
  rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
  by rewrite !nth_ord_enum.
Qed.

End HasIncr.

Definition setdiff (P1 P : seq nat) : {set 'I_n} :=
  [set i : 'I_n | nth 0%N P1 i < nth 0%N P i].

Lemma card_setdiff d k (P1 : intpartn d) (P : intpartn (d + k)) :
  size P <= n -> size P1 <= n -> vb_strip P1 P -> #|setdiff P1 P| = k.
Proof.
  move=> Hsz Hsz1 /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip.
  rewrite /setdiff -sum1dep_card.
  rewrite -{2}(addKn d k).
  rewrite -{4}(intpartn_sumn P1) -{2}(intpartn_sumn P).
  rewrite -(sum_iota_sumnE Hsz) -(sum_iota_sumnE Hsz1).
  set rhs := RHS.
  have {rhs} -> : rhs = (\sum_(0 <= i < n) (nth 0 P i - nth 0 P1 i)).
    rewrite /rhs {rhs} /index_iota subn0.
    elim: n {Hsz Hsz1} => [//= | i IHi]; first by rewrite !big_nil.
    rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
    rewrite subnDA subnAC -addnBA; last by have := Hstrip i => /andP [].
    rewrite addnC [RHS]addnC -IHi {IHi}.
    rewrite addnBA //.
    elim: i => [//= | i IHi]; first by rewrite !big_nil.
    rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
    apply leq_add; first exact: IHi.
    by have := Hstrip i => /andP [].
  rewrite big_mkord.
  rewrite [RHS](bigID (fun i : 'I_n => nth 0 P1 i < nth 0 P i)) /=.
  rewrite [X in (_ = _ + X)]big1 ?addn0; first last.
    move=> i; by rewrite -leqNgt /leq => /eqP.
  apply eq_bigr => i H.
  have:= Hstrip i => /andP [] H1 H2.
  suff -> : nth 0 P i = (nth 0 P1 i).+1 by rewrite subSn // subnn.
  apply anti_leq; by rewrite H2 H.
Qed.

Lemma nth_add_setdiff d k (P1 : intpartn d) (P : intpartn (d + k)) :
  size P <= n -> size P1 <= n -> vb_strip P1 P ->
  forall i,
  nth 0 [seq (mpart P1) i0 + (mesym1 (setdiff P1 P)) i0 | i0 <- enum 'I_n] i =
  nth 0 P i.
Proof.
  move=> Hsz Hsz1 /(vb_stripP (intpartnP _) (intpartnP _)) Hstr i.
  case: (ssrnat.ltnP i n) => Hi; first last.
    rewrite !nth_default //.
    - exact: leq_trans Hsz Hi.
    - by rewrite size_map size_enum_ord.
  have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
  rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
  rewrite inE /mpart /= (nth_enum_ord (Ordinal H0) Hi).
  case: ssrnat.ltnP => H /=; rewrite ?addn0 ?addn1.
  - apply anti_leq; rewrite H /=.
    by have := Hstr i => /andP [].
  - apply anti_leq; rewrite H /= andbT.
    by have := Hstr i => /andP [].
Qed.

Lemma nohasincr_setdiff d k (P1 : intpartn d) (P : intpartn (d + k)) :
  size P <= n -> size P1 <= n -> vb_strip P1 P -> ~~ hasincr P1 (setdiff P1 P).
Proof.
  move=> Hsz Hsz1 Hstrip.
  apply/hasPn => i; rewrite mem_iota add0n => /andP [] _ Hi.
  rewrite /mnm_add [val _]/= !nth_add_setdiff //.
  rewrite eq_sym ltn_eqF // ltnS.
  have := (is_partP _ (intpartnP P)) => [] [] _.
  by apply.
Qed.

Lemma add_mesymK d k (P1 : intpartn d) :
  size P1 <= n ->
  {in [pred P : intpartn (d + k) | vb_strip P1 P && (size P <= n)],
  cancel (fun P : intpartn (d + k) => setdiff P1 (val P)) (add_mesym k P1)}.
Proof.
  move=> Hsz1 P /=; rewrite inE => /andP [] Hstrip Hsz.
  have:= (vb_stripP (intpartnP _) (intpartnP _) Hstrip) => Hstr.
  apply/eqP/(part_eqP (intpartnP _) (intpartnP _)) => i.
  rewrite /add_mesym /=.
  rewrite Hsz1 card_setdiff // eq_refl /= nohasincr_setdiff //.
  by rewrite nth_rem_trail0 nth_add_setdiff.
Qed.

(* TODO : Fixme *)
Local Open Scope ring_scope.

Theorem alt_mpart_elementary d (P1 : intpartn d) k :
  size P1 <= n ->
  'a_(mpart P1 + rho) * 'e_k =
  \sum_(P : intpartn (d + k) | vb_strip P1 P && (size P <= n)) 'a_(mpart P + rho).
Proof.
  rewrite alt_elementary => Hsz.
  rewrite (bigID (hasincr P1)) /=.
  rewrite (eq_bigr (fun x => 0)); last by move=> i /andP [] _ /hasincr0.
  rewrite sumr_const mul0rn add0r.
  rewrite (eq_bigr (fun h => 'a_(mpart (add_mesym k P1 h) + rho))); first last.
    move=> i /andP [] Hk Hincr; by rewrite add_mesymE.
  rewrite (reindex_onto _ _ (add_mesymK Hsz)).
  apply eq_bigl => S; rewrite inE.
  apply (sameP idP); apply (iffP idP).
  - move=> /andP [] /andP [] Hstrip Hszle /eqP HS.
    rewrite -HS card_setdiff // eq_refl andTb.
    exact: nohasincr_setdiff.
  - move=> H; apply/andP; split; first (apply/andP; split).
    + apply/(vb_stripP (intpartnP _) (intpartnP _)) => i /=.
      rewrite Hsz H /= nth_rem_trail0.
      case: (ssrnat.ltnP i n) => Hi; first last.
        rewrite !nth_default //; first last.
        - exact: leq_trans Hsz Hi.
        - by rewrite size_map size_enum_ord.
      have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
      rewrite (nth_map (Ordinal H0)) ?size_enum_ord // !mnmE.
      rewrite /mpart (nth_enum_ord (Ordinal H0) Hi).
      by case: (_ \in _); rewrite ?addn0 ?addn1 leqnn ltnW.
    + rewrite /add_mesym /= Hsz H /=.
      apply (leq_trans (size_rem_trail0 _)).
      by rewrite size_map size_enum_ord.
    + rewrite /setdiff; apply/eqP; rewrite -setP => i.
      rewrite inE /= Hsz H /= nth_rem_trail0.
      have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      rewrite nth_ord_enum /= (mnm_nth 0) /= mnmE.
      rewrite /mpart /=.
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      rewrite nth_ord_enum.
      by case: (i \in S); rewrite ?addn0 ?addn1 ?ltnSn ?ltnn.
Qed.

Hypothesis Hn : n != 0%N.
Local Notation "''s_' k" := (Schur Hn R k) (at level 8, k at level 2, format "''s_' k").

Lemma Schur_cast d d' (P : intpartn d) (Heq : d = d') :
  's_P = Schur Hn R (intpartn_cast Heq P).
Proof. subst d'; by congr Schur. Qed.

Lemma vb_strip_rem_col0 d (P : intpartn d) :
  vb_strip (conj_part (behead (conj_part P))) P.
Proof.
  rewrite -{2}(conj_intpartnK P) /=.
  have Hc : is_part (conj_part P) by apply is_part_conj.
  apply hb_strip_conj => //; first by apply is_part_behead.
  elim: {d P} (conj_part P) Hc => [//=| s0 s IHs] /= /andP [] H0 /IHs {IHs}.
  case: s H0 => [//=| s1 s] /= -> ->.
  by rewrite leqnn.
Qed.


Lemma vb_strip_lex (d1 k : nat) (sh : intpartn (d1 + k)) p :
  vb_strip p sh ->
  sumn p = d1 ->
  is_part p -> (val sh <= incr_first_n p k)%Ord.
Proof.
  rewrite /=.
  elim: p d1 k sh => [| p0 p IHsh] d1 k sh Hstr.
    have {Hstr} Hstr := vb_stripP (is_true_true : is_part [::]) (intpartnP _) Hstr.
    move=> Hd1 _; subst d1.
    suff /= -> : val sh = nseq k 1%N by [].
    case: sh Hstr => sh /=; rewrite add0n => /andP [] /eqP.
    elim: sh k => [//= | s0 s IHs] /= k Hk; first by rewrite -Hk.
    rewrite -/(is_part (s0 :: s)) => Hpart Hstr.
    have Hs0 : s0 = 1%N.
      have := Hstr 0%N => /=.
      have /= := part_head_non0 Hpart.
      by case s0 => [| [| s0']].
    subst s0; rewrite -Hk add1n /= {1}(IHs (sumn s)) //.
    - exact: (is_part_consK Hpart).
    - move=> i; have /= := Hstr i.+1.
      by rewrite !nth_nil.
  case: sh Hstr => sh Hsh /= Hstr.
  case: k Hsh => [| k] Hsh Hd1; subst d1; rewrite -/(is_part (p0 :: p)) /= => /andP [] _ Hp.
    have Hincl := vb_strip_included Hstr.
    move: Hsh; rewrite addn0 /= -/(sumn (p0 :: p)) => /andP [] /eqP /esym Heq Hsh.
    by rewrite (included_sumnE Hsh Hincl Heq).
  case: sh Hstr Hsh => [//= |s0 sh] /= /andP [] H0 Hstrip.
  move=> /andP [] /eqP Heq /andP [] _ Hs.
  rewrite leqXE /= ltnXnatE ltnS.
  case: (leqP s0 p0) => //= Hp0.
  have Hs0 : s0 = p0.+1.
    apply anti_leq; rewrite Hp0.
    by move: H0 => /andP [] _ ->.
  subst s0; rewrite eq_refl /= {Hp0}.
  move: Heq; rewrite addSn addnS => /eqP; rewrite eqSS -addnA => /eqP /addnI Heq.
  have Hsh : is_part_of_n (sumn p + k)%N sh.
    by rewrite /= Heq eq_refl Hs.
  have /= := IHsh _ _ (IntPartN Hsh).
  by rewrite leqXE /=; apply.
Qed.

Theorem altE d (P : intpartn d) :
  size P <= n -> 'a_rho * 's_P = 'a_(mpart P + rho).
Proof.
  suff {d P} H : forall b d, d <= b -> forall (P : intpartn d),
    size P <= n -> 'a_rho * 's_P = 'a_(mpart P + rho) by apply: (H d).
  elim=> [ |b IHb] d Hd P.
    move: Hd; rewrite leqn0 => /eqP Hd; subst d.
    rewrite Schur0 mulr1 -{1}(add0m rho)=> _; congr 'a_(_ + rho).
    rewrite intpartn0 /mpart /= mnmP => i; by rewrite !mnmE /=.
  case: (leqP d b) => Hdb; first exact: (IHb _ Hdb).
  have {Hd Hdb} Hd : d = b.+1 by apply anti_leq; rewrite Hd Hdb.
  elim/lex_inpart_wf: P => P IHP HszP.
  pose k := head 1%N (conj_intpartn P).
  pose p1 := behead (conj_intpartn P); pose d1 := sumn p1.
  have Hk : (d = d1 + k)%N.
    have:= intpartn_sumn (conj_intpartn P).
    rewrite /d1 /k /p1 /=.
    case: (conj_part P) => [| [//= | c0] c] /=; by rewrite Hd // addnC.
  have Hd1 : d1 <= b.
    rewrite -ltnS -Hd Hk.
    have:= part_head_non0 (intpartnP (conj_intpartn P)).
    rewrite -/k; case k => //= k' _.
    rewrite addnS ltnS; exact: leq_addr.
  have p1P : is_part_of_n d1 p1 by rewrite /= /d1 eq_refl is_part_behead.
  pose P1 := IntPartN p1P.
  have HszP1 : size (conj_intpartn P1) <= n.
    rewrite size_conj_part //.
    apply: (leq_trans _ HszP); rewrite /= /p1.
    have := size_conj_part (intpartnP (conj_intpartn P)).
    rewrite conj_partK // => ->.
    have:= (intpartnP (conj_intpartn P)) => /=.
    by case: (conj_part P) => [| c0 [| c1 c]] //= /andP [].
  have := alt_mpart_elementary k HszP1.
  have {IHb HszP1 Hd1} <- := IHb _ Hd1 (conj_intpartn P1) HszP1.
  rewrite -mulrA elementaryE Pieri_elementary.
  rewrite (bigID (fun P0 : intpartn (d1 + k) => (size P0 <= n))) /= addrC.
  rewrite big1 ?add0r; first last.
    move=> i /andP [] _; rewrite -ltnNge; exact: Schur_oversize.
  rewrite mulr_sumr.
  pose P' := intpartn_cast Hk P.
  rewrite (bigID (pred1 P')) [X in _ = X](bigID (pred1 P')) /=.
  set prd := BIG_P.
  have Hprd : prd =1 pred1 P'.
    rewrite {}/prd => sh /=.
    case: eqP => [-> | _]; rewrite ?andbT ?andbF // {sh}.
    rewrite intpartn_castE {P' P1 d1 Hk p1P} HszP andbT /p1 /=.
    exact: vb_strip_rem_col0.
  rewrite !(eq_bigl _ _ Hprd) {Hprd prd} /= !big_pred1_eq intpartn_castE.
  set A := (X in _ + X); set B := (X in _ = _ + X).
  suff -> : A = B by move=> /addIr <- {A B}; rewrite -Schur_cast.
  apply eq_bigr => {A B} sh /andP [] /andP [] Hstrip Hsz Hsh.
  pose sh' := intpartn_cast (esym Hk) sh.
  have Hlex : (val sh' < P)%Ord.
    rewrite intpartn_castE /= {sh'}.
    rewrite ltnX_neqAleqX; apply/andP; split.
      move: Hsh; apply contra => /eqP H.
      apply/eqP; apply val_inj; by rewrite intpartn_castE.
    rewrite {Hsh Hsz P'}.
    have /= -> : val P = incr_first_n (conj_part p1) k.
      move: Hk; rewrite /d1 /p1 /= -{2}(conj_intpartnK P) /=.
      rewrite -{1}(intpartn_sumn (conj_intpartn P)) /=.
      case: (conj_part P) => [//= | p0 p] /=; first by rewrite add0n => <-.
      rewrite addnC -{2}(addKn (sumn p) k) => <-.
      by rewrite addKn.
    have:= intpartnP (conj_intpartn P1).
    have /= {Hk p1P P1} := intpartn_sumn (conj_intpartn P1).
    exact: vb_strip_lex.
  have Hsz' : size sh' <= n by rewrite intpartn_castE.
  have := IHP sh' Hlex Hsz'.
  rewrite -Schur_cast => ->.
  by rewrite intpartn_castE.
Qed.

End Alternant.



Section IdomainSymmetric.

Variable n : nat.
Variable R : idomainType.

Hypothesis Hn : n != 0%N.
Local Notation "''s_' k" := (Schur Hn R k) (at level 8, k at level 2, format "''s_' k").

Corollary alt_sym d (P : intpartn d) : size P <= n -> 's_P \is symmetric.
Proof.
  move=> HP.
  have := alt_anti R (mpart n P + rho n).
  rewrite -(altE _ _ HP).
  rewrite -sym_antiE //; last exact: alt_anti.
  exact: altrho_non0.
Qed.

End IdomainSymmetric.
