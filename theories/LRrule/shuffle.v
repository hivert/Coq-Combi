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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm binomial bigop.
Require Import tools vectNK subseq partition Yamanouchi ordtype std tableau stdtab.
Require Import Schensted plactic Greene_inv stdplact.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bool.

Import OrdNotations.

Section Defs.

Variable Alph : eqType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w : word.

(* Well founded recursive definition of shuffle (a :: u) v *)
Fixpoint shuffle_from_rec a u shuffu' v {struct v} :=
  if v is b :: v' then
    [seq a :: w | w <- shuffu' v] ++ [seq b :: w | w <- shuffle_from_rec a u shuffu' v']
  else [:: (a :: u)].

Fixpoint shuffle u v {struct u} :=
  if u is a :: u' then
    shuffle_from_rec a u' (shuffle u') v
  else [:: v].

Lemma shuffle_nil u : shuffle u [::] = [:: u].
Proof. by case u. Qed.

Lemma size_shuffle u v : size (shuffle u v) = binomial ((size u) + (size v)) (size u).
Proof.
  elim: u v => [| a u IHu] /= v; first by rewrite bin0.
  elim: v => [| b v IHv] /=; first by rewrite addn0 binn.
  rewrite size_cat !size_map IHu IHv /=.
  by rewrite !addSn addnS addnC -binS.
Qed.

Lemma shuffleC u v : perm_eq (shuffle u v) (shuffle v u).
Proof.
  elim: u v => [| a u IHu] /= v; first by rewrite shuffle_nil perm_eq_refl.
  elim: v => [| b v IHv] /=; first by rewrite perm_eq_refl.
  set sa := (X in X ++ _); set sb := (X in _ ++ X).
  apply: (@perm_eq_trans _ (sb ++ sa)); first by apply/perm_eqlP; apply: perm_catC.
  set sc := (X in perm_eq _ (X ++ _)).
  apply: (@perm_eq_trans _ (sc ++ sa)).
  - rewrite perm_cat2r /sb /sc /= {sa sb sc}.
    apply: perm_map; exact: IHv.
  - rewrite perm_cat2l /sa /= {sa sb sc}.
    apply: perm_map; exact: IHu.
Qed.


(* Tentative proof of associativity of shuffle *)

Lemma shuffle_perm_eq u l1 l2 :
  perm_eq l1 l2 ->
  perm_eq (flatten [seq shuffle u x | x <- l1])
          (flatten [seq shuffle u x | x <- l2]).
Proof.
  move /(perm_map (shuffle u)).
  move: [seq shuffle u i | i <- l1] => L1 {l1}.
  move: [seq shuffle u i | i <- l2] => L2 {l2}.
  move=> Hperm; apply/perm_eqP => P.
  rewrite !count_flatten.
  apply: perm_sumn.
  exact: perm_map.
Qed.

(*
Lemma shuffleA u v w :
  perm_eq (flatten [seq shuffle u x | x <- shuffle v w])
          (flatten [seq shuffle x w | x <- shuffle u v]).
Proof.
  elim: u v w => [| a u IHu] /= v w; first by rewrite cats0 flatten_seq1.
  elim: v w => [//= | b v IHv] /= w.
  elim: w => [//= | c w IHw] /=.
    rewrite (eq_map (f2 := (fun x => [:: x]))); last by move=> i /=; rewrite shuffle_nil.
    by rewrite cats0 flatten_seq1.
  have {IHv} /= IHv := IHv (c :: w).
  have {IHu} /= IHu := IHu (b :: v) (c :: w).
  apply (perm_eq_trans IHu).
Qed.
*)

Lemma perm_eq_shuffle u v : all (perm_eq (u ++ v)) (shuffle u v).
Proof.
  elim: u v => [| a u IHu] /= v; first by rewrite perm_eq_refl.
  elim: v => [| b v /allP IHv] /=; first by rewrite cats0 perm_eq_refl.
  rewrite all_cat; apply/andP; split; apply/allP => s /mapP [] t Ht -> {s} /=.
  - rewrite perm_cons.
    move/(_ (b :: v)): IHu => /allP; by apply.
  - apply: (@perm_eq_trans _ (b :: v ++ a :: u)).
    + apply/perm_eqlP; by have /= := perm_catC (a :: u) (b :: v).
    + rewrite perm_cons perm_eq_sym.
      move/(_ t Ht) : IHv; rewrite perm_eq_sym => /perm_eq_trans; apply.
      apply/perm_eqlP; by have /= := perm_catC (a :: u) v.
Qed.

Lemma all_size_shuffle u v : all (fun s => size s == size u + size v) (shuffle u v).
Proof.
  apply/allP => x Hx; rewrite -size_cat.
  apply/eqP; apply: perm_eq_size.
  have:= perm_eq_shuffle u v => /allP Hall.
  rewrite perm_eq_sym; exact: Hall.
Qed.

Lemma all_in_shufflel u v :
  predI (mem u) (mem v) =i pred0 ->
  all (fun s => filter (mem u) s == u) (shuffle u v).
Proof.
  elim: u v => [| a u IHu] /= v HI.
    by rewrite !andbT (eq_filter (a2 := pred0)) // filter_pred0.
  elim: v HI => [_ | b v IHv] /=.
  - rewrite !andbT inE eq_refl /=; apply/eqP; congr (a :: _).
    rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT.
    move => i /=; rewrite inE => ->; by rewrite orbT.
  - move=> HI; rewrite all_cat.
    apply/andP; split; apply/allP=> x /mapP [] s Hs -> {x} /=.
    + rewrite !inE eq_refl /=; apply/eqP; congr (a :: _).
      have {IHu} /IHu/allP Hu : [predI u & b :: v] =i pred0.
        move=> i; rewrite !inE; apply: negbTE.
        move/(_ i): HI; rewrite !inE => /negbT.
        apply: contra => /andP [] ->; by rewrite orbT.
      case (boolP (a \in u)) => Ha.
      * rewrite (eq_filter (a2 := mem u)); first by apply/eqP; apply: (Hu _ Hs).
        move => i /=; rewrite inE.
        apply/idP/idP => [| ->]; last by rewrite orbT.
        by move/orP => [/eqP ->|].
      * rewrite (eq_in_filter (a2 := mem u)); first by apply/eqP; apply: (Hu _ Hs).
        move => i /=; rewrite inE => Hi.
        apply/idP/idP; last by move ->; rewrite orbT.
        have /allP := perm_eq_shuffle u (b :: v) => /(_ _ Hs)/perm_eq_mem/(_ i).
        rewrite {}Hi /= mem_cat inE => /or3P []; first by move ->.
        - move/eqP -> => /orP [] // /eqP Habs; exfalso.
          move/(_ a): HI; by rewrite !inE Habs !eq_refl.
        - move=> Hi /orP [] // /eqP Habs; move: Hi; rewrite Habs {i Habs} => Habs.
          move/(_ a): HI; by rewrite !inE Habs !eq_refl /= orbT.
    + have := HI b; rewrite !inE /= eq_refl /= andbT => ->.
      have /IHv/allP : [predI a :: u & v] =i pred0.
        move=> i /=; rewrite !inE; apply: negbTE.
        move/(_ i): HI; rewrite !inE => /negbT.
        apply: contra => /andP [] -> ->; by rewrite orbT.
      by apply.
Qed.

Lemma all_in_shuffler u v :
  predI (mem u) (mem v) =i pred0 ->
  all (fun s => filter (mem v) s == v) (shuffle u v).
Proof.
  move=> HI.
  rewrite (all_perm_eq (shuffleC v u)) //.
  apply: all_in_shufflel.
  move=> i; by rewrite -(HI i) !inE andbC.
Qed.

Lemma mem_shuffle_predU u v s Pu Pv:
  predI Pu Pv =i pred0 ->
  filter Pu s = u -> filter Pv s = v -> size s = size u + size v ->
  filter (predU Pu Pv) s = s.
Proof.
  move=> HI Hu Hv Hsz.
  have /eqP := count_predUI Pu Pv s.
  rewrite -!size_filter Hu Hv (eq_filter HI) filter_pred0 /= addn0 -Hsz.
  by rewrite size_filter -all_count => /all_filterP.
Qed.

Lemma mem_shuffle_pred u v s Pu Pv:
  predI Pu Pv =i pred0 ->
  filter Pu s = u -> filter Pv s = v -> size s = size u + size v ->
  s \in shuffle u v.
Proof.
  move=> HI Hu Hv Hsz; have /all_filterP Hall := mem_shuffle_predU HI Hu Hv Hsz.
  elim: u v s Hu Hv {Hsz} Hall => [| a u' IHu] /= v s Hu Hv Hall.
    move: Hall => /all_filterP; rewrite (eq_in_filter (a2 := Pv));
      first by move <-; rewrite Hv mem_seq1.
    move=> i Hi /=; suff -> : Pu i = false by [].
    apply/(introF idP) => HPu.
    have : i \in [seq x <- s | Pu x] by rewrite mem_filter HPu Hi.
    by rewrite Hu /= in_nil.
  elim: v s Hv Hu Hall => [//= | b v IHv] /= s Hv Hu Hall.
    move: Hall => /all_filterP; rewrite (eq_in_filter (a2 := Pu));
      first by move <-; rewrite Hu mem_seq1.
    move=> i Hi /=; suff -> : Pv i = false by rewrite orbF.
    apply/(introF idP) => HPv.
    have : i \in [seq x <- s | Pv x] by rewrite mem_filter HPv Hi.
    by rewrite Hv /= in_nil.
  case: s Hu Hv Hall => [//= | s0 s] /=.
  case: (boolP (Pu s0)) => Hs0 /=.
  - have -> : Pv s0 = false by move/(_ s0): HI; rewrite !inE Hs0.
    move=> [] Ha; subst s0 => Hu Hv Hall.
    rewrite mem_cat; apply/orP; left.
    apply/mapP; exists s; last by [].
    exact: IHu.
  - move=> Hu Hv {Hs0} /andP [] Hs0 Hall.
    rewrite Hs0 /= in Hv; move: Hv => [] Htmp; subst s0 => Hv.
    rewrite mem_cat; apply/orP; right.
    apply/mapP; exists s; last by [].
    exact: IHv.
Qed.

Lemma mem_shuffle u v s :
  predI (mem u) (mem v) =i pred0 ->
  [&& filter (mem u) s == u, filter (mem v) s == v & (size s == size u + size v)] =
    (s \in shuffle u v).
Proof.
  move=> HI; apply/idP/idP.
  - move=> /and3P [] /eqP Hu /eqP Hv /eqP Hsz.
    exact: (mem_shuffle_pred HI).
  - move=> Hs.
    have:= all_in_shufflel HI => /allP/(_ _ Hs) -> /=.
    have:= all_in_shuffler HI => /allP/(_ _ Hs) -> /=.
    by have:= all_size_shuffle u v => /allP/(_ _ Hs).
Qed.

(* Unused lemma *)
Lemma swap_shuffle u v l a b r Pu Pv :
  predI Pu Pv =i pred0 ->
  let s := l ++ [:: a; b] ++ r in
  filter Pu s = u -> filter Pv s = v -> size s = size u + size v ->
  Pu a -> Pv b ->
  s \in shuffle u v ->
  l ++ [:: b; a] ++ r \in shuffle u v.
Proof.
  move=> HI s Hu Hv Hsz Ha Hb H.
  apply: (mem_shuffle_pred HI).
  - move: Hu; rewrite /s !filter_cat /= Ha.
    suff -> : Pu b = false by [].
    by move/(_ b): HI; rewrite !inE Hb andbT.
  - move: Hv; rewrite /s !filter_cat /= Hb.
    suff -> : Pv a = false by [].
    by move/(_ a): HI; rewrite !inE Ha.
  - by rewrite -Hsz /s !size_cat /=.
Qed.

End Defs.


Section ShiftedShuffle.

Implicit Type u v w : seq nat.

Definition shiftn n := map (addn n).
Definition sfiltergtn n := [fun v => filter (gtn n) v].
Definition sfilterleq n := [fun v => map (subn^~ n) (filter (leq n) v)].

Lemma shiftuK n : cancel (shiftn n) (map (subn^~ n)).
Proof.
  move=> s; rewrite /shiftn -map_comp.
  rewrite (eq_map (f2 := id)); first by rewrite map_id.
  move=> i /=; by rewrite /= addKn.
Qed.

Lemma sfilterleqK n v : shiftn n (sfilterleq n v) = [seq x <- v | n <= x].
Proof.
  rewrite /=; elim: v => [//= | v0 v IHv] /=.
  case: leqP => H /=; rewrite IHv; last by [].
  by rewrite subnKC.
Qed.

Lemma sfilterleqE n u v : u = sfilterleq n v <-> shiftn n u = filter (leq n) v.
Proof.
  split.
  - move=> -> {u} /=; by rewrite sfilterleqK.
  - move=> /= <- {v}; by rewrite shiftuK.
Qed.

Lemma mem_sfilterleqK n v i : i \in (sfilterleq n v) = (i + n \in v).
Proof.
  rewrite /=; elim: v => [//= | v0 v IHv] /=.
  case: leqP => H /=; rewrite !inE IHv.
  - congr (_ || _); by rewrite -{2}(subnK H) eqn_add2r.
  - suff -> : (i + n == v0) = false by [].
    apply: gtn_eqF; exact: ltn_addl.
Qed.

Lemma perm_eq_shiftn_std n s :
  is_std s -> perm_eq (shiftn n s) (iota n (size s)).
Proof.
  rewrite /is_std /shiftn -{2}(addn0 n) iota_addl.
  exact: perm_map.
Qed.

Definition shsh u v := shuffle u (shiftn (size u) v).

Lemma std_shsh u v : is_std u -> is_std v -> all is_std (shsh u v).
Proof.
  rewrite /is_std /shsh /shiftn => Hu Hv.
  apply/allP => s Hs.
  have /allP/(_ s Hs) := perm_eq_shuffle u (shiftn (size u) v).
  rewrite perm_eq_sym => /perm_eq_trans; apply.
  have /allP/(_ s Hs)/eqP := all_size_shuffle u (shiftn (size u) v).
  rewrite size_map => -> {s Hs}.
  rewrite iota_add.
  apply: (@perm_eq_trans _ (u ++ iota (size u) (size v))); last by rewrite perm_cat2r.
  rewrite perm_cat2l -{2}[size u]addn0 iota_addl.
  exact: perm_map.
Qed.

Lemma pred0_std u v : is_std u -> [predI u & shiftn (size u) v] =i pred0.
Proof.
  rewrite /is_std /shsh /shiftn => /perm_eq_mem Hu i /=.
  rewrite !inE Hu mem_iota add0n /=.
  apply: (introF idP) => /andP [] Hlt /mapP [] j _ Hi.
  move: Hlt; by rewrite Hi -{2}[size u]addn0 ltn_add2l.
Qed.

Lemma shsh_sfiltergtn p u v :
  is_std u -> p \in shsh u v -> u = sfiltergtn (size u) p.
Proof.
  move=> Hstdu; rewrite /shsh.
  rewrite -(mem_shuffle _ (pred0_std v Hstdu)) => /and3P [] /eqP Hu _ _.
  rewrite -{1}Hu; apply: eq_filter => i /=.
  by rewrite (perm_eq_mem Hstdu) mem_iota /= add0n.
Qed.

Lemma shsh_sfilterleq p u v :
  is_std u -> p \in shsh u v -> v = sfilterleq (size u) p.
Proof.
  move=> Hstdu; rewrite /shsh => Hsh.
  rewrite sfilterleqE.
  have:= Hsh; rewrite -(mem_shuffle _ (pred0_std v Hstdu)) /= => /and3P [] _ /eqP <- _.
  apply: eq_in_filter => i /= Hi.
  have /allP/(_ p Hsh) Hp := perm_eq_shuffle u (shiftn (size u) v).
  move: Hi; rewrite -(perm_eq_mem Hp) mem_cat => /orP [].
  - rewrite (perm_eq_mem Hstdu) mem_iota /= add0n /shiftn => Hi.
    rewrite leqNgt Hi /=; apply/(introF idP) => /mapP [] j Hj Heq.
    move: Hi; by rewrite Heq -{2}[size u]addn0 ltn_add2l.
  - move=> Hi; rewrite Hi; apply: esym.
    move: Hi; rewrite /shiftn => /mapP [] j _ ->.
    by rewrite -{1}[size u]addn0 leq_add2l.
Qed.

Lemma mem_shsh p u v : is_std u ->
  (p \in shsh u v) = ((sfiltergtn (size u) p == u) && (sfilterleq (size u) p == v)).
Proof.
  move=> Hstdu; apply/idP/idP.
  - move=> H; by rewrite {2}(shsh_sfiltergtn Hstdu H) (shsh_sfilterleq Hstdu H) !eq_refl.
  - rewrite /shsh -(mem_shuffle _ (pred0_std v Hstdu)).
    move/andP => [] /eqP /= Hu /eqP /= Hv.
    apply/and3P; split.
    + apply/eqP; rewrite -{2}Hu /=; apply: eq_filter => i.
      by rewrite /= (perm_eq_mem Hstdu) mem_iota /= add0n.
    + apply/eqP; rewrite -{2}Hv sfilterleqK /=; apply: eq_in_filter => i /= Hi.
      by rewrite -Hv sfilterleqK mem_filter Hi andbT.
    + rewrite -(count_predC (gtn (size u)) p) -!size_filter.
      have /eq_filter -> : (predC (gtn (size u))) =1 leq (size u).
        move=> i /=; by rewrite -leqNgt.
      by rewrite Hu -Hv !size_map.
Qed.

Lemma shift_plactcongr n u v : (u =Pl v) = (shiftn n u =Pl shiftn n v).
Proof.
  apply/idP/idP.
  - apply: plact_map_in_incr => x y _ _.
    by rewrite !ltnXnatE ltn_add2l.
  - rewrite -{2}[u](shiftuK n) -{2}[v](shiftuK n) /shiftn.
    apply: plact_map_in_incr => x y /mapP [] x0 Hx0 -> {x} /mapP [] y0 Hy0 -> {y}.
    by rewrite !ltnXnatE ltn_add2l !addKn.
Qed.

End ShiftedShuffle.

Section LRTriple.

Variable Alph : inhOrdType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w : word.
Implicit Type t : seq (seq nat).

Lemma perm_eq_sfiltergtn p n :
  is_std p -> perm_eq (sfiltergtn n p) (iota 0 (minn n (size p))).
Proof.
  move=> Hstd; apply: uniq_perm_eq.
  - apply: filter_uniq; exact: std_uniq.
  - exact: iota_uniq.
  - move=> i; rewrite mem_filter mem_iota /= add0n leq_min.
    congr (_ && _).
    rewrite (perm_eq_mem Hstd).
    by rewrite mem_iota /= add0n.
Qed.

Lemma perm_eq_sfilterleq p n :
  is_std p -> perm_eq (sfilterleq n p) (iota 0 ((size p) - n)).
Proof.
  move=> Hstd; apply: uniq_perm_eq.
  - rewrite map_inj_in_uniq.
    + apply: filter_uniq; exact: std_uniq.
    + move=> i j; rewrite !mem_filter => /andP [] Hi _ /andP [] Hj _ H.
      by rewrite -(subnK Hi) H (subnK Hj).
  - exact: iota_uniq.
  - move=> i; rewrite mem_sfilterleqK.
    rewrite (perm_eq_mem Hstd).
    rewrite !mem_iota /= !add0n.
    by rewrite ltn_subRL addnC.
Qed.

Lemma size_sfiltergtn p n :
  is_std p -> size (sfiltergtn n p) = minn n (size p).
Proof. move/(perm_eq_sfiltergtn n)/perm_eq_size ->; by rewrite size_iota. Qed.
Lemma size_sfilterleq p n :
  is_std p -> size (sfilterleq n p) = (size p) - n.
Proof. move/(perm_eq_sfilterleq n)/perm_eq_size ->; by rewrite size_iota. Qed.

Lemma sfiltergtn_is_std p n : is_std p -> is_std (sfiltergtn n p).
Proof.
  move=> Hstd; rewrite /is_std (size_sfiltergtn _ Hstd).
  exact: perm_eq_sfiltergtn.
Qed.
Lemma sfilterleq_is_std p n : is_std p -> is_std (sfilterleq n p).
Proof.
  move=> Hstd; rewrite /is_std (size_sfilterleq _ Hstd).
  exact: perm_eq_sfilterleq.
Qed.

Lemma size_sfiltergtn_cat u v :
  size (sfiltergtn (size u) (invstd (std (u ++ v)))) = size u.
Proof.
  rewrite (size_sfiltergtn _ (invstd_is_std _)); last exact: std_is_std.
  rewrite size_invstd size_std size_cat.
  by have /minn_idPl -> : size u <= size u + size v by apply: leq_addr.
Qed.
Lemma size_sfilterleq_cat u v :
  size (sfilterleq (size u) (invstd (std (u ++ v)))) = size v.
Proof.
  rewrite (size_sfilterleq _ (invstd_is_std _)); last exact: std_is_std.
  by rewrite size_invstd size_std size_cat addKn.
Qed.

Lemma index_leq_filter l (P : pred nat) i j :
  P i -> P j ->
  (index i (filter P l)) <= (index j (filter P l)) = (index i l <= index j l).
Proof.
  move=> Hi Hj.
  elim: l => [//= | l0 l IHl] /=.
  case (boolP (P l0)) => [Hl0|] /=.
  - case (altP (l0 =P i)) => Hil0; first by case (altP (l0 =P j)).
    + case (altP (l0 =P j)) => [//= | Hjl0].
    + by rewrite !ltnS IHl.
  - case (altP (l0 =P i)) => [->|Hil0]; first by rewrite Hi.
    case (altP (l0 =P j)) => [->|Hjl0]; first by rewrite Hj.
    by rewrite ltnS IHl.
Qed.

Lemma index_sfilterleq n s i :
  index i (sfilterleq n s) = index (i + n) (filter (leq n) s).
Proof.
  elim: s => [//= | s0 s IHs] /=.
  case: (leqP n s0) => Hv0 /=.
  - by rewrite -{2}(subnK Hv0) eqn_add2r IHs.
  - by rewrite IHs.
Qed.

Lemma index_invstd l i :
  is_std l -> i < size l ->
  (index i (invstd l)) = nth (inhabitant nat_inhOrdType) l i.
Proof. move=> Hstd Hi; by rewrite -{2}(invstdK Hstd) /invstd nth_mkseq //= size_mkseq. Qed.

Lemma invstd_catgtn u v :
  invstd (std u) = sfiltergtn (size u) (invstd (std (u ++ v))).
Proof.
  suff Heqinv : std u = invstd (sfiltergtn (size u) (invstd (std (u ++ v)))).
    rewrite Heqinv invstdK //=.
    apply: (@sfiltergtn_is_std (invstd (std (u ++ v))) (size u)).
    apply: invstd_is_std; exact: std_is_std.
  apply/eqP/stdP; apply: StdSpec.
    apply: invstd_is_std.
    apply: (@sfiltergtn_is_std (invstd (std (u ++ v))) (size u)).
    apply: invstd_is_std; exact: std_is_std.
  apply/eq_invP; split; first by rewrite size_invstd size_sfiltergtn_cat.
  move=> i j /andP [] Hij Hj.
  have Hi := leq_ltn_trans Hij Hj.
  rewrite leqXnatE /=.
  do 2 (rewrite nth_mkseq; last by rewrite size_sfiltergtn_cat).
  rewrite index_leq_filter //= -/(invstd (std (u++v))).
  have Hucat : size u <= size (std (u ++ v)) by rewrite size_std size_cat; apply: leq_addr.
  do 2 (rewrite (index_invstd (std_is_std (u ++ v)));
        last by apply: (@leq_trans (size u)); last exact Hucat).
  have /eq_invP := eq_inv_std (u ++ v) => [] [] _ Hinv.
  have Hijsz : i <= j < size (u ++ v).
    rewrite Hij /=; apply: (leq_trans Hj); rewrite size_cat; exact: leq_addr.
  rewrite -leqXnatE -(Hinv i j Hijsz).
  by rewrite !nth_cat Hi Hj.
Qed.

Lemma invstd_catleq u v :
  invstd (std v) = sfilterleq (size u) (invstd (std (u ++ v))).
Proof.
  suff Heqinv : std v = invstd (sfilterleq (size u) (invstd (std (u ++ v)))).
    rewrite Heqinv invstdK //=.
    apply: (@sfilterleq_is_std (invstd (std (u ++ v))) (size u)).
    apply: invstd_is_std; exact: std_is_std.
  apply/eqP/stdP; apply: StdSpec.
    apply: invstd_is_std.
    apply: (@sfilterleq_is_std (invstd (std (u ++ v))) (size u)).
    apply: invstd_is_std; exact: std_is_std.
  apply/eq_invP; split; first by rewrite size_invstd size_sfilterleq_cat.
  move=> i j /andP [] Hij Hj.
  have Hi := leq_ltn_trans Hij Hj.
  rewrite leqXnatE /=.
  do 2 (rewrite nth_mkseq; last by rewrite size_sfilterleq_cat).
  rewrite !index_sfilterleq index_leq_filter; try apply: leq_addl.
  do 2 (rewrite (index_invstd (std_is_std (u ++ v)));
    last by rewrite size_std size_cat addnC ltn_add2l).
  have /eq_invP := eq_inv_std (u ++ v) => [] [] _ Hinv.
  have Hijsz : i + size u <= j + size u < size (u ++ v).
    rewrite size_cat [size u + _]addnC.
    rewrite leq_add2r ltn_add2r.
    by rewrite Hij Hj.
  rewrite -leqXnatE -(Hinv _ _ Hijsz) {Hijsz}.
  rewrite !nth_cat.
  have H x : (x + size u < size u) = false by apply: negbTE; rewrite -leqNgt; apply: leq_addl.
  by rewrite !H !addnK.
Qed.

(* This is essentially the product rule of FQSym *)
Theorem invstd_cat_in_shsh u v :
  invstd (std (u ++ v)) \in shsh (invstd (std u)) (invstd (std v)).
Proof.
  rewrite mem_shsh; last by apply: invstd_is_std; apply: std_is_std.
  by rewrite {2}(invstd_catgtn u v) size_invstd size_std (invstd_catleq u v) !eq_refl.
Qed.

Definition langQ t := [pred w : word | (RStabmap w).2 == t].

Lemma size_langQ t u : u \in langQ t -> size u = size_tab t.
Proof.
  rewrite /langQ inE /RStabmap => /eqP <-.
  rewrite -size_RS -RSmapE.
  rewrite /size_tab shape_RSmap_eq.
  case: (RSmap u) => p q /=.
  by rewrite shape_stdtab_of_yam.
Qed.

Record LRtriple t1 t2 t : Prop :=
  LRTriple :
    forall p1 p2 p, RS p1 = t1 -> RS p2 = t2 -> RS p = t ->
                    p \in shsh p1 p2 -> LRtriple t1 t2 t.
Definition pred_LRtriple (t1 t2 : seq (seq nat)) :=
  [pred t : (seq (seq nat)) |
   has (fun p => RS p == t)
       (flatten [seq shsh p1 p2 | p1 <- RSclass _ t1, p2 <- RSclass _ t2])].
Definition pred_LRtriple_fast (t1 t2 : seq (seq nat)) :=
  [pred t : (seq (seq nat)) |
   has (fun p2 => to_word t \in shsh (to_word t1) p2) (RSclass _ t2)].

Lemma LRtripleP t1 t2 t :
  is_stdtab t1 -> is_stdtab t2 ->
  reflect (LRtriple t1 t2 t) (pred_LRtriple t1 t2 t).
Proof.
  rewrite /is_stdtab => /andP [] Htab1 _ /andP [] Htab2 _.
  apply: (iffP idP) => /=.
  - move=> /hasP [] p /flattenP [] shuf /allpairsP [] [p1 p2] /= [].
    move=> /mapP [] yam1
            /(allP (enum_yamevalP (is_part_sht Htab1))) /= /andP [] Hyam1 Hsh1 Hp1.
    move=> /mapP [] yam2
            /(allP (enum_yamevalP (is_part_sht Htab2))) /= /andP [] Hyam2 Hsh2 Hp2.
    move=> -> {shuf} Hshuf /eqP <- {t}.
    apply: (@LRTriple t1 t2 (RS p) p1 p2 p) => //=.
    + by rewrite Hp1 -RSmapE RSmapinv2K //= Htab1 Hyam1 eq_sym Hsh1.
    + by rewrite Hp2 -RSmapE RSmapinv2K //= Htab2 Hyam2 eq_sym Hsh2.
  - move=> [p1 p2 p]; rewrite -2!RSmapE => Hp1 Hp2 Hp Hsh.
    apply/hasP; exists p; last by rewrite Hp.
    apply/flattenP; exists (shsh p1 p2); last exact: Hsh.
    apply/allpairsP; exists (p1, p2); split; last by [].
    + rewrite /= -Hp1 RSmapE; exact: mem_RSclass.
    + rewrite /= -Hp2 RSmapE; exact: mem_RSclass.
Qed.

Lemma filter_gtnX_RS (T : inhOrdType) (w : seq T) n :
  RS (filter (gtnX n) w) = filter_gtnX_tab n (RS w).
Proof.
  apply/eqP.
  rewrite -(RS_tabE (is_tableau_filter_gtnX _ (is_tableau_RS w))) -plactic_RS /=.
  rewrite to_word_filter_nnil -filter_to_word.
  apply: plactic_filter_gtnX; exact: congr_RS.
Qed.

Lemma pred_LRtriple_fast_filter_gtnX t1 t2 t :
  is_stdtab t1 -> is_stdtab t ->
  pred_LRtriple_fast t1 t2 t -> t1 = filter_gtnX_tab (size_tab t1) t.
Proof.
  move=> Ht1 Ht /= /hasP [] p2 Hp2 Hshsh.
  move: Ht1; rewrite /is_stdtab => /andP [] Htab1 Hstd1.
  rewrite -{1}(RS_tabE Htab1) (shsh_sfiltergtn Hstd1 Hshsh) /=.
  rewrite -(eq_filter (gtnXnatE _)) -size_to_word.
  move: Ht; rewrite /is_stdtab => /andP [] Htab _.
  by rewrite filter_gtnX_RS /= (RS_tabE Htab).
Qed.

Lemma LRtriple_fastE t1 t2 t :
  is_stdtab t1 -> is_stdtab t2 -> is_stdtab t ->
  pred_LRtriple t1 t2 t = pred_LRtriple_fast t1 t2 t.
Proof.
  move=> Ht1 Ht2 Ht.
  apply/idP/idP.
  - move/(LRtripleP t Ht1 Ht2) => [] p1 p2 p Hp1 Hp2 Hp Hshsh /=.
    rewrite -Hp -Hp1 -Hp2.
    pose p' := (sfilterleq (size p1) (to_word (RS p))).
    have Hp' : RS p2 = RS p'.
      apply/eqP; rewrite -plactic_RS.
      move: Hshsh; have:= Ht1; rewrite -Hp1 RSstdE => /mem_shsh -> /andP [] _ /eqP <-.
      rewrite (shift_plactcongr (size p1)) /p' !sfilterleqK.
      apply: plactic_filter_leqX; apply congr_RS.
    apply/hasP; exists p'.
    + apply /mapP; exists (RSmap p').2.
      * apply/count_memPn; rewrite Hp'.
        have: is_yam_of_eval (shape (RS p')) (RSmap p').2.
          by rewrite /is_yam_of_eval is_yam_RSmap2 /= -RSmapE shape_RSmap_eq.
        by move/(enum_yameval_countE (is_part_sht (is_tableau_RS p'))) => ->.
      * rewrite Hp' -[RS p']RSmapE /=.
        have -> : ((RSmap p').1, (RSmap p').2) = RSmap p' by case RSmap.
        by rewrite RSmapK.
    + have: is_std (to_word (RS p1)) by move: Ht1; rewrite Hp1 /is_stdtab => /andP [].
      move/mem_shsh ->; apply/andP.
      rewrite size_to_word size_RS; split; last by [].
      move: Hshsh; have:= Ht1; rewrite -Hp1 RSstdE => /mem_shsh -> /andP [] /eqP {3}<- _.
      rewrite /= -!(eq_filter (gtnXnatE _)) filter_gtnX_RS.
      by rewrite filter_to_word to_word_filter_nnil.
  - move=> Hfast; apply/(LRtripleP t Ht1 Ht2).
    move: Hfast => /= /hasP [] p2 /mapP [] y2 Hy2.
    have:= Ht2; rewrite /is_stdtab => /andP [] Htab2 _.
    have:= (is_part_sht Htab2) => /enum_yamevalP/allP/(_ _ Hy2) {Hy2}.
    rewrite /is_yam_of_eval => /andP [] Hyam2 /eqP Hsh2 Hp2 Htshsh.
    have:= Ht1; rewrite /is_stdtab => /andP [] /RS_tabE => H1 _.
    have H2 : RS p2 = t2 by rewrite Hp2 -RSmapE RSmapinv2K //= Htab2 Hyam2 Hsh2 /=.
    have:= Ht; rewrite /is_stdtab => /andP [] /RS_tabE => Hres _.
    exact: (LRTriple H1 H2 Hres).
Qed.

Lemma is_stdtab_of_n_LRtriple t1 t2 t :
  is_stdtab t1 -> is_stdtab t2 -> LRtriple t1 t2 t ->
  is_stdtab_of_n ((size_tab t1) + (size_tab t2)) t.
Proof.
  move=> H1 H2 [] p1 p2 p Hp1 Hp2 <- {t} Hp /=.
  apply/andP; split.
  - rewrite RSstdE.
    have Hsp1 : is_std p1 by rewrite -(RSstdE) Hp1.
    have Hsp2 : is_std p2 by rewrite -(RSstdE) Hp2.
    have /allP:= (std_shsh Hsp1 Hsp2); by apply.
  - rewrite size_RS; move: Hp; rewrite /shsh => Hp.
    have /allP/(_ _ Hp)/eqP -> := all_size_shuffle p1 (shiftn (size p1) p2).
    by rewrite size_map -Hp1 -Hp2 !size_RS.
Qed.

Theorem LRtriple_cat_langQ t1 t2 u1 u2:
  is_stdtab t1 -> is_stdtab t2 -> u1 \in langQ t1 -> u2 \in langQ t2 ->
  LRtriple t1 t2 (RStabmap (u1 ++ u2)).2.
Proof.
  move=> Hstd1 Hstd2 Hu1 Hu2.
  have Hsz1 := size_langQ Hu1; have Hsz2 := size_langQ Hu2.
  move: Hu1 Hu2; rewrite !inE => /eqP Hu1 /eqP Hu2.
  apply: (LRTriple (p1 := invstd (std u1))
                        (p2 := invstd (std u2))
                        (p  := invstd (std (u1 ++ u2))) ).
  - by rewrite -Hu1 RSinvstdE.
  - by rewrite -Hu2 RSinvstdE.
  - by rewrite RSinvstdE.
  - exact: invstd_cat_in_shsh.
Qed.

Theorem LRtriple_cat_equiv t1 t2 :
  is_stdtab t1 -> is_stdtab t2 ->
  forall u1 u2 : word,
  ( (u1 \in langQ t1 /\ u2 \in langQ t2) <->
    [/\ size u1 = size_tab t1, size u2 = size_tab t2 &
     exists t, LRtriple t1 t2 t /\ u1 ++ u2 \in langQ t] ).
Proof.
  move=> Hstd1 Hstd2 u1 u2.
  split.
  - move=> [] Hu1 Hu2; split; try exact: size_langQ.
    exists (RStabmap (u1 ++ u2)).2; split.
    + exact: LRtriple_cat_langQ.
    + by rewrite inE.
  - move=> [] Hsz1 Hsz2 [] t [] [] p1 p2 p Hp1 Hp2 Htmp; subst t.
    rewrite !inE -!RSinvstdE -Hp1 -Hp2 -!plactic_RS => Hsh Hcat.
    have Hstdp1 : is_std p1 by rewrite -RSstdE Hp1.
    have Hszp : size p1 = size u1 by rewrite Hsz1 -size_RS Hp1.
    split.
    + rewrite (invstd_catgtn u1 u2) (shsh_sfiltergtn Hstdp1 Hsh) Hszp.
      rewrite /= -!(eq_filter (gtnXnatE (size u1))).
      exact: plactic_filter_gtnX.
    + rewrite (invstd_catleq u1 u2) (shsh_sfilterleq Hstdp1 Hsh) Hszp.
      rewrite (shift_plactcongr (size u1)) !sfilterleqK.
      exact: plactic_filter_leqX.
Qed.


Theorem LRtriple_conj t1 t2 t :
  is_stdtab t1 -> is_stdtab t2 -> is_stdtab t ->
  LRtriple t1 t2 t -> LRtriple (conj_tab t1) (conj_tab t2) (conj_tab t).
Proof.
  move=> Ht1 Ht2 Ht [] p1 p2 p Hp1 Hp2 Hp.
  rewrite mem_shsh; last by rewrite -RSstdE Hp1.
  move=> /= /andP [] /eqP Hsh1 /eqP Hsh2.
  apply: (@LRTriple _ _ _ (rev p1) (rev p2) (rev p)).
  - rewrite RS_rev_uniq; last by apply std_uniq; rewrite -RSstdE Hp1.
    by rewrite Hp1.
  - rewrite RS_rev_uniq; last by apply std_uniq; rewrite -RSstdE Hp2.
    by rewrite Hp2.
  - rewrite RS_rev_uniq; last by apply std_uniq; rewrite -RSstdE Hp.
    by rewrite Hp.
  - rewrite mem_shsh; first last.
      rewrite /is_std size_rev.
      have:= perm_eq_rev p1 => /perm_eqlP <-.
      by rewrite -/(is_std _)  -RSstdE Hp1.
    by rewrite /= size_rev !filter_rev map_rev Hsh1 Hsh2 !eq_refl.
Qed.

Theorem pred_LRtriple_conj t1 t2 t :
  is_stdtab t1 -> is_stdtab t2 -> is_stdtab t ->
  pred_LRtriple t1 t2 t = pred_LRtriple (conj_tab t1) (conj_tab t2) (conj_tab t).
Proof.
  move=> Ht1 Ht2 Ht.
  have Hc1 := is_stdtab_conj Ht1.
  have Hc2 := is_stdtab_conj Ht2.
  have Hc := is_stdtab_conj Ht.
  apply/idP/idP => /LRtripleP H; apply/LRtripleP => //=.
  - apply: LRtriple_conj => //; exact: H.
  - rewrite -[t1]conj_tabK; last by move: Ht1 => /andP [].
    rewrite -[t2]conj_tabK; last by move: Ht2 => /andP [].
    rewrite -[t]conj_tabK;  last by move: Ht  => /andP [].
    apply: LRtriple_conj => //; exact: H.
Qed.

End LRTriple.

Implicit Arguments langQ [Alph].

(*
(* First non trivial example of LR rule *)
Eval compute in map (@shape nat_ordType)
                    (filter
                       (pred_LRtriple [:: [:: 0; 1]; [:: 2]] [:: [:: 0; 1]; [:: 2]])
                       (enum_stdtabn 6)).

Eval compute in count
                  (pred_LRtriple [:: [:: 0; 1]; [:: 2]] [:: [:: 0; 1]; [:: 2]])
                  (enum_stdtabsh [:: 3; 2; 1]).

Eval compute in count
                  (pred_LRtriple_fast [:: [:: 0; 1]; [:: 2]] [:: [:: 0; 1]; [:: 2]])
                  (enum_stdtabsh [:: 3; 2; 1]).

Eval compute in count
                  (pred_LRtriple_fast [:: [:: 0; 1]; [:: 2; 3]] [:: [:: 0; 1]; [:: 2; 3]])
                  (enum_stdtabsh [:: 4; 4]).
*)
