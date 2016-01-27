(** * Combi.Combi.tableau : Young Tableaux *)
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
(** * Young Tableaux over an [ordtype]

We define the notion of (semistandard) Young tableau over an [ordType]
denoted [T].

- [is_row r] == r is sorted
- [dominate u v] == u dominate v, that is v is longer than u and
            the i-th letter of u is strictly larger than the i-th letter of v.
            this is a order.
- [is_tableau t] == t of type [(seq (seq T))] is a tableau that is a sequence
                    of non empty rows which is sorted for the dominate order.
- [get_tab t r c] == the element of t of coordinate (r c), or [inhabitant T]
                    if (r, c) is not is the tableau
- [to_word t] == the row reading of the tableau t
- [size_tab t] == the size (number of boxes) of t
- [filter_gtnX_tab n t] == the sub-tableau of t formed by the element smaller
                   than [n].

- [tabsh_reading sh w] == w is the row reading of a tableau of shape sh
*****)

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import path sorted.
Require Import tools partition ordtype sorted.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope N.

(** ** Specialization of sorted Lemmas *)
Section Rows.

  Variable T : inhOrdType.

  Implicit Type l : T.
  Implicit Type r : seq T.

  Notation is_row r := (sorted (@leqX_op T) r).

  Definition is_row1P Z r := sorted1P Z (@leqX_op T) r.
  Definition is_rowP Z r := sortedP Z (@leqX_trans T) (@leqXnn T) r.
  Definition is_row_cons := sorted_cons (@leqXnn T).
  Definition is_row_consK := sorted_consK (R := @leqX_op T).
  Definition is_row_rcons := sorted_rcons (R := @leqX_op T).
  Definition is_row_rconsK := sorted_rconsK (R := @leqX_op T).
  Definition is_row_last := sorted_last (@leqXnn T).
  Definition is_row_take := sorted_take (R := @leqX_op T).
  Definition is_row_drop := sorted_drop (R := @leqX_op T).
  Definition is_row_catL := sorted_catL (R := @leqX_op T).
  Definition is_row_catR := sorted_catR (R := @leqX_op T).
  Definition head_leq_last_row := head_leq_last_sorted (@leqX_trans T) (@leqXnn T).
  Lemma row_lt_by_pos Z r p q:
    is_row r -> p < size r -> q < size r -> (nth Z r p < nth Z r q)%Ord -> p < q.
  Proof.
    rewrite /ltnX_op. apply: (sorted_lt_by_pos (@leqX_trans T) (@leqXnn T) (@anti_leqX T)). 
  Qed.

End Rows.

Notation is_row r := (sorted (@leqX_op _) r).

(** ** Dominance order for rows *)
Section Dominate.

  Variable T : inhOrdType.
  Notation Z := (inhabitant T).

  Implicit Type l : T.
  Implicit Type r u v : seq T.

Lemma is_row_set_nth l r pos :
  is_row r -> (l < nth l r pos)%Ord ->
  (forall n : nat, (l < nth l r n)%Ord -> pos <= n) -> is_row (set_nth l r pos l).
Proof.
  move=> /is_row1P Hrow Hl Hmin. apply/(is_row1P l) => i.
  rewrite (lock (i.+1)) !nth_set_nth /=; unlock.
  case: (ltnP pos (size r)) Hl => [Hpos Hl |HH]; last by rewrite (nth_default l HH) ltnXnn.
  rewrite size_set_nth maxnC /maxn; move: Hpos; rewrite leqNgt; move/negbTE => -> Hi1lt.
  case eqP => Hipos; case eqP => Hi1pos.
  - exact: leqXnn.
  - apply: ltnXW; apply: (ltnX_leqX_trans Hl); rewrite -Hipos; exact: Hrow.
  - move: {Hmin} (contra (Hmin i)); rewrite -leqXNgtnX -ltnNge; apply.
    by rewrite Hi1pos leqnn.
  - exact: Hrow.
Qed.

  Definition dominate u v :=
    ((size u) <= (size v)) && (all (fun i => (nth Z u i > nth Z v i)%Ord) (iota 0 (size u))).

  Lemma dominateP u v :
    reflect ((size u) <= (size v) /\ forall i, i < size u -> (nth Z u i > nth Z v i)%Ord)
            (dominate u v).
  Proof.
    rewrite /dominate /mkseq ; apply/(iffP idP).
    - move=> /andP [] Hsz /allP Hall; split; first by exact Hsz.
      move=> i Hi; apply: Hall; by rewrite mem_iota add0n.
    - move=> [] -> /= H; apply/allP => i; rewrite mem_iota add0n; exact: H.
  Qed.

  Lemma dominate_nil u : dominate [::] u.
  Proof. apply/dominateP => /=; by split. Qed.

  Lemma dominate_trans r0 r1 r2 :
    dominate r0 r1 -> dominate r1 r2 -> dominate r0 r2.
  Proof.
    move=> /dominateP [] Hsz0 Hdom0 /dominateP [] Hsz1 Hdom1.
    apply/dominateP; split; first exact: (leq_trans Hsz0 Hsz1).
    move => i Hi.
    apply (ltnX_trans (Hdom1 i (leq_trans Hi Hsz0))).
    exact: Hdom0.
  Qed.

  Lemma dominate_rcons v u l : dominate u v -> dominate u (rcons v l).
  Proof.
    move /dominateP => [] Hsz Hlt.
    apply/dominateP; split => [|i Hi]; first by rewrite size_rcons; apply: leqW.
    move/(_ _ Hi) : Hlt; rewrite nth_rcons.
    case: (ltnP i (size v)) => //= /(leq_trans Hsz)/leq_ltn_trans/(_ Hi).
    by rewrite ltnn.
  Qed.

  Lemma dominate_rconsK u v l :
    size u <= size v -> dominate u (rcons v l) -> dominate u v.
  Proof.
    move=> Hsz /dominateP [] _ Hlt.
    apply/dominateP; split => [|i Hi]; first exact Hsz.
    move/(_ _ Hi) : Hlt; by rewrite nth_rcons (leq_trans Hi Hsz).
  Qed.

  Lemma dominate_head u v : u != [::] -> dominate u v -> (head Z v < head Z u)%Ord.
  Proof.
    move=> Hu /dominateP []; case: u Hu => [//=|u0 u _]; case: v => [|v0 v _] /=.
    - by rewrite ltn0.
    - move=> Hdom; exact: (Hdom 0 (ltn0Sn _)).
  Qed.

  Lemma dominate_tl a u b v :
    dominate (a :: u) (b :: v) -> dominate u v.
  Proof.
    move=> /dominateP [] /=; rewrite ltnS => Hsize Hdom.
    apply/dominateP; split; first exact Hsize.
    move=> i Hi; exact: (Hdom i.+1 Hi).
  Qed.

End Dominate.


(** * Tableaux : definition and basic properties *)
Section Tableau.

  Variable T : inhOrdType.
  Notation Z := (inhabitant T).

  Implicit Type l : T.
  Implicit Type r w : seq T.
  Implicit Type t : seq (seq T).

  Fixpoint is_tableau t :=
    if t is t0 :: t'
    then [&& (t0 != [::]), is_row t0, dominate (head [::] t') t0 & is_tableau t']
    else true.

  Definition get_tab (t : seq (seq T)) (r c : nat) :=
    nth (inhabitant T) (nth [::] t r) c.

  Definition to_word t := flatten (rev t).

  (* Shape is defined in seq.v *)
  (* Definition shape t := map size t. *)

  Lemma is_tableauP t : reflect
    [/\ forall i, i < size t -> (nth [::] t i) != [::], (* forbid empty lines *)
     forall i, is_row (nth [::] t i) &
     forall i j, i < j -> dominate (nth [::] t j) (nth [::] t i)]
    (is_tableau t).
  Proof.
    apply (iffP idP).
    - elim: t => [_ | t0 t IHt] /=.
        split=> i //=; first by rewrite nth_default.
        move=> j; by rewrite !nth_default.
      move=> /and4P [] Ht0 Hrow0 Hdom0 /IHt {IHt} [] Hnnil Hrow Hdom.
      split; try by case.
      case=> [| i] [| j] //=.
      + case: j => [|j] _; first by rewrite nth0.
        apply: (dominate_trans _ Hdom0).
        rewrite -nth0; exact: Hdom.
      + rewrite ltnS; exact: Hdom.
    - elim: t => [| t0 t IHt] //= [] Hnnil Hrow Hdom.
      apply/and4P; split.
      + exact: (Hnnil 0).
      + exact: (Hrow 0).
      + move: Hdom; case t => [| t1 tt] //= H.
        rewrite -/(nth [::] (t0 :: t1 :: tt) 0) -/(nth [::] (t0 :: t1 :: tt) 1).
        exact: H.
      + apply IHt; split => [i H | i | i j H].
        * exact: (Hnnil i.+1).
        * exact: (Hrow i.+1).
        * exact: (Hdom i.+1 j.+1).
  Qed.

  Lemma get_tab_default t (r c : nat) : ~~ is_in_shape (shape t) r c -> get_tab t r c = Z.
  Proof. rewrite /is_in_shape /get_tab -leqNgt nth_shape => Hc; exact: nth_default. Qed.

  Lemma to_word_cons r t : to_word (r :: t) = to_word t ++ r.
  Proof. by rewrite /to_word rev_cons flatten_rcons. Qed.
  Lemma to_word_rcons r t : to_word (rcons t r) = r ++ to_word t.
  Proof. by rewrite /to_word rev_rcons /=. Qed.

  Lemma mem_to_word t (r c : nat) :
    is_in_shape (shape t) r c -> (get_tab t r c) \in (to_word t).
  Proof.
    rewrite /is_in_shape /get_tab.
    elim: t r c => [//= | t0 t IHt] /= r c; first by rewrite nth_default.
    rewrite to_word_cons mem_cat => H.
    case: r H => [/mem_nth ->| r] /=; first by rewrite orbT.
    by move/IHt ->.
  Qed.

  Lemma to_wordK t : rev (reshape (rev (shape t)) (to_word t)) = t.
  Proof. by rewrite -shape_rev /to_word flattenK revK. Qed.

  Lemma tableau_is_row r t : is_tableau (r :: t) -> is_row r.
  Proof. by move=> /= /and4P []. Qed.

  Lemma  is_tableau_rconsK t (tn : seq T) :
    is_tableau (rcons t tn) -> is_tableau t.
  Proof.
    elim: t => [//= | t0 t IHt] /= /and4P [] -> -> Hdom /IHt -> /= {IHt}.
    case: t Hdom => [//=| t1 t]; by rewrite rcons_cons /= => ->.
  Qed.

  Lemma is_part_sht t : is_tableau t -> is_part (shape t).
  Proof.
    elim: t => [//= | t0 t IHt] /= /and4P [] Ht0 _ /dominateP [] Hdom _ Htab.
    rewrite (IHt Htab) andbT {IHt Htab} /shape.
    case: t Hdom => //=; by case: t0 Ht0.
  Qed.

  Lemma tab_eqP p q :
    is_tableau p -> is_tableau q -> reflect (forall i, nth [::] p i = nth [::] q i) (p == q).
  Proof.
    move=> Hp Hq.
    apply (iffP idP) => [/eqP -> //| H].
    have Hnth t i : nth 0 (shape t) i = size (nth [::] t i).
      case: (ltnP i (size t)) => Hi.
      - by rewrite /shape (nth_map [::] _ _ Hi).
      - by rewrite !nth_default // size_map.
    have Hsz : size p = size q.
      rewrite -!(size_map size); congr (size _).
      apply/eqP/(part_eqP (is_part_sht Hp) (is_part_sht Hq)) => i.
      by rewrite !Hnth H.
    apply/eqP; by apply (eq_from_nth (x0 := [::]) Hsz) => i _.
  Qed.

  Lemma is_tableau_sorted_dominate (t : seq (seq T)) :
    is_tableau t =
    [&& is_part (shape t), all (sorted (@leqX_op T)) t & sorted (fun x y => dominate y x) t].
  Proof.
    apply/idP/idP; elim: t => [//= | t0 t IHt].
    - move=> /=/and4P [] Hnnil Hrow0 Hdom /IHt /and3P [] Hpart Hall Hsort.
      rewrite Hpart Hrow0 Hall {Hpart Hrow0 Hall IHt} !andbT /=; apply/andP; split.
      + case: t Hdom {Hsort} => [_ | t1 t] /=; first by case: t0 Hnnil.
        by move => /dominateP [].
      + by case: t Hdom Hsort => [//=| t1 t]/= -> ->.
    - move=>/and3P [] Hpart.
      have:= part_head_non0 Hpart.
      rewrite [head _ _]/= [all _ _]/= [is_tableau _]/=.
      move=> /nilP /eqP -> /andP [] -> Hall Hsort /=.
      apply/andP; split.
      + by case: t Hsort {Hpart Hall IHt} => [//= | t1 t] /= /andP [].
      + apply: IHt; rewrite (is_part_consK Hpart) Hall /=.
        exact: (sorted_consK Hsort).
  Qed.

  Lemma is_tableau_getP (t : seq (seq T)) :
    reflect
      [/\ is_part (shape t),
       (forall (r c : nat), is_in_shape (shape t) r c.+1 ->
                    ((get_tab t r c) <= (get_tab t r c.+1))%Ord) &
       (forall (r c : nat), is_in_shape (shape t) r.+1 c ->
                    ((get_tab t r c) < (get_tab t r.+1 c)))%Ord]
      (is_tableau t).
  Proof.
    apply/(iffP idP).
    - move=> Htab; split.
      + exact: is_part_sht.
      + rewrite /is_in_shape /get_tab => r c Hrc.
        move: Htab => /is_tableauP [] _ Hrow _.
        apply: (is_row1P _ _ (Hrow r)); by rewrite -nth_shape.
      + rewrite /is_in_shape /get_tab => r c Hrc.
        move: Htab => /is_tableauP [] _ _ Hdom.
        have := dominateP _ _ (Hdom _ _ (ltnSn r)) => [] [] _; apply.
        by rewrite -nth_shape.
    - move=> [] Hpart Hrow Hcol.
      apply/is_tableauP; split.
      + move=> i Hi.
        have:= nth_part_non0 Hpart; rewrite size_map => H.
        have {H} := H _ Hi.
        apply contra => /eqP.
        by rewrite nth_shape => ->.
      + move=> r; apply/(is_row1P (inhabitant T)) => c.
        rewrite -nth_shape => /Hrow; by apply.
      + move=> i j Hij; case: (ltnP j (size t)) => Hjr.
        * have H : i < j < size t by rewrite Hij Hjr.
          have Htrans : transitive (fun x : seq T => (@dominate T)^~ x).
            move=> a b c /= Hab Hca; exact: dominate_trans Hca Hab.
          move: i j H {Hij Hjr}; rewrite (incr_equiv [::] Htrans t) => i Hi.
          apply/dominateP; rewrite -!nth_shape.
          split; first by have:= is_partP _ Hpart => [] [] _; apply.
          move=> j; by rewrite -/(is_in_shape _ _ _) -!/(get_tab _ _ _) => /Hcol ->.
        * rewrite (nth_default _ Hjr); exact: dominate_nil.
  Qed.

Lemma filter_gtnX_row r n :
  is_row r -> filter (gtnX n) r = take (count (gtnX n) r) r.
Proof.
  elim: r => [//= | r0 r IHr] Hrow /=.
  case: (ltnXP r0 n) => Hr0.
  - by rewrite add1n (IHr (is_row_consK Hrow)).
  - rewrite add0n; have Hcount : count (gtnX n) r = 0.
      elim: r r0 Hr0 Hrow {IHr} => [//= | r1 r /= IHr] r0 Hr0 /andP [] Hr0r1 Hpath.
      have Hr1 := leqX_trans Hr0 Hr0r1.
      by rewrite ltnXNgeqX Hr1 (IHr r1 Hr1 Hpath).
    rewrite Hcount.
    by apply/nilP; rewrite /nilp size_filter Hcount.
Qed.

Lemma count_gtnX_dominate r1 r0 n :
  dominate r1 r0 -> (count (gtnX n) r1) <= (count (gtnX n) r0).
Proof.
  move=> /dominateP [] Hsz Hdom.
  rewrite -[r0](mkseq_nth Z) -[r1](mkseq_nth Z) /mkseq !count_map.
  rewrite -(subnKC Hsz).
  rewrite iota_add count_cat.
  set s0 := (X in X + _).
  apply (@leq_trans s0); last exact: leq_addr.
  rewrite /s0 {s0} -!size_filter.
  set f1 := (X in filter X ); set f0 := (X in _ <= size (filter X _)).
  rewrite (eq_in_filter (a1 := f1) (a2 := predI f1 (gtn (size r1)))); first last.
    move=> i; rewrite mem_iota /= add0n => ->; by rewrite andbT.
  rewrite (eq_in_filter (a1 := f0) (a2 := predI f0 (gtn (size r1)))); first last.
    move=> i; rewrite mem_iota /= add0n => ->; by rewrite andbT.
  rewrite !size_filter; apply sub_count => i /=.
  rewrite /f1 /f0 {f1 f0} /= => /andP [] Hn Hi.
  rewrite Hi andbT.
  exact: (ltnX_trans (Hdom i Hi) Hn).
Qed.

Lemma filter_gtnX_dominate r1 r0 n :
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    dominate (filter (gtnX n) r1) (filter (gtnX n) r0).
Proof.
  move=> Hrow0 Hrow1 Hdom.
  have Hsize := count_gtnX_dominate n Hdom.
  move: Hdom => /dominateP [] Hsz Hdom.
  apply/dominateP; rewrite !size_filter.
  split; first exact Hsize.
  move=> i Hi.
  rewrite (filter_gtnX_row _ Hrow0) (filter_gtnX_row _ Hrow1) !nth_take.
  - apply Hdom; apply (leq_trans Hi); exact: count_size.
  - exact: Hi.
  - exact: (leq_trans Hi).
Qed.

Definition filter_gtnX_tab n :=
  [fun t : (seq (seq T)) => filter (fun r => r != [::])
                                   [seq [seq x <- i | gtnX n x] | i <- t]].

Lemma to_word_filter_nnil t : to_word (filter (fun r => r != [::]) t) = to_word t.
Proof.
  elim: t => [//= | t0 t IHt] /=.
  rewrite to_word_cons -IHt.
  case: (altP (t0 =P [::])) => [-> | _] /=; first by rewrite cats0.
  by rewrite to_word_cons.
Qed.

Lemma filter_to_word t p : filter p (to_word t) = to_word (map (filter p) t).
Proof.
    elim: t => [//= | t0 t IHt] /=.
    by rewrite !to_word_cons -IHt filter_cat.
Qed.

Lemma head_filter_gtnX_tab n t :
  is_tableau t ->
  head [::] (filter_gtnX_tab n t) = [seq x <- head [::] t | (x < n)%Ord].
Proof.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil0 Hrow0 Hdom Htab.
  case: (altP ([seq x <- t0 | (x < n)%Ord] =P [::])) => Ht0 //=.
  rewrite (IHt Htab) Ht0 {IHt}.
  case: t Hdom Htab => [//= | t1 t] /= Hdom /and3P [] Hnnil1 Hrow1 _.
  have /dominateP := filter_gtnX_dominate n Hrow0 Hrow1 Hdom => [] [].
  by rewrite Ht0 /= leqn0 => /nilP ->.
Qed.

Lemma is_tableau_filter_gtnX t n : is_tableau t -> is_tableau (filter_gtnX_tab n t).
Proof.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil Hrow Hdom Htab.
  case: (altP ([seq x <- t0 | (x < n)%Ord] =P [::])) => Ht0 /=; first exact: IHt.
  rewrite Ht0 /=; apply/and3P; split; last exact: IHt.
  - apply sorted_filter; last exact Hrow.
    move=> a b c; exact: leqX_trans.
  - rewrite (head_filter_gtnX_tab _ Htab).
    apply filter_gtnX_dominate => //=.
    move: Htab; by case t => [//= | t1 t'] /= /and3P [].
Qed.


Definition size_tab t := sumn (shape t).

Lemma tab0 t : is_tableau t -> size_tab t = 0 -> t = [::].
Proof.
  move/is_part_sht; rewrite /size_tab => /part0 H/H{H}.
  rewrite /shape; by case t.
Qed.

Lemma size_to_word t : size (to_word t) = size_tab t.
Proof.
  rewrite /size_tab; elim: t => [//= | t0 t IHt] /=.
  by rewrite to_word_cons size_cat IHt addnC.
Qed.

End Tableau.


Section TableauReading.

Variable A : inhOrdType.

Definition tabsh_reading (sh : seq nat) (w : seq A) :=
  (size w == sumn sh) && (is_tableau (rev (reshape (rev sh) w))).

Lemma tabsh_readingP (sh : seq nat) (w : seq A) :
  reflect
    (exists tab, [/\ is_tableau tab, shape tab = sh & to_word tab = w])
    (tabsh_reading sh w).
Proof.
  apply (iffP idP).
  - move=> /andP [] /eqP Hsz Htab.
    exists (rev (reshape (rev sh) w)); split => //.
    rewrite shape_rev -{2}(revK sh); congr (rev _).
    apply: reshapeKl; by rewrite sumn_rev Hsz.
    rewrite /to_word revK; apply: reshapeKr; by rewrite sumn_rev Hsz.
  - move=> [] tab [] Htab Hsh Hw; apply/andP; split.
    + by rewrite -Hw size_to_word /size_tab Hsh.
    + rewrite -Hw /to_word -Hsh.
      by rewrite /shape -map_rev -/(shape _) flattenK revK.
Qed.

End TableauReading.


Section FinType.

Variable n : nat.
(* Should be Variable A : finOrdType *)

Variable d : nat.
Variable sh : intpartn d.

Definition is_tab_of_shape sh :=
  [pred t | (is_tableau (T := [inhOrdType of 'I_n.+1]) t) && (shape t == sh) ].

Structure tabsh : predArgType :=
  TabSh {tabshval :> seq (seq 'I_n.+1); _ : is_tab_of_shape sh tabshval}.
Canonical tabsh_subType := Eval hnf in [subType for tabshval].
Definition tabsh_eqMixin := Eval hnf in [eqMixin of tabsh by <:].
Canonical tabsh_eqType := Eval hnf in EqType tabsh tabsh_eqMixin.
Definition tabsh_choiceMixin := Eval hnf in [choiceMixin of tabsh by <:].
Canonical tabsh_choiceType := Eval hnf in ChoiceType tabsh tabsh_choiceMixin.
Definition tabsh_countMixin := Eval hnf in [countMixin of tabsh by <:].
Canonical tabsh_countType := Eval hnf in CountType tabsh tabsh_countMixin.
Canonical tabsh_subCountType := Eval hnf in [subCountType of tabsh].

Lemma tabshP (t : tabsh) : is_tableau t.
Proof. by case: t => t /= /andP []. Qed.

Lemma shape_tabsh (t : tabsh) : shape t = sh.
Proof. by case: t => t /= /andP [] _ /eqP. Qed.

Require Import tuple.

Lemma tabsh_to_wordK (t : tabsh) :
  rev (reshape (rev sh) (to_word (val t))) = t.
Proof. rewrite /= -(shape_tabsh t); exact: to_wordK. Qed.

Let tabsh_enum : seq tabsh :=
  pmap insub [seq rev (reshape (rev sh) (val w)) | w in [finType of d.-tuple 'I_n.+1]].
Lemma finite_tabsh : Finite.axiom tabsh_enum.
Proof.
  case=> /= t Ht; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  move: Ht => /andP [] Htab /eqP Hsh.
  rewrite count_map.
  have Htw : size (to_word t) == d.
    by rewrite size_to_word /size_tab Hsh intpartn_sumn.
  rewrite (eq_in_count (a2 := pred1 (Tuple Htw))).
    rewrite enumT; exact: enumP (Tuple Htw).
  move=> w _ /=; apply/idP/idP.
  - move=> /eqP Ht; subst t.
    apply/eqP/val_inj => /=; rewrite /to_word revK.
    apply esym; apply: reshapeKr; by rewrite sumn_rev size_tuple intpartn_sumn.
  - move=> /eqP Hw; subst w; rewrite /=.
    by rewrite /to_word -Hsh -shape_rev flattenK revK.
Qed.

Canonical tabsh_finMixin := Eval hnf in FinMixin finite_tabsh.
Canonical tabsh_finType := Eval hnf in FinType tabsh tabsh_finMixin.
Canonical tabsh_subFinType := Eval hnf in [subFinType of tabsh_countType].


Lemma to_word_enum_tabsh :
  perm_eq
    [seq to_word (tabshval t) | t <- enum tabsh]
    [seq x <- [seq val i | i <- enum [finType of d.-tuple 'I_n.+1]]
    | tabsh_reading sh x].
Proof.
  apply uniq_perm_eq.
  - rewrite map_inj_in_uniq; first exact: enum_uniq.
    move=> t u _ _ /= Heq; apply val_inj.
    by rewrite /= -(tabsh_to_wordK t) -(tabsh_to_wordK u) Heq /=.
  - apply filter_uniq; rewrite map_inj_uniq; last exact: val_inj.
    exact: enum_uniq.
  move=> w /=; rewrite /tabsh_reading mem_filter; apply/idP/idP.
  - move=> /mapP [] t _ -> {w}.
    rewrite size_to_word /size_tab shape_tabsh eq_refl /=.
    rewrite tabsh_to_wordK tabshP /=.
    have Ht : size (to_word (val t)) == d.
      by rewrite size_to_word /size_tab shape_tabsh intpartn_sumn.
    have -> : to_word (val t) = val (Tuple Ht) by [].
    rewrite mem_map; last exact: val_inj.
    exact: mem_enum.
  - move=> /andP [] /andP [] /eqP Hsz Htab /mapP [] tpl _ hw; subst w.
    have Htsh : is_tab_of_shape sh (rev (reshape (rev sh) tpl)).
      rewrite /is_tab_of_shape /= Htab /= shape_rev reshapeKl ?revK //.
      by rewrite sumn_rev Hsz.
    suff -> : val tpl = to_word (TabSh Htsh).
      apply/mapP; exists (TabSh Htsh) => //; exact: mem_enum.
    rewrite /= /to_word revK reshapeKr //.
    by rewrite sumn_rev Hsz.
Qed.

End FinType.
