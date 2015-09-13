Require Import Arith.
Require Import List.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.

Section BraceFacts.

Inductive Brace : Set :=
  | Open : Brace | Close : Brace.

Lemma eq_brace_dec :
  forall b1 b2 : Brace, {b1 = b2} + {b1 <> b2}.
Proof.
  induction b1; induction b2.
  left; auto.
  right; unfold not; intro; inversion H.
  right; unfold not; intro; inversion H.
  left; auto.
Defined.

Lemma if_close_close :
  (if eq_brace_dec Close Close then 1 else 0) = 1.
Proof.
  destruct (eq_brace_dec Close Close); intros; auto with arith.
  destruct n; auto.
Qed.

Lemma if_close_open :
  (if eq_brace_dec Close Open then 1 else 0) = 0.
Proof.
  destruct (eq_brace_dec Close Open); intros; auto with arith.
  inversion e.
Qed.

Lemma if_open_close :
  (if eq_brace_dec Open Close then 1 else 0) = 0.
Proof.
  destruct (eq_brace_dec Open Close); intros; auto with arith.
  inversion e.
Qed.

Lemma if_open_open :
  (if eq_brace_dec Open Open then 1 else 0) = 1.
Proof.
  destruct (eq_brace_dec Open Open); intros; auto with arith.
  destruct n; auto.
Qed.

End BraceFacts.

Section DyckWord.

Fixpoint dyck_height (h : nat) (w : list Brace) : Prop :=
  match w with
    | nil => h = 0
    | Open::tlb => dyck_height (S h) tlb
    | Close::tlb =>
      match h with
        | 0    => False
        | S hh => dyck_height hh tlb
      end
  end.

Definition is_dyck (w : list Brace) : Prop := dyck_height 0 w.

Lemma nil_is_dyck : is_dyck nil.
Proof.
  compute; auto.
Qed.

Lemma hat_is_dyck : is_dyck (Open::Close::nil).
Proof.
  compute; auto.
Qed.

Lemma dyck_height_dec :
  forall (w : list Brace) (h : nat),
    {dyck_height h w} + {~ dyck_height h w}.
Proof.
  induction w.
  destruct h; [ left | right ]; compute; auto.
  intro H; inversion H.
  case a; intro h.
  elim (IHw (S h)); intro H; [ left | right ]; assumption.
  destruct h.
  simpl; right; auto.
  elim (IHw h); intros H.
  left; simpl; auto.
  right; simpl; auto.
Defined.

Lemma dyck_height_unique:
  forall (w : list Brace) (h1 h2 : nat),
    dyck_height h1 w -> dyck_height h2 w -> h1 = h2.
Proof.
  induction w.
  intros h1 h2 H1 H2.
  simpl in H1; simpl in H2; rewrite H1, H2; reflexivity.
  case a; intros h1 h2 H1 H2.
  simpl in H1; simpl in H2.
  apply eq_add_S.
  apply IHw; assumption.
  simpl in H1, H2.
  case h1, h2; auto with arith.
Qed.

Lemma is_dyck_dec:
  forall w : list Brace, {is_dyck w} + {~ is_dyck w}.
Proof.
  intro w.
  unfold is_dyck.
  apply dyck_height_dec.
Defined.

Lemma conc_is_dyck_height:
  forall w1 : list Brace, is_dyck w1 ->
    forall (h : nat) (w : list Brace), dyck_height h w -> dyck_height h (w ++ w1).
Proof.
  intros w1 H1 h w.
  generalize h; clear h.
  induction w.
  intro h.
  simpl.
  intro H; rewrite H; assumption.
  intro h; case a; simpl.
  apply IHw.
  case h; auto.
Qed.

Lemma conc_is_dyck:
  forall w1 w2 : list Brace, is_dyck w1 -> is_dyck w2 -> is_dyck (w1 ++ w2).
Proof.
  intros w1 w2 Hd1 Hd2.
  unfold is_dyck.
  apply conc_is_dyck_height; auto.
Qed.

Lemma conc_dyck_inv1_height :
  forall (w1 w2 : list Brace) (h : nat),
    dyck_height h w1 -> dyck_height h (w1 ++ w2) -> is_dyck w2.
Proof.
  induction w1.
  intros w2 h H H0.
  destruct h; auto.
  inversion H.
  intros w2 h H H0.
  destruct a; simpl in H0; simpl in H.
  apply IHw1 with (S h); auto.
  destruct h; auto.
  exfalso; auto.
  apply IHw1 with h; auto.
Qed.

Lemma conc_dyck_inv1:
  forall w1 w2 : list Brace,
    is_dyck w1 -> is_dyck (w1 ++ w2) -> is_dyck w2.
Proof.
  unfold is_dyck; intros w1 w2 H0 H1.
  apply conc_dyck_inv1_height with w1 0; auto.
Qed.

Lemma conc_dyck_inv2_height:
  forall (w1 w2 : list Brace) (h : nat),
    is_dyck w2 -> dyck_height h (w1 ++ w2) -> dyck_height h w1.
Proof.
  induction w1.
  intros w2 h H H0.
  destruct h; simpl; auto.
  simpl in H0.
  unfold is_dyck in H.
  apply dyck_height_unique with nil; auto.
  absurd (S h = 0); auto.
  apply dyck_height_unique with w2; auto.
  compute; auto.
  intros w2 h H H0.
  destruct a.
  simpl; simpl in H0.
  apply IHw1 with w2; auto.
  simpl; simpl in H0.
  destruct h; auto.
  apply IHw1 with w2; auto.
Qed.

Lemma conc_dyck_inv2:
  forall w1 w2 : list Brace,
    is_dyck w2 -> is_dyck (w1 ++ w2) -> is_dyck w1.
Proof.
  unfold is_dyck; intros w1 w2 H0 H1.
  apply conc_dyck_inv2_height with w2; auto.
Qed.


Fixpoint proper_dyck_height (h : nat) (w : list Brace) : Prop :=
  match w with
    | nil => False
    | Open::tlb => proper_dyck_height (S h) tlb
    | Close::nil => h = 1
    | Close::tlb => match h with
                        | 0 => False
                        | S hh => hh > 0 /\ proper_dyck_height hh tlb
                    end
  end.

Lemma proper_dyck_height_dec :
  forall (w : list Brace) (h : nat),
    {proper_dyck_height h w} + {~ proper_dyck_height h w}.
Proof.
  induction w; intro h.
  right; simpl; tauto.
  case a.
  elim IHw with (S h); intro H; [ left | right ]; simpl; auto.
  destruct h.
  destruct w; right; simpl; auto.
  destruct w.
  destruct h; [ left | right ]; simpl; auto.
  destruct h.
  right; simpl.
  intro H; decompose [and] H; clear H H1.
  inversion H0; inversion H1.
  elim IHw with (S h); intros H.
  left; simpl; auto.
  split; auto.
  auto with arith.
  right; simpl; auto.
  tauto.
Defined.

Lemma proper_is_dyck_height :
  forall (h : nat) (w : list Brace), proper_dyck_height h w -> dyck_height h w.
Proof.
  intros h w.
  generalize h; clear h.
  induction w.
  intros h H; simpl in H; tauto.
  intros h H; destruct a.
  simpl in H|-*.
  apply IHw; auto.
  destruct w.
  simpl in H|-*.
  rewrite H; auto.
  destruct h; simpl in H|-*; auto.
  apply IHw.
  decompose [and] H.
  apply H.
Qed.

Inductive proper_height_factor (h : nat) (w : list Brace) : Set :=
  height_factor : forall w1 w2 : list Brace,
                    proper_dyck_height h w1 -> w = (w1 ++ w2) -> proper_height_factor h w.

Lemma proper_dyck_height_factor :
  forall (w : list Brace) (h : nat), w <> nil -> dyck_height h w -> proper_height_factor h w.
Proof.
  induction w; intros h H.
  tauto.
  clear H; intro H.
  destruct a; simpl in H.
  elim IHw with (S h).
  intros w1 w2 Hp Hconc.
  apply height_factor with (Open :: w1) w2.
  simpl; auto.
  rewrite Hconc; simpl; auto.
  destruct w.
  simpl in H; inversion H.
  auto with datatypes.
  assumption.
  destruct w.
  destruct h.
  contradiction H.
  simpl in H; rewrite H.
  apply height_factor with (Close :: nil) nil.
  simpl; auto.
  auto with datatypes.
  destruct h.
  contradiction H.
  elim IHw with h.
  intros w1 w2 Hp Hconc.
  destruct h; auto with arith.
  apply height_factor with (Close :: nil) (b :: w).
  simpl; auto with arith.
  auto with datatypes.
  apply height_factor with (Close :: w1) w2.
  destruct w1.
  simpl in Hp; tauto.
  simpl; split.
  auto with arith.
  apply Hp.
  rewrite Hconc; auto with datatypes.
  auto with datatypes.
  assumption.
Defined.


Definition proper_dyck (w : list Brace) : Prop := proper_dyck_height 0 w.

Lemma hat_proper_dyck : proper_dyck (Open::Close::nil).
Proof.
  compute; auto.
Qed.

Lemma proper_is_dyck :
  forall w : list Brace, proper_dyck w -> is_dyck w.
Proof.
  unfold proper_dyck; unfold is_dyck.
  intros w H; apply proper_is_dyck_height; auto.
Qed.

Lemma dyck_factor :
  forall w : list Brace,
    w <> nil -> is_dyck w ->
    { factor : list Brace * list Brace |
      let (w1, w2) := factor in proper_dyck w1 /\ w = w1 ++ w2 }.
Proof.
  intros w wnil dw.
  elim proper_dyck_height_factor with w 0; auto.
  intros w1 w2 pw1 H.
  exists (w1, w2).
  split; auto.
Defined.

Lemma dyck_factor_height_unique :
  forall (w : list Brace) (h : nat) (wa1 wa2 wb1 wb2 : list Brace),
    dyck_height h w ->
    proper_dyck_height h wa1 -> w = wa1 ++ wa2 ->
    proper_dyck_height h wb1 -> w = wb1 ++ wb2 ->
    wa1 = wb1 /\ wa2 = wb2.
Proof.
  induction w; intros h wa1 wa2 wb1 wb2 Hd Hpa Hca Hpb Hcb.

  split;
    elim app_eq_nil with Brace wa1 wa2; [intros Ha1n Ha2n | auto | intros Ha1n Ha2n | auto ];
    elim app_eq_nil with Brace wb1 wb2; [intros Hb1n Hb2n | auto | intros Hb1n Hb2n | auto ];
    auto with datatypes.
  rewrite Ha1n; rewrite Hb1n; auto.
  rewrite Ha2n; rewrite Hb2n; auto.

  destruct a.
  destruct wa1.
  simpl in Hpa; contradiction.
  destruct b.
  destruct wb1.
  simpl in Hpb; contradiction.
  destruct b.

  elim IHw with (S h) wa1 wa2 wb1 wb2.
  intros Heq1 Heq2.
  rewrite Heq1; auto.

  simpl in Hd; auto.
  simpl in Hpa; auto.
  simpl in Hca; inversion Hca; auto.
  simpl in Hpb; auto.
  simpl in Hcb; inversion Hcb; auto.
  simpl in Hcb; inversion Hcb.
  simpl in Hca; inversion Hca.

  destruct h.
  simpl in Hd; contradiction.

  simpl in Hd.
  destruct wa1.
  simpl in Hpa; contradiction.
  destruct b.
  inversion Hca; simpl in Hca.
  destruct wb1.
  simpl in Hpb; contradiction.
  destruct b.
  inversion Hcb; simpl in Hcb.
  destruct h.
  destruct wa1.
  destruct wb1.
  split; auto.
  simpl in Hca, Hcb.
  inversion Hca; rewrite <- H0.
  inversion Hcb; rewrite <- H1.
  auto.
  simpl in Hpb; decompose [and] Hpb; inversion H.
  simpl in Hpa; decompose [and] Hpa; inversion H.
  elim IHw with (S h) wa1 wa2 wb1 wb2.
  intros Heq1 Heq2; rewrite Heq1; auto with datatypes.
  assumption.
  destruct wa1; inversion Hpa.
  apply H0.
  inversion Hca; auto.
  destruct wb1; inversion Hpb.
  apply H0.
  inversion Hcb; auto.
Qed.

Lemma proper_dyck_height_brace :
  forall (w : list Brace) (h : nat),  proper_dyck_height (S h) w ->
    { d : list Brace | dyck_height h d /\ w = d ++ Close :: nil }.
Proof.
  induction w.
  intros h H.
  simpl in H; contradiction.
  intros h H.
  destruct a.
  elim IHw with (S h).
  intros x HH; elim HH; clear HH; intros H0 H1.
  exists (Open::x); split.
  simpl; assumption.
  rewrite H1; auto with datatypes.
  simpl in H; assumption.
  destruct h.
  simpl in H.
  exists nil; split.
  simpl; auto.
  induction w; auto with datatypes.
  elim H; intro HH; inversion HH.
  elim IHw with h.
  intros x HH; elim HH; clear HH; intros Hd Hc.
  exists (Close::x); split.
  simpl; assumption.
  rewrite Hc; auto with datatypes.
  simpl in H.
  destruct w.
  inversion H.
  elim H; clear H; intros H H0.
  assumption.
Defined.

Lemma proper_dyck_brace :
  forall w : list Brace, proper_dyck w ->
    { d : list Brace | is_dyck d /\ w = Open :: d ++ Close :: nil }.
Proof.
  unfold proper_dyck.
  intros w H.
  destruct w.
  simpl in H; contradiction.
  destruct b.
  simpl in H.
  elim proper_dyck_height_brace with w 0.
  intros x H0; elim H0; clear H0; intros H0 H1.
  exists x; split.
  assumption.
  rewrite H1; auto with datatypes.
  simpl; auto.
  simpl in H.
  destruct w; contradict H.
  auto with arith.
Defined.


Theorem dyck_decompose_grammar :
  forall w : list Brace, w <> nil -> is_dyck w ->
    { factor : (list Brace * list Brace) |
      let (w1, w2) := factor in is_dyck w1 /\ is_dyck w2 /\ w = Open :: w1 ++ Close :: w2 }.
Proof.
  intros w H H0.
  elim dyck_factor with w; auto.
  intro x; elim x; clear x.
  intros w1 w2 H1.
  elim H1; clear H1; intros H1 H2.
  elim proper_dyck_brace with w1; auto; intros x HH.
  elim HH; clear HH; intros H3 H4.
  exists (x, w2); split; auto.
  split; auto.
  apply conc_dyck_inv1_height with w1 0.
  apply proper_is_dyck_height; auto.
  rewrite <- H2; auto.
  rewrite H2; rewrite H4.
  simpl.
  rewrite app_assoc_reverse.
  simpl; auto.
Defined.


Lemma dyck_proper_dyck_height :
  forall (w : list Brace) (h : nat),
    dyck_height h w -> proper_dyck_height (S h) (w ++ Close :: nil).
Proof.
  induction w.
  destruct h.
  intro H; compute; auto.
  intro H; simpl in H; inversion H.
  intros h H.
  destruct a.
  simpl.
  apply IHw.
  simpl in H; auto.
  destruct h.
  simpl in H; contradiction.
  simpl in H|-*.
  assert (w ++ Close :: nil <> nil).
  auto with datatypes.
  destruct (w ++ Close :: nil).
  contradiction H0; auto.
  split.
  auto with arith.
  apply IHw; auto.
Qed.

Lemma dyck_proper_dyck :
  forall w : list Brace, is_dyck w -> proper_dyck_height 1 (w ++ Close :: nil).
Proof.
  intros w dw.
  apply dyck_proper_dyck_height.
  auto.
Qed.

Lemma proper_is_proper_dyck :
  forall w : list Brace, is_dyck w -> proper_dyck (Open :: w ++ Close :: nil).
Proof.
  intros w Hdw; unfold proper_dyck; simpl.
  apply dyck_proper_dyck; auto.
Qed.

Lemma grammar_is_dyck:
  forall w1 w2 : list Brace, is_dyck w1 -> is_dyck w2 -> is_dyck (Open :: w1 ++ Close :: w2).
Proof.
  intros w1 w2 dw1 dw2.
  replace (Open :: w1 ++ Close :: w2) with (((Open :: w1) ++ Close :: nil) ++ w2).
  apply conc_is_dyck; auto.
  apply proper_is_dyck.
  simpl.
  apply proper_is_proper_dyck.
  auto.
  rewrite app_assoc_reverse.
  auto with datatypes.
Qed.

Theorem dyck_decompose_unique :
  forall wa1 wa2 wb1 wb2 : list Brace,
    is_dyck wa1 -> is_dyck wa2 -> is_dyck wb1 -> is_dyck wb2 ->
    Open :: wa1 ++ Close :: wa2  = Open :: wb1 ++ Close :: wb2 ->
    wa1 = wb1 /\ wa2 = wb2.
Proof.
  intros wa1 wa2 wb1 wb2 Hda1 Hda2 Hdb1 Hdb2 Heq.
  elim dyck_factor_height_unique with
  ((Open :: wa1 ++ Close :: nil) ++ wa2) 0
                                         (Open :: wa1 ++ Close :: nil) wa2
                                         (Open :: wb1 ++ Close :: nil) wb2.
  intros H Hc; split; auto.
  elim app_inj_tail with Brace wa1 wb1 Close Close; [intros H1 H2 | auto]; auto.
  inversion H; auto.
  apply conc_is_dyck_height; auto.
  apply proper_is_dyck_height.
  apply dyck_proper_dyck; auto.
  apply dyck_proper_dyck; auto.
  reflexivity.
  apply dyck_proper_dyck; auto.
  rewrite ?app_comm_cons.
  rewrite ?app_assoc_reverse.
  auto with datatypes.
Qed.

Lemma lel_app_1:
  forall a b : list Brace, lel a (a ++ b).
Proof.
  unfold lel.
  induction a.
  intro b; simpl; auto with arith.
  intro b; simpl.
  apply le_n_S; auto.
Qed.

Lemma lel_app_2:
  forall a b : list Brace, lel b (a ++ b).
Proof.
  unfold lel.
  induction a.
  intro b; simpl; auto with arith.
  intro b; simpl.
  apply le_trans with (length (a0 ++ b)); auto.
Qed.

Lemma dyck_grammar_length_1 :
  forall w a b : list Brace, w = (Open :: a) ++ (Close :: b) -> length a < length w.
Proof.
  intros w a b H.
  assert (length a < length (Open :: a)).
  simpl; auto with arith.
  assert (lel (Open :: a) w).
  rewrite H.
  apply lel_app_1; auto.
  unfold lel in H1.
  apply lt_le_trans with (length (Open :: a)); auto.
Qed.

Lemma dyck_grammar_length_2 :
  forall w a b : list Brace, w = (Open :: a) ++ (Close :: b) -> length b < length w.
Proof.
  intros w a b H.
  assert (length b < length (Close :: b)).
  simpl; auto with arith.
  assert (lel (Close :: b) w).
  rewrite H.
  apply lel_app_2; auto.
  unfold lel in H1.
  apply lt_le_trans with (length (Close :: b)); auto.
Qed.

End DyckWord.
