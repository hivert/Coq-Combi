
(*
   here we prove the equivalence between definitions from
   - the Coq proof (in directory ..), and
   - the Why3 proof (in file lrrule.mlw)
*)

Add LoadPath "..".
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
(* Require Import tuple finfun finset bigop path. *)
Require Import tools partition yama ordtype tableau std stdtab skewtab.

(* import definitions from Why3 *)
Require Import ssrint ssrwhy3.
Require spec.


Require Import ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
*)

Fixpoint convert_part (a : array int) : (seq nat) :=
  if a is i :: tl then
    match i with
      | Posz 0 => [::]
      | Posz n => n :: (convert_part tl)
      | _      => [::]
    end
  else [::].

Definition convert_part_inv (len : nat) (p : seq nat) : array int :=
  mkseq (fun i => (nth 0 p i):int) len.

Lemma size_convert_part (a : array int) :
  size (convert_part a) <= size a.
Proof.
  elim: a => [//= | a0 a IHa] /=.
  case: a0 => [] //= [] //= n.
Qed.

Lemma nth_getE (a : array int) x i :
  i < size (convert_part a) -> get a i = nth x (convert_part a) i.
Proof.
  elim: a i x => [//= | a0 a IHa] i /=.
  case: a0 => [] //= [] //= a0 x.
  case: i => [| i] //=.
  rewrite ltnS => /IHa; by apply.
Qed.

Lemma convert_part_impl (a : array int) :
  spec.is_part a -> is_part (convert_part a).
Proof.
  move=> H; apply/is_partP; split => [{H} |].
  - move: (X in last X.+1 _) => m.
    elim: a m => [| a0 a IHa] m //.
    by case: a0 => [] // [] // n.
  - move: H => [Hdec Hlast] i.
    case: (ltnP i.+1 (size (convert_part a))) => Hi.
    rewrite -lez_nat -(nth_getE _ Hi) -nth_getE; last by apply: (leq_trans _ Hi).
    apply Hdec; repeat split => //.
    + by rewrite lez_nat.
    + rewrite ltz_nat; apply: (leq_trans Hi).
      by apply size_convert_part.
  - by rewrite nth_default.
Qed.

Lemma get_convert_part_inv len p (i : nat) :
  get (convert_part_inv len p) i = nth 0 p i.
Proof.
  rewrite /get /convert_part_inv /length.
  case: (ltnP i len) => Hi.
  - by rewrite nth_mkseq.
  - rewrite nth_default.
    * admit.
    * by rewrite size_mkseq.
Qed.

Lemma convert_part_inv_impl (p : seq nat) len :
  is_part p -> spec.is_part (convert_part_inv len p).
Proof.
  rewrite /spec.is_part /length.
  elim: p => [| p0 p IHp] /=.
  - move=> _; split => [i j|].
    + rewrite size_mkseq => [] [].
      case: i => [i _ [] | //=].
      rewrite get_convert_part_inv nth_nil.
      case: j => [j _ | //=].
      by rewrite get_convert_part_inv nth_nil.
    + rewrite size_mkseq /=.
      case: len.
      * admit.       (* Problem de get array -1 si len == 0*)
      * admit.
  - admit.
Qed.

Lemma convert_included_size (a b : array int) :
  spec.included a b -> size (convert_part a) <= size (convert_part b).
Proof.
  rewrite /spec.included /length.
  elim: a b => [| a0 a IHa] [|b0 b] [] //= /eqP.
  rewrite eqz_nat eqSS => /eqP Hsize.
  case: a0 => [] //= [] //= a0.
  case: b0 => [[|b0]|b0] H /=.
  - exfalso; by have /H : (0 <= 0%:Z)%R /\ (0%:Z < (size b).+1)%R by [].
  - rewrite ltnS; apply IHa.
    split; first by rewrite Hsize.
    case=> i [] //= _; rewrite ltz_nat => Hi.
    suff /H /= : (0 <= i.+1%:Z)%R /\ (i.+1%:Z < (size b).+1)%R by [].
    split; first by rewrite lez_nat.
    by rewrite ltz_nat ltnS.
  - exfalso; by have /H : (0 <= 0%:Z)%R /\ (0%:Z < (size b).+1)%R by [].
Qed.

Lemma convert_included_impl (a b : array int) :
  spec.included a b -> included (convert_part a) (convert_part b).
Proof.
  move=> H; have Hsize := (convert_included_size H).
  move: H; rewrite /spec.included /length => [] [] Hlen Hincl.
  apply/includedP; split; first exact Hsize.
  move=> i.
  case: (ltnP i (size (convert_part a))) => Hi.
  + rewrite -lez_nat -(nth_getE _ Hi) -nth_getE; last by apply (leq_trans Hi).
    apply Hincl; split; first by [].
    rewrite ltz_nat; apply (leq_trans Hi).
    apply (leq_trans (size_convert_part a)).
    by rewrite -lez_nat Hlen.
  + by rewrite nth_default.
Qed.
