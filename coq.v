Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Lia.

Definition is_perm (l : list nat) (n : nat) : Prop :=
  NoDup l /\
  (forall x, In x l -> 1 <= x /\ x <= n) /\
  (forall x, 1 <= x -> x <= n -> In x l).

Definition abs_nat (a b : nat) : nat :=
  if a <? b then b - a else a - b.

Definition diffs (l : list nat) : list nat :=
  map (fun i => abs_nat (nth (i - 1) l 0) i) (seq 1 (length l)).

Definition full_diff_perm (l : list nat) : Prop :=
  is_perm l (length l) /\
  (forall d, In d (seq 0 (length l)) <->
             exists i, In i (seq 1 (length l)) /\ d = abs_nat (nth (i - 1) l 0) i).

Lemma in_seq_1_n : forall n x, In x (seq 1 n) <-> (1 <= x /\ x <= n).
Proof.
  intros n x.
  rewrite in_seq.            (* in_seq: In x (seq 1 n) <-> 1 ≤ x < 1+n *)
  rewrite Nat.lt_succ_r.      (* Nat.lt_succ_r: x < n+1 <-> x ≤ n *)
  split; intro H; destruct H as [H1 H2]; split; assumption.
Qed.

Fixpoint sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

Lemma seq_plus_gen : forall a n, forall b,
  seq (a + b) n = map (fun x => x + a) (seq b n).
Proof.
  intros a n.
  generalize dependent a.
  induction n as [| n' IH]; intros a b.
  - simpl; reflexivity.
  - simpl.
    f_equal.
    + apply Nat.add_comm.
    + (* Now we need to show:
           seq ((a+b)+1) n' = map (fun x => x + a) (seq (b+1) n').
         Observe that (a+b)+1 = a+(b+1), so we can apply the induction hypothesis with b replaced by b+1. *)
      rewrite <- Nat.add_succ_r.
      apply IH.
Qed.

Lemma sum_app : forall (l m : list nat),
  sum (l ++ m) = sum l + sum m.
Proof.
  induction l as [| x xs IH]; intros m; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite Nat.add_assoc.
    reflexivity.
Qed.
