From stdpp Require Import list.

Ltac inv H := inversion H; clear H; subst.

(* If two lists have the same elements at the same indices, then the two lists are equal.
   This Lemma differs from list_eq in that we do not have to consider out-of-bounds
   cases. *)
Lemma lookup_some_equality {A} (l1 l2 : list A) :
  (forall i a, l1 !! i = Some a <-> l2 !! i = Some a) ->
  l1 = l2.
Proof.
  intros.
  apply list_eq.
  intros.
  destruct (l1 !! i) eqn:E1.
  - apply H in E1.
    symmetry in E1.
    assumption.
  - destruct (l2 !! i) eqn:E2.
    + apply H in E2.
      rewrite E1 in E2.
      discriminate E2.
    + reflexivity.
Qed.
