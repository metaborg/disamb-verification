From disamb Require Export MixfixRepair2.
From disamb Require Export MixfixUtilsTheorems.
From disamb Require Import MyUtils.

Section MixfixReorderRepair.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)) (b : bool) (Q : crules T).

Lemma goiwnavoin g Q p1 p2 ts1 ts2 ts2' :
  complete_crules Q →
  wft g E (node p1 ts1) → wft g E (node p2 ts2) →
  reorder_forest_left_up p1 ts1 ts2 ts2' →
  repair_cl Q p1 (repair_cl_start Q p2 ts2) ts1 =
  repair_cl_start Q p2 ts2'.
Proof.
  intros. induction H2.
  - exfalso. inv H1. inv H5. inv H7. inv H6. eapply acyclic_productions; eauto.
  - simpl. rewrite IHreorder_forest_left_up.

Lemma reorder_step_repair Q t1 t2 :
  complete_crules Q → reorder_step_tree t1 t2 → repair Q t1 = repair Q t2.
Proof.
  intros. induction H0 using reorder_step_tree_forest_rec with
    (P0 := fun ts1 ts2 H => repair_forest Q ts1 = repair_forest Q ts2).
  - cbn [repair]. cbn [repair_forest]. cbn [repair]. simpl.
  - simpl. rewrite IHreorder_step_tree. reflexivity.
  - simpl. rewrite IHreorder_step_tree. reflexivity.
  - simpl. rewrite IHreorder_step_tree. reflexivity.

Lemma reorder_repair Q t1 t2 :
  complete_crules Q → reorder_tree t1 t2 → repair Q t1 = repair Q t2.
Proof.
  intros.
  induction H0; auto.
  rewrite <- IHrtc.
  inv H0.
  induction H0.
