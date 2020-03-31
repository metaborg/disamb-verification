Require Import PosTree.
Require Import PosTreeTheorems.
From stdpp Require Import list.
From stdpp Require Import relations.

Section Reorderings.

Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types pt : @pos_tree L O.

Inductive reorder_step : parse_tree -> parse_tree -> Prop :=
  | RI_LR t11 o1 t12 o t2 :
      reorder_step (INode (INode t11 o1 t12) o t2)
                   (INode t11 o1 (INode t12 o t2))
  | RI_RL t1 o t21 o2 t22 :
      reorder_step (INode t1 o (INode t21 o2 t22))
                   (INode (INode t1 o t21) o2 t22)
  | RI_t1 t1 o t2 t1' :
      reorder_step t1 t1' ->
      reorder_step (INode t1 o t2) (INode t1' o t2)
  | RI_t2 t1 o t2 t2' :
      reorder_step t2 t2' ->
      reorder_step (INode t1 o t2) (INode t1 o t2').

Definition reorder := rtc reorder_step.

Ltac super_simpl := try simpl in *; try simplify_list_eq; try reflexivity.

Lemma reorder_step_preserves_yields t t' :
  reorder_step t t' -> yield t = yield t'.
Proof.
  intros. induction H; super_simpl.
  - rewrite IHreorder_step. reflexivity.
  - rewrite IHreorder_step. reflexivity.
Qed.

Lemma reorder_preserves_yield t t' :
  reorder t t' -> yield t = yield t'.
Proof.
  unfold reorder. intros.
  induction H.
  - reflexivity.
  - rewrite <- IHrtc.
    apply reorder_step_preserves_yields.
    assumption.
Qed.

Inductive reorder_step_pos : pos_tree -> pos_tree -> Prop :=
  | PRI_LR pt11 o1 i1 pt12 o i pt2 :
      reorder_step_pos (PINode (PINode pt11 o1 i1 pt12) o i pt2)
                       (PINode pt11 o1 i1 (PINode pt12 o i pt2))
  | PRI_RL pt1 o i pt21 o2 i2 pt22 :
      reorder_step_pos (PINode pt1 o i (PINode pt21 o2 i2 pt22))
                      (PINode (PINode pt1 o i pt21) o2 i2 pt22)
  | PRI_pt1 pt1 o i pt2 pt1' :
      reorder_step_pos pt1 pt1' ->
      reorder_step_pos (PINode pt1 o i pt2) (PINode pt1' o i pt2)
  | PRI_pt2 pt1 o i pt2 pt2' :
      reorder_step_pos pt2 pt2' ->
      reorder_step_pos (PINode pt1 o i pt2) (PINode pt1 o i pt2').

Definition reorder_pos := rtc reorder_step_pos.

Lemma reorder_step_pos_symmetry pt1 pt2 :
  reorder_step_pos pt1 pt2 -> reorder_step_pos pt2 pt1.
Proof.
  intros.
  induction H.
  - apply PRI_RL.
  - apply PRI_LR.
  - apply PRI_pt1.
    assumption.
  - apply PRI_pt2.
    assumption.
Qed.

Lemma reorder_pos_symmetry pt1 pt2 :
  reorder_pos pt1 pt2 -> reorder_pos pt2 pt1.
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - apply reorder_step_pos_symmetry in H.
    eapply rtc_transitive.
    + apply IHrtc.
    + eapply rtc_l.
      * eassumption.
      * apply rtc_refl.
Qed.

Lemma reorder_step_pos_wf_pos_tree n0 pt n pt' :
  wf_pos_tree n0 pt n -> reorder_step_pos pt pt' -> wf_pos_tree n0 pt' n.
Proof.
  intros. revert H. revert n0 n.
  induction H0; intros.
  - inv H. inv H6.
    eauto with pos_tree.
  - inv H. inv H7.
    eauto with pos_tree.
  - inv H.
    eauto with pos_tree.
  - inv H.
    eauto with pos_tree.
Qed.

Lemma reorder_pos_wf_pos_tree n0 pt n pt' :
  wf_pos_tree n0 pt n -> reorder_pos pt pt' -> wf_pos_tree n0 pt' n.
Proof.
  intros. revert H.
  induction H0; eauto using reorder_step_pos_wf_pos_tree.
Qed.

Lemma reorder_step_pos_preserves_position pt pt' :
  reorder_step_pos pt pt' -> pos_equivalent pt pt'.
Proof.
  intros. unfold pos_equivalent.
  induction H; intros.
  - split; intros.
    + inv H; eauto with pos_tree.
      inv H2; eauto with pos_tree.
    + inv H; eauto with pos_tree.
      inv H2; eauto with pos_tree.
  - split; intros.
    + inv H; eauto with pos_tree.
      inv H2; eauto with pos_tree.
    + inv H; eauto with pos_tree.
      inv H2; eauto with pos_tree.
  - split; intros.
    + inv H0; eauto with pos_tree.
      apply IHreorder_step_pos in H3.
      eauto with pos_tree.
    + inv H0; eauto with pos_tree.
      apply IHreorder_step_pos in H3.
      eauto with pos_tree.
  - split; intros.
    + inv H0; eauto with pos_tree.
      apply IHreorder_step_pos in H3.
      eauto with pos_tree.
    + inv H0; eauto with pos_tree.
      apply IHreorder_step_pos in H3.
      eauto with pos_tree.
Qed.

Lemma reorder_pos_preserves_position pt pt' :
  reorder_pos pt pt' -> pos_equivalent pt pt'.
Proof.
  intros.
  induction H.
  - unfold pos_equivalent.
    auto.
  - apply reorder_step_pos_preserves_position in H.
    unfold pos_equivalent in *.
    intros.
    split; intros.
    + apply IHrtc. apply H. assumption.
    + apply H. apply IHrtc. assumption.
Qed.

Lemma reorder_pos_subtree_l pt1 o i pt2 pt1' :
  reorder_pos pt1 pt1' ->
  reorder_pos (PINode pt1 o i pt2) (PINode pt1' o i pt2).
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - eapply rtc_l.
    + apply PRI_pt1.
      eassumption.
    + assumption.
Qed.

Lemma reorder_pos_subtree_r pt1 o i pt2 pt2' :
  reorder_pos pt2 pt2' ->
  reorder_pos (PINode pt1 o i pt2) (PINode pt1 o i pt2').
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - eapply rtc_l.
    + apply PRI_pt2.
      eassumption.
    + assumption.
Qed.

Lemma reorder_pos_nth_op_top i o pt :
  nth_symbol i (inr o) pt ->
  exists pt1 pt2, reorder_pos pt (PINode pt1 o i pt2).
Proof.
  intros.
  induction pt; inv H.
  - eexists. eexists. eapply rtc_refl.
  - apply IHpt1 in H2.
    destruct H2. destruct H.
    eexists. eexists.
    eapply rtc_transitive.
    + eapply reorder_pos_subtree_l.
      eassumption.
    + eapply rtc_once.
      eapply PRI_LR.
  - apply IHpt2 in H2.
    destruct H2. destruct H.
    eexists. eexists.
    eapply rtc_transitive.
    + eapply reorder_pos_subtree_r.
      eassumption.
    + eapply rtc_once.
      eapply PRI_RL.
Qed.

Lemma pos_equivalent_reorder_pos pt1 pt2 n0 n :
  wf_pos_tree n0 pt1 n -> wf_pos_tree n0 pt2 n ->    
  pos_equivalent pt1 pt2 ->
  reorder_pos pt1 pt2.
Proof.
  intro. revert pt2.
  induction H.

  - intros.
    unfold pos_equivalent in H0.
    destruct pt2.
    + specialize H0 with (s := inl l) (i0 := i).
      destruct H0.
      assert (@nth_symbol L O i (inl l) (PANode l i)). apply L_nth.
      apply H0 in H2.
      inv H2.
      apply rtc_refl.
    + specialize H0 with (s := inr o) (i0 := n).
      destruct H0.
      assert (nth_symbol n (inr o) (PINode pt2_1 o n pt2_2)). apply O_nth.
      apply H1 in H2.
      inv H2.

  - intros.

    assert (H2' := H2).
    unfold pos_equivalent in H2'.
    specialize H2' with (s := inr o) (i := j).
    assert (nth_symbol j (inr o) (PINode pt1 o j pt2)). apply O_nth.
    apply H2' in H3. clear H2'.

    apply reorder_pos_nth_op_top in H3.
    destruct H3.
    destruct H3.
    eapply reorder_pos_wf_pos_tree in H3 as ?; eauto.
    inv H4.
    eapply reorder_pos_preserves_position in H3 as ?; eauto.
    assert (pos_equivalent (PINode pt1 o j pt2) (PINode x o j x0)). {
      eapply pos_equivalent_transitive; eassumption.
    }
    eapply pos_equivalent_subtrees in H5; eauto with pos_tree.
    destruct H5.
    apply IHwf_pos_tree1 in H5; auto.
    apply IHwf_pos_tree2 in H6; auto.
    eapply rtc_transitive.
    eapply reorder_pos_subtree_l.
    eassumption.
    eapply rtc_transitive.
    eapply reorder_pos_subtree_r.
    eassumption.
    apply reorder_pos_symmetry.
    assumption.
Qed.

Lemma reorder_step_pos_unpos_reorder_step pt pt' :
  reorder_step_pos pt pt' -> reorder_step (unpos pt) (unpos pt').
Proof.
  intros.
  induction H; simpl.
  - apply RI_LR.
  - apply RI_RL.
  - apply RI_t1. assumption.
  - apply RI_t2. assumption.
Qed.

Lemma reorder_pos_unpos_reorder pt pt' :
  reorder_pos pt pt' -> reorder (unpos pt) (unpos pt').
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - eapply rtc_l.
    + apply reorder_step_pos_unpos_reorder_step.
      eassumption.
    + assumption.
Qed.

Lemma reorder_pos_forall_unpos :
  (forall pt pt' n0 n,
    wf_pos_tree n0 pt n -> wf_pos_tree n0 pt' n ->
    pos_equivalent pt pt' -> reorder_pos pt pt') ->
  (forall t t', yield t = yield t' -> reorder t t').
Proof.
  intros.

  remember (pos t 0) as x.
  destruct x.
  symmetry in Heqx.
  apply pos_unpos in Heqx as ?.
  apply pos_wf_pos_tree in Heqx as ?.
  remember (pos t' 0) as x'.
  destruct x'.
  symmetry in Heqx'.
  apply pos_unpos in Heqx' as ?.
  apply pos_wf_pos_tree in Heqx' as ?.
  apply wf_pos_tree_size in H4 as ?.
  apply wf_pos_tree_size in H2 as ?.
  simpl in *. subst.
  rewrite H0 in H2.
  eapply pos_equivalence_yields in H0; eauto.
  apply reorder_pos_unpos_reorder.
  eapply H; eauto.
Qed.

Lemma reorder_completes_yields t t' :
  yield t = yield t' -> reorder t t'.
Proof.
  apply reorder_pos_forall_unpos.
  apply pos_equivalent_reorder_pos.
Qed.

Theorem yield_equivalence_are_reorderings t t' :
  yield t = yield t' <-> reorder t t'.
Proof.
  split.
  - apply reorder_completes_yields.
  - apply reorder_preserves_yield.
Qed.


