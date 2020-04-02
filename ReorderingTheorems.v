Require Export Reordering.
Require Export PosTreeTheorems.

Section ReorderingTheorems.
Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types pt : @pos_tree L O.

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

(* Reordering is a symmetric relation. *)
Lemma reorder_step_pos_symmetry pt1 pt2 :
  reorder_step_pos pt1 pt2 -> reorder_step_pos pt2 pt1.
Proof.
  intros.
  induction H; auto with reordering.
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

(* Reordering preserves well-formedness of trees *)
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
    eapply pos_equivalent_transitive; eauto.
Qed.

(* We can always reorder the left subtree. *)
Lemma reorder_pos_subtree_l pt1 o i pt2 pt1' :
  reorder_pos pt1 pt1' ->
  reorder_pos (PINode pt1 o i pt2) (PINode pt1' o i pt2).
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - eapply rtc_l; eauto with reordering.
Qed.

(* We can always reorder the right subtree. *)
Lemma reorder_pos_subtree_r pt1 o i pt2 pt2' :
  reorder_pos pt2 pt2' ->
  reorder_pos (PINode pt1 o i pt2) (PINode pt1 o i pt2').
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - eapply rtc_l; eauto with reordering.
Qed.

(* We can always reorder a pos_tree such that any operator ends up on top. *)
Lemma reorder_pos_ith_op_top i o pt :
  ith_symbol i (inr o) pt ->
  exists pt1 pt2, reorder_pos pt (PINode pt1 o i pt2).
Proof.
  intros.
  induction pt; inv H.
  (* CASE: (o, i) is already one top. *)
  - eexists. eexists. eapply rtc_refl.
  (* CASE: (o, i) is in the left subtree. *)
  - apply IHpt1 in H2.
    destruct H2. destruct H.
    eexists. eexists.
    eapply rtc_transitive.
    + eapply reorder_pos_subtree_l.
      eassumption.
    + eapply rtc_once.
      eapply PRI_LR.
  (* CASE: (o, i) is in the right subtree. *)
  - apply IHpt2 in H2.
    destruct H2. destruct H.
    eexists. eexists.
    eapply rtc_transitive.
    + eapply reorder_pos_subtree_r.
      eassumption.
    + eapply rtc_once.
      eapply PRI_RL.
Qed.

(* We can always reorder two position equivalent trees with each other. *)
Lemma pos_equivalent_reorder_pos pt1 pt2 n0 n :
  wf_pos_tree n0 pt1 n -> wf_pos_tree n0 pt2 n ->    
  pos_equivalent pt1 pt2 ->
  reorder_pos pt1 pt2.
Proof.
  intro. revert pt2.
  induction H.

  (* CASE: pt1 = (l, i) *)
  - intros.
    unfold pos_equivalent in H0.
    destruct pt2.
    (* CASE: pt2 = (l2, i2) *)
    + specialize H0 with (s := inl l) (i0 := i).
      destruct H0.
      assert (@ith_symbol L O i (inl l) (PANode l i)). { apply L_ith. }
      apply H0 in H2.
      inv H2.
      apply rtc_refl.
    (* CASE: pt2 = [pt21 (o, j) pt22]. Impossible case by position equivalence. *)
    + specialize H0 with (s := inr o) (i0 := n).
      destruct H0.
      assert (ith_symbol n (inr o) (PINode pt2_1 o n pt2_2)). { apply O_ith. }
      apply H1 in H2.
      inv H2.

  (* CASE: pt1 = [pt11 (o, i) pt12] *)
  - intros.

    (* This means (o, i) is also in pt2. *)
    assert (H2' := H2).
    unfold pos_equivalent in H2'.
    specialize H2' with (s := inr o) (i := j).
    assert (ith_symbol j (inr o) (PINode pt1 o j pt2)). { apply O_ith. }
    apply H2' in H3. clear H2'.
    (* This means we can reorder the operator to the top of pt2. *)
    apply reorder_pos_ith_op_top in H3.
    destruct H3. destruct H3.
    (* This new tree is also position equivalent. *)
    eapply reorder_pos_wf_pos_tree in H3 as ?; eauto.
    inv H4.
    eapply reorder_pos_preserves_position in H3 as ?; eauto.
    assert (pos_equivalent (PINode pt1 o j pt2) (PINode x o j x0)). {
      eapply pos_equivalent_transitive; eassumption.
    }
    (* The subtrees are position equivalent with each other. *)
    eapply pos_equivalent_subtrees in H5; eauto with pos_tree.
    destruct H5.
    (* By induction hypothesis we can reorder the subtrees to each other. *)
    apply IHwf_pos_tree1 in H5; auto.
    apply IHwf_pos_tree2 in H6; auto.
    (* In conclusion, we can reorder everything to each other. *)
    eapply rtc_transitive.
    eapply reorder_pos_subtree_l.
    eassumption.
    eapply rtc_transitive.
    eapply reorder_pos_subtree_r.
    eassumption.
    apply reorder_pos_symmetry.
    assumption.
Qed.

(* Reordering with pos_trees is the same as reordering with ordinary parse_trees *)
Lemma reorder_step_pos_unpos_reorder_step pt pt' :
  reorder_step_pos pt pt' -> reorder_step (unpos pt) (unpos pt').
Proof.
  intros.
  induction H; simpl; auto with reordering.
Qed.

Lemma reorder_pos_unpos_reorder pt pt' :
  reorder_pos pt pt' -> reorder (unpos pt) (unpos pt').
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - eapply rtc_l; eauto using reorder_step_pos_unpos_reorder_step.
Qed.

(* Proving that position equivalence implies reordering, is the same as proving that
   yield equivalence (for parse_trees) implies reordering. *)
Lemma reorder_pos_forall_unpos :
  (forall pt pt' n0 n,
    wf_pos_tree n0 pt n -> wf_pos_tree n0 pt' n ->
    pos_equivalent pt pt' -> reorder_pos pt pt') ->
  (forall t t', yield t = yield t' -> reorder t t').
Proof.
  (* By the following facts:
     - Yield equivalence is position equivalence.
     - All parse_trees can be transformed into pos_trees with the pos function.
     - unpos is the injective function of pos. *)
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

End ReorderingTheorems.
