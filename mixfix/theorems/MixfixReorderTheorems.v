From disamb Require Export MixfixReorder.
From disamb Require Import MyUtils.

Section ReorderTheorems.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)).

Lemma reorder_forest_left_up_preserves_yield p1 ts1 ts2 ts2' :
  reorder_forest_left_up p1 ts1 ts2 ts2' → yts ts2 ++ yts ts1 = yts ts2'.
Proof.
  intro Hreorder.
  induction Hreorder; simplify_list_eq; auto.
  rewrite IHHreorder. reflexivity.
Qed.

Lemma reorder_step_preserves_yield t1 t2 :
  reorder_step_tree t1 t2 → yt t1 = yt t2.
Proof.
  intro Hreorder_step.
  induction Hreorder_step using reorder_step_tree_forest_rec
      with (P0 := fun ts1 ts2 H => yts ts1 = yts ts2); simpl.
  - eauto using reorder_forest_left_up_preserves_yield.
  - assumption.
  - rewrite IHHreorder_step. reflexivity.
  - rewrite IHHreorder_step. reflexivity.
Qed.

Theorem reorder_preserves_yield t1 t2 :
  reorder_tree t1 t2 → yt t1 = yt t2.
Proof.
  intro Hreorder. induction Hreorder; auto.
  rewrite <- IHHreorder.
  destruct H.
  - auto using reorder_step_preserves_yield.
  - symmetry. auto using reorder_step_preserves_yield.
Qed.

Lemma reorder_forest_left_up_well_formed_1 g Xs1 p2 ts1 ts2 ts2' :
  g (E :: Xs1) →
  wfts g Xs1 ts1 → wfts g p2 ts2 → reorder_forest_left_up (E :: Xs1) ts1 ts2 ts2' → wfts g p2 ts2'.
Proof.
  intros Hp1 Hwfts1 Hwfts2 Hreorder. revert Hwfts2. revert p2.
  induction Hreorder; intros p2 Hwfts2.
  - inv Hwfts2. inv H3. inv H2.
    auto with mixfix.
  - inv Hwfts2.
    auto with mixfix.
Qed.

Lemma reorder_forest_left_up_well_formed_2 g p1 p2 ts1 ts2 ts2' :
  wfts g p2 ts2' → reorder_forest_left_up p1 ts1 ts2 ts2' →
  ∃ Xs1, p1 = E :: Xs1 ∧ g p1 ∧ wfts g Xs1 ts1 ∧ wfts g p2 ts2.
Proof.
  intros Hwfts2' Hreorder. revert Hwfts2'. revert p2.
  induction Hreorder; intros p2 Hwfts2'. 
  - inv Hwfts2'. inv H2. inv H5. inv H3. inv H2.
    eexists. split; auto with mixfix.
  - inv Hwfts2'.
    apply IHHreorder in H3.
    destruct H3 as [Xs1]. destruct H. destruct H0. destruct H1.
    subst.
    eexists. split; auto with mixfix.
Qed.

Lemma reorder_step_well_formed g X t1 t2 :
  reorder_step_tree t1 t2 → (wft g X t1 ↔ wft g X t2).
Proof.
  intros Hreorder. revert X.
  induction Hreorder using reorder_step_tree_forest_rec
      with (P0 := fun ts1 ts2 H => ∀ Xs, wfts g Xs ts1 ↔ wfts g Xs ts2).
  - intro X. split.
    + intro Hwf1.
      inv Hwf1. inv H3. inv H4.
      constructor; auto.
      eauto using reorder_forest_left_up_well_formed_1.
    + intro Hwf2.
      inv Hwf2.
      eapply reorder_forest_left_up_well_formed_2 in r; eauto.
      destruct r as [Xs1]. destruct H. destruct H0. destruct H1.
      subst.
      auto with mixfix.
  - intro X.
    split. 
    + intro Hwf1.
      inv Hwf1.
      constructor; auto.
      apply IHHreorder.
      assumption.
    + intro Hwfts'.
      inv Hwfts'.
      constructor; auto.
      apply IHHreorder.
      assumption.
  - intro Xs.
    split.
    + intro Hwfts1.
      inv Hwfts1.
      constructor; auto.
      apply IHHreorder.
      assumption.
    + intro Hwfts'.
      inv Hwfts'.
      constructor; auto.
      apply IHHreorder.
      assumption.
  - intro Xs.
    split.
    + intro Hwfts1.
      inv Hwfts1.
      constructor; auto.
      apply IHHreorder.
      assumption.
    + intro IHwfts'.
      inv IHwfts'.
      constructor; auto.
      apply IHHreorder.
      assumption.
Qed.

Theorem reorder_well_formed g X t1 t2 :
  wft g X t1 → reorder_tree t1 t2 → wft g X t2.
Proof.
  intros Hwft1 Hreorder.
  induction Hreorder; auto.
  apply IHHreorder.
  destruct H; eapply reorder_step_well_formed in H; eapply H; eauto.
Qed.

Lemma reorder_forest_reorder_tree ts ts' p :
  reorder_forest ts ts' → reorder_tree (node p ts) (node p ts').
Proof.
  intro Hreorder. induction Hreorder.
  - apply rtc_refl.
  - eapply rtc_l; eauto.
    destruct H.
    + apply sc_lr. constructor. assumption.
    + apply sc_rl. constructor. assumption.
Qed.

Lemma reorder_head_tree_reorder_forest t t' ts :
  reorder_tree t t' → reorder_forest (cons_forest t ts) (cons_forest t' ts).
Proof.
  intro Hreorder. induction Hreorder.
  - apply rtc_refl.
  - eapply rtc_l; eauto.
    inv H.
    + apply sc_lr. constructor. assumption.
    + apply sc_rl. constructor. assumption.
Qed.


Lemma left_reorderable_nil_false p :
  ¬ left_reorderable p [].
Proof.
  intro Hlr. induction p.
  + inv Hlr.
  + inv Hlr. auto.
Qed.

Lemma left_reorder_terminal_false p a :
  ¬ left_reorderable p [terminal a].
Proof.
  intro Hlr.
  induction p.
  - inv Hlr.
  - inv Hlr. auto.
Qed.

End ReorderTheorems.
