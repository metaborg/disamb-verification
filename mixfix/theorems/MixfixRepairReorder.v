From disamb Require Export MixfixRepair.
From disamb Require Export MixfixReorder.
From disamb Require Import MixfixUtilsTheorems.
From disamb Require Import MixfixReorderTheorems.
From disamb Require Import MyUtils.

Section MixfixRepairReorder.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)) (b : bool) (Q : crules T).

Lemma repair_cr_true_left_branching g X Q p ts tn t' :
  wft g X tn → repair_cr Q p ts tn = (t', true) → left_branching tn.
Proof.
  intros Hwft. revert t'. induction Hwft using well_formed_parse_tree_forest_rec
    with (P0 := fun pn tns Hwfts => ∀ t', repair_cr_forest Q p pn ts tns = (t', true) →
                                          left_branching_forest tns); simpl; intros.
  - inv H.
  - constructor. eauto.
  - inv H.
  - destruct (repair_cr Q p ts t) as [tn1' b] eqn:E.
    destruct (decide (b = true ∨ p CR X :: Xs ∠ Q)); [|inv H].
    destruct o.
      + subst. assert (left_branching t); eauto.
        inv H0. constructor.
      + inv H. apply conflict_right_well_formed in H0. destruct H0.
        inv H0.
        inv Hwft.
        constructor.
Qed.

Lemma wf_crule_node g X Xs Q p tn p1 :
  wft g X tn → p1 CR X :: Xs ∠ Q → X = E.
Proof.
  intros Hwft Hcrule.
  inv Hwft; auto.
  apply conflict_right_well_formed in Hcrule.
  destruct Hcrule.
  inv H0.
Qed.

Lemma repair_cr_conflict_node g X Q p ts tn t' b p1 Xs :
  wft g X tn → repair_cr Q p ts tn = (t', b) → (b = true ∨ p1 CR X :: Xs ∠ Q) → X = E.
Proof.
  intros.
  destruct H1.
  - subst.
    eapply repair_cr_true_left_branching in H0; eauto.
    inv H0.
    inv H.
    reflexivity.
  - eauto using wf_crule_node.
Qed.

Lemma repair_cr_reorder g X Q p ts tn t' b :
  wft g X tn → repair_cr Q p ts tn = (t', b) → reorder_tree (node p (add_last ts tn)) t'.
Proof.
  intro Hwft.
  revert t' b.
  induction Hwft using well_formed_parse_tree_forest_rec
    with (P0 := fun pn tns Hwfts => ∀ t' b, repair_cr_forest Q p pn ts tns = (t', b) →
                                            reorder_tree (node p (add_last ts (node pn tns))) t'); intros.
  - inv H. apply rtc_refl.
  - eauto.
  - inv H. apply rtc_refl.
  - simpl in H.
    destruct (repair_cr Q p ts t) eqn:E.
    destruct (decide (b0 = true ∨ p CR X :: Xs ∠ Q)).
    + inv H.
      assert (E' := E).
      eapply repair_cr_conflict_node in E'; eauto.
      subst.
      inv Hwft.
      rewrite <- E in IHHwft. apply IHHwft in E.
      eapply rtc_l.
      eapply sc_rl.
      eapply reorder_step_add_last.
      apply reorder_forest_reorder_tree.
      apply reorder_head_tree_reorder_forest.
      assumption.
    + inv H.
      apply rtc_refl.
Qed.

Lemma repair_cr_start_reorder g X Q t :
  wft g X t → reorder_tree t (repair_cr_start Q t).
Proof.
  intro Hwft.
  inv Hwft.
  - simpl. apply rtc_refl.
  - simpl. destruct ts as [|t ts].
    + apply rtc_refl.
    + destruct (split_last t ts) as [tsh tn] eqn:Hsplit.
      destruct (repair_cr Q p tsh tn) as [t' b] eqn:Hrepair.
      inv H0.
      eapply split_last_wf in Hsplit as Htnwf; eauto.
      destruct Htnwf as [Xn Htnwf].
      eapply repair_cr_reorder in Hrepair; eauto.
      erewrite split_last_add_last in Hrepair; eauto.
Qed.

Corollary repair_cr_start_wf g X Q t :
  wft g X t → wft g X (repair_cr_start Q t).
Proof.
  intro Hwft. eapply reorder_well_formed; eauto. eapply repair_cr_start_reorder; eauto.
Qed.

Corollary repair_cr_start_preserves_yield g Q X t :
  wft g X t → yt t = yt (repair_cr_start Q t).
Proof.
  intro Hwft. erewrite reorder_preserves_yield; eauto. eapply repair_cr_start_reorder; eauto.
Qed.

Lemma repair_cl_wf g p t1 ts Q :
  wft g E (node p (cons_forest t1 ts)) → wft g E (repair_cl Q p t1 ts).
Proof.
  revert p ts.
  induction t1 using parse_tree_forest_rec with
  (P0 := fun t1s => (∀ p p1 ts,
          wft g E (node p (cons_forest (node p1 t1s) ts)) →
          wft g E (repair_cl_forest1 Q p p1 t1s ts)) ∧
                    (∀ Xs p1 X1s ts ts',
          prod g (E :: Xs) →
          wfts g Xs ts →
          wfts g X1s t1s →
          repair_cl_forest2 Q (E :: Xs) p1 ts t1s = Some ts' →
          wfts g X1s ts')); try split; intros.
  - rename t into a.
    cbn [repair_cl]. apply repair_cr_start_wf. assumption.
  - rename p1 into p, p into p1, p0 into t1s.
    simpl. apply IHt1. assumption.
  - cbn [repair_cl_forest1]. apply repair_cr_start_wf. assumption.
  - inv H2.
  - rename p0 into p, t1 into t11, p into t1s.
    cbn [repair_cl_forest1]. destruct (repair_cl_forest2 Q p p1 ts t1s) as [ts'|] eqn:?.
    + apply IHt1.
      inv H. inv H3. inv H4. inv H6. rename X into X11, Xs0 into X1s.
      repeat constructor; auto.
      eapply IHt0; eauto.
    + apply repair_cr_start_wf. assumption.
  - rename t1 into t11, p into t1s.
    simpl in H2. destruct t1s as [|t12 t1s].
    + destruct t11 as [|p11 t11s]; inv H2.
      inv H1. inv H6. inv H5.
      repeat constructor.
      apply IHt1.
      repeat constructor; auto.
    + destruct (repair_cl_forest2 Q (E :: Xs) p1 ts (cons_forest t12 t1s)) as [t1s'|] eqn:?; inv H2.
      inv H1. constructor; auto.
      eapply IHt0; eauto.
Qed.

Lemma repair_cl_forest_wf g Q t1s :
  (∀ p p1 ts,
          wft g E (node p (cons_forest (node p1 t1s) ts)) →
          wft g E (repair_cl_forest1 Q p p1 t1s ts)) ∧
  (∀ Xs p1 X1s ts ts',
          prod g (E :: Xs) →
          wfts g Xs ts →
          wfts g X1s t1s →
          repair_cl_forest2 Q (E :: Xs) p1 ts t1s = Some ts' →
          wfts g X1s ts').
Proof.
  induction t1s using parse_forest_tree_rec with
  (P := fun t1 => ∀ p ts, wft g E (node p (cons_forest t1 ts)) → wft g E (repair_cl Q p t1 ts)); try split; intros.
  - rename t into a.
    cbn [repair_cl]. apply repair_cr_start_wf. assumption.
  - rename p0 into p, p into p1.
    simpl. apply IHt1s. assumption.
  - cbn [repair_cl_forest1]. apply repair_cr_start_wf. assumption.
  - inv H2.
  - rename p0 into p, p into t11.
    cbn [repair_cl_forest1]. destruct (repair_cl_forest2 Q p p1 ts t1s) as [ts'|] eqn:?.
    + apply IHt1s.
      inv H. inv H3. inv H4. inv H6. rename X into X11, Xs0 into X1s.
      repeat constructor; auto.
      eapply IHt1s0; eauto.
    + apply repair_cr_start_wf. assumption.
  - simpl in H2. destruct t1s as [|t12 t1s].
    + destruct p as [|p11 t11s]; inv H2.
      inv H1. inv H6. inv H5.
      repeat constructor.
      apply IHt1s.
      repeat constructor; auto.
    + destruct (repair_cl_forest2 Q (E :: Xs) p1 ts (cons_forest t12 t1s)) as [t1s'|] eqn:?; inv H2.
      inv H1. constructor; auto.
      eapply IHt1s0; eauto.
Qed.

Lemma repair_cl_preserves_yield g Q p t1 ts :
  wft g E (node p (cons_forest t1 ts)) → yt (node p (cons_forest t1 ts)) = yt (repair_cl Q p t1 ts).
Proof.
  revert p ts.
  induction t1 using parse_tree_forest_rec with 
  (P0 := fun t1s => (∀ p p1 ts,
                wft g E (node p (cons_forest (node p1 t1s) ts)) →
                yt (node p (cons_forest (node p1 t1s) ts)) = yt (repair_cl_forest1 Q p p1 t1s ts)) ∧
                    (∀ Xs p1 X1s ts t1s',
                prod g (E :: Xs) →
                wfts g Xs ts →
                wfts g X1s t1s →
                repair_cl_forest2 Q (E :: Xs) p1 ts t1s = Some t1s' →
                yts t1s ++ yts ts = yts t1s')); try split; intros.
  - cbn [repair_cl].
    erewrite repair_cr_start_preserves_yield; eauto.
  - rename p1 into p, p into p1, p0 into t1s.
    simpl. destruct IHt1. rewrite <- H0; auto.
  - cbn [repair_cl_forest1].
    erewrite repair_cr_start_preserves_yield; eauto.
  - inv H2.
  - rename p0 into p, t1 into t11, p into t1s.
    cbn [repair_cl_forest1]. destruct (repair_cl_forest2 Q p p1 ts t1s) as [ts'|] eqn:?.
    + simplify_list_eq.
      inv H. inv H3. inv H4. inv H6.
      rewrite <- IHt1; auto.
      destruct IHt0. erewrite H0; eauto.
      constructor; auto. constructor; auto.
      eapply repair_cl_forest_wf in Heqo; eauto.
    + erewrite repair_cr_start_preserves_yield; eauto.
  - rename t1 into t11, p into t1s.
    simplify_list_eq. destruct t1s as [|t12 t1s].
    + inv H1. inv H7.
      destruct t11 as [a|p11 t11s]; inv H2.
      simplify_list_eq. rewrite <- IHt1; auto.
      inv H6.
      repeat constructor; auto.
    + simpl.
      destruct (repair_cl_forest2 Q (E :: Xs) p1 ts (cons_forest t12 t1s)) as [t1s''|] eqn:?; inv H2.
      simpl. destruct IHt0. inv H1. eapply H3 in Heqo; eauto. rewrite <- Heqo.
      simplify_list_eq. reflexivity.
Qed.

Lemma repair_cl_start_wf g Q X p ts :
  wft g X (node p ts) → wft g E (repair_cl_start Q p ts).
Proof.
  intro Hwft. destruct ts as [|t1 ts].
  - simpl. inv Hwft. constructor; assumption.
  - simpl. apply repair_cl_wf. inv Hwft. constructor; assumption.
Qed.

Lemma repair_cl_start_preserves_yield g X p ts Q :
  wft g X (node p ts) → yt (node p ts) = yt (repair_cl_start Q p ts).
Proof.
  intro. destruct ts; auto.
  simpl. inv H. erewrite <- repair_cl_preserves_yield; eauto. constructor; eauto.
Qed.

Lemma repair_wf g Q X t :
  wft g X t → wft g X (repair Q t).
Proof.
  revert X. induction t using parse_tree_forest_rec with
  (P0 := fun ts => ∀ p, wfts g p ts → wfts g p (repair_forest Q ts)); simpl; intros.
  - assumption.
  - inv H. eapply repair_cl_start_wf.
    constructor; auto.
  - assumption.
  - inv H. constructor; auto.
Qed.

Lemma repair_forest_wf g Q ts :
  ∀ p, wfts g p ts → wfts g p (repair_forest Q ts).
Proof.
  induction ts using parse_forest_tree_rec with
  (P := fun t => ∀ X, wft g X t → wft g X (repair Q t)); simpl; intros; auto.
  - inv H. eapply repair_cl_start_wf.
    constructor; auto.
  - inv H. constructor; auto.
Qed.

Lemma repair_preserves_yield g X t Q : 
  wft g X t → yt t = yt (repair Q t).
Proof.
  revert X. induction t using parse_tree_forest_rec with
  (P0 := fun ts => ∀ p, wfts g p ts → yts ts = yts (repair_forest Q ts)); intros; auto.
  - simpl. inv H. erewrite <- repair_cl_start_preserves_yield; eauto.
    constructor; eauto. apply repair_forest_wf; auto.
  - simpl. inv H. erewrite <- IHt; eauto. erewrite IHt0; eauto.
Qed. 

(* Lemma repair_cl_reorder g p t1 ts Q :
  wft g E (node p (cons_forest t1 ts)) → reorder_tree (node p (cons_forest t1 ts)) (repair_cl Q p t1 ts).
Proof.
  revert p ts.
  induction t1 using parse_tree_forest_rec with
  (P0 := fun t1s => (∀ p p1 ts,
          wft g E (node p (cons_forest (node p1 t1s) ts)) →
          reorder_tree (node p (cons_forest (node p1 t1s) ts)) (repair_cl_forest1 Q p p1 t1s ts))
                  ∧ (∀ p p1 ts ts',
          repair_cl_forest2 Q p p1 ts t1s = Some ts' →
          reorder_forest_left_up p ts t1s ts')
); try split; intros.
  - rename t into a.
    cbn [repair_cl].
    eapply repair_cr_start_reorder; eauto.
  - rename p1 into p, p into p1, p0 into t1s.
    cbn [repair_cl].
    apply IHt1; auto.
  - cbn [repair_cl_forest1].
    eapply repair_cr_start_reorder; eauto.
  - inv H.
  - rename p0 into p, t1 into t11, p into t1s.
    cbn [repair_cl_forest1].
    destruct (repair_cl_forest2 Q p p1 ts t1s) as [ts'|] eqn:?.
    + apply rtc_transitive with (node p1 (cons_forest t11 ts')).
      eapply IHt0 in Heqo. *)

End MixfixRepairReorder.
