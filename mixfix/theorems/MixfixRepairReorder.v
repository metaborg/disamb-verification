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

(* Lemma repair_cl_reorder g p t1 ts Q :
  wft g E (node p (cons_forest t1 ts)) → reorder_tree (node p (cons_forest t1 ts)) (repair_cl Q p t1 ts).
Proof.
  intro Hwft.
  induction t1 as [a|p1 t1s].
  - cbn [repair_cl].
    eapply repair_cr_start_reorder; eauto.
  - cbn [repair_cl].
    destruct t1s.
    + eapply repair_cr_start_reorder; eauto.
    + destruct (repair_cl_forest Q p p1 ts t1s) eqn:E.
      * *)

End MixfixRepairReorder.