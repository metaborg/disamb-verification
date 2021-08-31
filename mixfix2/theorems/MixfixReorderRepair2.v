From disamb Require Export MixfixRepair3.
From disamb Require Import MyUtils.
From disamb Require Import MixfixRepairWellformed.
From disamb Require Import MixfixReorderWellformed.

Section MixfixReorderRepair2.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool) (Q : crules T).

Lemma repair_cr_leftmost_match Q p t1 τ tn :
  p LM repair_cr Q p t1 τ tn.
Proof.
  induction tn as [an|pn opt_an|pn pn1 ? τn pnn]; simpl; try constructor.
  destruct (decide (rncf Q p t1 τ (large_node pn pn1 τn pnn))).
  - constructor.
  - constructor. assumption.
Qed.

Lemma repair_cr_leftmost_match_2 Q px p t1 τ tn :
  px LM t1 → px LM repair_cr Q p t1 τ tn.
Proof.
  intros. induction tn as [an|pn opt_an|pn pn1 ? τn pnn]; simpl; try constructor; auto.
  destruct (decide (rncf Q p t1 τ (large_node pn pn1 τn pnn))).
  - constructor. assumption.
  - constructor. auto.
Qed.

Lemma repair_cr_assoc Q p1 t11 τ1 p2 t21 τ2 t22 :
  complete_crules Q → right_dangling p1 → left_dangling p2 →
  ¬ p2 CL p1 ∠ Q →
  (∀ p, p1 CR p ∠ Q → ¬ p LM t21) →
  repair_cr Q p1 t11 τ1 (repair_cr Q p2 t21 τ2 t22) = repair_cr Q p2 (large_node p1 t11 τ1 t21) τ2 t22.
Proof.
  intros. induction t22 as [a22|p22 opt_a22|p22 t221 ? τ22 t22n]; intros; simpl.
  - destruct (decide (rncf Q p2 (large_node p1 t11 τ1 t21) τ2 (leaf a22))).
      + destruct (decide (rncf Q p1 t11 τ1 (large_node p2 t21 τ2 (leaf a22)))).
        * exfalso. unfold complete_crules in H. apply H with (p2 := p1) in H1; eauto.
          destruct H1; auto. eapply r0; eauto. constructor. constructor.
        * destruct t21 as [a21|p21 opt_a21|p21 t211 τ21 t21n]; simpl; auto.
          destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))); auto.
          exfalso. apply n0. intros ???. inv H5. eapply H3; eauto.
      + destruct n. intros ???. inv H5. inv H7.
  - destruct (decide (rncf Q p2 (large_node p1 t11 τ1 t21) τ2 (small_node p22 opt_a22))).
      + destruct (decide (rncf Q p1 t11 τ1 (large_node p2 t21 τ2 (small_node p22 opt_a22)))).
        * exfalso. unfold complete_crules in H. apply H with (p2 := p1) in H1; eauto.
          destruct H1; auto. eapply r0; eauto. constructor. constructor.
        * destruct t21 as [a21|p21 opt_a21|p21 t211 τ21 t21n]; simpl; auto.
          destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))); auto.
          exfalso. apply n0. intros ???. inv H5. eapply H3; eauto.
      + destruct n. intros ???. inv H5. inv H7.
  - destruct (decide (rncf Q p2 t21 τ2 (large_node p22 t221 τ22 t22n))).
    + destruct (decide (rncf Q p2 (large_node p1 t11 τ1 t21) τ2 (large_node p22 t221 τ22 t22n))).
      * simpl. destruct (decide (rncf Q p1 t11 τ1 (large_node p2 t21 τ2 (large_node p22 t221 τ22 t22n)))).
        **exfalso. unfold complete_crules in H. apply H with (p2 := p1) in H1; eauto.
          destruct H1; auto. eapply r1; eauto. constructor. constructor.
        **destruct t21 as [a21|p21 opt_a21|p21 t211 τ21 t21n]; auto.
          simpl. destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))); auto.
          exfalso. apply n0. intros ???. inv H5. eapply H3; eauto.
      * destruct n. intros ???. inv H5.
        eapply r; eauto. constructor. assumption.
    + destruct (decide (rncf Q p2 (large_node p1 t11 τ1 t21) τ2 (large_node p22 t221 τ22 t22n))).
      * destruct n. intros ???. inv H5. eapply r; eauto. constructor. assumption.
      * simpl. destruct (decide (rncf Q p1 t11 τ1 (large_node p22 (repair_cr Q p2 t21 τ2 t221) τ22 t22n))).
        **exfalso. unfold complete_crules in H. apply H with (p1 := p2) in H0; auto.
          destruct H0; auto. eapply r; eauto. constructor. constructor. apply repair_cr_leftmost_match.
        **rewrite IHt22_1. reflexivity.
Qed.

Lemma repair_cr_assoc2 Q p1 t11 τ1 p2 p21 t211 τ21 t21n τ2 t22 :
  complete_crules Q →
  (p1 CR p21 ∠ Q ∨ ∃ p, p1 CR p ∠ Q ∧ p LM t211) →
  repair_cr Q p1 t11 τ1 (repair_cr Q p2 (large_node p21 t211 τ21 t21n) τ2 t22) =
  repair_cr Q p2 (large_node p21 (repair_cr Q p1 t11 τ1 t211) τ21 t21n) τ2 t22.
Proof.
  intro. induction t22 as [a22|p22 opt_a22|p22 t221 ? τ22 t22n]; intros; simpl.
  - destruct (decide (rncf Q p2 (large_node p21 (repair_cr Q p1 t11 τ1 t211) τ21 t21n) τ2 (leaf a22))).
    + simpl. destruct (decide (rncf Q p1 t11 τ1 (large_node p2 (large_node p21 t211 τ21 t21n) τ2 (leaf a22)))).
      * exfalso. destruct H0.
        **eapply r0; eauto. repeat constructor.
        **destruct H0 as [p]. inv H0. eapply r0; eauto. repeat constructor. assumption.
      * destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))); auto.
          exfalso. destruct H0.
        **eapply r0; eauto. repeat constructor.
        **destruct H0 as [p]. inv H0. eapply r0; eauto. repeat constructor. assumption.
    + destruct n. intros ???. inv H2. inv H4.
  - destruct (decide (rncf Q p2 (large_node p21 (repair_cr Q p1 t11 τ1 t211) τ21 t21n) τ2 (small_node p22 opt_a22))).
    + simpl. destruct (decide (rncf Q p1 t11 τ1 (large_node p2 (large_node p21 t211 τ21 t21n) τ2 (small_node p22 opt_a22)))).
      * exfalso. destruct H0.
        **eapply r0; eauto. repeat constructor.
        **destruct H0 as [p]. inv H0. eapply r0; eauto. repeat constructor. assumption.
      * destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))); auto.
        exfalso. destruct H0.
        **eapply r0; eauto. repeat constructor.
        **destruct H0 as [p]. inv H0. eapply r0; eauto. repeat constructor. assumption.
    + destruct n. intros ???. inv H2. inv H4.
  - destruct (decide (rncf Q p2 (large_node p21 t211 τ21 t21n) τ2 (large_node p22 t221 τ22 t22n))).
    + destruct (decide (rncf Q p2 (large_node p21 (repair_cr Q p1 t11 τ1 t211) τ21 t21n) τ2 (large_node p22 t221 τ22 t22n))).
      * simpl. destruct (decide (rncf Q p1 t11 τ1 (large_node p2 (large_node p21 t211 τ21 t21n) τ2 (large_node p22 t221 τ22 t22n)))).
        **exfalso. destruct H0.
          ***eapply r1; eauto. repeat constructor.
          ***destruct H0 as [p]. inv H0. eapply r1; eauto. repeat constructor. assumption.
        **destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))); auto.
          exfalso. destruct H0.
          ***eapply r1; eauto. repeat constructor.
          ***destruct H0 as [p]. inv H0. eapply r1; eauto. repeat constructor. assumption.
      * destruct n. intros ???. inv H2. eapply r; eauto. constructor. assumption.
    + destruct (decide (rncf Q p2 (large_node p21 (repair_cr Q p1 t11 τ1 t211) τ21 t21n) τ2 (large_node p22 t221 τ22 t22n))).
      * exfalso. apply n. intros ???. inv H2. eapply r; eauto. constructor. assumption.
      * simpl. destruct (decide (rncf Q p1 t11 τ1 (large_node p22 (repair_cr Q p2 (large_node p21 t211 τ21 t21n) τ2 t221) τ22 t22n))).
        **exfalso. destruct H0.
          ***eapply r; eauto. repeat constructor. apply repair_cr_leftmost_match_2. constructor.
          ***destruct H0 as [p]. inv H0. eapply r; eauto. repeat constructor.
            apply repair_cr_leftmost_match_2. constructor. assumption.
        **rewrite IHt22_1; eauto.
Qed.

Lemma not_rfncf_exists_match Q p t1 τ tn :
  ¬ rncf Q p t1 τ tn → ∃ px, p CR px ∠ Q ∧ px LM tn.
Proof.
  intro. unfold right_neighborhood_conflict_free in H.
  assert (¬ (∀ p2, p CR p2 ∠ Q → ¬ p2 LM tn)). {
    intro. destruct H. intros ???. inv H1. apply H0 in H. contradiction.
  }
  clear H. induction tn as [an|pn opt_an|pn tn1 ? τn tnn].
  - destruct H0. intros ???. inv H0.
  - destruct H0. intros ???. inv H0.
  - destruct (decide (p CR pn ∠ Q)).
    + exists pn. split; auto. constructor.
    + assert (∃ px : production T, p CR px ∠ Q ∧ px LM tn1). {
        apply IHtn1. intro. destruct H0. intros ???. inv H1; auto. eapply H; eauto.
      }
      destruct H as [px]. inv H. exists px. split; auto. repeat constructor. assumption.
Qed.

Lemma repair_top_repair_cr_assoc g X Q p1 t11 τ1 p2 t21 τ2 t22 :
  complete_crules Q → right_dangling p1 → left_dangling p2 → wft g X t21 →
  (∀ p, p1 CL p ∠ Q → ¬ p RM t11) →
  repair_cr Q p1 t11 τ1 (repair_top Q p2 t21 τ2 t22) = repair_top Q p2 (repair_cr Q p1 t11 τ1 t21) τ2 t22.
Proof.
  intro. revert X p1 t11 τ1 p2 τ2 t22. induction t21 as [a21|p21 opt_a21|p21 t211 ? τ21 t21n];
    intros ??????? HR HL Hwf ?; simpl.
  - destruct (decide (lncf Q p2 (large_node p1 t11 τ1 (leaf a21)) τ2 t22)).
    + rewrite repair_cr_assoc; auto.
      * intro. eapply l; eauto. constructor. constructor.
      * intros ???. inv H2.
    + destruct t11 as [a11|p11 opt_a11|p11 t111 τ11 t11n]; simpl; auto.
      * destruct (decide (lncf Q p1 (large_node p11 t111 τ11 t11n) τ1 (repair_cr Q p2 (leaf a21) τ2 t22))); auto.
        exfalso. apply n0. intros ???. inv H2. eapply H0; eauto.
  - destruct (decide (lncf Q p2 (large_node p1 t11 τ1 (small_node p21 opt_a21)) τ2 t22)).
    + rewrite repair_cr_assoc; auto.
      * intro. eapply l; eauto. constructor. constructor.
      * intros ???. inv H2.
    + destruct t11 as [a11|p11 opt_a11|p11 t111 τ11 t11n]; simpl; auto.
      * destruct (decide (lncf Q p1 (large_node p11 t111 τ11 t11n) τ1 (repair_cr Q p2 (small_node p21 opt_a21) τ2 t22))); auto.
        exfalso. apply n0. intros ???. inv H2. eapply H0; eauto.
  - destruct (decide (lncf Q p2 (large_node p21 t211 τ21 t21n) τ2 t22)).
    + destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))).
      * simpl. destruct (decide (lncf Q p2 (large_node p1 t11 τ1 (large_node p21 t211 τ21 t21n)) τ2 t22)).
        **rewrite repair_cr_assoc; auto.
          ***intro. eapply l0; eauto. constructor. constructor.
          ***intros ???. eapply r; eauto. constructor. assumption.
        **destruct (decide (lncf Q p2 (large_node p21 t211 τ21 t21n) τ2 t22)); try contradiction.
          destruct t11 as [a11|p11 opt_a11|p11 t111 τ11 t11n]; simpl; auto.
          destruct (decide (lncf Q p1 (large_node p11 t111 τ11 t11n) τ1 (repair_cr Q p2 (large_node p21 t211 τ21 t21n) τ2 t22))); auto.
          exfalso. apply n0. intros ???. inv H2. eapply H0; eauto.
      * simpl. destruct (decide (lncf Q p2 (large_node p21 (repair_cr Q p1 t11 τ1 t211) τ21 t21n) τ2 t22)).
        **rewrite repair_cr_assoc2; auto. apply not_rfncf_exists_match in n. destruct n as [px]. inv H1.
          inv H3; auto. right. eauto.
        **exfalso. apply n0. intros ???. inv H2. eapply l; eauto. constructor. inv H4; constructor. assumption.
    + destruct (decide (rncf Q p1 t11 τ1 (large_node p21 t211 τ21 t21n))).
      * simpl. destruct (decide (lncf Q p2 (large_node p1 t11 τ1 (large_node p21 t211 τ21 t21n)) τ2 t22)).
        **exfalso. apply n. intros ???. inv H2. eapply l; eauto. constructor. constructor. assumption.
        **destruct (decide (lncf Q p2 (large_node p21 t211 τ21 t21n) τ2 t22)).
          ***exfalso. apply n. intros ???. inv H2. eapply l; eauto. constructor. assumption.
          ***destruct t11 as [a11|p11 opt_a11|p11 t111 τ11 t11n]; simpl; auto.
            destruct (decide (lncf Q p1 (large_node p11 t111 τ11 t11n) τ1 (repair_top Q p21 t211 τ21 (repair_top Q p2 t21n τ2 t22)))); auto.
            exfalso. apply n2. intros ???. inv H2. eapply H0; eauto.
      * simpl. destruct (decide (lncf Q p2 (large_node p21 (repair_cr Q p1 t11 τ1 t211) τ21 t21n) τ2 t22)).
        **exfalso. apply n. intros ???. inv H2. eapply l; eauto. constructor. inv H4; constructor. assumption.
        **inv Hwf. erewrite IHt21_1; eauto. inv H7; try constructor. exfalso.
          apply n0. intros ???. inv H2. inv H4.
          ***apply conflict_right_well_formed in H1. inv H1. inv H3.
          ***inv H3.
Qed.

Lemma repair_top_assoc g X Q p1 t11 τ1 p2 t21 τ2 t22 :
  complete_crules Q →
  right_dangling p1 → left_dangling p2 → wft g X (large_node p1 t11 τ1 (large_node p2 t21 τ2 t22)) →
  repair_top Q p1 t11 τ1 (repair_top Q p2 t21 τ2 t22) = repair_top Q p2 (repair_top Q p1 t11 τ1 t21) τ2 t22.
Proof.
  intro. revert X p1 τ1 p2 t21 τ2 t22. induction t11 as [a11|p11 opt_a11|p11 t111 ? τ11 t11n];
    intros ??????? HL HR Hwft; simpl.
  - inv Hwft. inv H8. erewrite repair_top_repair_cr_assoc; eauto. intros ???. inv H1.
  - inv Hwft. inv H8. erewrite repair_top_repair_cr_assoc; eauto. intros ???. inv H1.
  - destruct (decide (lncf Q p1 (large_node p11 t111 τ11 t11n) τ1 (repair_top Q p2 t21 τ2 t22))).
    + destruct (decide (lncf Q p1 (large_node p11 t111 τ11 t11n) τ1 t21)).
      * inv Hwft. inv H8. erewrite repair_top_repair_cr_assoc; eauto. intros ???. eapply l0; eauto.
        constructor. assumption.
      * destruct n. intros ???. inv H1. eapply l; eauto. constructor. assumption.
    + destruct (decide (lncf Q p1 (large_node p11 t111 τ11 t11n) τ1 t21)).
      * destruct n. intros ???. inv H1. eapply l; eauto. constructor. assumption.
      * inv Hwft. inv H6. inv H8.
        assert (Xn0 = E). {
          inv H12; auto. exfalso. apply n. intros ???. inv H1. inv H3.
          - apply conflict_left_well_formed in H0. inv H0. inv H2.
          - inv H2.
        }
        subst.
        assert (wft g E
          (large_node (large_production E σ E) t11n τ1 (large_node (large_production X1 σ1 Xn1) t21 τ2 t22))). {
          constructor; auto.
          constructor; auto.
        }
        erewrite IHt11n; eauto.
        erewrite IHt11_1; eauto. constructor. 
        constructor; auto. constructor; auto.
        inv HR. apply repair_top_well_formed. constructor; auto.
Qed.

Lemma reorder_step_repair g X Q t1 t2 :
  complete_crules Q → wft g X t1 → wft g X t2 → reorder_step t1 t2 → repair Q t1 = repair Q t2.
Proof.
  intros. revert H0 H1. revert X. induction H2 using reorder_step_tree_list_rec with
    (P0 := fun τ τ' H => ∀ Xs, wfτ g Xs τ → wfτ g Xs τ' → repair_list Q τ = repair_list Q τ'); intros; simpl.
  - inv H0. inv H1. erewrite repair_top_assoc; eauto.
    + inv H10. constructor.
    + inv H6. constructor.
    + constructor; eauto.
      * apply repair_well_formed. assumption.
      * apply repair_list_well_formed. assumption.
      * inv H10. constructor; auto.
        **apply repair_well_formed. assumption.
        **apply repair_list_well_formed. assumption.
        **apply repair_well_formed. assumption.
  - inv H0. inv H1. erewrite IHreorder_step; eauto.
  - inv H0. inv H1. erewrite IHreorder_step; eauto.
  - inv H0. inv H1. erewrite IHreorder_step; eauto.
  - inv H0. inv H1. erewrite IHreorder_step; eauto.
  - inv H0. inv H1. erewrite IHreorder_step; eauto.
Qed.

Lemma reorder_repair g X1 X2 Q t1 t2 :
  complete_crules Q → wft g X1 t1 → wft g X2 t2 → reorder t1 t2 → repair Q t1 = repair Q t2.
Proof.
  intros. induction H2; auto.
  inv H2.
  - eapply reorder_step_well_formed in H4 as ?; eauto.
    rewrite <- IHrtc; auto. erewrite reorder_step_repair; eauto.
  - eapply reorder_step_well_formed_2 in H4 as ?; eauto.
    rewrite <- IHrtc; auto. symmetry. erewrite reorder_step_repair; eauto.
Qed.

End MixfixReorderRepair2.
