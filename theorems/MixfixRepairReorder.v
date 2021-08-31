From disamb Require Export MixfixRepair.
From disamb Require Import MyUtils.
From disamb Require Import MixfixRepairWellformed.

Section MixfixRepairReorder.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool) (Q : crules T).

Lemma reorder_t1 p t1 t1' τ tn :
  reorder t1 t1' → reorder (large_node p t1 τ tn) (large_node p t1' τ tn).
Proof.
  intro. induction H.
  - reflexivity.
  - eapply rtc_l; eauto. inv H.
    + apply sc_lr. constructor. assumption.
    + apply sc_rl. constructor. assumption.
Qed.

Lemma reorder_τ p t1 τ τ' tn :
  reorder_list τ τ' → reorder (large_node p t1 τ tn) (large_node p t1 τ' tn).
Proof.
  intro. induction H.
  - reflexivity.
  - eapply rtc_l; eauto. inv H.
    + apply sc_lr. constructor. assumption.
    + apply sc_rl. constructor. assumption.
Qed.

Lemma reorder_tn p t1 τ tn tn' :
  reorder tn tn' → reorder (large_node p t1 τ tn) (large_node p t1 τ tn').
Proof.
  intro. induction H.
  - reflexivity.
  - eapply rtc_l; eauto. inv H.
    + apply sc_lr. constructor. assumption.
    + apply sc_rl. constructor. assumption.
Qed.

Lemma reorder_list_head t t' τ :
  reorder t t' → reorder_list (parse_cons t τ) (parse_cons t' τ).
Proof.
  intro. induction H.
  - reflexivity.
  - eapply rtc_l; eauto. inv H.
    + apply sc_lr. constructor. assumption.
    + apply sc_rl. constructor. assumption.
Qed.

Lemma reorder_list_tail t τ τ' :
  reorder_list τ τ' → reorder_list (parse_cons t τ) (parse_cons t τ').
Proof.
  intro. induction H.
  - reflexivity.
  - eapply rtc_l; eauto. inv H.
    + apply sc_lr. constructor. assumption.
    + apply sc_rl. constructor. assumption.
Qed.

Lemma repair_cr_reorder g X Q p t1 τ tn :
  wft g X (large_node p t1 τ tn) →
  reorder (large_node p t1 τ tn) (repair_cr Q p t1 τ tn).
Proof.
  revert X. induction tn as [an|pn opt_an|pn tn1 ? τn tnn]; intros; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (decide (rncf Q p t1 τ (large_node pn tn1 τn tnn))).
    + reflexivity.
    + inv H. inv H8.
      assert (X0 = E). {
        inv H9; auto. destruct n. intros ???. inv H0. inv H2.
        - apply conflict_right_well_formed in H. inv H. inv H1.
        - inv H1.
      }
      subst.
      eapply rtc_l.
      * apply sc_lr. constructor.
        inv H9; constructor.
      * apply reorder_t1. eapply IHtn1. constructor; auto.
Qed. 

Lemma repair_top_reorder g X Q p t1 τ tn :
  wft g X (large_node p t1 τ tn) →
  reorder (large_node p t1 τ tn) (repair_top Q p t1 τ tn).
Proof.
  revert X p τ tn. induction t1 as [a1|p1 opt_a1|p1 t11 ? τ1 t1n]; intros; simpl.
  - eapply repair_cr_reorder; eauto.
  - eapply repair_cr_reorder; eauto.
  - destruct (decide (lncf Q p (large_node p1 t11 τ1 t1n) τ tn)).
    + eapply repair_cr_reorder; eauto.
    + inv H. inv H6.
      assert (Xn0 = E). {
        inv H11; auto. destruct n. intros ???. inv H0. inv H2.
        - apply conflict_left_well_formed in H. inv H. inv H1.
        - inv H1.
      }
      subst.
      eapply rtc_l. apply sc_rl. constructor. inv H11; constructor.
      eapply rtc_transitive.
      eapply reorder_tn. eapply IHt1n. constructor; auto.
      eapply IHt1_1. constructor; auto. apply repair_top_well_formed. constructor; auto.
Qed.  


Lemma repair_reorder g X Q t :
  wft g X t → reorder t (repair Q t).
Proof.
  revert X. induction t as [a|p opt_a|p t1 ? τ ? tn| |t ? τ] using parse_tree_list_rec with
      (P0 := fun τ => ∀ σ, wfτ g σ τ → reorder_list τ (repair_list Q τ)); intros; simpl.
  - reflexivity.
  - reflexivity.
  - inv H.
    eapply rtc_transitive.
    apply reorder_t1. eapply IHt1. eassumption.
    eapply rtc_transitive.
    apply reorder_τ. eapply IHt2. eassumption.
    eapply rtc_transitive.
    apply reorder_tn. eapply IHtn. eassumption.
    eapply repair_top_reorder. constructor; eauto using repair_well_formed, repair_list_well_formed.
  - reflexivity.
  - inv H.
    eapply rtc_transitive.
    eapply reorder_list_head. eapply IHt. eassumption.
    apply reorder_list_tail. eapply IHt0. eassumption.
Qed.

End MixfixRepairReorder.
