From disamb Require Export MixfixRepair.
From disamb Require Import MyUtils.

Section MixfixRepairConflictFree.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool) (Q : crules T).

Lemma repair_cr_rm Q px p t1 τ tn :
  px RM repair_cr Q p t1 τ tn → px RM tn ∨ px = p.
Proof.
  intro. induction tn as [an|pn opt_an|pn tn1 ? τn tnn]; simpl in H.
  - inv H; auto.
  - inv H; auto.
  - destruct (decide (rncf Q p t1 τ (large_node pn tn1 τn tnn))).
    + inv H; auto.
    + left. inv H; constructor. assumption.
Qed.

Lemma repair_cr_cf Q p t1 τ tn :
  safe_crules Q → cf Q t1 → cfl Q τ → cf Q tn → lncf Q p t1 τ tn → cf Q (repair_cr Q p t1 τ tn).
Proof.
  intros. induction tn as [an|pn opt_an|pn tn1 ? τn tnn]; simpl.
  - constructor; auto. intros ???. inv H5. inv H7.
  - constructor; auto. intros ???. inv H5. inv H7.
  - destruct (decide (rncf Q p t1 τ (large_node pn tn1 τn tnn))).
    + constructor; auto.
    + inv H2. constructor; auto.
      * intros ???. inv H4.
        eapply H8; eauto. constructor.
        apply repair_cr_rm in H6 as ?. destruct H4; auto. subst.
        destruct tn1 as [an1|pn1 opt_an1|pn1 tn11 τn1 tn1n]; simpl in H6.
        **destruct n. intros ???. inv H5. inv H13.
          ***eapply H; eauto.
          ***inv H7.
        **destruct n. intros ???. inv H5. inv H13.
          ***eapply H; eauto.
          ***inv H7.
        **destruct (decide (rncf Q p t1 τ (large_node pn1 tn11 τn1 tn1n))).
          ***destruct n. intros ???. inv H5. inv H13.
            ****eapply H; eauto.
            ****inv H7.
              *****eapply r; eauto. constructor. constructor.
              *****eapply r; eauto. constructor. constructor. assumption.
          ***inv H6; constructor. assumption.
      * intros ???. inv H4. eapply H9; eauto. constructor. assumption.
      * apply IHtn1; auto. intros ???. eapply H3; eauto.
        inv H4; constructor. assumption.
Qed.

Lemma repair_top_cf Q p t1 τ tn :
  safe_crules Q → cf Q t1 → cfl Q τ → cf Q tn → cf Q (repair_top Q p t1 τ tn).
Proof.
  intros ??. revert p τ tn. induction t1 as [a1|p1 opt_a1|p1 t11 ? τ1 t1n]; intros; simpl.
  - apply repair_cr_cf; auto. intros ???. inv H4. inv H6.
  - apply repair_cr_cf; auto. intros ???. inv H4. inv H6.
  - destruct (decide (lncf Q p (large_node p1 t11 τ1 t1n) τ tn)).
    + apply repair_cr_cf; auto.
    + inv H0. auto.
Qed. 

Lemma repair_conflict_free Q t :
  safe_crules Q → cf Q (repair Q t).
Proof.
  intro Hsafe. induction t as [a|p opt_a|p t1 ? τ tn| |t ? τ] using parse_tree_list_rec with
      (P0 := fun τ => cfl Q (repair_list Q τ)); simpl.
  - constructor.
  - constructor.
  - apply repair_top_cf; auto.
  - constructor.
  - constructor; auto.
Qed.

End MixfixRepairConflictFree.
