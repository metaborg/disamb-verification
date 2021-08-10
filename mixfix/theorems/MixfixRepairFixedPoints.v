From disamb Require Export MixfixRepair2.
From disamb Require Export MixfixUtilsTheorems.
From disamb Require Import MyUtils.


Section MixfixRepairFixedPoints.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)) (b : bool) (Q : crules T).

Lemma repair_cr_conflict_free_fixed Q p ts tn :
  (∀ p2, p CR p2 ∠ Q → ¬ p2 LM tn) → repair_cr Q p ts tn = (node p (add_last ts tn), false).
Proof.
  induction tn using parse_tree_forest_rec with
    (P0 := fun tns =>
      ∀ pn, (∀ p2, p CR p2 ∠ Q → ¬ p2 LMf tns) → ¬ p CR pn ∠ Q →
      repair_cr_forest Q p pn ts tns = (node p (add_last ts (node pn tns)), false)); auto; intros.
  - rename p0 into pn, p1 into tns. simpl.
    apply IHtn. intros ???. eapply H; eauto. constructor. assumption.
    intro. eapply H; eauto. constructor.
  - rename tn into tns1, p0 into tns. simpl.
    destruct (repair_cr Q p ts tns1) eqn:?.
    destruct (decide (b = true ∨ p CR pn ∠ Q)); auto.
    exfalso.
    destruct o.
    + subst. assert ((p0, true) = (node p (add_last ts tns1), false)). {
        apply IHtn. intros ???. apply H with p2; auto. constructor. assumption.
      }
      inv H1.
    + contradiction.
Qed.

Lemma split_last_lmcf Q p t1 ts tsh tn :
  rncf Q p (cons_forest t1 ts) → split_last t1 ts = (tsh, tn) → ∀ p2, p CR p2 ∠ Q → ¬ p2 LM tn.
Proof.
  revert t1 tsh. induction ts; intros ???????.
  - simpl in H0. inv H0. apply H with p2; auto. constructor. constructor. assumption.
  - rename p0 into t2. simpl in H0. destruct (split_last t2 ts) eqn:?. inv H0.
    eapply IHts; eauto. intros ???. apply H with p1; auto.
    inv H3. constructor. constructor. assumption.
Qed.

Lemma repair_cr_start_conflict_free_fixed Q t :
  cf Q t → repair_cr_start Q t = t.
Proof.
  intro. destruct t; auto. rename p0 into ts. simpl.
  destruct ts; auto. rename p0 into t1.
  destruct (split_last t1 ts) as (tsh, tn) eqn:?.
  destruct (repair_cr Q p tsh tn) as (t', b) eqn:?.
  inv H. assert (∀ p2, p CR p2 ∠ Q → ¬ p2 LM tn). {
    eapply split_last_lmcf; eauto. 
  }
  rewrite repair_cr_conflict_free_fixed in Heqp1; auto. inv Heqp1.
  erewrite split_last_add_last; eauto.
Qed.

Lemma repair_cl_conflict_free_fixed Q p t1 ts :
  cf Q (node p (cons_forest t1 ts)) → repair_cl Q p t1 ts = node p (cons_forest t1 ts).
Proof.
  intro. destruct t1; cbn [repair_cl].
  - destruct (decide (∀ p2 : production T, p CL p2 ∠ Q → ¬ p2 RM leaf t)).
    + auto using repair_cr_start_conflict_free_fixed.
    + exfalso. apply n. intros ???. inv H1.
  - rename p0 into p1, p1 into t1s.
    destruct (decide (∀ p2 : production T, p CL p2 ∠ Q → ¬ p2 RM node p1 t1s)).
    + auto using repair_cr_start_conflict_free_fixed.
    + exfalso. apply n. intros ???. inv H. apply H4 with p2; auto. constructor. assumption.
Qed.

Lemma repair_cl_start_conflict_free_fixed Q p ts :
  cf Q (node p ts) → repair_cl_start Q p ts = node p ts.
Proof.
  intro. destruct ts.
  - reflexivity.
  - rename p0 into t. simpl. auto using repair_cl_conflict_free_fixed.
Qed.

Lemma repair_conflict_free_fixed Q t :
  cf Q t → repair Q t = t.
Proof.
  induction t using parse_tree_forest_rec
      with (P0 := fun ts => cff Q ts → repair_forest Q ts = ts).
  - intro. reflexivity.
  - rename p0 into ts. intro. simpl. assert (H' := H). inv H. rewrite IHt; auto.
    auto using repair_cl_start_conflict_free_fixed.
  - intros. reflexivity.
  - intros. simpl. inv H. rewrite IHt; auto. rewrite IHt0; auto.
Qed.

End MixfixRepairFixedPoints.
