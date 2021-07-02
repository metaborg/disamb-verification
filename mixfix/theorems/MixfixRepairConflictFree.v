From disamb Require Export MixfixRepair.
From disamb Require Export MixfixUtilsTheorems.
From disamb Require Import MyUtils.

Section MixfixRepairConflictFree.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)) (b : bool) (Q : crules T).

Lemma add_last_rncf Q p ts t :
  (∀ p2, p CR p2 ∠ Q → p2 LM t → False) → rncf Q p (add_last ts t).
Proof.
  intros Hnlm p2 Hcr Hrn. induction ts; simpl in Hrn.
  - inv Hrn.
    inv H0.
    eauto.
    inv H1.
  - inv Hrn.
    inv H0.
    destruct ts; inv H2.
    apply IHts.
    constructor. assumption.
Qed.

Lemma add_last_cff Q ts tn :
  cff Q ts → cf Q tn → cff Q (add_last ts tn).
Proof.
  intros Hcff Hcf.
  induction Hcff; simpl.
  - constructor; auto. constructor.
  - constructor; auto.
Qed.

Lemma repair_cr_forest_true_conflict Q p pn ts tns t' :
  repair_cr_forest Q p pn ts tns = (t', true) → ∃ p2, p CR p2 ∠ Q ∧ (p2 = pn ∨ p2 LMf tns).
Proof.
  revert t' pn.
  induction tns using parse_forest_tree_rec with
    (P := fun tn => ∀ t', repair_cr Q p ts tn = (t', true) →
                            ∃ p2, p CR p2 ∠ Q ∧ p2 LM tn); simpl.
  - intros. inv H.
  - rename p0 into pn.
    intros. 
    apply IHtns in H.
    destruct H as [p2].
    exists p2. destruct H.
    split; auto.
    destruct H0.
    + subst.
      constructor.
    + constructor.
      assumption.
  - intros. inv H.
  - rename p0 into tn.
    intros.
    destruct (repair_cr Q p ts tn) as [tn1' b] eqn:E.
    destruct (decide (b = true ∨ p CR pn ∠ Q)).
    + inv H.
      destruct o.
      * subst.
        edestruct IHtns as [p2]; eauto.
        destruct H.
        exists p2.
        split; auto.
        right.
        constructor.
        assumption.
      * exists pn.
        split; auto.
    + inv H.
Qed.

Lemma repair_cr_forest_conflict_true g X Q p p2 pn ts tns t' :
  wft g X (node pn tns) →
  p CR p2 ∠ Q →
  (p2 = pn ∨ p2 LMf tns) →
  ∃ t', repair_cr_forest Q p pn ts tns = (t', true).
Proof.
  intros.
  inv H.
  revert H1 H5 H6.
  revert pn.
  induction tns using parse_forest_tree_rec with
    (P := fun tn => ∀ X, wft g X tn → p CR p2 ∠ Q → p2 LM tn → ∃ t', repair_cr Q p ts tn = (t', true)); simpl.
  - intros.
    inv H2.
  - intros.
    inv H.
    apply IHtns in H7; auto.
    inv H2; auto.
  - intros.
    exfalso.
    inv H6.
    destruct H1.
    + subst.
      apply conflict_right_well_formed in H0.
      destruct H0.
      inv H0.
    + inv H.
  - intros.
    inv H6.
    destruct (repair_cr Q p ts p0) eqn:E.
    destruct (decide (b = true ∨ p CR X :: Xs ∠ Q)).
    + eexists. eauto.
    + exfalso.
      apply IHtns in H4; auto. {
        destruct H4.
        inv H.
        apply n.
        auto.
      } {
        destruct H1.
        - exfalso.
          subst.
          apply n.
          auto.
        - inv H.
          assumption.
      }
Qed.

Lemma add_last_lncf Q p ts tn1 tn2 :
  ts ≠ nil_forest →
  lncf Q p (add_last ts tn1) →
  lncf Q p (add_last ts tn2).
Proof.
  intros ?????.
  destruct ts; simpl in *.
  - contradiction.
  - inv H2.
    eapply H0; eauto.
    constructor.
    assumption.
Qed.

Lemma add_last_rmf p ts tn :
  p RMf add_last ts tn → p RM tn.
Proof.
  intro.
  induction ts; simpl in H.
  - inv H; auto.
    inv H1.
  - apply IHts.
    inv H; auto.
    destruct ts; inv H2.
Qed.

Lemma add_last_lm_rnf p ts tn :
  p LM tn ↔ p RNf add_last ts tn.
Proof.
  split.
  - intro.
    induction ts; simpl.
    + constructor.
      assumption.
    + constructor.
      assumption.
  - intro.
    induction ts; simpl in H.
    + inv H.
      assumption.
      inv H1.
    + apply IHts.
      inv H.
      destruct ts; inv H2.
      assumption.
Qed.

Lemma repair_cr_conflict_free g X Q p ts tn t' b :
  safe_crules Q →
  ts ≠ nil_forest →
  wft g X tn →
  lncf Q p (add_last ts tn) →
  cff Q ts →
  cf Q tn →
  repair_cr Q p ts tn = (t', b) →
  cf Q t'.
Proof.
  intro Hsafe. intros. revert H H0 H1 H2 H4. revert t' X b.
  induction H3 using conflict_free_tree_forest
    with (P0 := fun tns IHcfftns => ∀ X pn t' b,
                                             ts ≠ nil_forest →
                                             wft g X (node pn tns) →
                                             cff Q ts →
                                             lncf Q p (add_last ts (node pn tns)) →
                                             lncf Q pn tns →
                                             rncf Q pn tns →
                                             repair_cr_forest Q p pn ts tns = (t', b) →
                                             cf Q t').
  - simpl.
    intros.
    inv H4.
    constructor; auto.

    apply add_last_rncf.
    intros.
    inv H4.

    apply add_last_cff; auto.
    constructor.
  - rename p0 into pn, ts0 into tns.
    simpl.
    intros.
    eapply IHconflict_free; eauto.
  - simpl.
    intros ????????? Hrncf ?.
    inv H4.
    constructor; auto.

    apply add_last_rncf.
    intros.
    inv H5.
    inv H0.
    inv H9.
    apply conflict_right_well_formed in H4. destruct H4.
    inv H4.
    inv H7.

    apply add_last_cff; auto.
    constructor.
    intros ???. inv H5.
    intros ???. inv H5. inv H7.
    constructor.
  - rename t into tn1, ts0 into tns.
    intros ????????? Hrncf ?.
    assert (Hrep := H5).
    simpl in H5.
    destruct (repair_cr Q p ts tn1) as [tns' bn] eqn:Hreptns1.
    destruct (decide (bn = true ∨ p CR pn ∠ Q)).
    + inv H5.
      apply repair_cr_forest_true_conflict in Hrep.
      destruct Hrep as [p2]. destruct H5.
      inv H0.
      inv H11.
      apply IHconflict_free with (t' := tns') (b := bn) in H9 as ?; eauto using add_last_lncf.
      constructor. {
        intros p3 ??.
        inv H8.
        destruct tn1 as [a|pn1 tn1s]; simpl in Hreptns1.
        - inv Hreptns1.
          inv H13.
          + destruct o.
            inv H8.
            eapply Hsafe; eauto.
          + apply add_last_rmf in H11.
            inv H11.
        - destruct tn1s as [|tn11 tn1s]; simpl in Hreptns1.
          + inv Hreptns1.
            inv H13.
            * destruct o.
              inv H8.
              eapply Hsafe; eauto.
            * apply add_last_rmf in H11.
              apply H4 with p3; auto.
              constructor.
              assumption.
          + destruct (repair_cr Q p ts tn11) as [tn11' bn11] eqn:Hreptn11.
            destruct (decide (bn11 = true ∨ p CR pn1 ∠ Q)).
            * inv Hreptns1.
              inv H13.
              **apply H4 with pn1; auto.
                constructor. constructor.
              **apply H4 with p3; auto.
                constructor. constructor.
                inv H11.
                ***exfalso.
                  inv H9.
                  inv H16.
                  inv H17.
                  inv H14.
                  ****simpl in Hreptn11.
                    inv Hreptn11.
                    destruct o0.
                    inv H8.
                    apply conflict_right_well_formed in H8. destruct H8.
                    inv H9.
                  ****eapply acyclic_productions; eauto.
                ***constructor.
                  assumption.
            * inv Hreptns1.
              inv H13.
              **destruct o.
                inv H8.
                eapply Hsafe; eauto.
              **apply add_last_rmf in H11.
                apply H4 with p3; auto.
                constructor.
                assumption.
      } {
        intros p3 ??.
        inv H8.
        inv H13.
        - inv H12.
          apply conflict_right_well_formed in H7. destruct H7.
          inv H7.
          eapply acyclic_productions; eauto.
          inv H13.
        - apply Hrncf with p3; auto.
          constructor.
          constructor.
          assumption.
      } {
        constructor; auto.
      }
    + inv H5. constructor; auto. {
        intros ???.
        inv H6.
        apply add_last_lm_rnf in H8.
        eapply repair_cr_forest_conflict_true with (ts := ts) in H0; eauto. {
          destruct H0.
          rewrite Hrep in H0.
          inv H0.
        } {
          inv H8; auto.
        }
      } {
        apply add_last_cff; auto.
        constructor; auto.
        constructor; auto.
      }
Qed.

Lemma split_last_cf Q t ts tsh tn :
  cf Q t →
  cff Q ts →
  split_last t ts = (tsh, tn) →
  cff Q tsh ∧ cf Q tn.
Proof.
  intros Hcf Hcff.
  revert Hcf. revert t tsh.
  induction Hcff; simpl; intros.
  - inv H.
    split.
    constructor.
    assumption.
  - destruct (split_last t ts) eqn:?.
    inv H0.
    apply IHHcff in Heqp; auto.
    destruct Heqp.
    split; auto.
    constructor; assumption.
Qed.


Lemma repair_cr_start_conflict_free g X Q t :
  safe_crules Q →
  wft g X t →
  match t with
  | leaf a => True
  | node p ts => lncf Q p ts ∧ cff Q ts
  end → cf Q (repair_cr_start Q t).
Proof.
  intros.
  inv H0; simpl.
  - constructor.
  - destruct H1.
    destruct ts as [|t1 ts].
    + constructor. {
        intros ???.
        inv H5.
      } {
        intros ???.
        inv H5.
        inv H7.
      } {
        constructor.
      }
    + inv H3.
      inv H1.
      destruct (split_last t1 ts) as [tsh tn] eqn:?.
      destruct (repair_cr Q (X :: Xs) tsh tn) as [t' b] eqn:?.
      eapply split_last_cf in Heqp as ?; eauto.
      destruct H1.
      destruct ts as [|t2 ts]; inv H8.
      * inv Heqp.
        inv H7.
        **inv Heqp0.
          constructor; auto. {
            intros ???.
            inv H7. inv H9. inv H8. inv H8.
          } {
            repeat constructor.
          }
        **exfalso.
          eapply acyclic_productions; eauto.
      * simpl in Heqp.
        destruct (split_last t2 ts) as [tsh2 tnm1] eqn:?.
        inv Heqp.
        eapply split_last_wf in Heqp1 as ?; eauto.
        destruct H4 as [Xn].
        eapply repair_cr_conflict_free in Heqp0; eauto.
        intros ???.
        inv H9.
        apply H0 with p2; auto.
        constructor.
        assumption.
Qed.  

End MixfixRepairConflictFree.
