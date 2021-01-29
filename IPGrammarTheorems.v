Require Import MyUtils.
Require Export IPGrammar.

Section IPGrammarTheorems.

Create HintDb IPGrammar.
Hint Resolve CPrio_infix_infix_1 : IPGrammar.
Hint Resolve CPrio_infix_infix_2 : IPGrammar.
Hint Resolve CPrio_prefix_infix : IPGrammar.
Hint Resolve CLeft : IPGrammar.
Hint Resolve CRight : IPGrammar.
Hint Resolve HMatch : IPGrammar.
Hint Resolve InfixMatch : IPGrammar.
Hint Resolve PrefixMatch : IPGrammar.
Hint Resolve Atomic_wf : IPGrammar.
Hint Resolve Infix_wf : IPGrammar.
Hint Resolve Prefix_wf : IPGrammar.
Hint Resolve Atomic_cf : IPGrammar.
Hint Resolve Atomic_drmcf : IPGrammar.

Lemma is_i_conflict_pattern_true {g} (pr : drules g) q :
  i_conflict_pattern pr q <-> is_i_conflict_pattern pr q = true.
Proof.
  split; intro.
  - inv H; simpl; auto using decide_True, decide_False.
    + destruct (decide (prio pr (InfixProd o1) (InfixProd o2))); auto using decide_True, decide_False.
    + destruct (decide (prio pr (InfixProd o1) (InfixProd o2))); auto using decide_True, decide_False.
  - destruct q; inv H.
    + destruct q1, q2; inv H1.
      * destruct q2_1, q2_2; inv H0.
        destruct (decide (prio pr (InfixProd o) (InfixProd o0))); eauto with IPGrammar.
        destruct (decide (left_a pr (InfixProd o) (InfixProd o0))); eauto with IPGrammar.
        inv H1.
      * destruct q1_1, q1_2; inv H0.
        destruct (decide (prio pr (InfixProd o) (InfixProd o0))); eauto with IPGrammar.
        destruct (decide (right_a pr (InfixProd o) (InfixProd o0))); eauto with IPGrammar.
        inv H1.
      * destruct q1_1, q1_2; inv H0.
      * destruct q1_1, q1_2; inv H0.
    + destruct q; inv H1.
      destruct q1, q2; inv H0.
      destruct (decide (prio pr (PrefixProd o) (InfixProd o0))); eauto with IPGrammar.
      inv H1.
Qed.

Lemma is_i_conflict_pattern_false {g} (pr : drules g) q :
  ~ i_conflict_pattern pr q <-> is_i_conflict_pattern pr q = false.
Proof.
  split; intro.
  - destruct (is_i_conflict_pattern pr q) eqn:E; auto.
    exfalso. destruct H. apply is_i_conflict_pattern_true.
    assumption.
  - intro. apply is_i_conflict_pattern_true in H0.
    rewrite H in H0. inv H0.
Qed.

Lemma safe_infix_infix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o1) ->
  False.
Proof.
  intros H_safe H_CL H_CR. unfold safe_pr in H_safe.
  inv H_CL; inv H_CR; eauto.
Qed.

Lemma safe_infix_prefix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  rm_conflict_pattern pr (CL_infix_prefix o1 o2) ->
  i_conflict_pattern pr (CR_prefix_infix o2 o1) ->
  False.
Proof.
  intros. unfold safe_pr in H.
  inv H0; inv H1; eauto.
Qed.

Ltac linsert_lo_inode_destruct pr o1 o2 :=
    cbn [linsert_lo] in *;
     destruct (is_i_conflict_pattern pr (CR_infix_infix o1 o2)) eqn:E;
     [apply is_i_conflict_pattern_true in E | apply is_i_conflict_pattern_false in E].

Ltac linsert_o_inode_destruct pr o1 o2 :=
    cbn [linsert_o] in *;
     destruct (is_i_conflict_pattern pr (CR_prefix_infix o1 o2)) eqn:E;
     [apply is_i_conflict_pattern_true in E | apply is_i_conflict_pattern_false in E].

Lemma linsert_lo_wf {g} (pr : drules g) l1 o t2 :
  wf_parse_tree g t2 ->
  g.(prods) (InfixProd o) ->
  wf_parse_tree g (linsert_lo pr l1 o t2).
Proof.
  intros. induction H; eauto with IPGrammar.
  linsert_lo_inode_destruct pr o o0; auto with IPGrammar.
Qed.

Lemma linsert_o_wf {g} (pr : drules g) o t2 :
  wf_parse_tree g t2 ->
  g.(prods) (PrefixProd o) ->
  wf_parse_tree g (linsert_o pr o t2).
Proof.
  intros. induction H; eauto with IPGrammar.
  linsert_o_inode_destruct pr o o0; auto with IPGrammar.
Qed.

Lemma linsert_to_wf {g} (pr : drules g) t1 o t2 :
  wf_parse_tree g t1 ->
  wf_parse_tree g t2 ->
  g.(prods) (InfixProd o) ->
  wf_parse_tree g (linsert_to pr t1 o t2).
Proof.
  intro.
  revert t2 o. induction H; simpl; auto using linsert_lo_wf, linsert_o_wf.
Qed.

Lemma repair_wf {g} (pr : drules g) t :
  wf_parse_tree g t ->
  wf_parse_tree g (repair pr t).
Proof.
  intro. induction H; simpl; auto using linsert_o_wf, linsert_to_wf with IPGrammar.
Qed.

Lemma linsert_lo_yield_preserve {g} (pr : drules g) l1 o t2 :
  yield (linsert_lo pr l1 o t2) = inl l1 :: inr o :: yield t2.
Proof.
  induction t2; try reflexivity.
  linsert_lo_inode_destruct pr o o0; simpl; auto.
  rewrite IHt2_1. reflexivity.
Qed.

Lemma linsert_o_yield_preserve {g} (pr : drules g) o t2 :
  yield (linsert_o pr o t2) = inr o :: yield t2.
Proof.
  induction t2; try reflexivity.
  linsert_o_inode_destruct pr o o0; simpl; auto.
  rewrite IHt2_1. reflexivity.
Qed.

Lemma linsert_to_yield_preserve {g} (pr : drules g) t1 o t2 :
  yield (linsert_to pr t1 o t2) = yield t1 ++ inr o :: yield t2.
Proof.
  revert o t2.
  induction t1; intros; simpl.
  - auto using linsert_lo_yield_preserve.
  - simplify_list_eq. rewrite <- IHt1_2. rewrite <- IHt1_1.
    reflexivity.
  - rewrite <- IHt1.
    auto using linsert_o_yield_preserve.
Qed.

Lemma repair_yield_preserve {g} (pr : drules g) t :
  yield (repair pr t) = yield t.
Proof.
  induction t; simpl.
  - reflexivity.
  - rewrite <- IHt2. auto using linsert_to_yield_preserve.
  - rewrite <- IHt. auto using linsert_o_yield_preserve.
Qed.

Lemma i_conflict_pattern_cases {g} (pr : drules g) q :
  i_conflict_pattern pr q -> exists o1 o2,
  q = CR_infix_infix o1 o2 \/
  q = CL_infix_infix o1 o2 \/
  q = CR_prefix_infix o1 o2.
Proof.
  intros. inv H; eauto.
Qed.

Ltac icp_cases H :=
  apply i_conflict_pattern_cases in H as T; destruct T as [? T1]; destruct T1 as [? T2];
  destruct T2 as [T4|T3]; [|destruct T3 as [T4|T4]]; rewrite T4 in *; clear T4.

Lemma inode_single_icfree {g} (pr : drules g) l1 o l2 :
  i_conflict_free (i_conflict_pattern pr)
    (InfixNode (AtomicNode l1) o (AtomicNode l2)).
Proof.
  apply Infix_cf; auto using Atomic_cf.
  intro. inv H. destruct H0.
  icp_cases H; inv H0. inv H8. inv H3.
Qed.

Lemma linsert_lo_top {g} (pr : drules g) l1 o t2 :
  matches (linsert_lo pr l1 o t2) (InfixPatt HPatt o HPatt) \/
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (linsert_lo pr l1 o t2) (InfixPatt HPatt o2 HPatt)).
Proof.
  destruct t2; eauto 6 with IPGrammar.
  linsert_lo_inode_destruct pr o o0; eauto 6 with IPGrammar.
Qed.

Lemma linsert_lo_icfree {g} (pr : drules g) l1 o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  i_conflict_free (i_conflict_pattern pr) (linsert_lo pr l1 o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22].
  - simpl. apply inode_single_icfree.
  - linsert_lo_inode_destruct pr o o2.
    + inv H0. apply Infix_cf; auto with IPGrammar.
      intro. destruct H0 as [q]. inv H0. icp_cases H1.
      * inv H2. rename x into o2. inv H12. rename x0 into o22, t1 into t221, t2 into t222.
        clear H7 H8 H10.
        apply H4. eexists. eauto with IPGrammar.
      * inv H2. clear H12. rename x into o2.
        inv H7. clear H8 H10.
        destruct (linsert_lo_top pr l1 o t21).
        **rewrite <- H0 in H2. inv H2.
          eauto using safe_infix_infix.
        **destruct H2 as [o21]. inv H2.
          rewrite <- H0 in H7.
          inv H7. inv H3. clear H9 H14 H10 H12.
          apply H4. eexists. eauto with IPGrammar.
      * inv H2.
    + apply Infix_cf; auto with IPGrammar.
      intro. destruct H1 as [q]. inv H1.
      icp_cases H2; inv H3.
      * inv H10. contradiction.
      * inv H5.
  - simpl. apply Infix_cf; auto with IPGrammar.
    intro. destruct H1 as [q]. inv H1.
    icp_cases H2; inv H3. inv H10. inv H5.
Qed.

Lemma linsert_o_top {g} (pr : drules g) o t2 :
  matches (linsert_o pr o t2) (PrefixPatt o HPatt) \/
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (linsert_o pr o t2) (InfixPatt HPatt o2 HPatt)).
Proof.
  destruct t2; eauto 6 with IPGrammar.
  linsert_o_inode_destruct pr o o0; eauto 6 with IPGrammar.
Qed.

Lemma linsert_o_icfree {g} (pr : drules g) o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  i_conflict_free (i_conflict_pattern pr) (linsert_o pr o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22].
  - simpl. apply Prefix_cf; auto with IPGrammar.
    intro. destruct H1 as [q]. inv H1.
    icp_cases H2; inv H3. inv H4.
  - linsert_o_inode_destruct pr o o2.
    + inv H0. apply Infix_cf; auto with IPGrammar.
      intro. destruct H0 as [q]. inv H0.
      icp_cases H1; inv H2.
      * rename x into o2. inv H12. rename x0 into o22. clear H7 H8 H10.
        apply H4. eexists. eauto with IPGrammar.
      * rename x into o2. clear H12. inv H7. clear H8 H10.
        destruct (linsert_o_top pr o t21).
        **rewrite <- H0 in H2. inv H2.
        **destruct H2 as [o21]. inv H2.
          rewrite <- H0 in H7. inv H7. clear H9 H14.
          inv H3. clear H9 H11.
          apply H4. eexists. eauto with IPGrammar.
    + apply Prefix_cf; auto with IPGrammar.
      intro. destruct H1 as [q]. inv H1.
      icp_cases H2; inv H3.
      inv H4. contradiction.
  - simpl.
    apply Prefix_cf; auto with IPGrammar.
    intro. destruct H1 as [q]. inv H1.
    icp_cases H2; inv H3. inv H4.
Qed.

Lemma linsert_to_icfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  i_conflict_free (i_conflict_pattern pr) (linsert_to pr t1 o t2).
Proof.
  intro. revert o t2.
  induction t1; eauto using linsert_lo_icfree, linsert_o_icfree.
Qed.

Lemma repair_icfree {g} (pr : drules g) t :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) (repair pr t).
Proof.
  intro.
  induction t; eauto using linsert_to_icfree, linsert_o_icfree with IPGrammar.
Qed.

Lemma inode_single_drmcfree {g} (pr : drules g) l1 o l2 :
  drm_conflict_free (rm_conflict_pattern pr)
    (InfixNode (AtomicNode l1) o (AtomicNode l2)).
Proof.
  apply Infix_drmcf; auto using Atomic_drmcf.
  intro. destruct H as [q]. inv H. inv H0.
  inv H1. inv H3. inv H0.
Qed.

Lemma matches_rm_hpatt {g} (t : parse_tree g) :
  matches_rm t HPatt.
Proof.
  apply Match_rm. apply HMatch.
Qed.

Lemma linsert_lo_matches_rm {g} (pr : drules g) l1 o1 t2 o2 :
  matches_rm (linsert_lo pr l1 o1 t2) (PrefixPatt o2 HPatt) ->
  matches_rm t2 (PrefixPatt o2 HPatt).
Proof.
  intros. destruct t2.
  - simpl in H. inv H. inv H0. inv H4. inv H.
  - linsert_lo_inode_destruct pr o1 o.
    + inv H. inv H0. auto using InfixMatch_rm.
    + inv H. inv H0. assumption.
  - simpl in H. inv H. inv H0. assumption.
Qed.

Lemma linsert_lo_drmcfree {g} (pr : drules g) l1 o t2 :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t2 ->
  drm_conflict_free (rm_conflict_pattern pr) (linsert_lo pr l1 o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22].
  - simpl. apply inode_single_drmcfree.
  - linsert_lo_inode_destruct pr o o2.
    + inv H0. apply Infix_drmcf; auto.
      intro. destruct H0 as [q]. inv H0.
      destruct H4. exists q. split; try assumption.
      inv H1. inv H2.
      apply InfixMatch_drm; eauto using matches_rm_hpatt, linsert_lo_matches_rm.
    + apply Infix_drmcf; auto with IPGrammar.
      intro. destruct H1 as [q]. inv H1.
      inv H2. inv H3. inv H5. inv H2.
  - apply Infix_drmcf; auto with IPGrammar.
    intro. destruct H1 as [q]. inv H1.
    inv H2. inv H3. inv H5. inv H2.
Qed.

Lemma prefixnode_single_drmcfree {g} (pr : drules g) o l2 :
  drm_conflict_free (rm_conflict_pattern pr)
    (PrefixNode o (AtomicNode l2)).
Proof.
  apply Prefix_drmcf; auto using Atomic_drmcf.
  intro. destruct H as [q]. inv H. inv H0.
  inv H1.
Qed.

Lemma linsert_o_matches_rm {g} (pr : drules g) o t2 o2 :
  matches_rm (linsert_o pr o t2) (PrefixPatt o2 HPatt) ->
  matches_rm t2 (PrefixPatt o2 HPatt) \/ o2 = o.
Proof.
  intros. destruct t2.
  - simpl in H. inv H.
    + inv H0. auto.
    + inv H3. inv H.
  - linsert_o_inode_destruct pr o o0.
    + inv H. inv H0.
      left. auto using InfixMatch_rm.
    + inv H; auto.
      inv H0. auto.
  - inv H; auto.
    inv H0. auto.
Qed.

Lemma linsert_o_drmcfree {g} (pr : drules g) o t2 :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t2 ->
  drm_conflict_free (rm_conflict_pattern pr) (linsert_o pr o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22].
  - simpl. apply prefixnode_single_drmcfree.
  - linsert_o_inode_destruct pr o o2.
    + inv H0. apply Infix_drmcf; auto.
      intro. destruct H0 as [q]. inv H0.
      inv H1. inv H2. rename o1 into o2.
      apply linsert_o_matches_rm in H7.
      inv H7.
      * destruct H4. eexists. split. eauto using CPrio_infix_prefix.
        unfold CL_infix_prefix. apply InfixMatch_drm; auto using Match_rm, HMatch.
      * eapply safe_infix_prefix; eauto using CPrio_infix_prefix.
    + apply Prefix_drmcf; auto. intro.
      inv H1. inv H2. inv H1. inv H3.
  - apply Prefix_drmcf; auto. intro.
      inv H1. inv H2. inv H1. inv H3.
Qed.

Lemma linsert_to_drmcfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t2 ->
  drm_conflict_free (rm_conflict_pattern pr) (linsert_to pr t1 o t2).
Proof.
  intro. revert o t2.
  induction t1; simpl; auto using linsert_lo_drmcfree, linsert_o_drmcfree.
Qed.

Lemma repair_drmcfree {g} (pr : drules g) t :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) (repair pr t).
Proof.
  intro. induction t; simpl; auto using linsert_to_drmcfree, linsert_o_drmcfree with IPGrammar.
Qed.

Theorem safety {g} (pr : drules g) :
  safe_pr pr ->
  safe pr.
Proof.
  unfold safe. unfold language. unfold dlanguage. unfold conflict_free.
  intros. destruct H0 as [t]. destruct H0.
  exists (repair pr t).
  rewrite repair_yield_preserve.
  auto using repair_wf, repair_yield_preserve, repair_icfree, repair_drmcfree.
Qed.

End IPGrammarTheorems.
