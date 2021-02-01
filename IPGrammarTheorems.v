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
Hint Resolve Match_rm : IPGrammar.
Hint Resolve InfixMatch_rm : IPGrammar.
Hint Resolve PrefixMatch_rm : IPGrammar.
Hint Resolve InfixMatch_drm : IPGrammar.
Hint Resolve PrefixMatch_drm : IPGrammar.

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

Ltac slinsert_to_inode_destruct pr o1 o2 :=
    cbn [slinsert_to] in *;
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

(* ####################################### *)
(* ####################################### *)
(* ####################################### *)
(* ####################################### *)
(* ####################################### *)
(* ####################################### *)

Lemma linsert_lo_slinsert_to_anode {g} (pr : drules g) l1 o t2 :
  linsert_lo pr l1 o t2 = slinsert_to pr (AtomicNode l1) o t2.
Proof.
  induction t2; auto.
  simpl. rewrite IHt2_1. reflexivity.
Qed.

Lemma complete_trans_1 {g} (pr : drules g) o1 o2 o3 :
  i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o3) ->
  i_conflict_pattern pr (CL_infix_infix o1 o3).
Admitted.

Lemma complete_trans_2 {g} (pr : drules g) o1 o2 o3 :
  i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_prefix_infix o1 o3).
Admitted.

Lemma complete_trans_3 {g} (pr : drules g) o1 o2 o3 :
  i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_prefix_infix o1 o3).
Admitted.

Lemma complete_trans_4 {g} (pr : drules g) o1 o2 o3 :
  i_conflict_pattern pr (CR_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_infix_infix o1 o3).
Admitted.

Lemma complete_neg_1 {g} (pr : drules g) o1 o2 :
  ~ i_conflict_pattern pr (CR_infix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o1).
Admitted.

Lemma complete_neg_2 {g} (pr : drules g) o1 o2 :
  ~ rm_conflict_pattern pr (CL_infix_prefix o1 o2) ->
  i_conflict_pattern pr (CR_prefix_infix o2 o1).
Admitted.

Lemma complete_neg_3 {g} (pr : drules g) o1 o2 :
  ~ i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o1).
Admitted.

Lemma linsert_o_complete {g} (pr : drules g) o t2 :
  i_conflict_free (i_conflict_pattern pr) (PrefixNode o t2) ->
  linsert_o pr o t2 = PrefixNode o t2.
Proof.
  intro. destruct t2; auto.
  rename t2_1 into t21, o0 into o2, t2_2 into t2.
  linsert_o_inode_destruct pr o o2; auto.
  inv H. destruct H2.
  eexists. eauto with IPGrammar.
Qed.

Lemma slinsert_to_prefix {g} (pr : drules g) o1 t12 o t2 :
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (PrefixNode o1 t12) ->
  ~ rm_conflict_pattern pr (CL_infix_prefix o o1) ->
  slinsert_to pr (PrefixNode o1 t12) o t2 = linsert_o pr o1 (slinsert_to pr t12 o t2).
Proof.
  intros. inv H.
  induction t2.
  - cbn [slinsert_to]. linsert_o_inode_destruct pr o1 o.
    + rewrite linsert_o_complete; auto.
    + destruct E.
      auto using complete_neg_2.
  - rename t2_1 into t21, o0 into o2, t2_2 into t22.
    slinsert_to_inode_destruct pr o o2.
    + rewrite IHt2_1.
      rename E into E1.
      linsert_o_inode_destruct pr o1 o2; auto.
      destruct E.
      apply complete_trans_3 with o; auto.
      apply complete_neg_2. assumption.
    + rename E into E1. linsert_o_inode_destruct pr o1 o.
      * rewrite linsert_o_complete; auto.
      * destruct E.
        auto using complete_neg_2.
  - rename o0 into o2, t2 into t22.
    cbn [slinsert_to].
    linsert_o_inode_destruct pr o1 o.
    + rewrite linsert_o_complete; auto.
    + destruct E.
      auto using complete_neg_2.
Qed.

Lemma slinsert_to_complete {g} (pr : drules g) t1 o t2 :
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (InfixNode t1 o t2) ->
  slinsert_to pr t1 o t2 = InfixNode t1 o t2.
Proof.
  intro. destruct t2 as [?|t21 o2 t22|?]; auto.
  slinsert_to_inode_destruct pr o o2; auto.
  exfalso. inv H. inv H0. destruct H4.
  eexists. eauto with IPGrammar.
Qed.

Lemma slinsert_to_assoc {g} (pr : drules g) t11 o1 t12 o t2 :
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (InfixNode t11 o1 t12) ->
  ~ i_conflict_pattern pr (CL_infix_infix o o1) ->
  slinsert_to pr (InfixNode t11 o1 t12) o t2 = slinsert_to pr t11 o1 (slinsert_to pr t12 o t2).
Proof.
  intros. induction t2.
  - slinsert_to_inode_destruct pr o1 o.
    + rewrite slinsert_to_complete; auto.
    + destruct H0. auto using complete_neg_1.
  - rename t2_1 into t21, o0 into o2, t2_2 into t22.
    slinsert_to_inode_destruct pr o o2.
    + rewrite IHt2_1.
      rename E into E'.
      slinsert_to_inode_destruct pr o1 o2; auto.
      destruct E.
      apply complete_trans_4 with o; auto.
      auto using complete_neg_3.
    + rename E into E'.
      slinsert_to_inode_destruct pr o1 o.
      * rewrite slinsert_to_complete; auto.
      * destruct H0.
        auto using complete_neg_1.
  - rename o0 into o2, t2 into t22.
    slinsert_to_inode_destruct pr o1 o.
    + rewrite slinsert_to_complete; auto.
    + destruct H0. auto using complete_neg_1.
Qed.

Lemma linsert_to_slinsert_to {g} (pr : drules g) t1 o t2 :
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) t1 ->
  (forall x1, matches t1 (InfixPatt HPatt x1 HPatt) -> ~ i_conflict_pattern pr (CL_infix_infix o x1)) ->
  (forall x1, matches_rm t1 (PrefixPatt x1 HPatt) -> ~ rm_conflict_pattern pr (CL_infix_prefix o x1)) ->
  linsert_to pr t1 o t2 = slinsert_to pr t1 o t2.
Proof.
  intro. revert o t2.
  induction t1; intros; simpl.
  - apply linsert_lo_slinsert_to_anode.
  - rename t1_1 into t11, o into o1, t1_2 into t12, o0 into o.
    rewrite IHt1_2.
    + rewrite IHt1_1.
      * rewrite slinsert_to_assoc; auto with IPGrammar.
      * inv H. inv H2. inv H3. split; assumption.
      * intros. inv H2.
        rename t1 into t111, t0 into t112, x1 into o11.
        intro.
        inv H. inv H3. destruct H9.
        eexists. eauto with IPGrammar.
      * intros.
        intro.
        inv H. inv H5. destruct H8.
        eexists. eauto with IPGrammar.
    + inv H. inv H2. inv H3. split; assumption.
    + intros. inv H2.
      rename t1 into t121, t0 into t122, x1 into o12. clear H6 H8.
      intro.
      specialize H0 with o1. apply H0; auto with IPGrammar.
      apply complete_trans_1 with o12; auto.
      apply complete_neg_1. intro.
      inv H. inv H4. destruct H8.
      eexists. eauto with IPGrammar.
    + intros. 
      apply H1.
      auto with IPGrammar.
  - rename o into o1, t1 into t12, o0 into o.
    rewrite IHt1.
    + rewrite slinsert_to_prefix; auto with IPGrammar.
    + inv H. inv H2. inv H3. split; assumption.
    + intros. inv H2.
      rename t1 into t121, t0 into t122, x1 into o12. clear H6 H8.
      intro.
      inv H. inv H3. destruct H6.
      exists (CR_prefix_infix o1 o12).
      split; [|unfold CR_prefix_infix; auto with IPGrammar].
      apply complete_trans_2 with o; auto.
      specialize H0 with o1.
      apply complete_neg_2.
      apply H1. auto with IPGrammar.
    + intros. 
      apply H1.
      auto with IPGrammar.
Qed.

Lemma linsert_to_complete {g} (pr : drules g) t1 o t2 :
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (InfixNode t1 o t2) ->
  linsert_to pr t1 o t2 = InfixNode t1 o t2.
Proof.
  intros. assert (H' := H). inv H. inv H0. inv H1.
  rewrite linsert_to_slinsert_to.
  - rewrite slinsert_to_complete; auto.
  - split; assumption.
  - intros. inv H. intro. destruct H4. eexists. eauto with IPGrammar.
  - intros. intro. destruct H3. eexists. eauto with IPGrammar.
Qed.

Lemma repair_complete {g} (pr : drules g) t :
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) t ->
  repair pr t = t.
Proof.
  intros. induction t; simpl; auto.
  - rewrite IHt2.
    + rewrite linsert_to_complete; auto.
    + inv H. inv H0. inv H1. split; assumption.
  - rewrite IHt.
    + rewrite linsert_o_complete; auto.
      inv H. assumption.
    + inv H. inv H0. inv H1. split; assumption.
Qed.

End IPGrammarTheorems.
