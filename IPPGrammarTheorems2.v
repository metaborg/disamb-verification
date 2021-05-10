From stdpp Require Export relations.
Require Import MyUtils.
Require Export IPPGrammarTheorems.

Section IPPGrammarTheorems2.

Create HintDb IPPGrammar.
Hint Resolve CPrio_infix_infix_1 CPrio_infix_infix_2 CPrio_prefix_infix CPrio_infix_prefix CLeft_prefix_infix
  CRight_infix_prefix CRight_postfix_infix CRight_postfix_infix CPrio_postfix_infix CPrio_postfix_prefix
  CPrio_infix_postfix CLeft_infix_postfix CPrio_prefix_postfix CLeft_prefix_postfix CRight_postfix_prefix CLeft CRight
  HMatch InfixMatch PrefixMatch PostfixMatch Atomic_wf Infix_wf Prefix_wf Postfix_wf Atomic_cf Infix_cf Prefix_cf
  Postfix_cf Atomic_drmcf Infix_drmcf Prefix_drmcf Postfix_drmcf Match_rm InfixMatch_rm PrefixMatch_rm InfixMatch_drm
  PrefixMatch_drm PostfixMatch_drm Atomic_dlmcf Infix_dlmcf Prefix_dlmcf Postfix_dlmcf Match_lm InfixMatch_lm
  PostfixMatch_lm InfixMatch_dlm PrefixMatch_dlm PostfixMatch_dlm
    : IPPGrammar.

Inductive reorder_step {g} : parse_tree g -> parse_tree g -> Prop :=
  | RStep1 t11 o1 t12 o t2 :
      reorder_step (InfixNode (InfixNode t11 o1 t12) o t2) (InfixNode t11 o1 (InfixNode t12 o t2))
  | RStep2 o1 t12 o t2 :
      reorder_step (InfixNode (PrefixNode o1 t12) o t2) (PrefixNode o1 (InfixNode t12 o t2))
  | RStep3 t1 o t21 o2 :
      reorder_step (InfixNode t1 o (PostfixNode t21 o2)) (PostfixNode (InfixNode t1 o t21) o2)
  | RStep4 o t21 o2 :
      reorder_step (PrefixNode o (PostfixNode t21 o2)) (PostfixNode (PrefixNode o t21) o2)
  | RStep5 t1 o t2 t1':
      reorder_step t1 t1' ->
      reorder_step (InfixNode t1 o t2) (InfixNode t1' o t2)
  | RStep6 t1 o t2 t2' :
      reorder_step t2 t2' ->
      reorder_step (InfixNode t1 o t2) (InfixNode t1 o t2')
  | RStep7 o t2 t2' :
      reorder_step t2 t2' ->
      reorder_step (PrefixNode o t2) (PrefixNode o t2')
  | RStep8 t1 o t1' :
      reorder_step t1 t1' ->
      reorder_step (PostfixNode t1 o) (PostfixNode t1' o).

Definition reorder {g} := rtsc (@reorder_step g).


Inductive posttree {g} : parse_tree g -> Prop :=
  | AtomicPTree l :
      posttree (AtomicNode l)
  | PostfixPTree t1 o :
      posttree (PostfixNode t1 o).

Lemma insert_in_matches_lm {g} (pr : drules g) t1 o t2 q :
  matches_lm t1 q ->
  matches_lm (insert_in pr t1 o t2) q.
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. auto with IPPGrammar.
  - insert_in_inode_destruct pr o t21 o2 t22; auto with IPPGrammar.
  - simpl. auto with IPPGrammar.
  - insert_in_pnode_destruct pr o t21 o2; auto with IPPGrammar.
Qed.

Lemma insert_in_postfix_assoc {g} (pr : drules g) t11 o1 t121 o12 o t2 :
  (∃ x : OP g,
      lm_conflict_pattern pr (CR_infix_postfix o1 x)
      ∧ matches_lm (PostfixNode t121 o12) (PostfixPatt HPatt x)) ->
  insert_in pr (PostfixNode (insert_in pr t11 o1 t121) o12) o t2 =
  insert_in pr t11 o1 (insert_in pr (PostfixNode t121 o12) o t2).
Proof.
  intros. inv H. inv H0. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - assert (insert_in pr (PostfixNode (insert_in pr t11 o1 t121) o12) o (AtomicNode l2) =
            InfixNode (PostfixNode (insert_in pr t11 o1 t121) o12) o (AtomicNode l2)); auto. rewrite H0. clear H0.
    assert (insert_in pr (PostfixNode t121 o12) o (AtomicNode l2)
            = InfixNode (PostfixNode t121 o12) o (AtomicNode l2)); auto. rewrite H0. clear H0.
    insert_in_inode_destruct pr o1 (PostfixNode t121 o12) o (AtomicNode l2).
    + destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
    + destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
    + clear E2. exfalso. eapply H0; eauto with IPPGrammar.
  - insert_in_inode_destruct pr o t21 o2 t22.
    + rewrite IHt2_1. rename E into E1.
      insert_in_inode_destruct pr o1 (insert_in pr (PostfixNode t121 o12) o t21) o2 t22; auto. clear E2. exfalso.
      eapply H0; eauto with IPPGrammar. apply InfixMatch_lm. apply insert_in_matches_lm; auto.
    + rewrite IHt2_1. rename E into E1, E2 into E3.
      insert_in_inode_destruct pr o1 (insert_in pr (PostfixNode t121 o12) o t21) o2 t22; auto. clear E2. exfalso.
      eapply H0; eauto with IPPGrammar. apply InfixMatch_lm. apply insert_in_matches_lm; auto.
    + clear E2. rename E into E1. insert_in_inode_destruct pr o1 (PostfixNode t121 o12) o (InfixNode t21 o2 t22).
      * destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E2; auto. exfalso.
        eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
      * destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E3; auto. exfalso.
        eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
      * clear E2. exfalso. eapply H2; eauto with IPPGrammar.
  - assert (insert_in pr (PostfixNode t121 o12) o (PrefixNode o2 t22) =
            InfixNode (PostfixNode t121 o12) o (PrefixNode o2 t22)); auto. rewrite H0. clear H0.
    insert_in_inode_destruct pr o1 (PostfixNode t121 o12) o (PrefixNode o2 t22).
    + destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
    + destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
    + clear E2. exfalso. eapply H0; eauto with IPPGrammar.
  - insert_in_pnode_destruct pr o t21 o2.
    + rewrite IHt2. rename E into E1. insert_in_pnode_destruct pr o1 (insert_in pr (PostfixNode t121 o12) o2 t21) o2.
      * destruct (has_infix_lm_conflicts pr o1 (PostfixNode (insert_in pr (PostfixNode t121 o12) o t21) o2)) eqn:E2.
        auto. exfalso. eapply has_infix_lm_conflicts_false; eauto. apply PostfixMatch_lm.
        auto using insert_in_matches_lm.
      * clear E. exfalso. eapply H0; eauto. apply PostfixMatch_lm. apply insert_in_matches_lm. auto with IPPGrammar.
    + clear E. insert_in_inode_destruct pr o1 (PostfixNode t121 o12) o (PostfixNode t21 o2).
      * destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
        eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
      * destruct (has_infix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
        eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
      * clear E2. exfalso. eapply H2; eauto. inv H1.
        **inv H3. auto with IPPGrammar.
        **auto with IPPGrammar.
Qed.

Lemma repair_in_insert_in_posttree {g} (pr : drules g) t1 o t2 :
  posttree t1 -> repair_in pr t1 o t2 = insert_in pr t1 o t2.
Proof.
  intros. destruct H; auto.
Qed.

Lemma repair_in_insert_in_assoc {g} (pr : drules g) t11 o1 t12 o t2 :
  posttree t11 ->
  repair_in pr (insert_in pr t11 o1 t12) o t2 = insert_in pr t11 o1 (repair_in pr t12 o t2).
Proof.
  revert o1 o t2.
  induction t12 as [l12|t121 ? o12 t122|o12 t122|t121 ? o12]; intros.
  - simpl. rewrite repair_in_insert_in_posttree; auto.
  - insert_in_inode_destruct pr o1 t121 o12 t122.
    + simpl. rewrite IHt12_1; auto.
    + simpl. rewrite IHt12_1; auto.
    + simpl. rewrite repair_in_insert_in_posttree; auto.
  - simpl. rewrite repair_in_insert_in_posttree; auto.
  - insert_in_pnode_destruct pr o1 t121 o12.
    + simpl. apply insert_in_postfix_assoc. assumption.
    + simpl. rewrite repair_in_insert_in_posttree; auto.
Qed.

Lemma insert_in_postfix_insert_pre_assoc {g} (pr : drules g) o1 t121 o12 o t2 :
  (∃ x : OP g,
      lm_conflict_pattern pr (CR_prefix_postfix o1 x)
      ∧ matches_lm (PostfixNode t121 o12) (PostfixPatt HPatt x)) ->
  insert_in pr (PostfixNode (insert_pre pr o1 t121) o12) o t2 =
  insert_pre pr o1 (insert_in pr (PostfixNode t121 o12) o t2).
Proof.
  intros. inv H. inv H0. induction t2 as [l2|t21 ? o2 t22|o2 t22| t21 ? o2].
  - assert (insert_in pr (PostfixNode (insert_pre pr o1 t121) o12) o (AtomicNode l2) =
            InfixNode (PostfixNode (insert_pre pr o1 t121) o12) o (AtomicNode l2)); auto. rewrite H0. clear H0.
    assert (insert_in pr (PostfixNode t121 o12) o (AtomicNode l2) =
            InfixNode (PostfixNode t121 o12) o (AtomicNode l2)); auto. rewrite H0. clear H0.
    insert_pre_inode_destruct pr o1 (PostfixNode t121 o12) o (AtomicNode l2).
    + destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
    + destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
    + exfalso. eapply H0; eauto with IPPGrammar.
  - insert_in_inode_destruct pr o t21 o2 t22.
    + rewrite IHt2_1. rename E into E1.
      insert_pre_inode_destruct pr o1 (insert_in pr (PostfixNode t121 o12) o t21) o2 t22; auto. clear E2. exfalso.
      eapply H0; eauto using insert_in_matches_lm with IPPGrammar.
    + rewrite IHt2_1. rename E into E1, E2 into E3.
      insert_pre_inode_destruct pr o1 (insert_in pr (PostfixNode t121 o12) o t21) o2 t22; auto. clear E2. exfalso.
      eapply H0; eauto using insert_in_matches_lm with IPPGrammar.
    + rename E into E1, E2 into E3.
      insert_pre_inode_destruct pr o1 (PostfixNode t121 o12) o (InfixNode t21 o2 t22).
      * destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E2; auto. exfalso.
        eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
      * destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E4; auto. exfalso.
        eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
      * exfalso. eapply H2; eauto with IPPGrammar.
  - assert (insert_in pr (PostfixNode (insert_pre pr o1 t121) o12) o (PrefixNode o2 t22) =
            InfixNode (PostfixNode (insert_pre pr o1 t121) o12) o (PrefixNode o2 t22)); auto. rewrite H0. clear H0.
    assert (insert_in pr (PostfixNode t121 o12) o (PrefixNode o2 t22) = 
            InfixNode (PostfixNode t121 o12) o (PrefixNode o2 t22)); auto. rewrite H0. clear H0.
    insert_pre_inode_destruct pr o1 (PostfixNode t121 o12) o (PrefixNode o2 t22).
    + destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
    + destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E1; auto. exfalso.
      eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
    + exfalso. eapply H0; eauto with IPPGrammar.
  - insert_in_pnode_destruct pr o t21 o2.
    + rewrite IHt2. rename E into E1.
      insert_pre_pnode_destruct pr o1 (insert_in pr (PostfixNode t121 o12) o t21) o2; auto. clear E. exfalso.
      eapply H0; eauto. eauto using insert_in_matches_lm with IPPGrammar.
    + rename E into E1. insert_pre_inode_destruct pr o1 (PostfixNode t121 o12) o (PostfixNode t21 o2).
      * destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E2; auto. exfalso.
        eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
      * destruct (has_prefix_lm_conflicts pr o1 (PostfixNode t121 o12)) eqn:E3; auto. exfalso.
        eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
      * exfalso. eapply H2; eauto with IPPGrammar.
Qed.

Lemma repair_in_insert_pre_assoc {g} (pr : drules g) o1 t12 o t2 :
  repair_in pr (insert_pre pr o1 t12) o t2 = insert_pre pr o1 (repair_in pr t12 o t2).
Proof.
  revert o1 o t2. induction t12 as [l12|t121 ? o12 t122|o12 t122|t121 ? o12]; intros.
  - simpl. reflexivity.
  - insert_pre_inode_destruct pr o1 t121 o12 t122.
    + simpl. rewrite IHt12_1. reflexivity.
    + simpl. rewrite IHt12_1. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
  - insert_pre_pnode_destruct pr o1 t121 o12.
    + simpl. apply insert_in_postfix_insert_pre_assoc. assumption.
    + simpl. reflexivity.
Qed.

Lemma repair_in_assoc {g} (pr : drules g) t11 o1 t12 o t2 :
  repair_in pr (repair_in pr t11 o1 t12) o t2 = repair_in pr t11 o1 (repair_in pr t12 o t2).
Proof.
  revert o1 t12 o t2. induction t11 as [l11|t111 ? o11 t112|o11 t112|t111 ? o11]; intros.
  - simpl. apply repair_in_insert_in_assoc. apply AtomicPTree.
  - simpl. rewrite IHt11_1. rewrite IHt112. reflexivity.
  - simpl. rewrite <- IHt112. apply repair_in_insert_pre_assoc.
  - simpl. apply repair_in_insert_in_assoc. apply PostfixPTree.
Qed.

Lemma insert_in_insert_post_assoc {g} (pr : drules g) t1 o t21 o2 :
  safe_pr pr -> complete_pr pr ->
  insert_in pr t1 o (insert_post pr t21 o2) = insert_post pr (insert_in pr t1 o t21) o2.
Proof.
  intros HSafe HComplete. destruct t21 as [l21|t211 o21 t212|o21 t212|t211 o21].
  - cbn [insert_post]. insert_in_pnode_destruct pr o (AtomicNode l21) o2.
    + rename E into E1. insert_post_inode_destruct pr t1 o (AtomicNode l21) o2; auto.
      * inv E1. inv H. inv H1.
        **inv H. exfalso. eauto using safe_infix_postfix.
        **inv H4. inv H.
      * inv E2. inv H. inv H1. inv H. inv H5. inv H.
    + rename E into E1. insert_post_inode_destruct pr t1 o (AtomicNode l21) o2.
      * reflexivity.
      * reflexivity.
      * exfalso. apply H with o2; eauto using complete_neg_4 with IPPGrammar.
  - insert_post_inode_destruct pr t211 o21 t212 o2.
    + rename E into E1. insert_in_inode_destruct pr o t211 o21 t212.
      * rename E into E3. insert_post_inode_destruct pr (insert_in pr t1 o t211) o21 t212 o2; auto.
        contradiction.
      * inv E2. inv H. inv H1. inv H.
        destruct (has_infix_lm_conflicts pr o (InfixNode t211 o21 (insert_post pr t212 o2))) eqn:E2.
        **clear E2. rename E into E3. insert_post_inode_destruct pr (insert_in pr t1 o t211) o21 t212 o2; auto.
          contradiction.
        **exfalso. eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
      * clear E2.
        destruct (has_infix_lm_conflicts pr o (InfixNode t211 o21 (insert_post pr t212 o2))) eqn:E2.
        **exfalso. apply has_infix_lm_conflicts_true in E2. inv E2. inv H0. inv H2. inv H0.
          eapply H; eauto with IPPGrammar.
        **clear E2. rename E into E3. insert_post_inode_destruct pr t1 o (InfixNode t211 o21 t212) o2.
          ***destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E4; auto.
            apply is_i_conflict_pattern_false in E4. contradiction.
          ***destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E4; auto.
            apply is_i_conflict_pattern_false in E4. contradiction.
          ***exfalso. clear E2. apply complete_neg_1 in E3; auto. apply E. eauto using complete_trans_5.
    + rename E into E1, E2 into E3. insert_in_inode_destruct pr o t211 o21 t212.
      * rename E into E4. insert_post_inode_destruct pr (insert_in pr t1 o t211) o21 t212 o2; auto.
        exfalso. inv E3. inv H0. inv H2. inv H0. eapply H; eauto with IPPGrammar.
      * destruct (has_infix_lm_conflicts pr o (InfixNode t211 o21 (insert_post pr t212 o2))) eqn:E4.
        **clear E4. rename E into E4, E2 into E5.
          insert_post_inode_destruct pr (insert_in pr t1 o t211) o21 t212 o2; auto.
          exfalso. inv E3. inv H0. inv H2. inv H0. eapply H; eauto with IPPGrammar.
        **exfalso. inv E2. inv H. inv H1. inv H. eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
      * clear E2. destruct (has_infix_lm_conflicts pr o (InfixNode t211 o21 (insert_post pr t212 o2))) eqn:E4.
        **exfalso. apply has_infix_lm_conflicts_true in E4. inv E4. inv H0. inv H2. inv H0.
          eapply H; eauto with IPPGrammar.
        **clear E4. rename E into E4. insert_post_inode_destruct pr t1 o (InfixNode t211 o21 t212) o2.
          ***destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E5; auto. clear E5.
            destruct (has_postfix_rm_conflicts pr (InfixNode t211 o21 t212) o2) eqn:E5; auto.
            exfalso. inv E3. inv H0. inv H2. inv H0. eapply has_postfix_rm_conflicts_false; eauto with IPPGrammar.
          ***destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E5; auto. clear E5.
            destruct (has_postfix_rm_conflicts pr (InfixNode t211 o21 t212)) eqn:E5; auto. exfalso.
            inv E3. inv H0. inv H2. inv H0. eapply has_postfix_rm_conflicts_false; eauto with IPPGrammar.
          ***exfalso. clear E2. inv E3. inv H1. inv H3. inv H1. eapply H0; eauto with IPPGrammar.
    + clear E2. rename E into E1. insert_in_pnode_destruct pr o (InfixNode t211 o21 t212) o2.
      * destruct (is_i_conflict_pattern pr (CR_infix_infix o o21)) eqn:E2.
        **apply is_i_conflict_pattern_true in E2. rename E into E3, E2 into E4.
          insert_post_inode_destruct pr (insert_in pr t1 o t211) o21 t212 o2; auto.
          ***contradiction.
          ***exfalso. inv E2. inv H0. inv H2. inv H0. eapply H; eauto with IPPGrammar.
        **apply is_i_conflict_pattern_false in E2.
          destruct (has_infix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E3.
          ***clear E3. rename E into E3, E2 into E4.
            insert_post_inode_destruct pr (insert_in pr t1 o t211) o21 t212 o2; auto.
            ****contradiction.
            ****exfalso. inv E2. inv H0. inv H2. inv H0. eapply H; eauto with IPPGrammar.
          ***rename E into E4, E2 into E5. insert_post_inode_destruct pr t1 o (InfixNode t211 o21 t212) o2; auto.
            ****exfalso. inv E4. inv H0. inv H2.
              *****inv H0. eauto using safe_infix_postfix.
              *****inv H5. inv H0. eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
            ****exfalso. inv E2. inv H0. inv H2. inv H0. inv H6. inv H0. eapply H; eauto with IPPGrammar.
      * clear E. destruct (is_i_conflict_pattern pr (CR_infix_infix o o21)) eqn:E2.
        **apply is_i_conflict_pattern_true in E2. exfalso. apply complete_neg_4 in E1; auto.
          eapply H0; eauto with IPPGrammar. eauto using complete_trans_7.
        **apply is_i_conflict_pattern_false in E2.
          destruct (has_infix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E.
          ***exfalso. apply has_infix_lm_conflicts_true in E. inv E. inv H1. inv H3. inv H1.
            eapply H0; eauto with IPPGrammar.
          ***rename E2 into E3, E into E4.
            insert_post_inode_destruct pr t1 o (InfixNode t211 o21 t212) o2.
            ****destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E5.
              *****exfalso. apply is_i_conflict_pattern_true in E5. contradiction.
              *****clear E5. destruct (has_postfix_rm_conflicts pr (InfixNode t211 o21 t212)) eqn:E6; auto. exfalso.
                apply has_postfix_rm_conflicts_true in E6. inv E6. inv H1. inv H3. inv H1.
                eapply H; eauto with IPPGrammar.
            ****exfalso. inv E2. inv H1. inv H3. inv H1. inv H7. inv H1. eapply H; eauto with IPPGrammar.
            ****clear E2. exfalso. eapply H0; eauto using complete_neg_4 with IPPGrammar.
  - insert_post_pnode_destruct pr o21 t212 o2.
    + inv E. inv H. cbn [insert_in].
      insert_post_inode_destruct pr t1 o (PrefixNode o21 t212) o2.
      * destruct (has_postfix_rm_conflicts pr (PrefixNode o21 t212) o2) eqn:E1; auto.
        exfalso. eapply has_postfix_rm_conflicts_false; eauto with IPPGrammar.
      * clear E2. destruct (has_postfix_rm_conflicts pr (PrefixNode o21 t212) o2) eqn:E1; auto.
        exfalso. eapply has_postfix_rm_conflicts_false; eauto with IPPGrammar.
      * clear E2. exfalso. eapply H; eauto with IPPGrammar.
    + clear E. assert (insert_in pr t1 o (PrefixNode o21 t212) = InfixNode t1 o (PrefixNode o21 t212)); auto.
      rewrite H0. clear H0. insert_in_pnode_destruct pr o (PrefixNode o21 t212) o2.
      * inv E. inv H0. inv H2.
        **inv H0. clear H3. insert_post_inode_destruct pr t1 o (PrefixNode o21 t212) x; auto.
          ***exfalso. eauto using safe_infix_postfix.
          ***exfalso. inv E2. inv H0. inv H3. inv H0. eapply H; eauto with IPPGrammar.
        **inv H5. inv H0.
      * clear E. insert_post_inode_destruct pr t1 o (PrefixNode o21 t212) o2.
        **destruct (has_postfix_rm_conflicts pr (PrefixNode o21 t212) o2) eqn:E1; auto. exfalso.
          apply has_postfix_rm_conflicts_true in E1. inv E1. inv H1. eapply H; eauto with IPPGrammar.
        **exfalso. inv E2. inv H1. inv H3. inv H1. eapply H; eauto with IPPGrammar.
        **clear E2. exfalso. eapply H0; eauto using complete_neg_4 with IPPGrammar.
  - assert (insert_post pr (PostfixNode t211 o21) o2 = PostfixNode (PostfixNode t211 o21) o2); auto.
    rewrite H. clear H. insert_in_pnode_destruct pr o (PostfixNode t211 o21) o2.
    + inv E. inv H. destruct (has_infix_lm_conflicts pr o (PostfixNode t211 o21)) eqn:E; auto.
      rename E into E1. insert_post_inode_destruct pr t1 o (PostfixNode t211 o21) o2; auto.
      * exfalso. inv H1.
        **inv H. eauto using safe_infix_postfix.
        **eapply has_infix_lm_conflicts_false; eauto with IPPGrammar.
      * exfalso. inv E2. inv H. inv H3. inv H. inv H7. inv H.
    + clear E. destruct (has_infix_lm_conflicts pr o (PostfixNode t211 o21)) eqn:E.
      * exfalso. apply has_infix_lm_conflicts_true in E. inv E. inv H0. eapply H; eauto with IPPGrammar.
      * clear E. insert_post_inode_destruct pr t1 o (PostfixNode t211 o21) o2; auto.
        clear E2. exfalso. apply H with o2; eauto using complete_neg_4 with IPPGrammar.
Qed.

Lemma insert_pre_insert_post_assoc {g} (pr : drules g) o t21 o2 :
  safe_pr pr -> complete_pr pr ->
  insert_pre pr o (insert_post pr t21 o2) = insert_post pr (insert_pre pr o t21) o2.
Proof.
  intros HSafe HComplete. destruct t21 as [l21|t211 o21 t212|o21 t212|t211 o21].
  - assert (insert_post pr (AtomicNode l21) o2 = PostfixNode (AtomicNode l21) o2); auto. rewrite H. clear H.
    assert (insert_pre pr o (AtomicNode l21) = PrefixNode o (AtomicNode l21)); auto. rewrite H. clear H.
    insert_pre_pnode_destruct pr o (AtomicNode l21) o2.
    + inv E. inv H.
      insert_post_pnode_destruct pr o (AtomicNode l21) o2; auto.
      exfalso. inv E. inv H.
      inv H1.
      * inv H. clear H4. inv H3.
        **inv H. eauto using safe_prefix_postfix.
        **inv H5. inv H.
      * inv H6. inv H.
    + clear E. specialize H with o2. insert_post_pnode_destruct pr o (AtomicNode l21) o2; auto. clear E.
      exfalso. eapply H; eauto using complete_neg_5 with IPPGrammar.
  - insert_post_inode_destruct pr t211 o21 t212 o2.
    + rename E into E1. insert_pre_inode_destruct pr o t211 o21 (insert_post pr t212 o2).
      * rename E into E3. insert_post_inode_destruct pr (insert_pre pr o t211) o21 t212 o2; auto. contradiction.
      * inv E2. inv H. inv H1. inv H. destruct (has_prefix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E2.
        **clear E2. rename E into E3. insert_post_inode_destruct pr (insert_pre pr o t211) o21 t212 o2; auto. clear E2.
          exfalso. contradiction.
        **exfalso. eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
      * clear E2. destruct (has_prefix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E2.
        **exfalso. apply has_prefix_lm_conflicts_true in E2. inv E2. inv H0. inv H2. inv H0.
          eapply H; eauto with IPPGrammar.
        **clear E2. rename E into E3. insert_post_pnode_destruct pr o (InfixNode t211 o21 t212) o2.
          ***destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E4; auto. exfalso.
            apply is_i_conflict_pattern_false in E4. contradiction.
          ***clear E. exfalso. eapply H0; eauto with IPPGrammar. apply complete_neg_6 in E3; auto.
            eauto using complete_trans_6 with IPPGrammar.
    + inv E2. inv H. inv H1. inv H. rename E into E1. insert_pre_inode_destruct pr o t211 o21 (insert_post pr t212 o2).
      * rename E into E3. insert_post_inode_destruct pr (insert_pre pr o t211) o21 t212 o2; auto. clear E2. exfalso.
        eapply H; eauto with IPPGrammar.
      * inv E2. inv H. inv H2. inv H. destruct (has_prefix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E3.
        **apply has_prefix_lm_conflicts_true in E3. inv E3. inv H. inv H3. inv H.
          rename E into E3. insert_post_inode_destruct pr (insert_pre pr o t211) o21 t212 o2; auto. clear E2 E. exfalso.
          eapply H; eauto with IPPGrammar.
        **exfalso. eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
      * clear E2. destruct (has_prefix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E3.
        **apply has_prefix_lm_conflicts_true in E3. inv E3. inv H1. inv H3. inv H1. exfalso.
          eapply H; eauto with IPPGrammar.
        **clear E3. rename E into E3. insert_post_pnode_destruct pr o (InfixNode t211 o21 t212) o2.
          ***inv E. inv H1. destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E4; auto. clear E4.
            destruct (has_postfix_rm_conflicts pr (InfixNode t211 o21 t212) o2) eqn:E4; auto. exfalso.
            eapply has_postfix_rm_conflicts_false; eauto with IPPGrammar.
          ***exfalso. eapply has_postfix_rm_conflicts_false; eauto with IPPGrammar.
    + clear E2. rename E into E1. insert_pre_pnode_destruct pr o (InfixNode t211 o21 t212) o2.
      * inv E. inv H0. destruct (is_i_conflict_pattern pr (CR_prefix_infix o o21)) eqn:E3.
        **apply is_i_conflict_pattern_true in E3.
          insert_post_inode_destruct pr (insert_pre pr o t211) o21 t212 o2; auto.
          ***contradiction.
          ***exfalso. inv E2. inv H0. inv H4. inv H0. eapply H; eauto with IPPGrammar.
        **apply is_i_conflict_pattern_false in E3.
          destruct (has_prefix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E4.
          ***apply has_prefix_lm_conflicts_true in E4. inv E4. inv H0. inv H4. inv H0.
            insert_post_inode_destruct pr (insert_pre pr o t211) o21 t212 o2; auto.
            ****contradiction.
            ****exfalso. inv E2. inv H0. inv H5. inv H0. eapply H; eauto with IPPGrammar.
          ***insert_post_pnode_destruct pr o (InfixNode t211 o21 t212) o2; auto. exfalso. inv E. inv H0. inv H4.
            ****inv H0. clear H5. inv H2.
              *****inv H0. eauto using safe_prefix_postfix.
              *****inv H6. inv H0. eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
            ****inv H7. inv H0. eapply H; eauto with IPPGrammar.
      * clear E. destruct (is_i_conflict_pattern pr (CR_prefix_infix o o21)) eqn:E3.
        **apply is_i_conflict_pattern_true in E3. exfalso. apply complete_neg_4 in E1; auto.
          eapply H0; eauto using complete_trans_8 with IPPGrammar.
        **apply is_i_conflict_pattern_false in E3.
          destruct (has_prefix_lm_conflicts pr o (InfixNode t211 o21 t212)) eqn:E4.
          ***exfalso. apply has_prefix_lm_conflicts_true in E4. inv E4. inv H1. inv H3. inv H1.
            eapply H0; eauto with IPPGrammar.
          ***insert_post_pnode_destruct pr o (InfixNode t211 o21 t212) o2.
            ****destruct (is_i_conflict_pattern pr (CL_postfix_infix o2 o21)) eqn:E5.
              *****exfalso. apply is_i_conflict_pattern_true in E5. contradiction.
              *****clear E5. destruct (has_postfix_rm_conflicts pr (InfixNode t211 o21 t212) o2) eqn:E5; auto. exfalso.
                apply has_postfix_rm_conflicts_true in E5. inv E5. inv H1. inv H3. inv H1.
                eapply H; eauto with IPPGrammar.
            ****clear E. exfalso. eapply H0; eauto using complete_neg_5 with IPPGrammar.
  - insert_post_pnode_destruct pr o21 t212 o2.
    + inv E. inv H. cbn [insert_pre]. insert_post_pnode_destruct pr o (PrefixNode o21 t212) o2.
      * inv E. inv H. destruct (has_postfix_rm_conflicts pr (PrefixNode o21 t212) o2) eqn:E; auto. exfalso.
        eapply has_postfix_rm_conflicts_false; eauto with IPPGrammar.
      * clear E. exfalso. eapply H; eauto with IPPGrammar.
    + clear E. assert (insert_pre pr o (PrefixNode o21 t212) = PrefixNode o (PrefixNode o21 t212)); auto.
      rewrite H0. clear H0. insert_pre_pnode_destruct pr o (PrefixNode o21 t212) o2.
      * inv E. inv H0. insert_post_pnode_destruct pr o (PrefixNode o21 t212) o2; auto. exfalso. inv E. inv H0.
        inv H4.
        **inv H0. inv H2.
          ***inv H0. eauto using safe_prefix_postfix.
          ***inv H7. inv H0.
        **eapply H; eauto with IPPGrammar.
      * clear E. insert_post_pnode_destruct pr o (PrefixNode o21 t212) o2.
        **inv E. inv H1. destruct (has_postfix_rm_conflicts pr (PrefixNode o21 t212) o2) eqn:E; auto. exfalso.
          apply has_postfix_rm_conflicts_true in E. inv E. inv H1. eapply H; eauto with IPPGrammar.
        **clear E. exfalso. eapply H0; eauto using complete_neg_5 with IPPGrammar.
  - cbn [insert_post]. insert_pre_pnode_destruct pr o (PostfixNode t211 o21) o2.
    + inv E. inv H. destruct (has_prefix_lm_conflicts pr o (PostfixNode t211 o21)) eqn:E1.
      * simpl. reflexivity.
      * insert_post_pnode_destruct pr o (PostfixNode t211 o21) o2; auto. exfalso. inv E. inv H. inv H1.
        **inv H. inv H3.
          ***inv H. eauto using safe_prefix_postfix.
          ***inv H6. inv H.
        **eapply has_prefix_lm_conflicts_false; eauto with IPPGrammar.
    + clear E. destruct (has_prefix_lm_conflicts pr o (PostfixNode t211 o21)) eqn:E1.
      * exfalso. apply has_prefix_lm_conflicts_true in E1. inv E1. inv H0. eapply H; eauto with IPPGrammar.
      * insert_post_pnode_destruct pr o (PostfixNode t211 o21) o2; auto. clear E. exfalso.
        apply H with o2; eauto using complete_neg_5 with IPPGrammar.
Qed.

Lemma repair_in_insert_post_assoc {g} (pr : drules g) t1 o t21 o2 :
  safe_pr pr -> complete_pr pr ->
  repair_in pr t1 o (insert_post pr t21 o2) =
  insert_post pr (repair_in pr t1 o t21) o2.
Proof.
  intros Hsafe Hcomplte.
  revert o t21 o2. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1]; intros.
  - simpl. auto using insert_in_insert_post_assoc.
  - simpl. rewrite IHt12. rewrite IHt1_1. reflexivity.
  - simpl. rewrite IHt12. auto using insert_pre_insert_post_assoc.
  - simpl. auto using insert_in_insert_post_assoc.
Qed.

Lemma reorder_step_repair {g} (pr : drules g) t1 t2 :
  safe_pr pr -> complete_pr pr ->
  reorder_step t1 t2 -> repair pr t1 = repair pr t2.
Proof.
  intros HSafe HComplete ?. induction H.
  - apply repair_in_assoc.
  - simpl. auto using repair_in_insert_pre_assoc.
  - simpl. auto using repair_in_insert_post_assoc.
  - simpl. auto using insert_pre_insert_post_assoc.
  - simpl. rewrite IHreorder_step. reflexivity.
  - simpl. rewrite IHreorder_step. reflexivity.
  - simpl. rewrite IHreorder_step. reflexivity.
  - simpl. rewrite IHreorder_step. reflexivity.
Qed.

Lemma reorder_repair {g} (pr : drules g) t1 t2 :
  safe_pr pr -> complete_pr pr ->
  reorder t1 t2 -> repair pr t1 = repair pr t2.
Proof.
  intros HSafe HComplete ?. induction H.
  - reflexivity.
  - rewrite <- IHrtc. inv H.
    + auto using reorder_step_repair.
    + symmetry. auto using reorder_step_repair.
Qed.

End IPPGrammarTheorems2.
