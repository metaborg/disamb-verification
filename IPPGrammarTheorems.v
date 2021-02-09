Require Import MyUtils.
Require Export IPPGrammar.

Section IPPGrammarTheorems.

Create HintDb IPPGrammar.
Hint Resolve CPrio_infix_infix_1 : IPPGrammar.
Hint Resolve CPrio_infix_infix_2 : IPPGrammar.
Hint Resolve CPrio_prefix_infix : IPPGrammar.
Hint Resolve CPrio_infix_prefix : IPPGrammar.
Hint Resolve CLeft_prefix_infix : IPPGrammar.
Hint Resolve CRight_infix_prefix : IPPGrammar.
Hint Resolve CRight_postfix_infix : IPPGrammar.
Hint Resolve CRight_postfix_infix : IPPGrammar.
Hint Resolve CPrio_postfix_infix : IPPGrammar.
Hint Resolve CPrio_postfix_prefix : IPPGrammar.
Hint Resolve CPrio_infix_postfix : IPPGrammar.
Hint Resolve CLeft_infix_postfix : IPPGrammar.
Hint Resolve CPrio_prefix_postfix : IPPGrammar.
Hint Resolve CLeft_prefix_postfix : IPPGrammar.
Hint Resolve CRight_postfix_prefix : IPPGrammar.
Hint Resolve CLeft : IPPGrammar.
Hint Resolve CRight : IPPGrammar.
Hint Resolve HMatch : IPPGrammar.
Hint Resolve InfixMatch : IPPGrammar.
Hint Resolve PrefixMatch : IPPGrammar.
Hint Resolve PostfixMatch : IPPGrammar.
Hint Resolve Atomic_wf : IPPGrammar.
Hint Resolve Infix_wf : IPPGrammar.
Hint Resolve Prefix_wf : IPPGrammar.
Hint Resolve Postfix_wf : IPPGrammar.
Hint Resolve Atomic_cf : IPPGrammar.
Hint Resolve Atomic_drmcf : IPPGrammar.
Hint Resolve Match_rm : IPPGrammar.
Hint Resolve InfixMatch_rm : IPPGrammar.
Hint Resolve PrefixMatch_rm : IPPGrammar.
Hint Resolve InfixMatch_drm : IPPGrammar.
Hint Resolve PrefixMatch_drm : IPPGrammar.
Hint Resolve PostfixMatch_drm : IPPGrammar.
Hint Resolve Atomic_dlmcf : IPPGrammar.
Hint Resolve Match_lm : IPPGrammar.
Hint Resolve InfixMatch_lm : IPPGrammar.
Hint Resolve PostfixMatch_lm : IPPGrammar.
Hint Resolve InfixMatch_dlm : IPPGrammar.
Hint Resolve PrefixMatch_dlm : IPPGrammar.
Hint Resolve PostfixMatch_dlm : IPPGrammar.

Lemma is_i_conflict_pattern_true {g} (pr : drules g) q :
  i_conflict_pattern pr q <-> is_i_conflict_pattern pr q = true.
Proof.
  split; intro.
  - inv H; simpl; auto using decide_True, decide_False.
    + destruct (decide (prio pr (InfixProd o1) (InfixProd o2))); auto using decide_True, decide_False.
    + destruct (decide (prio pr (InfixProd o1) (InfixProd o2))); auto using decide_True, decide_False.
    + destruct (decide (prio pr (PrefixProd o1) (InfixProd o2))); auto using decide_True, decide_False.
    + destruct (decide (prio pr (PostfixProd o1) (InfixProd o2))); auto using decide_True, decide_False.
  - destruct q; inv H.
    + destruct q1, q2; inv H1.
      * destruct q2_1, q2_2; inv H0.
        destruct (decide (prio pr (InfixProd o) (InfixProd o0))); eauto with IPPGrammar.
        destruct (decide (left_a pr (InfixProd o) (InfixProd o0))); eauto with IPPGrammar.
        inv H1.
      * destruct q1_1, q1_2; inv H0.
        destruct (decide (prio pr (InfixProd o) (InfixProd o0))); eauto with IPPGrammar.
        destruct (decide (right_a pr (InfixProd o) (InfixProd o0))); eauto with IPPGrammar.
        inv H1.
      * destruct q1_1, q1_2; inv H0.
      * destruct q1_1, q1_2; inv H0.
      * destruct q1_1, q1_2; inv H0.
    + destruct q; inv H1.
      destruct q1, q2; inv H0.
      destruct (decide (prio pr (PrefixProd o) (InfixProd o0))); eauto with IPPGrammar.
      destruct (decide (left_a pr (PrefixProd o) (InfixProd o0))); eauto with IPPGrammar.
      inv H1.
    + destruct q; inv H1.
      destruct q1, q2; inv H0.
      destruct (decide (prio pr (PostfixProd o) (InfixProd o0))); eauto with IPPGrammar.
      destruct (decide (right_a pr (PostfixProd o) (InfixProd o0))); eauto with IPPGrammar.
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

Lemma is_lm_conflict_pattern_true {g} (pr : drules g) q :
  lm_conflict_pattern pr q <-> is_lm_conflict_pattern pr q = true.
Proof.
  split; intro.
  - inv H; simpl; auto using decide_True, decide_False.
    + destruct (decide (prio pr (InfixProd o1) (PostfixProd o2))); auto using decide_True, decide_False.
    + destruct (decide (prio pr (PrefixProd o1) (PostfixProd o2))); auto using decide_True, decide_False.
  - destruct q; inv H.
    + destruct q1, q2; inv H1.
      destruct q2; inv H0.
      destruct (decide (prio pr (InfixProd o) (PostfixProd o0))); eauto with IPPGrammar.
      destruct (decide (left_a pr (InfixProd o) (PostfixProd o0))); eauto with IPPGrammar.
      inv H1.
    + destruct q; inv H1.
      destruct q; inv H0.
      destruct (decide (prio pr (PrefixProd o) (PostfixProd o0))); eauto with IPPGrammar.
      destruct (decide (left_a pr (PrefixProd o) (PostfixProd o0))); eauto with IPPGrammar.
      inv H1.
Qed.

Lemma is_lm_conflict_pattern_false {g} (pr : drules g) q :
  ~ lm_conflict_pattern pr q <-> is_lm_conflict_pattern pr q = false.
Proof.
  split; intro.
  - destruct (is_lm_conflict_pattern pr q) eqn:E; auto.
    exfalso. destruct H. apply is_lm_conflict_pattern_true.
    assumption.
  - intro. apply is_lm_conflict_pattern_true in H0.
    rewrite H in H0. inv H0.
Qed.

Lemma has_infix_lm_conflicts_true {g} (pr : drules g) o t2 :
  has_infix_lm_conflicts pr o t2 = true
  <-> exists x, lm_conflict_pattern pr (CR_infix_postfix o x)
      /\ matches_lm t2 (PostfixPatt HPatt x).
Proof.
  induction t2; split; intros.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - apply IHt2_1 in H.
    inv H. inv H0. eauto with IPPGrammar.
  - simpl. inv H. inv H0.
    inv H1. 
    + inv H0.
    + apply IHt2_1. eauto with IPPGrammar.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - cbn [has_infix_lm_conflicts] in H.
    destruct (is_lm_conflict_pattern pr (CR_infix_postfix o o0)) eqn:E.
    + apply is_lm_conflict_pattern_true in E.
      eauto with IPPGrammar.
    + apply IHt2 in H.
      inv H. inv H0. eauto with IPPGrammar.
  - inv H. inv H0. cbn [has_infix_lm_conflicts].
    destruct (is_lm_conflict_pattern pr (CR_infix_postfix o o0)) eqn:E; auto.
    inv H1.
    + inv H0. apply is_lm_conflict_pattern_true in H.
      rewrite H in E. inv E.
    + rewrite IHt2.
      eauto with IPPGrammar.
Qed.

Lemma has_infix_lm_conflicts_false {g} (pr : drules g) o t2 :
  has_infix_lm_conflicts pr o t2 = false
  <-> (forall x, matches_lm t2 (PostfixPatt HPatt x) -> ~ lm_conflict_pattern pr (CR_infix_postfix o x)).
Proof.
  split; intros.
  - intro. assert (has_infix_lm_conflicts pr o t2 = true). {
      apply has_infix_lm_conflicts_true. eauto.
    }
    rewrite H in H2. inv H2.
  - destruct (has_infix_lm_conflicts pr o t2) eqn:E; auto.
    apply has_infix_lm_conflicts_true in E.
    inv E. inv H0. exfalso. eapply H; eauto.
Qed.

Lemma has_prefix_lm_conflicts_true {g} (pr : drules g) o t2 :
  has_prefix_lm_conflicts pr o t2 = true
  <-> exists x, lm_conflict_pattern pr (CR_prefix_postfix o x)
      /\ matches_lm t2 (PostfixPatt HPatt x).
Proof.
  induction t2; split; intros.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - apply IHt2_1 in H.
    inv H. inv H0. eauto with IPPGrammar.
  - simpl. inv H. inv H0.
    inv H1. 
    + inv H0.
    + apply IHt2_1. eauto with IPPGrammar.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - cbn [has_prefix_lm_conflicts] in H.
    destruct (is_lm_conflict_pattern pr (CR_prefix_postfix o o0)) eqn:E.
    + apply is_lm_conflict_pattern_true in E.
      eauto with IPPGrammar.
    + apply IHt2 in H.
      inv H. inv H0. eauto with IPPGrammar.
  - inv H. inv H0. cbn [has_prefix_lm_conflicts].
    destruct (is_lm_conflict_pattern pr (CR_prefix_postfix o o0)) eqn:E; auto.
    inv H1.
    + inv H0. apply is_lm_conflict_pattern_true in H.
      rewrite H in E. inv E.
    + rewrite IHt2.
      eauto with IPPGrammar.
Qed.

Lemma has_prefix_lm_conflicts_false {g} (pr : drules g) o t2 :
  has_prefix_lm_conflicts pr o t2 = false
  <-> (forall x, matches_lm t2 (PostfixPatt HPatt x) -> ~ lm_conflict_pattern pr (CR_prefix_postfix o x)).
Proof.
  split; intros.
  - intro. assert (has_prefix_lm_conflicts pr o t2 = true). {
      apply has_prefix_lm_conflicts_true. eauto.
    }
    rewrite H in H2. inv H2.
  - destruct (has_prefix_lm_conflicts pr o t2) eqn:E; auto.
    apply has_prefix_lm_conflicts_true in E.
    inv E. inv H0. exfalso. eapply H; eauto.
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

Lemma safe_infix_postfix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  lm_conflict_pattern pr (CR_infix_postfix o1 o2) ->
  i_conflict_pattern pr (CL_postfix_infix o2 o1) ->
  False.
Proof.
  intros. unfold safe_pr in H.
  inv H0; inv H1; eauto.
Qed.

Ltac linsert_lo_inode_destruct pr o t21 o2 t22 :=
    cbn [linsert_lo] in *;
    destruct (is_i_conflict_pattern pr (CR_infix_infix o o2)) eqn:E;
    [ apply is_i_conflict_pattern_true in E |
      apply is_i_conflict_pattern_false in E;
      destruct (has_infix_lm_conflicts pr o (InfixNode t21 o2 t22)) eqn:E2;
      [ apply has_infix_lm_conflicts_true in E2 |
        assert (forall x, matches_lm (InfixNode t21 o2 t22) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_infix_postfix o x));
        [apply has_infix_lm_conflicts_false; assumption|]
      ]
    ].

Ltac linsert_lo_pnode_destruct pr o t21 o2 :=
    cbn [linsert_lo] in *;
     destruct (has_infix_lm_conflicts pr o (PostfixNode t21 o2)) eqn:E;
     [apply has_infix_lm_conflicts_true in E |
      assert (forall x, matches_lm (PostfixNode t21 o2) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_infix_postfix o x));
      [apply has_infix_lm_conflicts_false; assumption|]
    ].

Ltac slinsert_to_inode_destruct pr o t21 o2 t22 :=
    cbn [slinsert_to] in *;
    destruct (is_i_conflict_pattern pr (CR_infix_infix o o2)) eqn:E;
    [ apply is_i_conflict_pattern_true in E |
      apply is_i_conflict_pattern_false in E;
      destruct (has_infix_lm_conflicts pr o (InfixNode t21 o2 t22)) eqn:E2;
      [ apply has_infix_lm_conflicts_true in E2 |
        assert (forall x, matches_lm (InfixNode t21 o2 t22) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_infix_postfix o x));
        [apply has_infix_lm_conflicts_false; assumption|]
      ]
    ].

Ltac slinsert_to_pnode_destruct pr o t21 o2 :=
    cbn [slinsert_to] in *;
     destruct (has_infix_lm_conflicts pr o (PostfixNode t21 o2)) eqn:E;
     [apply has_infix_lm_conflicts_true in E |
      assert (forall x, matches_lm (PostfixNode t21 o2) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_infix_postfix o x));
      [apply has_infix_lm_conflicts_false; assumption|]
    ].

Ltac linsert_o_inode_destruct pr o t21 o2 t22 :=
    cbn [linsert_o] in *;
    destruct (is_i_conflict_pattern pr (CR_prefix_infix o o2)) eqn:E;
    [ apply is_i_conflict_pattern_true in E |
      apply is_i_conflict_pattern_false in E;
      destruct (has_prefix_lm_conflicts pr o (InfixNode t21 o2 t22)) eqn:E2;
      [ apply has_prefix_lm_conflicts_true in E2 |
        assert (forall x, matches_lm (InfixNode t21 o2 t22) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_prefix_postfix o x));
        [apply has_prefix_lm_conflicts_false; assumption|]
      ]
    ].

Ltac linsert_o_pnode_destruct pr o t21 o2 :=
    cbn [linsert_o] in *;
     destruct (has_prefix_lm_conflicts pr o (PostfixNode t21 o2)) eqn:E;
     [apply has_prefix_lm_conflicts_true in E |
      assert (forall x, matches_lm (PostfixNode t21 o2) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_prefix_postfix o x));
      [apply has_prefix_lm_conflicts_false; assumption|]
    ].

Lemma linsert_lo_size_preserve {g} (pr : drules g) l1 o t2 :
  size (linsert_lo pr l1 o t2) = size (InfixNode (AtomicNode l1) o t2).
Proof.
  induction t2; auto.
  - linsert_lo_inode_destruct pr o t2_1 o0 t2_2; auto; simpl in *; rewrite IHt2_1; auto.
  - linsert_lo_pnode_destruct pr o t2 o0; auto.
    simpl. rewrite IHt2. reflexivity.
Qed.

Lemma slinsert_to_size_preserve {g} (pr : drules g) t1 o t2 :
  size (slinsert_to pr t1 o t2) = size (InfixNode t1 o t2).
Proof.
  induction t2; auto.
  - slinsert_to_inode_destruct pr o t2_1 o0 t2_2; auto; simpl in *; rewrite IHt2_1; lia.
  - slinsert_to_pnode_destruct pr o t2 o0; auto.
    simpl in *. rewrite IHt2. lia.
Qed.

Lemma linsert_o_size_preserve {g} (pr : drules g) o t2 :
  size (linsert_o pr o t2) = size (PrefixNode o t2).
Proof.
  induction t2; auto.
  - linsert_o_inode_destruct pr o t2_1 o0 t2_2; auto; simpl in *; rewrite IHt2_1; auto.
  - linsert_o_pnode_destruct pr o t2 o0; auto.
    simpl in *. rewrite IHt2. reflexivity.
Qed.

Lemma linsert_to_size_preserve {g} (pr : drules g) t1 o opt_t2 fuel t' :
  linsert_to pr t1 o opt_t2 fuel = Some t' ->
  (forall t2, opt_t2 = Some t2 -> size t' = size (InfixNode t1 o t2)) /\
  (opt_t2 = None -> size t' = size (PostfixNode t1 o)).
Proof.
  revert t1 o opt_t2 t'. induction fuel; intros; simpl in *.
  - split; inv H.
  - destruct opt_t2.
    + split; intros.
      * inv H0.
        destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1]; simpl in *.
        **inv H. rewrite linsert_lo_size_preserve. reflexivity.
        **destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H.
          apply IHfuel in E. apply IHfuel in H1.
          inv E. inv H1.
          rewrite H2 with p; auto.
          rewrite H with t2; auto.
          lia.
        **destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H.
          rewrite linsert_o_size_preserve. simpl.
          apply IHfuel in E. inv E.
          rewrite H with t2; auto.
        **destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H.
          destruct p; auto.
          ***apply IHfuel in E. apply IHfuel in H1.
            inv E. inv H1.
            rewrite H2 with t2; auto.
            rewrite H0; auto.
          ***apply IHfuel in E. apply IHfuel in H1.
            inv E. inv H1.
            rewrite H2 with t2; auto.
            rewrite H0; auto.
          ***apply IHfuel in E. apply IHfuel in H1.
            inv E. inv H1.
            rewrite H2 with t2; auto.
            rewrite H0; auto.
          ***inv H1.
            rewrite slinsert_to_size_preserve.
            apply IHfuel in E. inv E.
            assert (size (PostfixNode p o0) = S (size t11)); auto.
            simpl in *. auto.
    * inv H0.
  + split; intros.
    * inv H0.
    * destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1]; simpl in *.
      **inv H. reflexivity.
      **destruct (linsert_to pr t12 o None fuel) eqn:E; inv H.
        apply IHfuel in E. apply IHfuel in H2.
        inv E. inv H2.
        rewrite H3 with p; auto.
        rewrite H1; auto.
      **destruct (linsert_to pr t12 o None fuel) eqn:E; inv H.
        rewrite linsert_o_size_preserve. simpl.
        apply IHfuel in E. inv E.
        rewrite H1; auto.
      **destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H.
        apply IHfuel in E. inv E. assert (size p = S (size t11)); auto. clear H1.
        destruct p; inv H2.
        ***simpl in *. lia.
        ***destruct (linsert_to pr p2 o None fuel) eqn:E; inv H4.
          apply IHfuel in H2. inv H2. rewrite H1 with p; auto.
          apply IHfuel in E. inv E. rewrite H5; auto.
          simpl in *. lia.
        ***destruct (linsert_to pr p o None fuel) eqn:E; inv H4.
          rewrite linsert_o_size_preserve. simpl.
          apply IHfuel in E. inv E. rewrite H2; auto. 
        ***simpl in *. lia.
Qed.

Lemma linsert_to_some {g} (pr : drules g) t1 o opt_t2 fuel :
  fuel > (size t1 * size t1) + size2 t1 ->
  exists t', linsert_to pr t1 o opt_t2 fuel = Some t'.
Proof.
  revert t1 o opt_t2.
  induction fuel; try lia.
  intros. simpl in *.
  destruct opt_t2.
  - destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1]; simpl in *.
    + eauto.
    + destruct (linsert_to pr t12 o (Some p) fuel) eqn:E.
      * apply IHfuel. destruct t11; simpl in *; lia.
      * exfalso.
        assert (exists t', linsert_to pr t12 o (Some p) fuel = Some t'). {
          apply IHfuel. destruct t12; simpl in *; lia.
        }
        inv H0. rewrite E in H1. inv H1.
    + destruct (linsert_to pr t12 o (Some p) fuel) eqn:E; eauto.
      exfalso.
      assert (exists t', linsert_to pr t12 o (Some p) fuel = Some t'). {
        apply IHfuel. destruct t12; simpl in *; lia.
      }
      inv H0. rewrite E in H1. inv H1.
    + destruct (linsert_to pr t11 o1 None fuel) eqn:E.
      * destruct p0; simpl in *; eauto.
        **apply IHfuel. simpl. lia.
        **apply IHfuel. simpl.
          apply linsert_to_size_preserve in E. inv E.
          simpl in H1.
          assert (S (size p0_1 + size p0_2) = S (size t11)); auto.
          lia.
        **apply IHfuel. simpl.
          apply linsert_to_size_preserve in E. inv E.
          simpl in H1.
          assert (S (size p0) = S (size t11)); auto.
          lia.
      * exfalso.
        assert (exists t', linsert_to pr t11 o1 None fuel = Some t'). {
          apply IHfuel. destruct t11; simpl in *; lia.
        }
        inv H0. rewrite E in H1. inv H1.
  - destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1]; simpl in *.
    + eauto.
    + destruct (linsert_to pr t12 o None fuel) eqn:E.
      * apply IHfuel. destruct t11; simpl in *; lia.
      * exfalso.
        assert (exists t', linsert_to pr t12 o None fuel = Some t'). {
          apply IHfuel. destruct t12; simpl in *; lia.
        }
        inv H0. rewrite E in H1. inv H1.
    + destruct (linsert_to pr t12 o None fuel) eqn:E; eauto.
      exfalso.
      assert (exists t', linsert_to pr t12 o None fuel = Some t'). {
        apply IHfuel. destruct t12; simpl in *; lia.
      }
      inv H0. rewrite E in H1. inv H1.
    + destruct (linsert_to pr t11 o1 None fuel) eqn:E; eauto.
      * destruct p; eauto.
        **destruct (linsert_to pr p2 o None fuel) eqn:E2.
          ***apply IHfuel. apply linsert_to_size_preserve in E.
            inv E. assert (size (InfixNode p1 o0 p2) = size (PostfixNode t11 o1)); auto.
            simpl in *. inv H2. rewrite <- H4 in *.
            destruct p1; simpl in *; lia.
            clear H1 H0. lia.
            lra.
            assert (size p2 = 0). admit. rewrite <- H0 in *. destruct p1; simpl in *; lia.
            assert (ge (size p2) 0). lia.
            simpl in *. inv H2. rewrite <- H3 in H.
            inv H. assert (size p2 = 0). admit. rewrite H. destruct p1; simpl in *; lia.
            destruct p1; simpl in *; lia.
      * exfalso.
        assert (exists t', linsert_to pr t11 o1 None fuel = Some t'). {
          apply IHfuel. destruct t11; simpl in *; lia.
        }
        inv H0. rewrite E in H1. inv H1.
Qed.

Lemma linsert_to_fueled_some {g} (pr : drules g) t1 o opt_t2 :
  exists t', linsert_to_fueled pr t1 o opt_t2 = Some t'.
Proof.
  apply linsert_to_some. destruct t1; simpl; lia.
Qed.

Lemma repair_some {g} (pr : drules g) t :
  exists t', repair pr t = Some t'.
Proof.
  induction t; eauto using linsert_to_fueled_some.
  - simpl. inv IHt2. rewrite H. eauto using linsert_to_fueled_some.
  - simpl. inv IHt. rewrite H. eauto.
Qed.

Lemma linsert_lo_wf {g} (pr : drules g) l1 o t2 :
  wf_parse_tree g t2 ->
  g.(prods) (InfixProd o) ->
  wf_parse_tree g (linsert_lo pr l1 o t2).
Proof.
  intros. induction H; eauto with IPPGrammar.
  - linsert_lo_inode_destruct pr o t1 o0 t2; auto with IPPGrammar.
  - linsert_lo_pnode_destruct pr o t o0; auto with IPPGrammar.
Qed.

Lemma linsert_o_wf {g} (pr : drules g) o t2 :
  wf_parse_tree g t2 ->
  g.(prods) (PrefixProd o) ->
  wf_parse_tree g (linsert_o pr o t2).
Proof.
  intros. induction H; eauto with IPPGrammar.
  - linsert_o_inode_destruct pr o t1 o0 t2; auto with IPPGrammar.
  - linsert_o_pnode_destruct pr o t o0; auto with IPPGrammar.
Qed.

Lemma slinsert_to_wf {g} (pr : drules g) t1 o t2 :
  wf_parse_tree g t1 ->
  wf_parse_tree g t2 ->
  g.(prods) (InfixProd o) ->
  wf_parse_tree g (slinsert_to pr t1 o t2).
Proof.
  intros. induction t2.
  - simpl. auto with IPPGrammar.
  - inv H0. slinsert_to_inode_destruct pr o t2_1 o0 t2_2; auto with IPPGrammar.
  - simpl. inv H0. auto with IPPGrammar.
  - inv H0. slinsert_to_pnode_destruct pr o t2 o0; auto with IPPGrammar.
Qed.

Lemma linsert_to_wf {g} (pr : drules g) t1 o opt_t2 t' fuel :
  wf_parse_tree g t1 ->
  (forall t2, opt_t2 = Some t2 -> wf_parse_tree g t2 /\ g.(prods) (InfixProd o)) ->
  (opt_t2 = None -> g.(prods) (PostfixProd o)) ->
  linsert_to pr t1 o opt_t2 fuel = Some t' ->
  wf_parse_tree g t'.
Proof.
  revert t1 o opt_t2 t'.
  induction fuel; simpl; intros. inv H2.
  destruct opt_t2.
  - specialize H0 with p. rename p into t2.
    assert (Some t2 = Some t2). { reflexivity. }
    apply H0 in H3. inv H3.
    destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1]; inv H2.
    + auto using linsert_lo_wf.
    + destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H6.
      inv H.
      apply IHfuel with t11 o1 (linsert_to pr t12 o (Some t2) fuel); intros; auto.
      * split; auto.
        apply IHfuel with t12 o (Some t2); intros; auto.
        inv H2. auto.
      * rewrite E in H. inv H.
      * rewrite E. rewrite H3. reflexivity.
    + assert (Some t2 = Some t2). { reflexivity. }
      apply H0 in H2.
      inv H.
      destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H6.
      apply linsert_o_wf; auto.
      eapply IHfuel; eauto.
      intros. inv H. split; assumption.
    + destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H6.
      inv H.
      destruct p; simpl in *.
      * apply IHfuel with (AtomicNode l) o (Some t2); auto with IPPGrammar.
        intros. inv H. split; assumption.
      * apply IHfuel with (InfixNode p1 o0 p2) o (Some t2); auto.
        ** apply IHfuel with t11 o1 None; auto.
           intros. inv H.
        ** intros. inv H. split; assumption.
      * apply IHfuel with (PrefixNode o0 p) o (Some t2); auto.
        ** apply IHfuel with t11 o1 None; auto.
           intros. inv H.
        ** intros. inv H. split; assumption.
      * inv H3. apply slinsert_to_wf; auto.
        apply IHfuel with t11 o1 None; auto.
        intros. inv H.
  - assert (prods g (PostfixProd o)); auto.
    destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1]; inv H2.
    + auto with IPPGrammar.
    + inv H.
      destruct (linsert_to pr t12 o None fuel) eqn:E; inv H5.
      apply IHfuel with t11 o1 (Some p); intros; auto.
      * inv H. split; try assumption.
        eauto using IHfuel.
      * inv H.
    + inv H.
      destruct (linsert_to pr t12 o None fuel) eqn:E; inv H5.
      apply linsert_o_wf; try assumption.
      eauto using IHfuel.
    + inv H.
      destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H5.
      apply Postfix_wf; auto.
      apply IHfuel in E; auto. intros. inv H.
Qed.

Lemma linsert_to_fueled_wf {g} (pr : drules g) t1 o opt_t2 t' :
  wf_parse_tree g t1 ->
  (forall t2, opt_t2 = Some t2 -> wf_parse_tree g t2 /\ g.(prods) (InfixProd o)) ->
  (opt_t2 = None -> g.(prods) (PostfixProd o)) ->
  linsert_to_fueled pr t1 o opt_t2 = Some t' ->
  wf_parse_tree g t'.
Proof.
  unfold linsert_to_fueled. eauto using linsert_to_wf.
Qed.

Lemma repair_wf {g} (pr : drules g) t t' :
  wf_parse_tree g t ->
  repair pr t = Some t' ->
  wf_parse_tree g t'.
Proof.
  intro. revert t'. induction H; simpl; intros.
  - inv H. auto with IPPGrammar.
  - destruct (repair pr t2) eqn:E; inv H2.
    apply linsert_to_fueled_wf with pr t1 o (Some p); auto.
    intros. inv H2.
  - destruct (repair pr t) eqn:E; inv H1.
    auto using linsert_o_wf.
  - apply linsert_to_fueled_wf with pr t o None; auto.
    intros. inv H2.
Qed.

Lemma linsert_lo_yield_preserve {g} (pr : drules g) l1 o t2 :
  yield (linsert_lo pr l1 o t2) = inl l1 :: inr o :: yield t2.
Proof.
  induction t2; try reflexivity.
  - linsert_lo_inode_destruct pr o t2_1 o0 t2_2; auto; simpl; rewrite IHt2_1; auto.
  - linsert_lo_pnode_destruct pr o t2 o0; simpl; auto.
    rewrite IHt2. reflexivity.
Qed.

Lemma linsert_o_yield_preserve {g} (pr : drules g) o t2 :
  yield (linsert_o pr o t2) = inr o :: yield t2.
Proof.
  induction t2; try reflexivity.
  - linsert_o_inode_destruct pr o t2_1 o0 t2_2; auto; simpl; rewrite IHt2_1; auto.
  - linsert_o_pnode_destruct pr o t2 o0; simpl; auto.
    rewrite IHt2. reflexivity.
Qed.

Lemma slinsert_to_yield_preserve {g} (pr : drules g) t1 o t2 :
  yield (slinsert_to pr t1 o t2) = yield t1 ++ inr o :: yield t2.
Proof.
  induction t2; try reflexivity.
  - slinsert_to_inode_destruct pr o t2_1 o0 t2_2; simpl; auto.
    + rewrite IHt2_1. simplify_list_eq. reflexivity.
    + rewrite IHt2_1. simplify_list_eq. reflexivity.
  - slinsert_to_pnode_destruct pr o t2 o0; simpl; auto.
    rewrite IHt2. simplify_list_eq. reflexivity.
Qed.

Lemma linsert_to_yield_preserve {g} (pr : drules g) t1 o opt_t2 fuel t' :
  linsert_to pr t1 o opt_t2 fuel = Some t' ->
  (forall t2, opt_t2 = Some t2 -> yield t' = yield t1 ++ inr o :: yield t2) /\
  (opt_t2 = None -> yield t' = yield t1 ++ [inr o]).
Proof.
  revert t1 o opt_t2 t'.
  induction fuel; [intros; simpl in H; inv H|].
  intros. simpl in H. split; intros.
  - rewrite H0 in *.
    destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1].
    + simpl. inv H. rewrite linsert_lo_yield_preserve.
      reflexivity.
    + simpl. destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H.
      apply IHfuel in H2. inv H2. rewrite H with p; auto.
      apply IHfuel in E. inv E. rewrite H1 with t2; auto.
      simplify_list_eq. reflexivity.
    + simpl. destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H.
      rewrite linsert_o_yield_preserve.
      apply IHfuel in E. inv E. rewrite H with t2; auto.
    + destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H.
      apply IHfuel in E. inv E. assert (yield p = yield t11 ++ [inr o1]); auto.
      destruct p; simpl.
      * apply IHfuel in H2. inv H2. rewrite H3 with t2; auto.
        rewrite H1. reflexivity.
      * apply IHfuel in H2. inv H2. rewrite H3 with t2; auto.
        rewrite H1. reflexivity.
      * apply IHfuel in H2. inv H2. rewrite H3 with t2; auto.
        rewrite H1. reflexivity.
      * inv H2.
        rewrite slinsert_to_yield_preserve.
        rewrite H1. reflexivity.
  - rewrite H0 in *.
    destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1].
    + inv H. reflexivity.
    + simpl. destruct (linsert_to pr t12 o None fuel) eqn:E; inv H.
      apply IHfuel in H2. inv H2. rewrite H with p; auto.
      apply IHfuel in E. inv E. rewrite H2; auto.
      simplify_list_eq. reflexivity.
    + simpl. destruct (linsert_to pr t12 o None fuel) eqn:E; inv H.
      rewrite linsert_o_yield_preserve.
      apply IHfuel in E. inv E. rewrite H0; auto.
    + simpl. destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H.
      simpl. apply IHfuel in E. inv E. rewrite H0; auto.
Qed.

Lemma linsert_to_fueled_yield_preserve {g} (pr : drules g) t1 o opt_t2 t' :
  linsert_to_fueled pr t1 o opt_t2 = Some t' ->
  (forall t2, opt_t2 = Some t2 -> yield t' = yield t1 ++ inr o :: yield t2) /\
  (opt_t2 = None -> yield t' = yield t1 ++ [inr o]).
Proof.
  unfold linsert_to_fueled. apply linsert_to_yield_preserve.
Qed.

Lemma repair_yield_preserve {g} (pr : drules g) t t' :
  repair pr t = Some t' ->
  yield t' = yield t.
Proof.
  revert t'. induction t; simpl in *; intros.
  - inv H. reflexivity.
  - destruct (repair pr t2) eqn:E; inv H.
    apply linsert_to_fueled_yield_preserve in H1.
    inv H1. rewrite H with p; auto.
    rewrite IHt2 with p; auto.
  - destruct (repair pr t) eqn:E; inv H.
    rewrite linsert_o_yield_preserve.
    rewrite IHt with p; auto.
  - apply linsert_to_fueled_yield_preserve in H.
    inv H. rewrite H1; auto.
Qed.

Lemma i_conflict_pattern_cases {g} (pr : drules g) q :
  i_conflict_pattern pr q -> exists o1 o2,
  q = CR_infix_infix o1 o2 \/
  q = CL_infix_infix o1 o2 \/
  q = CR_prefix_infix o1 o2 \/
  q = CL_postfix_infix o1 o2.
Proof.
  intros. inv H; eauto 7.
Qed.

Ltac icp_cases H :=
  apply i_conflict_pattern_cases in H as T; destruct T as [? T1]; destruct T1 as [? T2];
  destruct T2 as [T5|T3]; [|destruct T3 as [T5|T4]; [|destruct T4 as [T5|T5]]]; rewrite T5 in *; clear T5.

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
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (linsert_lo pr l1 o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (linsert_lo pr l1 o t2) (PostfixPatt HPatt o2)).
Proof.
  destruct t2; eauto 6 with IPPGrammar.
  - linsert_lo_inode_destruct pr o t2_1 o0 t2_2; eauto 7 with IPPGrammar.
  - linsert_lo_pnode_destruct pr o t2 o0; eauto 7 with IPPGrammar.
Qed.

Lemma linsert_lo_top_unchanged {g} (pr : drules g) l1 o t2 x :
  matches_lm t2 (PostfixPatt HPatt x) ->
  lm_conflict_pattern pr (CR_infix_postfix o x) ->
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (linsert_lo pr l1 o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (linsert_lo pr l1 o t2) (PostfixPatt HPatt o2)).
Proof.
  intros. destruct t2.
  - inv H. inv H1.
  - inv H. inv H1. left.
    eexists. split; auto with IPPGrammar.
    linsert_lo_inode_destruct pr o t2_1 o0 t2_2; auto with IPPGrammar.
    exfalso. apply H with x; auto with IPPGrammar.
  - inv H. inv H1.
  - right. eexists. split; auto with IPPGrammar.
    linsert_lo_pnode_destruct pr o t2 o0; auto with IPPGrammar.
    exfalso. apply H1 with x; auto.
Qed.

Lemma linsert_lo_icfree {g} (pr : drules g) l1 o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  i_conflict_free (i_conflict_pattern pr) (linsert_lo pr l1 o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply inode_single_icfree.
  - linsert_lo_inode_destruct pr o t21 o2 t22.
    + inv H0. apply Infix_cf; auto.
      intro. destruct H0 as [q]. inv H0.
      icp_cases H1; inv H2.
      * clear H7. rename x into o2.
        inv H12. rename x0 into o22. clear H7 H9.
        destruct H4. eexists. eauto with IPPGrammar.
      * clear H12. rename x into o2.
        decompose [or] (linsert_lo_top pr l1 o t21).
        **inv H7. rewrite <- H2 in H0.
          inv H0. eauto using safe_infix_infix.
        **destruct H2 as [o21]. inv H7.
          rewrite <- H2 in *.
          inv H0. inv H7.
          inv H3. destruct H4.
          eexists. eauto with IPPGrammar.
        **destruct H2 as [o21]. inv H7.
          rewrite <- H2 in *. inv H0. inv H7.
    + inv H0. apply Infix_cf; auto with IPPGrammar.
      inv E2. inv H0.
      intro. destruct H0 as [q]. inv H0.
      icp_cases H3; inv H7.
      * destruct H4. eexists. eauto with IPPGrammar.
      * inv H2. inv H0.
        apply linsert_lo_top_unchanged with pr l1 o t21 x in H11; auto.
        destruct H11.
        **inv H0. inv H2. inv H9. rewrite <- H2 in *. inv H7.
          destruct H4. eexists. eauto with IPPGrammar.
        **inv H0. inv H2. inv H7. rewrite <- H2 in H9. inv H9.
    + apply Infix_cf; auto with IPPGrammar.
      intro. destruct H2 as [q]. inv H2.
      icp_cases H3; inv H4. 
      * inv H11. contradiction.
      * inv H6.
  - simpl.
    apply Infix_cf; auto with IPPGrammar.
    intro. destruct H1 as [q]. inv H1.
    icp_cases H2; inv H3. inv H10. inv H5.
  - linsert_lo_pnode_destruct pr o t21 o2.
    + inv H0. apply Postfix_cf; auto with IPPGrammar.
      intro. destruct H0 as [q]. inv H0.
      icp_cases H1; inv H2.
      inv E. inv H0. inv H6.
      * inv H0. decompose [or] (linsert_lo_top pr l1 o t21).
        **inv H5. rewrite <- H6 in *. inv H0.
          eauto using safe_infix_postfix.
        **inv H5. rewrite <- H0 in *.
          inv H6. inv H5. inv H6. inv H8.
          destruct H3. eexists. eauto with IPPGrammar.
        **inv H6. inv H0.
          inv H5. rewrite <- H0 in *. inv H8.
      * apply linsert_lo_top_unchanged with pr l1 o t21 x1 in H9; auto.
        destruct H9.
        **inv H0. inv H6. inv H5. rewrite <- H6 in *. inv H7.
          inv H0. destruct H3. eexists. eauto with IPPGrammar.
        **inv H0. inv H6. inv H5. rewrite <- H6 in *. inv H7.
    + apply Infix_cf; auto with IPPGrammar.
      intro. inv H2. inv H3. icp_cases H2; inv H4.
      inv H11. inv H6.
Qed.

Lemma linsert_o_top {g} (pr : drules g) o t2 :
  matches (linsert_o pr o t2) (PrefixPatt o HPatt) \/
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (linsert_o pr o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (linsert_o pr o t2) (PostfixPatt HPatt o2)).
Proof.
  destruct t2; eauto with IPPGrammar.
  - linsert_o_inode_destruct pr o t2_1 o0 t2_2; eauto 7 with IPPGrammar.
  - linsert_o_pnode_destruct pr o t2 o0; eauto 7 with IPPGrammar.
Qed.

Lemma linsert_o_top_unchanged {g} (pr : drules g) o t2 x :
  matches_lm t2 (PostfixPatt HPatt x) ->
  lm_conflict_pattern pr (CR_prefix_postfix o x) ->
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (linsert_o pr o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (linsert_o pr o t2) (PostfixPatt HPatt o2)).
Proof.
  intros. destruct t2.
  - inv H. inv H1.
  - inv H. inv H1. left.
    eexists. split; auto with IPPGrammar.
    linsert_o_inode_destruct pr o t2_1 o0 t2_2; auto with IPPGrammar.
    exfalso. apply H with x; auto with IPPGrammar.
  - inv H. inv H1.
  - right. eexists. split; auto with IPPGrammar.
    linsert_o_pnode_destruct pr o t2 o0; auto with IPPGrammar.
    exfalso. apply H1 with x; auto.
Qed.

Lemma linsert_o_icfree {g} (pr : drules g) o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  i_conflict_free (i_conflict_pattern pr) (linsert_o pr o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply Prefix_cf; auto.
    intro. inv H1. inv H2. icp_cases H1; inv H3. inv H4.
  - linsert_o_inode_destruct pr o t21 o2 t22.
    + inv H0. apply Infix_cf; auto.
      intro. inv H0. inv H1. icp_cases H0; inv H2.
      * inv H12. destruct H4. eexists. eauto with IPPGrammar.
      * decompose [or] (linsert_o_top pr o t21).
        **inv H7. rewrite <- H2 in *. inv H1.
        **inv H2. inv H1. inv H7. rewrite <- H1 in *. inv H3.
          destruct H4. eexists. eauto with IPPGrammar.
        **inv H2. inv H1. inv H7. rewrite <- H1 in *. inv H3.
    + inv H0. apply Infix_cf; auto.
      intro. inv H0. inv H1. inv E2. inv H1. inv H7. inv H1.
      icp_cases H0; inv H2.
      * destruct H4. eexists. eauto with IPPGrammar.
      * apply linsert_o_top_unchanged with pr o t21 x0 in H11; auto.
        destruct H11.
        **inv H1. inv H2. inv H8. rewrite <- H2 in *. inv H7.
          destruct H4. eexists. eauto with IPPGrammar.
        **inv H1. inv H2. inv H8. rewrite <- H2 in *. inv H7.
    + apply Prefix_cf; auto.
      intro. inv H2. inv H3. icp_cases H2; inv H4.
      inv H5. contradiction.
  - simpl. apply Prefix_cf; auto.
    intro. inv H1. inv H2. inv H1; inv H3. inv H4. inv H4.
  - linsert_o_pnode_destruct pr o t21 o2.
    + inv H0. apply Postfix_cf; auto.
      inv E. inv H0. intro. inv H0. inv H5. icp_cases H0; inv H6. inv H7.
      inv H2.
      * inv H6. decompose [or] (linsert_o_top pr o t21); rewrite <- H5 in *.
        ** inv H2.
        ** inv H6. inv H2. inv H8. destruct H3. eexists. eauto with IPPGrammar.
        ** inv H6. inv H2. inv H8.
      * apply linsert_o_top_unchanged with pr o t21 x in H10; auto.
        destruct H10; rewrite <- H5 in *.
        ** inv H2. inv H6. inv H7. destruct H3. eexists. eauto with IPPGrammar.
        ** inv H2. inv H6. inv H7.
    + apply Prefix_cf; auto.
      intro. inv H2. inv H3. icp_cases H2; inv H4. inv H5.
Qed.

Lemma slinsert_to_top {g} (pr : drules g) t1 o t2 :
  matches (slinsert_to pr t1 o t2) (InfixPatt HPatt o HPatt) \/
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (slinsert_to pr t1 o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (slinsert_to pr t1 o t2) (PostfixPatt HPatt o2)).
Proof.
  destruct t2; eauto 6 with IPPGrammar.
  - slinsert_to_inode_destruct pr o t2_1 o0 t2_2; eauto 7 with IPPGrammar.
  - slinsert_to_pnode_destruct pr o t2 o0; eauto 7 with IPPGrammar.
Qed.

Lemma slinsert_to_top_unchanged {g} (pr : drules g) t1 o t2 x :
  matches_lm t2 (PostfixPatt HPatt x) ->
  lm_conflict_pattern pr (CR_infix_postfix o x) ->
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (slinsert_to pr t1 o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (slinsert_to pr t1 o t2) (PostfixPatt HPatt o2)).
Proof.
  intros. destruct t2.
  - inv H. inv H1.
  - inv H. inv H1. left.
    eexists. split; auto with IPPGrammar.
    slinsert_to_inode_destruct pr o t2_1 o0 t2_2; auto with IPPGrammar.
    exfalso. apply H with x; auto with IPPGrammar.
  - inv H. inv H1.
  - right. eexists. split; auto with IPPGrammar.
    slinsert_to_pnode_destruct pr o t2 o0; auto with IPPGrammar.
    exfalso. apply H1 with x; auto.
Qed.

Lemma slinsert_to_icfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t1 ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  (forall o1, i_conflict_pattern pr (CL_infix_infix o o1) -> ~ matches t1 (InfixPatt HPatt o1 HPatt)) ->
  i_conflict_free (i_conflict_pattern pr) (slinsert_to pr t1 o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2]; intros.
  - simpl. apply Infix_cf; auto with IPPGrammar.
    intro. inv H3. inv H4. icp_cases H3; inv H5. inv H12.
    apply H2 with x1; auto.
  - slinsert_to_inode_destruct pr o t21 o2 t22.
    + inv H1. apply Infix_cf; auto.
      intro. inv H1. inv H3. icp_cases H1; inv H4.
      * destruct H6. eexists. eauto with IPPGrammar.
      * inv H9. decompose [or] (slinsert_to_top pr t1 o t21); rewrite <- H3 in *.
        **inv H4. eauto using safe_infix_infix.
        **inv H5. inv H4. inv H9.
          destruct H6. eexists. eauto with IPPGrammar.
        **inv H5. inv H4. inv H9.
    + inv H1. apply Infix_cf; auto with IPPGrammar.
      intro. inv H1. inv H3. icp_cases H1; inv H4.
      * destruct H6. eexists. eauto with IPPGrammar.
      * inv E2. inv H3. inv H5. inv H3.
        inv H9. apply slinsert_to_top_unchanged with pr t1 o t21 x2 in H13; auto.
        destruct H13; rewrite <- H3 in *.
        **inv H5. inv H9. inv H10.
          destruct H6. eexists. eauto with IPPGrammar.
        **inv H5. inv H9. inv H10.
    + apply Infix_cf; auto.
      intro. inv H4. inv H5. icp_cases H4; inv H6.
      * inv H13. contradiction.
      * inv H8. apply H2 with x1; auto with IPPGrammar.
  - simpl. apply Infix_cf; auto with IPPGrammar.
    intro. inv H3. inv H4. icp_cases H3; inv H5. inv H12.
    inv H1. eapply H2; eauto with IPPGrammar.
  - slinsert_to_pnode_destruct pr o t21 o2.
    + inv H1. apply Postfix_cf; auto with IPPGrammar.
      intro. inv H1. inv H3. icp_cases H1; inv H4.
      inv H7. inv E. inv H4. inv H8.
      * inv H4. decompose [or] (slinsert_to_top pr t1 o t21); rewrite <- H3 in *.
        **inv H4. eauto using safe_infix_postfix.
        **inv H8. inv H4. inv H12.
          destruct H5. eexists. eauto with IPPGrammar.
        **inv H8. inv H4. inv H12.
      * apply slinsert_to_top_unchanged with pr t1 o t21 x2 in H13; auto.
        destruct H13; auto; rewrite <- H3 in *.
        **inv H4. inv H8. inv H10.
          destruct H5. eexists. eauto with IPPGrammar.
        **inv H4. inv H8. inv H10.
    + apply Infix_cf; auto with IPPGrammar.
      intro. inv H4. inv H5. icp_cases H4; inv H6. inv H13.
      inv H8. eapply H2; eauto with IPPGrammar.
Qed.

Lemma linsert_to_icfree {g} (pr : drules g) t1 o opt_t2 fuel t' :
  safe_pr pr ->
  (forall t2, opt_t2 = Some t2 -> i_conflict_free (i_conflict_pattern pr) t2) ->
  linsert_to pr t1 o opt_t2 fuel = Some t' ->
  i_conflict_free (i_conflict_pattern pr) t'.
Proof.
  intro. revert t1 o opt_t2 t'. induction fuel; intros; simpl in *. inv H1.
  destruct opt_t2.
  - rename p into t2. assert (i_conflict_free (i_conflict_pattern pr) t2); auto. clear H0.
    destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1].
    + inv H1. auto using linsert_lo_icfree.
    + destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H1.
      apply IHfuel with t11 o1 (Some p); auto.
      intros. inv H0.
      apply IHfuel with t12 o (Some t2); auto.
      intros. inv H0. assumption.
    + destruct (linsert_to pr t12 o (Some t2) fuel) eqn:E; inv H1.
      apply linsert_o_icfree; auto.
      eapply IHfuel; eauto. intros. inv H0. assumption.
    + destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H1.
      destruct p; inv H3.
      * eapply IHfuel; eauto. intros. inv H0. assumption.
      * eapply IHfuel; eauto. intros. inv H0. assumption.
      * eapply IHfuel; eauto. intros. inv H0. assumption.
      * apply slinsert_to_icfree; auto.
        **eapply IHfuel; eauto. intros. inv H0.
        **intros. intro. inv H1.
  - clear H0. destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1].
    + inv H1. apply Postfix_cf; auto with IPPGrammar.
      intro. inv H0. inv H1. icp_cases H0; inv H2. inv H3.
    + destruct (linsert_to pr t12 o None fuel) eqn:E; inv H1.
      eapply IHfuel; eauto. intros. inv H0.
      eapply IHfuel; eauto. intros. inv H0.
    + destruct (linsert_to pr t12 o None fuel) eqn:E; inv H1.
      apply linsert_o_icfree; auto.
      eapply IHfuel; eauto. intros. inv H0.
    + destruct (linsert_to pr t11 o1 None fuel) eqn:E; inv H1.
      apply Postfix_cf.
      * intro. inv H0. inv H1. icp_cases H0; inv H2.
  

(* 



















TODO from here
 *)

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
  intro. destruct H as [q]. inv H. rmcp_cases H0.
  inv H1. inv H3. inv H.
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
      rmcp_cases H1. inv H2.
      apply InfixMatch_drm; eauto using matches_rm_hpatt, linsert_lo_matches_rm.
    + apply Infix_drmcf; auto with IPGrammar.
      intro. destruct H1 as [q]. inv H1.
      rmcp_cases H2. inv H3. inv H5. inv H1.
  - apply Infix_drmcf; auto with IPGrammar.
    intro. destruct H1 as [q]. inv H1.
    rmcp_cases H2. inv H3. inv H5. inv H1.
Qed.

Lemma prefixnode_single_drmcfree {g} (pr : drules g) o l2 :
  drm_conflict_free (rm_conflict_pattern pr)
    (PrefixNode o (AtomicNode l2)).
Proof.
  apply Prefix_drmcf; auto using Atomic_drmcf.
  intro. destruct H as [q]. inv H. rmcp_cases H0.
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
      rmcp_cases H1. inv H2. rename x into o2, x0 into x.
      apply linsert_o_matches_rm in H7.
      inv H7.
      * destruct H4. eexists. split. eauto using CPrio_infix_prefix.
        unfold CL_infix_prefix. apply InfixMatch_drm; auto using Match_rm, HMatch.
      * eapply safe_infix_prefix; eauto using CPrio_infix_prefix.
    + apply Prefix_drmcf; auto. intro.
      inv H1. inv H2. rmcp_cases H1. inv H3.
  - apply Prefix_drmcf; auto. intro.
      inv H1. inv H2. rmcp_cases H1. inv H3.
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
  complete_pr pr ->
  i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o3) ->
  i_conflict_pattern pr (CL_infix_infix o1 o3).
Proof.
  intros. destruct H.
  inv H0; inv H1; eauto with IPGrammar.
Qed.

Lemma complete_trans_2 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_prefix_infix o1 o3).
Proof.
  intros. destruct H.
  inv H0; inv H1; eauto with IPGrammar.
  edestruct complete_10; eauto.
Qed.

Lemma complete_trans_3 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_prefix_infix o1 o3).
Proof.
  intros. destruct H.
  inv H0; inv H1; eauto with IPGrammar.
Qed.

Lemma complete_trans_4 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CR_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_infix_infix o1 o3).
Proof.
  intros. destruct H.
  inv H0; inv H1; eauto with IPGrammar.
Qed.

Lemma complete_neg_1 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ i_conflict_pattern pr (CR_infix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (InfixProd o1) (InfixProd o2).
  decompose [or] complete_1; auto with IPGrammar.
  - destruct H0. auto with IPGrammar.
  - destruct H0. auto with IPGrammar.
Qed.

Lemma complete_neg_2 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ rm_conflict_pattern pr (CL_infix_prefix o1 o2) ->
  i_conflict_pattern pr (CR_prefix_infix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (PrefixProd o2) (InfixProd o1) .
  decompose [or] complete_1; auto with IPGrammar.
  - destruct H0. auto with IPGrammar.
  - destruct H0. auto with IPGrammar.
Qed.

Lemma complete_neg_3 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (InfixProd o2) (InfixProd o1).
  decompose [or] complete_1; auto with IPGrammar.
  - destruct H0. auto with IPGrammar.
  - destruct H0. auto with IPGrammar.
Qed.

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
  complete_pr pr ->
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (PrefixNode o1 t12) ->
  ~ rm_conflict_pattern pr (CL_infix_prefix o o1) ->
  slinsert_to pr (PrefixNode o1 t12) o t2 = linsert_o pr o1 (slinsert_to pr t12 o t2).
Proof.
  intros. inv H0.
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
      auto using complete_neg_2.
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
  complete_pr pr ->
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (InfixNode t11 o1 t12) ->
  ~ i_conflict_pattern pr (CL_infix_infix o o1) ->
  slinsert_to pr (InfixNode t11 o1 t12) o t2 = slinsert_to pr t11 o1 (slinsert_to pr t12 o t2).
Proof.
  intros. induction t2.
  - slinsert_to_inode_destruct pr o1 o.
    + rewrite slinsert_to_complete; auto.
    + destruct H1. auto using complete_neg_1.
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
      * destruct H1.
        auto using complete_neg_1.
  - rename o0 into o2, t2 into t22.
    slinsert_to_inode_destruct pr o1 o.
    + rewrite slinsert_to_complete; auto.
    + destruct H1. auto using complete_neg_1.
Qed.

Lemma linsert_to_slinsert_to {g} (pr : drules g) t1 o t2 :
  complete_pr pr ->
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
      * inv H0. inv H3. inv H4. split; assumption.
      * intros. inv H3.
        rename t1 into t111, t0 into t112, x1 into o11.
        intro.
        inv H0. inv H4. destruct H10.
        eexists. eauto with IPGrammar.
      * intros.
        intro.
        inv H0. inv H6. destruct H9.
        eexists. eauto with IPGrammar.
    + inv H0. inv H3. inv H4. split; assumption.
    + intros. inv H3.
      rename t1 into t121, t0 into t122, x1 into o12. clear H7 H9.
      intro.
      specialize H1 with o1. apply H1; auto with IPGrammar.
      apply complete_trans_1 with o12; auto.
      apply complete_neg_1; auto. intro.
      inv H0. inv H5. destruct H9.
      eexists. eauto with IPGrammar.
    + intros. 
      apply H2.
      auto with IPGrammar.
  - rename o into o1, t1 into t12, o0 into o.
    rewrite IHt1.
    + rewrite slinsert_to_prefix; auto with IPGrammar.
    + inv H0. inv H3. inv H4. split; assumption.
    + intros. inv H3.
      rename t1 into t121, t0 into t122, x1 into o12. clear H7 H9.
      intro.
      inv H0. inv H4. destruct H7.
      exists (CR_prefix_infix o1 o12).
      split; [|unfold CR_prefix_infix; auto with IPGrammar].
      apply complete_trans_2 with o; auto.
      specialize H1 with o1.
      apply complete_neg_2; auto.
      apply H2. auto with IPGrammar.
    + intros. 
      apply H2.
      auto with IPGrammar.
Qed.

Lemma linsert_to_complete {g} (pr : drules g) t1 o t2 :
  complete_pr pr ->
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (InfixNode t1 o t2) ->
  linsert_to pr t1 o t2 = InfixNode t1 o t2.
Proof.
  intros. assert (H0' := H0). inv H0. inv H1. inv H2.
  rewrite linsert_to_slinsert_to; auto.
  - rewrite slinsert_to_complete; auto.
  - split; assumption.
  - intros. inv H0. intro. destruct H5. eexists. eauto with IPGrammar.
  - intros. intro. destruct H4. eexists. eauto with IPGrammar.
Qed.

Lemma repair_complete {g} (pr : drules g) t :
  complete_pr pr ->
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) t ->
  repair pr t = t.
Proof.
  intros. induction t; simpl; auto.
  - rewrite IHt2.
    + rewrite linsert_to_complete; auto.
    + inv H0. inv H1. inv H2. split; assumption.
  - rewrite IHt.
    + rewrite linsert_o_complete; auto.
      inv H0. assumption.
    + inv H0. inv H1. inv H2. split; assumption.
Qed.

Lemma yield_struct_app {g} (w1 : word g) o w2 :
  yield_struct w1 →
  yield_struct w2 →
  yield_struct (w1 ++ inr o :: w2).
Proof.
  intro. induction H; intros; simpl; auto using LOYield, OYield.
Qed.

Lemma yield_is_yield_struct {g} (t : parse_tree g) :
  yield_struct (yield t).
Proof.
  induction t; simpl.
  - apply LYield.
  - auto using yield_struct_app.
  - auto using OYield.
Qed.

Lemma parse_yield_struct_some {g} (pr : drules g) (w : word g) :
  yield_struct w ->
  exists t, parse pr w = Some t.
Proof.
  intros. induction H; eauto.
  - destruct IHyield_struct.
    eexists. simpl. rewrite H0. reflexivity.
  - destruct IHyield_struct.
    eexists. simpl. rewrite H0. reflexivity.
Qed.

Lemma parse_yield_some {g} (pr : drules g) t :
  exists t', parse pr (yield t) = Some t'.
Proof.
  auto using yield_is_yield_struct, parse_yield_struct_some.
Qed.

Lemma parse_app {g} (pr : drules g) t1 t2 t2' o :
  parse pr (yield t2) = Some t2' ->
  parse pr (yield t1 ++ inr o :: yield t2) = Some (linsert_to pr t1 o t2').
Proof.
  revert t2 t2' o. induction t1; intros; simpl.
  - rewrite H. reflexivity.
  - simplify_list_eq. rename o into o1, o0 into o.
    destruct (parse_yield_some pr t1_2).
    erewrite IHt1_1 with (t2 := (InfixNode t1_2 o t2)); auto.
    simpl. erewrite IHt1_2; auto.
  - destruct (parse_yield_some pr t1).
    erewrite IHt1; auto.
Qed.

Lemma repair_parse {g} (pr : drules g) t :
  parse pr (yield t) = Some (repair pr t).
Proof.
  induction t; simpl; auto.
  - erewrite parse_app; eauto.
  - rewrite IHt. reflexivity.
Qed.

Lemma repair_is_fully_yield_dependent {g} (pr : drules g) t1 t2 :
  yield t1 = yield t2 ->
  repair pr t1 = repair pr t2.
Proof.
  intro.
  assert (Some (repair pr t1) = Some (repair pr t2)). {
    rewrite <- repair_parse.
    rewrite H.
    rewrite repair_parse.
    reflexivity.
  }
  inv H0. reflexivity.
Qed.

Theorem completeness {g} (pr : drules g) :
  complete_pr pr ->
  complete pr.
Proof.
  intro. intro. unfold complete. intros.
  apply repair_is_fully_yield_dependent with pr t1 t2 in H0.
  rewrite repair_complete in H0; auto.
  rewrite repair_complete in H0; auto.
Qed.

End IPGrammarTheorems.
