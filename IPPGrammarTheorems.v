Require Import MyUtils.
Require Export IPPGrammar.

Section IPPGrammarTheorems.

Create HintDb IPPGrammar.
Hint Resolve CPrio_infix_infix_1 CPrio_infix_infix_2 CPrio_prefix_infix CPrio_infix_prefix CLeft_prefix_infix
  CRight_infix_prefix CRight_postfix_infix CRight_postfix_infix CPrio_postfix_infix CPrio_postfix_prefix
  CPrio_infix_postfix CLeft_infix_postfix CPrio_prefix_postfix CLeft_prefix_postfix CRight_postfix_prefix CLeft CRight
  HMatch InfixMatch PrefixMatch PostfixMatch Atomic_wf Infix_wf Prefix_wf Postfix_wf Atomic_cf Infix_cf Prefix_cf
  Postfix_cf Atomic_drmcf Infix_drmcf Prefix_drmcf Postfix_drmcf Match_rm InfixMatch_rm PrefixMatch_rm InfixMatch_drm
  PrefixMatch_drm PostfixMatch_drm Atomic_dlmcf Infix_dlmcf Prefix_dlmcf Postfix_dlmcf Match_lm InfixMatch_lm
  PostfixMatch_lm InfixMatch_dlm PrefixMatch_dlm PostfixMatch_dlm
    : IPPGrammar.


(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas relate to the functions boolean functions that check for conflicts in trees,
   such as [is_i_conflict_pattern]. *)

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
    exfalso. destruct H. apply is_i_conflict_pattern_true. assumption.
  - intro. apply is_i_conflict_pattern_true in H0. rewrite H in H0. inv H0.
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
    exfalso. destruct H. apply is_lm_conflict_pattern_true. assumption.
  - intro. apply is_lm_conflict_pattern_true in H0. rewrite H in H0. inv H0.
Qed.

Lemma has_infix_lm_conflicts_true {g} (pr : drules g) o t2 :
  has_infix_lm_conflicts pr o t2 = true <->
  exists x, lm_conflict_pattern pr (CR_infix_postfix o x) /\ matches_lm t2 (PostfixPatt HPatt x).
Proof.
  induction t2; split; intros.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - apply IHt2_1 in H. inv H. inv H0. eauto with IPPGrammar.
  - simpl. inv H. inv H0.
    inv H1. 
    + inv H0.
    + apply IHt2_1. eauto with IPPGrammar.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - cbn [has_infix_lm_conflicts] in H.
    destruct (is_lm_conflict_pattern pr (CR_infix_postfix o o0)) eqn:E.
    + apply is_lm_conflict_pattern_true in E. eauto with IPPGrammar.
    + apply IHt2 in H. inv H. inv H0. eauto with IPPGrammar.
  - inv H. inv H0. cbn [has_infix_lm_conflicts].
    destruct (is_lm_conflict_pattern pr (CR_infix_postfix o o0)) eqn:E; auto.
    inv H1.
    + inv H0. apply is_lm_conflict_pattern_true in H. rewrite H in E. inv E.
    + rewrite IHt2. eauto with IPPGrammar.
Qed.

Lemma has_infix_lm_conflicts_false {g} (pr : drules g) o t2 :
  has_infix_lm_conflicts pr o t2 = false <->
  (forall x, matches_lm t2 (PostfixPatt HPatt x) -> ~ lm_conflict_pattern pr (CR_infix_postfix o x)).
Proof.
  split; intros.
  - intro. assert (has_infix_lm_conflicts pr o t2 = true). { apply has_infix_lm_conflicts_true. eauto. }
    rewrite H in H2. inv H2.
  - destruct (has_infix_lm_conflicts pr o t2) eqn:E; auto.
    apply has_infix_lm_conflicts_true in E. inv E. inv H0. exfalso. eapply H; eauto.
Qed.

Lemma has_prefix_lm_conflicts_true {g} (pr : drules g) o t2 :
  has_prefix_lm_conflicts pr o t2 = true <->
  exists x, lm_conflict_pattern pr (CR_prefix_postfix o x) /\ matches_lm t2 (PostfixPatt HPatt x).
Proof.
  induction t2; split; intros.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - apply IHt2_1 in H. inv H. inv H0. eauto with IPPGrammar.
  - simpl. inv H. inv H0.
    inv H1. 
    + inv H0.
    + apply IHt2_1. eauto with IPPGrammar.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - cbn [has_prefix_lm_conflicts] in H.
    destruct (is_lm_conflict_pattern pr (CR_prefix_postfix o o0)) eqn:E.
    + apply is_lm_conflict_pattern_true in E. eauto with IPPGrammar.
    + apply IHt2 in H. inv H. inv H0. eauto with IPPGrammar.
  - inv H. inv H0. cbn [has_prefix_lm_conflicts].
    destruct (is_lm_conflict_pattern pr (CR_prefix_postfix o o0)) eqn:E; auto.
    inv H1.
    + inv H0. apply is_lm_conflict_pattern_true in H. rewrite H in E. inv E.
    + rewrite IHt2. eauto with IPPGrammar.
Qed.

Lemma has_prefix_lm_conflicts_false {g} (pr : drules g) o t2 :
  has_prefix_lm_conflicts pr o t2 = false <->
  (forall x, matches_lm t2 (PostfixPatt HPatt x) -> ~ lm_conflict_pattern pr (CR_prefix_postfix o x)).
Proof.
  split; intros.
  - intro. assert (has_prefix_lm_conflicts pr o t2 = true). { apply has_prefix_lm_conflicts_true. eauto. }
    rewrite H in H2. inv H2.
  - destruct (has_prefix_lm_conflicts pr o t2) eqn:E; auto.
    apply has_prefix_lm_conflicts_true in E. inv E. inv H0. exfalso. eapply H; eauto.
Qed.

Lemma has_postfix_rm_conflicts_true {g} (pr : drules g) t1 o :
  has_postfix_rm_conflicts pr t1 o = true <->
  exists x, rm_conflict_pattern pr (CL_postfix_prefix o x) /\ matches_rm t1 (PrefixPatt x HPatt).
Proof.
  induction t1; split; intros.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
  - simpl in H. apply IHt1_2 in H. inv H. inv H0. eauto with IPPGrammar.
  - simpl. inv H. inv H0.
    inv H1.
    + inv H0.
    + apply IHt1_2. eauto with IPPGrammar.
  - simpl in H. destruct (decide (prio pr (PostfixProd o) (PrefixProd o0))).
    + eexists. eauto with IPPGrammar.
    + destruct (decide (right_a pr (PostfixProd o) (PrefixProd o0))).
      * eexists. eauto with IPPGrammar.
      * apply IHt1 in H. inv H. inv H0. eexists. eauto with IPPGrammar.
  - simpl. destruct (decide (prio pr (PostfixProd o) (PrefixProd o0))),
             (decide (right_a pr (PostfixProd o) (PrefixProd o0))); auto.
    inv H. inv H0.
    inv H1.
    + inv H0. exfalso. inv H; auto.
    + apply IHt1. eexists. eauto.
  - inv H.
  - inv H. inv H0. inv H1. inv H0.
Qed.

Lemma has_postfix_rm_conflicts_false {g} (pr : drules g) t1 o :
  has_postfix_rm_conflicts pr t1 o = false <->
  (forall x, matches_rm t1 (PrefixPatt x HPatt) -> ~ rm_conflict_pattern pr (CL_postfix_prefix o x)).
Proof.
  split; intros.
  - intro. assert (has_postfix_rm_conflicts pr t1 o = true). { apply has_postfix_rm_conflicts_true. eauto. }
    rewrite H in H2. inv H2.
  - destruct (has_postfix_rm_conflicts pr t1 o) eqn:E; auto.
    apply has_postfix_rm_conflicts_true in E. inv E. inv H0. edestruct H; eauto.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas relate safety to relations between conflict patterns. *)

Lemma safe_infix_infix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o1) ->
  False.
Proof.
  intros H_safe H_CL H_CR. unfold safe_pr in H_safe. inv H_CL; inv H_CR; eauto.
Qed.

Lemma safe_infix_prefix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  rm_conflict_pattern pr (CL_infix_prefix o1 o2) ->
  i_conflict_pattern pr (CR_prefix_infix o2 o1) ->
  False.
Proof.
  intros. unfold safe_pr in H. inv H0; inv H1; eauto.
Qed.

Lemma safe_infix_postfix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  lm_conflict_pattern pr (CR_infix_postfix o1 o2) ->
  i_conflict_pattern pr (CL_postfix_infix o2 o1) ->
  False.
Proof.
  intros. unfold safe_pr in H. inv H0; inv H1; eauto.
Qed.

Lemma safe_prefix_postfix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  lm_conflict_pattern pr (CR_prefix_postfix o1 o2) ->
  rm_conflict_pattern pr (CL_postfix_prefix o2 o1) ->
  False.
Proof.
  intros. unfold safe_pr in H. inv H0; inv H1; eauto.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Helper tactics for simplifying specific repair terms. *)

(* Simplifies the term [insert_in pr t1 o (InfixNode t21 o2 t22)] *)
Ltac insert_in_inode_destruct pr o t21 o2 t22 :=
    cbn [insert_in] in *;
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

(* Simplifies the term [insert_in pr t1 o (PostfixNode t21 o2)] *)
Ltac insert_in_pnode_destruct pr o t21 o2 :=
    cbn [insert_in] in *;
     destruct (has_infix_lm_conflicts pr o (PostfixNode t21 o2)) eqn:E;
     [apply has_infix_lm_conflicts_true in E |
      assert (forall x, matches_lm (PostfixNode t21 o2) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_infix_postfix o x));
      [apply has_infix_lm_conflicts_false; assumption|]
    ].

(* Simplifies the term [insert_pre pr o (InfixNode t21 o2 t22)] *)
Ltac insert_pre_inode_destruct pr o t21 o2 t22 :=
    cbn [insert_pre] in *;
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

(* Simplifies the term [insert_pre pr o (PostfixNode t21 o2)] *)
Ltac insert_pre_pnode_destruct pr o t21 o2 :=
    cbn [insert_pre] in *;
     destruct (has_prefix_lm_conflicts pr o (PostfixNode t21 o2)) eqn:E;
     [apply has_prefix_lm_conflicts_true in E |
      assert (forall x, matches_lm (PostfixNode t21 o2) (PostfixPatt HPatt x) ->
              ~ lm_conflict_pattern pr (CR_prefix_postfix o x));
      [apply has_prefix_lm_conflicts_false; assumption|]
    ].

(* Simplifies the term [insert_post pr (InfixNode t11 o1 t12) o] *)
Ltac insert_post_inode_destruct pr t11 o1 t12 o :=
    cbn [insert_post] in *;
    destruct (is_i_conflict_pattern pr (CL_postfix_infix o o1)) eqn:E;
    [ apply is_i_conflict_pattern_true in E |
      apply is_i_conflict_pattern_false in E;
      destruct (has_postfix_rm_conflicts pr (InfixNode t11 o1 t12) o) eqn:E2;
      [ apply has_postfix_rm_conflicts_true in E2 |
        assert (forall x, matches_rm (InfixNode t11 o1 t12) (PrefixPatt x HPatt) ->
              ~ rm_conflict_pattern pr (CL_postfix_prefix o x));
        [apply has_postfix_rm_conflicts_false; assumption|]
      ]
    ].

(* Simplifies the term [insert_post pr (PrefixNode o1 t12) o] *)
Ltac insert_post_pnode_destruct pr o1 t12 o :=
    cbn [insert_post] in *;
    destruct (has_postfix_rm_conflicts pr (PrefixNode o1 t12) o) eqn:E;
    [ apply has_postfix_rm_conflicts_true in E |
      assert (forall x, matches_rm (PrefixNode o1 t12) (PrefixPatt x HPatt) ->
            ~ rm_conflict_pattern pr (CL_postfix_prefix o x));
      [apply has_postfix_rm_conflicts_false; assumption|]
    ].

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Lemmas that show well-formedness of [repair] *)

Lemma insert_in_wf {g} (pr : drules g) t1 o t2 :
  wf_parse_tree g t1 -> wf_parse_tree g t2 -> g.(prods) (InfixProd (inl o)) ->
  wf_parse_tree g (insert_in pr t1 (inl o) t2).
Proof.
  intros. induction t2.
  - simpl. auto with IPPGrammar.
  - inv H0.
    insert_in_inode_destruct pr (@inl (OPinpre g) (OPpost g) o) t2_1 (@inl (OPinpre g) (OPpost g) o1) t2_2;
    auto with IPPGrammar.
  - simpl. inv H0. auto with IPPGrammar.
  - inv H0.
    insert_in_pnode_destruct pr (@inl (OPinpre g) (OPpost g) o) t2 (@inr (OPinpre g) (OPpost g) o1);
    auto with IPPGrammar.
Qed.

Lemma insert_pre_wf {g} (pr : drules g) o t2 :
  wf_parse_tree g t2 -> g.(prods) (PrefixProd (inl o)) ->
  wf_parse_tree g (insert_pre pr (inl o) t2).
Proof.
  intros. induction H; eauto with IPPGrammar.
  - insert_pre_inode_destruct pr (@inl (OPinpre g) (OPpost g) o) t1 (@inl (OPinpre g) (OPpost g) o0) t2;
    auto with IPPGrammar.
  - insert_pre_pnode_destruct pr (@inl (OPinpre g) (OPpost g) o) t (@inr (OPinpre g) (OPpost g) o0);
    auto with IPPGrammar.
Qed.

Lemma repair_in_wf {g} (pr : drules g) t1 o t2 :
  wf_parse_tree g t1 -> wf_parse_tree g t2 -> g.(prods) (InfixProd (inl o)) ->
  wf_parse_tree g (repair_in pr t1 (inl o) t2).
Proof.
  intro. revert o t2. induction H; intros; simpl; auto using insert_in_wf, insert_pre_wf with IPPGrammar.
Qed.

Lemma insert_post_wf {g} (pr : drules g) t1 o :
  wf_parse_tree g t1 -> g.(prods) (PostfixProd (inr o)) ->
  wf_parse_tree g (insert_post pr t1 (inr o)).
Proof.
  intros. induction H; eauto with IPPGrammar.
  - insert_post_inode_destruct pr t1 (@inl (OPinpre g) (OPpost g) o0) t2 (@inr (OPinpre g) (OPpost g) o);
    auto with IPPGrammar.
  - insert_post_pnode_destruct pr (@inl (OPinpre g) (OPpost g) o0) t (@inr (OPinpre g) (OPpost g) o);
    auto with IPPGrammar.
Qed.

Lemma repair_wf {g} (pr : drules g) t :
  wf_parse_tree g t ->
  wf_parse_tree g (repair pr t).
Proof.
  intro. induction H; simpl; auto using repair_in_wf, insert_pre_wf, insert_post_wf with IPPGrammar.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Lemmas that show yield-preservation of [repair] *)

Lemma insert_pre_yield_preserve {g} (pr : drules g) o t2 :
  yield (insert_pre pr o t2) = inr o :: yield t2.
Proof.
  induction t2; try reflexivity.
  - insert_pre_inode_destruct pr o t2_1 o0 t2_2; auto; simpl; rewrite IHt2_1; auto.
  - insert_pre_pnode_destruct pr o t2 o0; simpl; auto. rewrite IHt2. reflexivity.
Qed.

Lemma insert_in_yield_preserve {g} (pr : drules g) t1 o t2 :
  yield (insert_in pr t1 o t2) = yield t1 ++ inr o :: yield t2.
Proof.
  induction t2; try reflexivity.
  - insert_in_inode_destruct pr o t2_1 o0 t2_2; simpl; auto.
    + rewrite IHt2_1. simplify_list_eq. reflexivity.
    + rewrite IHt2_1. simplify_list_eq. reflexivity.
  - insert_in_pnode_destruct pr o t2 o0; simpl; auto. rewrite IHt2. simplify_list_eq. reflexivity.
Qed.

Lemma repair_in_yield_preserve {g} (pr : drules g) t1 o t2 :
  yield (repair_in pr t1 o t2) = yield t1 ++ inr o :: yield t2.
Proof.
  revert o t2. induction t1; intros.
  - simpl. rewrite insert_in_yield_preserve. reflexivity.
  - simplify_list_eq. rewrite <- IHt1_2. rewrite <- IHt1_1. reflexivity.
  - simpl. rewrite <- IHt1. rewrite insert_pre_yield_preserve. reflexivity.
  - simpl. rewrite insert_in_yield_preserve. reflexivity.
Qed.

Lemma insert_post_yield_preserve {g} (pr : drules g) t1 o :
  yield (insert_post pr t1 o) = yield t1 ++ [inr o].
Proof.
  induction t1; try reflexivity.
  - insert_post_inode_destruct pr t1_1 o0 t1_2 o; auto; simplify_list_eq; rewrite IHt1_2; auto.
  - insert_post_pnode_destruct pr o0 t1 o; auto; simplify_list_eq; rewrite IHt1; auto.
Qed.

Lemma repair_yield_preserve {g} (pr : drules g) t :
  yield (repair pr t) = yield t.
Proof.
  induction t; auto; simpl.
  - rewrite repair_in_yield_preserve. rewrite IHt1. rewrite IHt2. reflexivity.
  - rewrite insert_pre_yield_preserve. rewrite IHt. reflexivity.
  - rewrite insert_post_yield_preserve. rewrite IHt. reflexivity.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Auxiliary lemmas and tactics that help proving safety. *)

Lemma i_conflict_pattern_cases {g} (pr : drules g) q :
  i_conflict_pattern pr q -> exists o1 o2,
  q = CR_infix_infix o1 o2 \/ q = CL_infix_infix o1 o2 \/ q = CR_prefix_infix o1 o2 \/ q = CL_postfix_infix o1 o2.
Proof.
  intros. inv H; eauto 7.
Qed.

Ltac icp_cases H :=
  apply i_conflict_pattern_cases in H as T; destruct T as [? T1]; destruct T1 as [? T2]; destruct T2 as [T5|T3];
  [|destruct T3 as [T5|T4]; [|destruct T4 as [T5|T5]]]; rewrite T5 in *; clear T5.

Lemma rm_conflict_pattern_cases {g} (pr : drules g) q :
  rm_conflict_pattern pr q -> exists o1 o2,
  q = CL_infix_prefix o1 o2 \/ q = CL_postfix_prefix o1 o2.
Proof.
  intros. inv H; eauto.
Qed.

Ltac rcp_cases H :=
  apply rm_conflict_pattern_cases in H as T; destruct T as [? T1]; destruct T1 as [? T2]; destruct T2; subst.

Lemma lm_conflict_pattern_cases {g} (pr : drules g) q :
  lm_conflict_pattern pr q -> exists o1 o2,
  q = CR_infix_postfix o1 o2 \/ q = CR_prefix_postfix o1 o2.
Proof.
  intros. inv H; eauto.
Qed.

Ltac lcp_cases H :=
  apply lm_conflict_pattern_cases in H as T; destruct T as [? T1]; destruct T1 as [? T2]; destruct T2; subst.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Proving safety of shallow conflict patterns (i_conflict_patterns). *)

Lemma insert_in_top {g} (pr : drules g) t1 o t2 :
  matches (insert_in pr t1 o t2) (InfixPatt HPatt o HPatt) \/
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (insert_in pr t1 o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (insert_in pr t1 o t2) (PostfixPatt HPatt o2)).
Proof.
  destruct t2; eauto 6 with IPPGrammar.
  - insert_in_inode_destruct pr o t2_1 o0 t2_2; eauto 7 with IPPGrammar.
  - insert_in_pnode_destruct pr o t2 o0; eauto 7 with IPPGrammar.
Qed.

Lemma insert_in_top_unchanged {g} (pr : drules g) t1 o t2 x :
  matches_lm t2 (PostfixPatt HPatt x) ->
  lm_conflict_pattern pr (CR_infix_postfix o x) ->
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (insert_in pr t1 o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (insert_in pr t1 o t2) (PostfixPatt HPatt o2)).
Proof.
  intros. destruct t2.
  - inv H. inv H1.
  - inv H. inv H1. left.
    eexists. split; auto with IPPGrammar.
    insert_in_inode_destruct pr o t2_1 o0 t2_2; auto with IPPGrammar. exfalso. apply H with x; auto with IPPGrammar.
  - inv H. inv H1.
  - right. eexists. split; auto with IPPGrammar.
    insert_in_pnode_destruct pr o t2 o0; auto with IPPGrammar. exfalso. apply H1 with x; auto.
Qed.

Lemma insert_in_icfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t1 ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  (forall o1, i_conflict_pattern pr (CL_infix_infix o o1) -> ~ matches t1 (InfixPatt HPatt o1 HPatt)) ->
  i_conflict_free (i_conflict_pattern pr) (insert_in pr t1 o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply Infix_cf; auto. intro. inv H3. inv H4. icp_cases H3; inv H5. inv H12. eapply H2; eauto.
  - insert_in_inode_destruct pr o t21 o2 t22.
    + inv H1. apply Infix_cf; auto. intro. inv H1. inv H3. icp_cases H1; inv H4.
      * destruct H6. eexists. eauto with IPPGrammar.
      * inv H9. decompose [or] (insert_in_top pr t1 o t21); rewrite <- H3 in *.
        **inv H4. eauto using safe_infix_infix.
        **inv H5. inv H4. inv H9. destruct H6. eexists. eauto with IPPGrammar.
        **inv H5. inv H4. inv H9.
    + inv H1. apply Infix_cf; auto with IPPGrammar. intro. inv H1. inv H3. icp_cases H1; inv H4.
      * destruct H6. eexists. eauto with IPPGrammar.
      * inv E2. inv H3. inv H5. inv H3.
        inv H9. apply insert_in_top_unchanged with pr t1 o t21 x2 in H13; auto. destruct H13; rewrite <- H3 in *.
        **inv H5. inv H9. inv H10. destruct H6. eexists. eauto with IPPGrammar.
        **inv H5. inv H9. inv H10.
    + apply Infix_cf; auto. intro. inv H4. inv H5. icp_cases H4; inv H6.
      * inv H13. contradiction.
      * inv H8. apply H2 with x1; auto with IPPGrammar.
  - simpl. apply Infix_cf; auto with IPPGrammar. intro. inv H3. inv H4. icp_cases H3; inv H5. inv H12. inv H1.
    eapply H2; eauto with IPPGrammar.
  - insert_in_pnode_destruct pr o t21 o2.
    + inv H1. apply Postfix_cf; auto with IPPGrammar. intro. inv H1. inv H3. icp_cases H1; inv H4. inv H7. inv E.
      inv H4. inv H8.
      * inv H4. decompose [or] (insert_in_top pr t1 o t21); rewrite <- H3 in *.
        **inv H4. eauto using safe_infix_postfix.
        **inv H8. inv H4. inv H12. destruct H5. eexists. eauto with IPPGrammar.
        **inv H8. inv H4. inv H12.
      * apply insert_in_top_unchanged with pr t1 o t21 x2 in H13; auto. destruct H13; auto; rewrite <- H3 in *.
        **inv H4. inv H8. inv H10. destruct H5. eexists. eauto with IPPGrammar.
        **inv H4. inv H8. inv H10.
    + apply Infix_cf; auto with IPPGrammar. intro. inv H4. inv H5. icp_cases H4; inv H6. inv H13. inv H8.
      eapply H2; eauto with IPPGrammar.
Qed.

Lemma insert_pre_top {g} (pr : drules g) o t2 :
  matches (insert_pre pr o t2) (PrefixPatt o HPatt) \/
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (insert_pre pr o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (insert_pre pr o t2) (PostfixPatt HPatt o2)).
Proof.
  destruct t2; eauto with IPPGrammar.
  - insert_pre_inode_destruct pr o t2_1 o0 t2_2; eauto 7 with IPPGrammar.
  - insert_pre_pnode_destruct pr o t2 o0; eauto 7 with IPPGrammar.
Qed.

Lemma insert_pre_top_unchanged {g} (pr : drules g) o t2 x :
  matches_lm t2 (PostfixPatt HPatt x) ->
  lm_conflict_pattern pr (CR_prefix_postfix o x) ->
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\ matches (insert_pre pr o t2) (InfixPatt HPatt o2 HPatt)) \/
  (exists o2, matches t2 (PostfixPatt HPatt o2) /\ matches (insert_pre pr o t2) (PostfixPatt HPatt o2)).
Proof.
  intros. destruct t2.
  - inv H. inv H1.
  - inv H. inv H1. left.
    eexists. split; auto with IPPGrammar.
    insert_pre_inode_destruct pr o t2_1 o0 t2_2; auto with IPPGrammar. exfalso. apply H with x; auto with IPPGrammar.
  - inv H. inv H1.
  - right. eexists. split; auto with IPPGrammar.
    insert_pre_pnode_destruct pr o t2 o0; auto with IPPGrammar. exfalso. apply H1 with x; auto.
Qed.

Lemma insert_pre_icfree {g} (pr : drules g) o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  i_conflict_free (i_conflict_pattern pr) (insert_pre pr o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply Prefix_cf; auto. intro. inv H1. inv H2. icp_cases H1; inv H3. inv H4.
  - insert_pre_inode_destruct pr o t21 o2 t22.
    + inv H0. apply Infix_cf; auto. intro. inv H0. inv H1. icp_cases H0; inv H2.
      * inv H12. destruct H4. eexists. eauto with IPPGrammar.
      * decompose [or] (insert_pre_top pr o t21).
        **inv H7. rewrite <- H2 in *. inv H1.
        **inv H2. inv H1. inv H7. rewrite <- H1 in *. inv H3. destruct H4. eexists. eauto with IPPGrammar.
        **inv H2. inv H1. inv H7. rewrite <- H1 in *. inv H3.
    + inv H0. apply Infix_cf; auto. intro. inv H0. inv H1. inv E2. inv H1. inv H7. inv H1. icp_cases H0; inv H2.
      * destruct H4. eexists. eauto with IPPGrammar.
      * apply insert_pre_top_unchanged with pr o t21 x0 in H11; auto. destruct H11.
        **inv H1. inv H2. inv H8. rewrite <- H2 in *. inv H7. destruct H4. eexists. eauto with IPPGrammar.
        **inv H1. inv H2. inv H8. rewrite <- H2 in *. inv H7.
    + apply Prefix_cf; auto. intro. inv H2. inv H3. icp_cases H2; inv H4. inv H5. contradiction.
  - simpl. apply Prefix_cf; auto. intro. inv H1. inv H2. icp_cases H1; inv H3. inv H4.
  - insert_pre_pnode_destruct pr o t21 o2.
    + inv H0. apply Postfix_cf; auto. inv E. inv H0. intro. inv H0. inv H5. icp_cases H0; inv H6. inv H7. inv H2.
      * inv H6. decompose [or] (insert_pre_top pr o t21); rewrite <- H5 in *.
        ** inv H2.
        ** inv H6. inv H2. inv H8. destruct H3. eexists. eauto with IPPGrammar.
        ** inv H6. inv H2. inv H8.
      * apply insert_pre_top_unchanged with pr o t21 x in H10; auto.
        destruct H10; rewrite <- H5 in *.
        ** inv H2. inv H6. inv H7. destruct H3. eexists. eauto with IPPGrammar.
        ** inv H2. inv H6. inv H7.
    + apply Prefix_cf; auto.
      intro. inv H2. inv H3. icp_cases H2; inv H4. inv H5.
Qed.

Lemma repair_in_icfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t1 ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  i_conflict_free (i_conflict_pattern pr) (repair_in pr t1 o t2).
Proof.
  intro. revert o t2. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1]; intros; simpl.
  - apply insert_in_icfree; auto with IPPGrammar. intros. intro. inv H3.
  - inv H0. auto.
  - inv H0. apply insert_pre_icfree; auto.
  - apply insert_in_icfree; auto with IPPGrammar. intros. intro. inv H3. 
Qed.

Lemma insert_post_top {g} (pr : drules g) t1 o :
  matches (insert_post pr t1 o) (PostfixPatt HPatt o) \/
  (exists o1, matches t1 (InfixPatt HPatt o1 HPatt) /\ matches (insert_post pr t1 o) (InfixPatt HPatt o1 HPatt)) \/
  (exists o1, matches t1 (PrefixPatt o1 HPatt) /\ matches (insert_post pr t1 o) (PrefixPatt o1 HPatt)).
Proof.
  destruct t1; eauto with IPPGrammar.
  - insert_post_inode_destruct pr t1_1 o0 t1_2 o; eauto 7 with IPPGrammar.
  - insert_post_pnode_destruct pr o0 t1 o; eauto 7 with IPPGrammar.
Qed.

Lemma insert_post_top_unchanged {g} (pr : drules g) t1 o x :
  matches_rm t1 (PrefixPatt x HPatt) ->
  rm_conflict_pattern pr (CL_postfix_prefix o x) ->
  (exists o1, matches t1 (InfixPatt HPatt o1 HPatt) /\ matches (insert_post pr t1 o) (InfixPatt HPatt o1 HPatt)) \/
  (exists o1, matches t1 (PrefixPatt o1 HPatt) /\ matches (insert_post pr t1 o) (PrefixPatt o1 HPatt)).
Proof.
  intros. destruct t1.
  - inv H. inv H1.
  - inv H. inv H1. left.
    eexists. split; auto with IPPGrammar.
    insert_post_inode_destruct pr t1_1 o0 t1_2 o; auto with IPPGrammar. exfalso. apply H with x; auto with IPPGrammar.
  - right. eexists. split; auto with IPPGrammar.
    insert_post_pnode_destruct pr o0 t1 o; auto with IPPGrammar. exfalso. apply H1 with x; auto.
  - inv H. inv H1.
Qed.

Lemma insert_post_icfree {g} (pr : drules g) t1 o :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t1 ->
  i_conflict_free (i_conflict_pattern pr) (insert_post pr t1 o).
Proof.
  intros. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1].
  - simpl. apply Postfix_cf; auto. intro. inv H1. inv H2. icp_cases H1; inv H3. inv H4.
  - insert_post_inode_destruct pr t11 o1 t12 o.
    + inv H0. apply Infix_cf; auto. intro. inv H0. inv H1. icp_cases H0; inv H2.
      * decompose [or] (insert_post_top pr t12 o).
        **inv H12. rewrite <- H2 in *. inv H1.
        **inv H2. inv H1. inv H12. rewrite <- H1 in *. inv H3. destruct H4. eexists. eauto with IPPGrammar.
        **inv H2. inv H1. inv H12. rewrite <- H1 in *. inv H3.
      * inv H12. destruct H4. eexists. eauto with IPPGrammar.
    + inv H0. apply Infix_cf; auto. intro. inv H0. inv H1. inv E2. inv H1. inv H7. inv H1. icp_cases H0; inv H2.
      * apply insert_post_top_unchanged with pr t12 o x0 in H11; auto. destruct H11.
        **inv H1. inv H2. inv H7. rewrite <- H2 in *. inv H14. destruct H4. eexists. eauto with IPPGrammar.
        **inv H1. inv H2. inv H7. rewrite <- H2 in *. inv H14.
      * destruct H4. eexists. eauto with IPPGrammar.
    + apply Postfix_cf; auto. intro. inv H2. inv H3. icp_cases H2; inv H4. inv H5. contradiction.
  - insert_post_pnode_destruct pr o1 t12 o.
    + inv H0. apply Prefix_cf; auto. inv E. inv H0. intro. inv H0. inv H5. icp_cases H0; inv H6. inv H7. inv H2.
      * inv H6. decompose [or] (insert_post_top pr t12 o); rewrite <- H5 in *.
        **inv H2.
        **inv H6. inv H2. inv H8. destruct H3. eexists. eauto with IPPGrammar.
        **inv H6. inv H2. inv H8.
      * apply insert_post_top_unchanged with pr t12 o x in H10; auto.
        destruct H10; rewrite <- H5 in *.
        **inv H2. inv H6. inv H7. destruct H3. eexists. eauto with IPPGrammar.
        **inv H2. inv H6. inv H7.
    + apply Postfix_cf; auto. intro. inv H2. inv H3. icp_cases H2; inv H4. inv H5.
  - simpl. apply Postfix_cf; auto. intro. inv H1. inv H2. icp_cases H1; inv H3. inv H4.
Qed.

Lemma repair_icfree {g} (pr : drules g) t :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) (repair pr t).
Proof.
  intro. induction t; simpl; auto using repair_in_icfree, insert_pre_icfree, insert_post_icfree with IPPGrammar.
Qed.


(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Proving safety of deep rm conflict patterns. *)

Lemma insert_in_matches_rm {g} (pr : drules g) t1 o1 t2 o2 :
  matches_rm (insert_in pr t1 o1 t2) (PrefixPatt o2 HPatt) ->
  matches_rm t2 (PrefixPatt o2 HPatt).
Proof.
  intros. destruct t2.
  - simpl in H. inv H. inv H0. inv H4. inv H.
  - insert_in_inode_destruct pr o1 t2_1 o t2_2.
    + inv H. inv H0. auto with IPPGrammar.
    + inv H. inv H0. auto with IPPGrammar.
    + inv H. inv H1. assumption.
  - simpl in H. inv H. inv H0. assumption.
  - insert_in_pnode_destruct pr o1 t2 o.
    + inv H. inv H0.
    + inv H. inv H1. inv H5. inv H.
Qed.

Lemma insert_in_drmcfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t1 ->
  drm_conflict_free (rm_conflict_pattern pr) t2 ->
  (forall x, rm_conflict_pattern pr (CL_infix_prefix o x) -> ~ matches_rm t1 (PrefixPatt x HPatt)) ->
  drm_conflict_free (rm_conflict_pattern pr) (insert_in pr t1 o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply Infix_drmcf; auto. intro. inv H3. inv H4. rcp_cases H3; inv H5. eapply H2; eauto.
  - insert_in_inode_destruct pr o t21 o2 t22.
    + inv H1. apply Infix_drmcf; auto. intro. inv H1. inv H3. rcp_cases H1; inv H4.
      destruct H6. eexists. eauto using insert_in_matches_rm with IPPGrammar.
    + inv H1. apply Infix_drmcf; auto. intro. inv H1. inv H3. rcp_cases H1; inv H4.
      destruct H6. eexists. eauto using insert_in_matches_rm with IPPGrammar.
    + apply Infix_drmcf; auto with IPPGrammar. intro. inv H4. inv H5. rcp_cases H4; inv H6. eapply H2; eauto.
  - simpl. apply Infix_drmcf; auto with IPPGrammar. intro. inv H3. inv H4. rcp_cases H3; inv H5. eapply H2; eauto.
  - insert_in_pnode_destruct pr o t21 o2.
    + inv H1. apply Postfix_drmcf; auto. intro. inv H1. inv H3. rcp_cases H1; inv H4.
      destruct H5. eexists. eauto using insert_in_matches_rm with IPPGrammar.
    + apply Infix_drmcf; auto with IPPGrammar. intro. inv H4. inv H5. rcp_cases H4; inv H6. eapply H2; eauto.
Qed.

Lemma prefixnode_single_drmcfree {g} (pr : drules g) o l2 :
  drm_conflict_free (rm_conflict_pattern pr) (PrefixNode o (AtomicNode l2)).
Proof.
  apply Prefix_drmcf; auto using Atomic_drmcf. intro. destruct H as [q]. inv H. rcp_cases H0; inv H1.
Qed.

Lemma insert_pre_matches_rm {g} (pr : drules g) o t2 o2 :
  matches_rm (insert_pre pr o t2) (PrefixPatt o2 HPatt) ->
  matches_rm t2 (PrefixPatt o2 HPatt) \/ o2 = o.
Proof.
  intros. destruct t2.
  - simpl in H. inv H.
    + inv H0. auto.
    + inv H3. inv H.
  - insert_pre_inode_destruct pr o t2_1 o0 t2_2.
    + inv H. inv H0. left. auto with IPPGrammar.
    + inv H. inv H0. left. auto with IPPGrammar.
    + inv H; auto. inv H1. auto.
  - inv H; auto. inv H0. auto.
  - insert_pre_pnode_destruct pr o t2 o0.
    + inv H. inv H0.
    + inv H; auto. inv H1. auto.
Qed.

Lemma insert_pre_drmcfree {g} (pr : drules g) o t2 :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t2 ->
  drm_conflict_free (rm_conflict_pattern pr) (insert_pre pr o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply prefixnode_single_drmcfree.
  - insert_pre_inode_destruct pr o t21 o2 t22.
    + inv H0. apply Infix_drmcf; auto. intro. inv H0. inv H1. rcp_cases H0; inv H2.
      apply insert_pre_matches_rm in H7. inv H7.
      * destruct H4. eexists. eauto with IPPGrammar.
      * eapply safe_infix_prefix; eauto using CPrio_infix_prefix.
    + inv H0. apply Infix_drmcf; auto. intro. inv H0. inv H1. rcp_cases H0; inv H2. inv E2. inv H1. inv H3. inv H1.
      destruct t21.
      **inv H11. inv H1.
      **inv H11. inv H1. rename E into E'. insert_pre_inode_destruct pr o t21_1 o0 t21_2.
        ***inv H7. inv H1. destruct H4. eexists. eauto with IPPGrammar.
        ***inv H7. inv H1. destruct H4. eexists. eauto with IPPGrammar.
        ***eapply H1; eauto with IPPGrammar.
      **inv H11. inv H1.
      **rename E into E'. insert_pre_pnode_destruct pr o t21 o0.
        ***inv H7. inv H1.
        ***eapply H1; eauto.
    + apply Prefix_drmcf; auto. intro. inv H2. inv H3. rcp_cases H2; inv H4.
  - simpl. apply Prefix_drmcf; auto. intro. inv H1. inv H2. rcp_cases H1; inv H3.
  - insert_pre_pnode_destruct pr o t21 o2.
    + inv H0. apply Postfix_drmcf; auto. intro. inv H0. inv H1. rcp_cases H0; inv H2. inv E. inv H1. inv H6.
      * inv H1. destruct t21.
        **simpl in H5. inv H5.
          ***inv H1. eauto using safe_prefix_postfix.
          ***inv H9. inv H1.
        **insert_pre_inode_destruct pr o t21_1 o0 t21_2.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5.
            ****inv H6. eauto using safe_prefix_postfix.
            ****inv H10. inv H5. destruct H3. eexists. eauto with IPPGrammar.
        **simpl in H5. inv H5.
          ***inv H1. eauto using safe_prefix_postfix.
          ***destruct H3. eexists. eauto with IPPGrammar.
        **insert_pre_pnode_destruct pr o t21 o0.
          ***inv H5. inv H1.
          ***inv H5.
            ****inv H6. eauto using safe_prefix_postfix.
            ****inv H10. inv H5.
      * destruct t21.
        **inv H9. inv H1.
        **inv H9. inv H1. insert_pre_inode_destruct pr o t21_1 o0 t21_2.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5.
            ****inv H6. eapply H1; eauto with IPPGrammar.
            ****inv H9. inv H5. destruct H3. eexists. eauto with IPPGrammar.
        **inv H9. inv H1.
        **insert_pre_pnode_destruct pr o t21 o0.
          ***inv H5. inv H1.
          ***eapply H1; eauto.
    + apply Prefix_drmcf; auto. intro. inv H2. inv H3. rcp_cases H2; inv H4.
Qed.

Lemma postfixnode_single_drmcfree {g} (pr : drules g) o l1 :
  drm_conflict_free (rm_conflict_pattern pr) (PostfixNode (AtomicNode l1) o).
Proof.
  apply Postfix_drmcf; auto using Atomic_drmcf. intro. destruct H as [q]. inv H. rcp_cases H0; inv H1. inv H2. inv H.
Qed.

Lemma insert_post_drmcfree {g} (pr : drules g) t1 o :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t1 ->
  drm_conflict_free (rm_conflict_pattern pr) (insert_post pr t1 o).
Proof.
  intros. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1].
  - simpl. apply Postfix_drmcf; auto. intro. inv H1. inv H2. rcp_cases H1; inv H3. inv H4. inv H2.
  - insert_post_inode_destruct pr t11 o1 t12 o.
    + inv H0. apply Infix_drmcf; auto. intro. inv H0. inv H1. rcp_cases H0; inv H2.
      destruct H4. eexists. eauto with IPPGrammar.
    + inv H0. apply Infix_drmcf; auto. intro. inv H0. inv H1. rcp_cases H0; inv H2.
      destruct H4. eexists. eauto with IPPGrammar.
    + apply Postfix_drmcf; auto. intro. inv H2. inv H3. rcp_cases H2; inv H4. inv H5. inv H3.
      eapply H1; eauto with IPPGrammar.
  - insert_post_pnode_destruct pr o1 t12 o.
    + inv H0. apply Prefix_drmcf; auto. intro. inv H0. inv H1. rcp_cases H0; inv H2.
    + apply Postfix_drmcf; auto. intro. inv H2. inv H3. rcp_cases H2; inv H4. eapply H1; eauto.
  - simpl. apply Postfix_drmcf; auto. intro. inv H1. inv H2. rcp_cases H1; inv H3. inv H4. inv H2.
Qed.

Lemma repair_in_drmcfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t1 ->
  drm_conflict_free (rm_conflict_pattern pr) t2 ->
  drm_conflict_free (rm_conflict_pattern pr) (repair_in pr t1 o t2).
Proof.
  intro. revert o t2. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1]; intros; simpl.
  - apply insert_in_drmcfree; auto with IPPGrammar. intros. intro. inv H3. inv H4.
  - inv H0. auto.
  - inv H0. apply insert_pre_drmcfree; auto.
  - apply insert_in_drmcfree; auto with IPPGrammar. intros. intro. inv H3. inv H4. 
Qed.

Lemma repair_drmcfree {g} (pr : drules g) t :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) (repair pr t).
Proof.
  intro. induction t; simpl; auto using repair_in_drmcfree, insert_pre_drmcfree, insert_post_drmcfree with IPPGrammar.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Proving safety of deep lm conflict patterns. *)

Lemma insert_in_dlmcfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  dlm_conflict_free (lm_conflict_pattern pr) t1 ->
  dlm_conflict_free (lm_conflict_pattern pr) t2 ->
  dlm_conflict_free (lm_conflict_pattern pr) (insert_in pr t1 o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply Infix_dlmcf; auto. intro. inv H2. inv H3. lcp_cases H2; inv H4. inv H11. inv H3.
  - insert_in_inode_destruct pr o t21 o2 t22.
    + inv H1. apply Infix_dlmcf; auto. intro. inv H1. inv H2. lcp_cases H1; inv H3.
      destruct H5. eexists. eauto with IPPGrammar.
    + inv H1. apply Infix_dlmcf; auto. intro. inv H1. inv H2. lcp_cases H1; inv H3.
      destruct H5. eexists. eauto with IPPGrammar.
    + apply Infix_dlmcf; auto. intro. inv H3. inv H4. lcp_cases H3; inv H5. inv H12. inv H4.
      eapply H2; eauto with IPPGrammar.
  - simpl. apply Infix_dlmcf; auto with IPPGrammar. intro. inv H2. inv H3. lcp_cases H2; inv H4. inv H11. inv H3.
  - insert_in_pnode_destruct pr o t21 o2.
    + inv H1. apply Postfix_dlmcf; auto. intro. inv H1. inv H2. lcp_cases H1; inv H3.
    + apply Infix_dlmcf; auto with IPPGrammar. intro. inv H3. inv H4. lcp_cases H3; inv H5. eapply H2; eauto.
Qed.

Lemma insert_pre_dlmcfree {g} (pr : drules g) o t2 :
  safe_pr pr ->
  dlm_conflict_free (lm_conflict_pattern pr) t2 ->
  dlm_conflict_free (lm_conflict_pattern pr) (insert_pre pr o t2).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - simpl. apply Prefix_dlmcf; auto. intro. inv H1. inv H2. lcp_cases H1; inv H3. inv H4. inv H2.
  - insert_pre_inode_destruct pr o t21 o2 t22.
    + inv H0. apply Infix_dlmcf; auto. intro. inv H0. inv H1. lcp_cases H0; inv H2.
      destruct H4. eexists. eauto with IPPGrammar.
    + inv H0. apply Infix_dlmcf; auto. intro. inv H0. inv H1. lcp_cases H0; inv H2.
      destruct H4. eexists. eauto with IPPGrammar.
    + apply Prefix_dlmcf; auto. intro. inv H2. inv H3. lcp_cases H2; inv H4. inv H5. inv H3.
      eapply H1; eauto with IPPGrammar.
  - simpl. apply Prefix_dlmcf; auto. intro. inv H1. inv H2. lcp_cases H1; inv H3. inv H4. inv H2.
  - insert_pre_pnode_destruct pr o t21 o2.
    + inv H0. apply Postfix_dlmcf; auto. intro. inv H0. inv H1. lcp_cases H0; inv H2.
    + apply Prefix_dlmcf; auto with IPPGrammar. intro. inv H2. inv H3. lcp_cases H2; inv H4. eapply H1; eauto.
Qed.

Lemma postfixnode_single_dlmcfree {g} (pr : drules g) o l1 :
  dlm_conflict_free (lm_conflict_pattern pr) (PostfixNode (AtomicNode l1) o).
Proof.
  apply Postfix_dlmcf; auto with IPPGrammar. intro. destruct H as [q]. inv H. lcp_cases H0; inv H1.
Qed.

Lemma insert_post_matches_lm {g} (pr : drules g) o t1 o1 :
  matches_lm (insert_post pr t1 o) (PostfixPatt HPatt o1) ->
  matches_lm t1 (PostfixPatt HPatt o1) \/ o1 = o.
Proof.
  intros. destruct t1.
  - simpl in H. inv H.
    + inv H0. auto.
    + inv H3. inv H.
  - insert_post_inode_destruct pr t1_1 o0 t1_2 o.
    + inv H. inv H0. left. auto with IPPGrammar.
    + inv H. inv H0. left. auto with IPPGrammar.
    + inv H; auto. inv H1. auto.
  - insert_post_pnode_destruct pr o0 t1 o.
    + inv H. inv H0.
    + inv H; auto. inv H1; auto.
  - inv H; auto. inv H0. auto.
Qed.

Lemma insert_post_dlmcfree {g} (pr : drules g) t1 o :
  safe_pr pr ->
  dlm_conflict_free (lm_conflict_pattern pr) t1 ->
  dlm_conflict_free (lm_conflict_pattern pr) (insert_post pr t1 o).
Proof.
  intros. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1].
  - simpl. apply postfixnode_single_dlmcfree.
  - insert_post_inode_destruct pr t11 o1 t12 o.
    + inv H0. apply Infix_dlmcf; auto. intro. inv H0. inv H1. lcp_cases H0; inv H2.
      apply insert_post_matches_lm in H12. inv H12.
      * destruct H4. eexists. eauto with IPPGrammar.
      * eauto using safe_infix_postfix.
    + inv H0. apply Infix_dlmcf; auto. intro. inv H0. inv H1. lcp_cases H0; inv H2. inv E2. inv H1. inv H3. inv H1.
      destruct t12.
      **inv H11. inv H1.
      **inv H11. inv H1. rename E into E'. insert_post_inode_destruct pr t12_1 o0 t12_2 o.
        ***inv H12. inv H1. destruct H4. eexists. eauto with IPPGrammar.
        ***inv H12. inv H1. destruct H4. eexists. eauto with IPPGrammar.
        ***eapply H1; eauto with IPPGrammar.
      **rename E into E'. insert_post_pnode_destruct pr o0 t12 o.
        ***inv H12. inv H1.
        ***eapply H1; eauto.
      **inv H11. inv H1.
    + apply Postfix_dlmcf; auto. intro. inv H2. inv H3. lcp_cases H2; inv H4.
  - insert_post_pnode_destruct pr o1 t12 o.
    + inv H0. apply Prefix_dlmcf; auto. intro. inv H0. inv H1. lcp_cases H0; inv H2. inv E. inv H1. inv H6.
      * inv H1. destruct t12.
        **simpl in H5. inv H5.
          ***inv H1. eauto using safe_prefix_postfix.
          ***inv H9. inv H1.
        **insert_post_inode_destruct pr t12_1 o0 t12_2 o.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5.
            ****inv H6. eauto using safe_prefix_postfix.
            ****inv H10. inv H5. destruct H3. eexists. eauto with IPPGrammar.
        **insert_post_pnode_destruct pr o0 t12 o.
          ***inv H5. inv H1.
          ***inv H5.
            ****inv H6. eauto using safe_prefix_postfix.
            ****inv H10. inv H5.
        **simpl in H5. inv H5.
          ***inv H1. eauto using safe_prefix_postfix.
          ***destruct H3. eexists. eauto with IPPGrammar.
      * destruct t12.
        **inv H9. inv H1.
        **inv H9. inv H1. insert_post_inode_destruct pr t12_1 o0 t12_2 o.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5. inv H1. destruct H3. eexists. eauto with IPPGrammar.
          ***inv H5.
            ****inv H6. eapply H1; eauto with IPPGrammar.
            ****inv H9. inv H5. destruct H3. eexists. eauto with IPPGrammar.
        **insert_post_pnode_destruct pr o0 t12 o.
          ***inv H5. inv H1.
          ***eapply H1; eauto.
        **inv H9. inv H1.
    + apply Postfix_dlmcf; auto. intro. inv H2. inv H3. lcp_cases H2; inv H4.
  - simpl. apply Postfix_dlmcf; auto. intro. inv H1. inv H2. lcp_cases H1; inv H3.
Qed.

Lemma repair_in_dlmcfree {g} (pr : drules g) t1 o t2 :
  safe_pr pr ->
  dlm_conflict_free (lm_conflict_pattern pr) t1 ->
  dlm_conflict_free (lm_conflict_pattern pr) t2 ->
  dlm_conflict_free (lm_conflict_pattern pr) (repair_in pr t1 o t2).
Proof.
  intro. revert o t2. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1]; intros; simpl.
  - apply insert_in_dlmcfree; auto with IPPGrammar.
  - inv H0. auto.
  - inv H0. apply insert_pre_dlmcfree; auto.
  - apply insert_in_dlmcfree; auto with IPPGrammar. 
Qed.

Lemma repair_dlmcfree {g} (pr : drules g) t :
  safe_pr pr ->
  dlm_conflict_free (lm_conflict_pattern pr) (repair pr t).
Proof.
  intro. induction t; simpl; auto using repair_in_dlmcfree, insert_pre_dlmcfree, insert_post_dlmcfree with IPPGrammar.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* SAFETY *)

Theorem safety {g} (pr : drules g) :
  safe_pr pr -> safe pr.
Proof.
  unfold safe. unfold language. unfold dlanguage. unfold cfree. unfold conflict_free.
  intros. destruct H0 as [t]. destruct H0.
  exists (repair pr t).
  erewrite repair_yield_preserve; eauto.
  eauto 10 using repair_wf, repair_yield_preserve, repair_icfree, repair_drmcfree, repair_dlmcfree.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas relate completeness to relations between conflict patterns. *)

Lemma complete_trans_1 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o3) ->
  i_conflict_pattern pr (CL_infix_infix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_trans_2 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  rm_conflict_pattern pr (CL_infix_prefix o2 o3) ->
  rm_conflict_pattern pr (CL_infix_prefix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_trans_3 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_prefix_infix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_trans_4 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CR_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o3) ->
  i_conflict_pattern pr (CR_infix_infix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_trans_5 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CL_postfix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o3) ->
  i_conflict_pattern pr (CL_postfix_infix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_trans_6 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CL_postfix_infix o1 o2) ->
  rm_conflict_pattern pr (CL_infix_prefix o2 o3) ->
  rm_conflict_pattern pr (CL_postfix_prefix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_trans_7 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CR_infix_infix o1 o2) ->
  lm_conflict_pattern pr (CR_infix_postfix o2 o3) ->
  lm_conflict_pattern pr (CR_infix_postfix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_trans_8 {g} (pr : drules g) o1 o2 o3 :
  complete_pr pr ->
  i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
  lm_conflict_pattern pr (CR_infix_postfix o2 o3) ->
  lm_conflict_pattern pr (CR_prefix_postfix o1 o3).
Proof.
  intros. destruct H. inv H0; inv H1; eauto with IPPGrammar.
Qed.

Lemma complete_neg_1 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ i_conflict_pattern pr (CR_infix_infix o1 o2) ->
  i_conflict_pattern pr (CL_infix_infix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (InfixProd o1) (InfixProd o2).
  decompose [or] complete_1; auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
Qed.

Lemma complete_neg_2 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ rm_conflict_pattern pr (CL_infix_prefix o1 o2) ->
  i_conflict_pattern pr (CR_prefix_infix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (PrefixProd o2) (InfixProd o1) .
  decompose [or] complete_1; auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
Qed.

Lemma complete_neg_3 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ i_conflict_pattern pr (CL_infix_infix o1 o2) ->
  i_conflict_pattern pr (CR_infix_infix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (InfixProd o2) (InfixProd o1).
  decompose [or] complete_1; auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
Qed.

Lemma complete_neg_4 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ i_conflict_pattern pr (CL_postfix_infix o1 o2) ->
  lm_conflict_pattern pr (CR_infix_postfix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (InfixProd o2) (PostfixProd o1).
  decompose [or] complete_1; auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
Qed.

Lemma complete_neg_5 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ rm_conflict_pattern pr (CL_postfix_prefix o1 o2) ->
  lm_conflict_pattern pr (CR_prefix_postfix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (PrefixProd o2) (PostfixProd o1).
  decompose [or] complete_1; auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
Qed.

Lemma complete_neg_6 {g} (pr : drules g) o1 o2 :
  complete_pr pr ->
  ~ i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
  rm_conflict_pattern pr (CL_infix_prefix o2 o1).
Proof.
  intros. destruct H.
  specialize complete_1 with (PrefixProd o1) (InfixProd o2).
  decompose [or] complete_1; auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
  - destruct H0. auto with IPPGrammar.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Lemmas showing [repair t] = t if [t] is conflict free *)

Lemma insert_in_complete {g} (pr : drules g) t1 o t2 :
  complete_pr pr ->
  cfree pr (InfixNode t1 o t2) ->
  insert_in pr t1 o t2 = InfixNode t1 o t2.
Proof.
  intros. inv H0. inv H2. destruct t2; auto.
  - insert_in_inode_destruct pr o t2_1 o0 t2_2; auto.
    + inv H1. destruct H6. eexists. eauto with IPPGrammar.
    + inv E2. inv H2. inv H3. destruct H8. eexists. eauto with IPPGrammar.
  - insert_in_pnode_destruct pr o t2 o0; auto. inv E. inv H2. inv H3. destruct H8. eexists. eauto with IPPGrammar.
Qed.

Lemma insert_in_matches_lm {g} (pr : drules g) t1 o t2 x :
  lm_conflict_pattern pr (CR_infix_postfix o x) ->
  matches_lm t2 (PostfixPatt HPatt x) ->
  matches_lm (insert_in pr t1 o t2) (PostfixPatt HPatt x).
Proof.
  intros. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - inv H0. inv H1.
  - inv H0. inv H1. insert_in_inode_destruct pr o t21 o2 t22.
    + auto with IPPGrammar.
    + inv E2. inv H0. inv H2. inv H0. auto with IPPGrammar.
    + edestruct H0; eauto with IPPGrammar.
  - inv H0. inv H1.
  - insert_in_pnode_destruct pr o t21 o2.
    + inv H0.
      * inv H1. auto with IPPGrammar.
      * auto with IPPGrammar.
    + edestruct H1; eauto with IPPGrammar.
Qed.

Lemma insert_in_assoc {g} (pr : drules g) t11 o1 t12 o t2 :
  complete_pr pr ->
  cfree pr (InfixNode t11 o1 t12) ->
  ~ i_conflict_pattern pr (CL_infix_infix o o1) ->
  insert_in pr t11 o1 (insert_in pr t12 o t2) = insert_in pr (InfixNode t11 o1 t12) o t2.
Proof.
  intros. assert (H0' := H0). inv H0'. inv H3.
  induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - assert (insert_in pr t12 o (AtomicNode l2) = InfixNode t12 o (AtomicNode l2)); auto. rewrite H3.
    insert_in_inode_destruct pr o1 t12 o (AtomicNode l2).
    + rewrite insert_in_complete; auto.
    + rewrite insert_in_complete; auto.
    + exfalso. destruct H1. auto using complete_neg_1.
  - insert_in_inode_destruct pr o t21 o2 t22.
    + rewrite <- IHt2_1. rename E into E'. insert_in_inode_destruct pr o1 (insert_in pr t12 o t21) o2 t22; auto.
      destruct E. apply complete_trans_4 with o; auto. auto using complete_neg_3.
    + rewrite <- IHt2_1. rename E into E'. rename E2 into E2'.
      insert_in_inode_destruct pr o1 (insert_in pr t12 o t21) o2 t22; auto. exfalso. inv E2'. inv H6. inv H8.
      inv H6. apply insert_in_matches_lm with pr t12 o t21 x in H12; auto. edestruct H3; eauto with IPPGrammar.
      apply complete_trans_7 with o; auto. auto using complete_neg_3.
    + rename E into E'. rename E2 into E2'. insert_in_inode_destruct pr o1 t12 o (InfixNode t21 o2 t22).
      * rewrite insert_in_complete; auto.
      * destruct H1. auto using complete_neg_1.
      * destruct H1. auto using complete_neg_1.
  - insert_in_inode_destruct pr o1 t12 o (PrefixNode o2 t22).
    + rewrite insert_in_complete; auto.
    + rewrite insert_in_complete; auto.
    + destruct H1. auto using complete_neg_1.
  - insert_in_pnode_destruct pr o t21 o2.
    + rewrite <- IHt2. rename E into E'. insert_in_pnode_destruct pr o1 (insert_in pr t12 o t21) o2; auto.
      exfalso. inv E'. inv H6. inv H8.
      * inv H6. edestruct H3; eauto with IPPGrammar. apply complete_trans_7 with o; auto. auto using complete_neg_3.
      * apply insert_in_matches_lm with pr t12 o t21 x in H11; auto. edestruct H3; eauto with IPPGrammar.
        apply complete_trans_7 with o; auto. auto using complete_neg_3.
    + rename E into E'. insert_in_inode_destruct pr o1 t12 o (PostfixNode t21 o2).
      * rewrite insert_in_complete; auto.
      * destruct H1. auto using complete_neg_1.
      * destruct H1. auto using complete_neg_1.
Qed.

Lemma insert_pre_complete {g} (pr : drules g) o t2 :
  cfree pr (PrefixNode o t2) ->
  insert_pre pr o t2 = PrefixNode o t2.
Proof.
  intro. inv H. inv H1. destruct t2 as [l2|t21 o2 t22|o2 t22|t21 o2]; auto.
  - insert_pre_inode_destruct pr o t21 o2 t22; auto.
    + inv H0. destruct H4. eexists. eauto with IPPGrammar.
    + inv E2. inv H1. inv H4. inv H1. inv H2. destruct H5. eexists. eauto with IPPGrammar.
  - insert_pre_pnode_destruct pr o t21 o2; auto. inv E. inv H1. inv H2. destruct H6. eexists. eauto with IPPGrammar.
Qed.

Lemma insert_in_prefix {g} (pr : drules g) o1 t12 o t2 :
  complete_pr pr ->
  cfree pr (PrefixNode o1 t12) ->
  ~ rm_conflict_pattern pr (CL_infix_prefix o o1) ->
  insert_in pr (PrefixNode o1 t12) o t2 = insert_pre pr o1 (insert_in pr t12 o t2).
Proof.
  intros. assert (H0' := H0). inv H0'. inv H3. induction t2 as [l2|t21 ? o2 t22|o2 t22|t21 ? o2].
  - cbn [insert_in]. insert_pre_inode_destruct pr o1 t12 o (AtomicNode l2).
    + rewrite insert_pre_complete; auto.
    + rewrite insert_pre_complete; auto.
    + destruct E. auto using complete_neg_2.
  - insert_in_inode_destruct pr o t21 o2 t22.
    + rewrite IHt2_1. rename E into E'. insert_pre_inode_destruct pr o1 (insert_in pr t12 o t21) o2 t22; auto.
      destruct E. apply complete_trans_3 with o; auto. auto using complete_neg_2.
    + rewrite IHt2_1. rename E into E', E2 into E2'.
      insert_pre_inode_destruct pr o1 (insert_in pr t12 o t21) o2 t22; auto. exfalso. inv E2'. inv H6. inv H8. inv H6.
      apply insert_in_matches_lm with pr t12 o t21 x in H12; auto. edestruct H3; eauto with IPPGrammar.
      apply complete_trans_8 with o; auto. auto using complete_neg_2.
    + rename E into E', E2 into E2'. insert_pre_inode_destruct pr o1 t12 o (InfixNode t21 o2 t22).
      * rewrite insert_pre_complete; auto.
      * rewrite insert_pre_complete; auto.
      * destruct E. auto using complete_neg_2.
  - cbn [insert_in]. insert_pre_inode_destruct pr o1 t12 o (PrefixNode o2 t22).
    + rewrite insert_pre_complete; auto.
    + rewrite insert_pre_complete; auto.
    + destruct E. auto using complete_neg_2.
  - insert_in_pnode_destruct pr o t21 o2.
    + rewrite IHt2. rename E into E'. insert_pre_pnode_destruct pr o1 (insert_in pr t12 o t21) o2; auto. exfalso.
      inv E'. inv H6. inv H8.
      * inv H6. edestruct H3; eauto with IPPGrammar. apply complete_trans_8 with o; auto. auto using complete_neg_2.
      * apply insert_in_matches_lm with pr t12 o t21 x in H11; auto. edestruct H3; eauto with IPPGrammar.
        apply complete_trans_8 with o; auto. auto using complete_neg_2.
    + rename E into E'. insert_pre_inode_destruct pr o1 t12 o (PostfixNode t21 o2).
      * rewrite insert_pre_complete; auto.
      * rewrite insert_pre_complete; auto.
      * destruct E. auto using complete_neg_2.
Qed.

Lemma repair_in_insert_in {g} (pr : drules g) t1 o t2 :
  complete_pr pr ->
  cfree pr t1 ->
  (forall x1, matches t1 (InfixPatt HPatt x1 HPatt) -> ~ i_conflict_pattern pr (CL_infix_infix o x1)) ->
  (forall x1, matches_rm t1 (PrefixPatt x1 HPatt) -> ~ rm_conflict_pattern pr (CL_infix_prefix o x1)) ->
  repair_in pr t1 o t2 = insert_in pr t1 o t2.
Proof.
  unfold cfree. unfold conflict_free. intro. intro.
  revert o t2. induction t1 as [l1|t11 ? o1 t12|o1 t12|t11 ? o1]; intros; simpl; auto.
  - rewrite IHt12.
    + rewrite IHt1_1.
      * rewrite insert_in_assoc; auto. apply H1. auto with IPPGrammar.
      * inv H0. inv H4. inv H3. inv H0. inv H5. auto.
      * intros. inv H3. rename x1 into o11, t1 into t111, t0 into t112. intro. inv H0. inv H4. destruct H10.
        eexists. eauto with IPPGrammar.
      * intros. intro. inv H0. inv H6. inv H0. destruct H10. eexists. eauto with IPPGrammar.
    + inv H0. inv H4. inv H3. inv H0. inv H5. auto.
    + intros. inv H3. rename x1 into o12, t1 into t121, t0 into t122. intro. apply H1 with o1; auto with IPPGrammar.
      apply complete_trans_1 with o12; auto. apply complete_neg_1; auto. intro. inv H0. inv H5. destruct H11. eexists.
      eauto with IPPGrammar.
    + intros. apply H2. auto with IPPGrammar.
  - rewrite IHt12.
    + rewrite insert_in_prefix; auto. apply H2. auto with IPPGrammar.
    + inv H0. inv H4. inv H3. inv H0. inv H5. auto.
    + intros. inv H3. rename x1 into o12, t1 into t121, t0 into t122. intro. apply H2 with o1; auto with IPPGrammar.
      apply complete_trans_2 with o12; auto. apply complete_neg_6; auto. intro. inv H0. inv H5. destruct H10. eexists.
      eauto with IPPGrammar.
    + intros. apply H2. auto with IPPGrammar.
Qed.

Lemma repair_in_complete {g} (pr : drules g) t1 o t2 :
  complete_pr pr ->
  cfree pr (InfixNode t1 o t2) ->
  repair_in pr t1 o t2 = InfixNode t1 o t2.
Proof.
  intros. assert (H0' := H0). inv H0. inv H2. inv H1. inv H0. inv H3. rewrite repair_in_insert_in; auto.
  - rewrite insert_in_complete; auto.
  - unfold cfree. unfold conflict_free. auto.
  - intros. intro. destruct H6. eexists. eauto with IPPGrammar.
  - intros. intro. destruct H5. eexists. eauto with IPPGrammar.
Qed.

Lemma insert_post_complete {g} (pr : drules g) t1 o :
  cfree pr (PostfixNode t1 o) ->
  insert_post pr t1 o = PostfixNode t1 o.
Proof.
  intro. inv H. inv H1. destruct t1 as [l1|t11 o1 t12|o1 t12|t11 o1]; auto.
  - insert_post_inode_destruct pr t11 o1 t12 o; auto.
    + inv H0. destruct H4. eexists. eauto with IPPGrammar.
    + inv E2. inv H1. inv H4. inv H1. inv H. destruct H5. eexists. eauto with IPPGrammar.
  - insert_post_pnode_destruct pr o1 t12 o; auto. inv E. inv H1. inv H. destruct H6. eexists. eauto with IPPGrammar.
Qed.

Lemma repair_complete {g} (pr : drules g) t :
  complete_pr pr ->
  cfree pr t ->
  repair pr t = t.
Proof.
  intro. induction t; simpl; auto; intros.
  - assert (H0' := H0). inv H0'. inv H2. inv H1. inv H3. inv H4. rewrite IHt1; try split; auto.
    rewrite IHt2; try split; auto. apply repair_in_complete; auto.
  - assert (H0' := H0). inv H0'. inv H2. inv H1. inv H3. inv H4. rewrite IHt; try split; auto.
    apply insert_pre_complete; auto.
  - assert (H0' := H0). inv H0'. inv H2. inv H1. inv H3. inv H4. rewrite IHt; try split; auto.
    apply insert_post_complete; auto.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* COMPLETENESS *)

Theorem completeness {g} (pr : drules g) :
  complete_pr pr ->
  complete pr.
Proof.
  intro. intro. intros.
  assert (repair_fully_yield_dependent: forall x y, yield x = yield y -> repair pr x = repair pr y). {
    admit. (* FUTURE WORK *)
  }
  apply repair_fully_yield_dependent in H0.
  rewrite repair_complete in H0; auto. rewrite repair_complete in H0; auto.
Admitted.

End IPPGrammarTheorems.
