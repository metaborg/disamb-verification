Require Import MyUtils.
Load IPPGrammar.

Section IPPGrammarTheorems.

Arguments InfixProd {_} _.
Arguments PrefixProd {_} _.

Arguments HPatt {_}.
Arguments InfixPatt {_} _ _ _.
Arguments PrefixPatt {_} _ _.

Arguments prio {_} _ _ _.
Arguments left_a {_} _ _ _.
Arguments right_a {_} _ _ _.

(* Existential Lemmas *)

Lemma dec_i_conflict_pattern {g} (pr : drules g) `{drules_dec pr} (q : tree_pattern g) :
  Decision (i_conflict_pattern pr q).
Proof.
  destruct drules_dec0.
  unfold Decision. destruct q.
  - right. intro. inv H.
  - destruct q1, q2.
    + right. intro. inv H.
    + destruct q2_1. destruct q2_2.
      * replace (InfixPatt HPatt o (InfixPatt HPatt o0 HPatt)) with (CR_infix_infix o o0); try reflexivity.
        specialize dec_prio0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        specialize dec_left_a0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        destruct dec_prio0, dec_left_a0; auto using CPrio_infix_infix_2, CLeft.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
    + destruct q1_1. destruct q1_2.
      * replace (InfixPatt (InfixPatt HPatt o0 HPatt) o HPatt) with (CL_infix_infix o o0); try reflexivity.
        specialize dec_prio0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        specialize dec_right_a0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        destruct dec_prio0, dec_right_a0; auto using CPrio_infix_infix_1, CRight.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
    + right. intro. inv H.
    + right. intro. inv H.
    + right. intro. inv H.
    + right. intro. inv H.
  - destruct q.
    + right. intro. inv H.
    + destruct q1, q2.
      * replace (PrefixPatt o (InfixPatt HPatt o0 HPatt)) with (CR_prefix_infix o o0); try reflexivity.
        specialize dec_prio0 with (p1 := PrefixProd o) (p2 := InfixProd o0).
        destruct dec_prio0; auto using CPrio_prefix_infix.
        right. intro. inv H. contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
Qed.

Lemma linsert_one_exists {g} (pr : drules g) `{drules_dec pr} l o t :
  exists t', linsert_one pr l o t t'.
Proof.
  induction t.
  - eauto using Atomic_LInsert_One.
  - assert (Decision (i_conflict_pattern pr (CR_infix_infix o o0))). {
      auto using dec_i_conflict_pattern.
    }
    destruct IHt1, IHt2.
    destruct H.
    + eauto using Infix_LInsert_One_2.
    + eauto using Infix_LInsert_One_1.
  - eauto using Prefix_LInsert_One.
Qed.

Lemma linsert_op_exists {g} (pr : drules g) `{drules_dec pr} o t :
  exists t', linsert_op pr o t t'.
Proof.
  induction t.
  - eauto using Atomic_LInsert_Op.
  - assert (Decision (i_conflict_pattern pr (CR_prefix_infix o o0))). {
      auto using dec_i_conflict_pattern.
    }
    destruct IHt1, IHt2.
    destruct H.
    + eauto using Infix_LInsert_Op_2.
    + eauto using Infix_LInsert_Op_1.
  - eauto using Prefix_LInsert_Op.
Qed.

Lemma linsert_exists {g} (pr : drules g) `{drules_dec pr} o t1 t2 :
  exists t', linsert pr t1 o t2 t'.
Proof.
  revert o t2. induction t1; intros.
  - assert (exists t', linsert_one pr l o t2 t'). {
      auto using linsert_one_exists.
    }
    destruct H. eauto using Atomic_LInsert.
  - specialize IHt1_2 with o0 t2. destruct IHt1_2.
    specialize IHt1_1 with o x. destruct IHt1_1.
    eauto using Infix_LInsert.
  - specialize IHt1 with o0 t2. destruct IHt1.
    assert (exists t', linsert_op pr o x t'). {
      auto using linsert_op_exists.
    }
    destruct H0.
    eauto using Prefix_LInsert.
Qed.

Lemma fix_tree_exists {g} (pr : drules g) `{drules_dec pr} t :
  exists t', fix_tree pr t t'.
Proof.
  induction t.
  - eauto using Atomic_fix.
  - destruct IHt2.
    assert (exists t', linsert pr t1 o x t'). {
      auto using linsert_exists.
    }
    destruct H0.
    eauto using Infix_fix.
  - destruct IHt.
    assert (exists t', linsert_op pr o x t'). {
      auto using linsert_op_exists.
    }
    destruct H0.
    eauto using Prefix_fix.
Qed.

(* Well-formedness Lemmas *)

Lemma linsert_one_wf {g} (pr : drules g) l o t t' :
  wf_parse_tree g t ->
  g.(prods) (InfixProd o) ->
  linsert_one pr l o t t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H1.
  - auto using Infix_wf, Atomic_wf.
  - auto using Infix_wf, Atomic_wf.
  - inv H. auto using Infix_wf.
  - auto using Infix_wf, Atomic_wf, Prefix_wf.
Qed.

Lemma linsert_op_wf {g} (pr : drules g) o1 t t' :
  wf_parse_tree g t ->
  g.(prods) (PrefixProd o1) ->
  linsert_op pr o1 t t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H1.
  - auto using Prefix_wf, Atomic_wf.
  - auto using Prefix_wf, Infix_wf.
  - inv H. auto using Infix_wf.
  - auto using Prefix_wf.
Qed.

Lemma linsert_wf {g} (pr : drules g) o t1 t2 t' :
  wf_parse_tree g t1 ->
  g.(prods) (InfixProd o) ->
  wf_parse_tree g t2 ->
  linsert pr t1 o t2 t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H2.
  - eauto using linsert_one_wf.
  - inv H. auto.
  - inv H. eauto using linsert_op_wf.
Qed.

Lemma fix_tree_wf {g} (pr : drules g) t t' :
  wf_parse_tree g t ->
  fix_tree pr t t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H0.
  - apply Atomic_wf.
  - inv H. eauto using linsert_wf.
  - inv H. eauto using linsert_op_wf.
Qed.

(* Yield Lemmas *)

Lemma linsert_one_yield {g} (pr : drules g) l1 o1 t t' :
  linsert_one pr l1 o1 t t' ->
  yield t' = inl l1 :: inr o1 :: yield t.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHlinsert_one. reflexivity.
Qed.

Lemma linsert_op_yield {g} (pr : drules g) o1 t t' :
  linsert_op pr o1 t t' ->
  yield t' = inr o1 :: yield t.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHlinsert_op. reflexivity.
Qed.

Lemma linsert_yield {g} (pr : drules g) o t1 t2 t' :
  linsert pr t1 o t2 t' ->
  yield t' = yield t1 ++ inr o :: yield t2.
Proof.
  intro. induction H; simpl; eauto using linsert_one_yield.
  - rewrite IHlinsert2. rewrite IHlinsert1.
    simplify_list_eq. reflexivity.
  - apply linsert_op_yield in H0.
    rewrite H0. rewrite IHlinsert.
    reflexivity.
Qed.

Lemma fix_tree_yield {g} (pr : drules g) t t' :
  fix_tree pr t t' ->
  yield t' = yield t.
Proof.
  intros. induction H; simpl.
  - reflexivity.
  - apply linsert_yield in H0. rewrite H0.
    rewrite IHfix_tree.
    reflexivity.
  - apply linsert_op_yield in H0. rewrite H0.
    rewrite IHfix_tree.
    reflexivity.
Qed.

(* pr safety lemmas *)

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

(* general insertion lemmas *)

Lemma linsert_one_match {g} (pr : drules g) l o1 t t' :
  linsert_one pr l o1 t t' ->
  matches t' (InfixPatt HPatt o1 HPatt) \/
  (exists o2, matches t (InfixPatt HPatt o2 HPatt) /\ matches t' (InfixPatt HPatt o2 HPatt)).
Proof.
  intros. inv H.
  - left. apply InfixMatch; apply HMatch.
  - left. apply InfixMatch; apply HMatch.
  - right. exists o2. split; apply InfixMatch; apply HMatch.
  - left. apply InfixMatch; apply HMatch.
Qed.

Lemma linsert_op_match {g} (pr : drules g) o1 t t' :
  linsert_op pr o1 t t' ->
  matches t' (PrefixPatt o1 HPatt) \/
  (exists o2, matches t (InfixPatt HPatt o2 HPatt) /\ matches t' (InfixPatt HPatt o2 HPatt)).
Proof.
  intros. inv H; auto using PrefixMatch, HMatch.
  right. exists o2. auto using InfixMatch, HMatch.
Qed. 

(* i-conflict-free lemmas *)

Lemma i_conflict_pattern_cases {O} (pr : drules O) (q : tree_pattern O) (P : Prop) :
  (forall o1 o2, q = CL_infix_infix o1 o2 -> P) ->
  (forall o1 o2, q = CR_infix_infix o1 o2 -> P) ->
  (forall o1 o2, q = CR_prefix_infix o1 o2 -> P) ->
  (i_conflict_pattern pr q -> P).
Proof.
  intros. inv H2; eauto.
Qed.

Lemma linsert_one_icfree {g} (pr : drules g) l1 o1 t t' :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t ->
  linsert_one pr l1 o1 t t' ->
  i_conflict_free (i_conflict_pattern pr) t'.
Proof.
  intro H_safe. intros. induction H0.
  - apply Infix_cf; auto using Atomic_cf.
    intro. inv H0. inv H1. inv H0; inv H2.
    inv H9. inv H4. inv H4. inv H9.
  - apply Infix_cf; auto using Atomic_cf.
    intro. destruct H0. destruct H1 as [q]. inv H0.
    inv H2. inv H1. inv H7; inv H6; inv H1.
    auto using CLeft. auto using CPrio_infix_infix_2.
  - inv H. apply Infix_cf; auto. clear H6 H7.
    intro. destruct H as [q]. inv H.
    eapply i_conflict_pattern_cases; try eassumption; intros; subst; inv H3.
    + apply linsert_one_match in H1. destruct H1.
      * inv H. inv H6. eauto using safe_infix_infix.
      * destruct H5.
        inv H. inv H1. inv H. inv H3. inv H6.
        exists (CL_infix_infix o0 o3). split; auto.
        unfold CL_infix_infix. auto using HMatch, InfixMatch.
    + inv H11. destruct H5.
      exists (CR_infix_infix o0 o3). split; auto.
      unfold CR_infix_infix. auto using HMatch, InfixMatch.
  - apply Infix_cf; auto using Atomic_cf.
    intro. destruct H0 as [q]. inv H0.
    inv H2. inv H1. inv H7; inv H6; inv H1.
Qed.

Lemma linsert_op_icfree {g} (pr : drules g) o1 t t' :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t ->
  linsert_op pr o1 t t' ->
  i_conflict_free (i_conflict_pattern pr) t'.
Proof.
  intro H_safe. intros. induction H0.
  - apply Prefix_cf; auto using Atomic_cf.
    intro. inv H0. inv H1. inv H0; inv H2.
    inv H3.
  - apply Prefix_cf; auto.
    intro. destruct H0.
    destruct H1 as [q]. inv H0. inv H1; inv H2.
    inv H3. auto using CPrio_prefix_infix.
  - inv H. apply Infix_cf; auto.
    intro. destruct H5. destruct H as [q]. inv H.
    eapply i_conflict_pattern_cases; try eassumption; intros; subst; inv H3.
    + apply linsert_op_match in H1. destruct H1.
      * inv H. inv H5.
      * inv H. inv H1. inv H. inv H5. inv H3.
        eexists. split. eassumption.
        unfold CL_infix_infix. auto using InfixMatch, HMatch.
    + inv H12.
      eexists. split. eassumption.
      unfold CR_infix_infix. auto using InfixMatch, HMatch.
  - apply Prefix_cf; auto.
    intro. inv H0. inv H1. inv H0; inv H2. inv H3.
Qed.

Lemma linsert_icfree {g} (pr : drules g) o t1 t2 t' :
  safe_pr pr ->
  i_conflict_free (i_conflict_pattern pr) t2 ->
  linsert pr t1 o t2 t' ->
  i_conflict_free (i_conflict_pattern pr) t'.
Proof.
  intros. induction H1; eauto using linsert_one_icfree, linsert_op_icfree.
Qed.

Lemma fix_tree_icfree {g} (pr : drules g) t t' :
  safe_pr pr ->
  fix_tree pr t t' ->
  i_conflict_free (i_conflict_pattern pr) t'.
Proof.
  intros. induction H0.
  - apply Atomic_cf.
  - eauto using linsert_icfree.
  - eauto using linsert_op_icfree.
Qed.

(* rm-conflict-free lemmas *)

Lemma matches_rm_hpatt {g} (t : parse_tree g) :
  matches_rm t HPatt.
Proof.
  apply Match_rm. apply HMatch.
Qed.

Lemma linsert_one_matches_rm {g} (pr : drules g) l1 o1 t o t' :
  linsert_one pr l1 o1 t t' ->
  matches_rm t' (PrefixPatt o HPatt) ->
  matches_rm t (PrefixPatt o HPatt).
Proof.
  intros. inv H.
  - inv H0. inv H. inv H4. inv H.
  - inv H0. inv H. assumption.
  - inv H0. inv H. auto using InfixMatch_rm.
  - inv H0. inv H. assumption.
Qed.

Lemma linsert_one_drmcfree {g} (pr : drules g) l1 o1 t t' :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t ->
  linsert_one pr l1 o1 t t' ->
  drm_conflict_free (rm_conflict_pattern pr) t'.
Proof.
  intros. induction H1.
  - apply Infix_drmcf; auto using Atomic_drmcf.
    intro. destruct H1 as [q].
    inv H1. inv H2. inv H3. inv H5. inv H2.
  - apply Infix_drmcf; auto using Atomic_drmcf.
    intro. destruct H2 as [q].
    inv H2. inv H3. inv H4. inv H6. inv H3.
  - inv H0. apply Infix_drmcf; auto.
    intro. destruct H0 as [q]. inv H0.
    destruct H6. exists q. split. assumption.
    inv H3. inv H4.
    apply InfixMatch_drm; eauto using matches_rm_hpatt, linsert_one_matches_rm.
  - apply Infix_drmcf; auto using Atomic_drmcf.
    intro. destruct H1 as [q]. inv H1.
    inv H2. inv H3. inv H5. inv H2.
Qed.

Lemma linsert_op_matches_rm {g} (pr : drules g) o1 t o t' :
  linsert_op pr o1 t t' ->
  matches_rm t' (PrefixPatt o HPatt) ->
  matches_rm t (PrefixPatt o HPatt) \/ o = o1.
Proof.
  intros. inv H.
  - inv H0.
    + inv H. auto.
    + inv H3. inv H.
  - inv H0; auto.
    inv H. auto.
  - inv H0. inv H.
    left. auto using InfixMatch_rm.
  - inv H0; auto.
    inv H. auto.
Qed.

Lemma linsert_op_drmcfree {g} (pr : drules g) o1 t t' :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t ->
  linsert_op pr o1 t t' ->
  drm_conflict_free (rm_conflict_pattern pr) t'.
Proof.
  intros. induction H1.
  - apply Prefix_drmcf; auto using Atomic_drmcf.
    intro. inv H1. inv H2. inv H3. inv H1.
  - apply Prefix_drmcf; auto.
    intro. inv H2. inv H3. inv H2. inv H4.
  - inv H0. apply Infix_drmcf; auto.
    intro. destruct H0 as [q]. inv H0. inv H3. inv H4.
    eapply linsert_op_matches_rm in H2; eauto.
    inv H2.
    + destruct H6.
      eexists. split. eauto using CPrio_infix_prefix.
      unfold CL_infix_prefix. apply InfixMatch_drm; auto using Match_rm, HMatch.
    + eapply safe_infix_prefix; eauto using CPrio_infix_prefix.
  - apply Prefix_drmcf; auto.
    intro. destruct H1 as [q]. inv H1.
    inv H2. inv H3.
Qed.

Lemma linsert_drmcfree {g} (pr : drules g) t1 o t2 t' :
  safe_pr pr ->
  drm_conflict_free (rm_conflict_pattern pr) t2 ->
  linsert pr t1 o t2 t' ->
  drm_conflict_free (rm_conflict_pattern pr) t'.
Proof.
  intros. induction H1; eauto using linsert_one_drmcfree, linsert_op_drmcfree.
Qed.

Lemma fix_tree_drmcfree {g} (pr : drules g) t t' :
  safe_pr pr ->
  fix_tree pr t t' ->
  drm_conflict_free (rm_conflict_pattern pr) t'.
Proof.
  intros. induction H0.
  - apply Atomic_drmcf.
  - eauto using linsert_drmcfree.
  - eauto using linsert_op_drmcfree.
Qed.

(* safety *)

Theorem safety {g} (pr : drules g) `{drules_dec pr} w :
  safe_pr pr ->
  language w -> dlanguage pr w.
Proof.
  unfold language, dlanguage. intros.
  destruct H0 as [t]. inv H0.
  assert (exists t', fix_tree pr t t'). {
    auto using fix_tree_exists.
  }
  destruct H0 as [t'].
  exists t'.
  split; try split; try split.
  - eauto using fix_tree_wf.
  - eauto using fix_tree_yield.
  - eauto using fix_tree_icfree.
  - eauto using fix_tree_drmcfree.
Qed.

End IPPGrammarTheorems.
