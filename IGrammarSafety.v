Require Export IGrammar.
Require Import MyUtils.

Section IGrammarSafety.

Arguments ANode {_ _} _.
Arguments INode {_ _} _ _ _.

Arguments HPatt {_}.
Arguments IPatt {_} _ _ _.

Arguments prio {_} _ _ _.
Arguments left_a {_} _ _ _.
Arguments right_a {_} _ _ _.

Lemma dec_conflict_pattern {O} (pr : drules O) `{drules_dec pr} (q : tree_pattern O) :
  Decision (conflict_pattern pr q).
Proof.
  destruct drules_dec0.
  unfold Decision. destruct q.
  - right. intro. inv H.
  - destruct q1, q2.
    + right. intro. inv H.
    + destruct q2_1. destruct q2_2.
      * replace (IPatt HPatt o (IPatt HPatt o0 HPatt)) with (CR o o0); try reflexivity.
        specialize dec_prio with (o1 := o) (o2 := o0).
        specialize dec_left_a with (o1 := o) (o2 := o0).
        destruct dec_prio, dec_left_a; auto using CPrio2, CLeft.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
    + destruct q1_1. destruct q1_2.
      * replace (IPatt (IPatt HPatt o0 HPatt) o HPatt) with (CL o o0); try reflexivity.
        specialize dec_prio with (o1 := o) (o2 := o0).
        specialize dec_right_a with (o1 := o) (o2 := o0).
        destruct dec_prio, dec_right_a; auto using CPrio1, CRight.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
Qed.

Lemma safe_cl_cr {O} (o1 o2 : O) (pr : drules O) `{safety_props pr} :
  (conflict_pattern pr (CL o1 o2) /\ conflict_pattern pr (CR o2 o1)) -> False.
Proof.
  intros H_CL_CR. destruct safety_props0.
  destruct H_CL_CR as [H_CL H_CR].
  inv H_CL; inv H_CR.
  - apply prio_antisym in H0. contradiction.
  - apply left_a_sym in H1.
    apply prio_one in H0. destruct H0. contradiction.
  - apply right_a_sym in H0.
    apply prio_one in H1. destruct H1. contradiction.
  - apply right_a_sym in H0.
    apply left_a_one in H1. destruct H1. contradiction.
Qed.

Lemma linsert_one_match {L O} (pr : drules O) (l : L) (o1 : O) (t t' : parse_tree L O) :
  linsert_one pr l o1 t t' ->
  matches t' (IPatt HPatt o1 HPatt) \/
  (exists o2 : O, matches t (IPatt HPatt o2 HPatt) /\ matches t' (IPatt HPatt o2 HPatt)).
Proof.
  intros. inv H.
  - left. apply IMatch; apply HMatch.
  - left. apply IMatch; apply HMatch.
  - right. exists o2. split; apply IMatch; apply HMatch.
Qed.

Lemma conflict_pattern_cases {O} (pr : drules O) (q : tree_pattern O) (P : Prop) :
  (forall o1 o2, q = CL o1 o2 -> P) ->
  (forall o1 o2, q = CR o1 o2 -> P) ->
  (conflict_pattern pr q -> P).
Proof.
  intros. inv H1; eauto.
Qed.

Lemma linsert_one_safe {L O} (pr : drules O) `{safety_props pr}
    (l1 : L) (o1 : O) (t t' : parse_tree L O) :
  conflict_free (conflict_pattern pr) t ->
  linsert_one pr l1 o1 t t' ->
  conflict_free (conflict_pattern pr) t'.
Proof.
  intros. induction H0.
  - apply INode_cfree; auto using ANode_cfree.
    intro. inv H0. inv H1. inv H0; inv H2.
    inv H4. inv H9. inv H9. inv H4.
  - apply INode_cfree; auto using ANode_cfree.
    intro. inv H1. inv H2. 
    eapply conflict_pattern_cases; try eassumption; intros; subst; inv H3.
    + inv H5.
    + inv H10. eauto using safe_cl_cr.
  - inv H. apply INode_cfree; auto.
    intro. inv H. inv H2.
    eapply conflict_pattern_cases; try eassumption; intros; subst; inv H3.
    + apply linsert_one_match in H1. destruct H1.
      * inv H1. inv H8. eauto using safe_cl_cr.
      * inv H1. inv H2. inv H8. inv H3. inv H1.
        apply H5. exists (CL o0 x). split; try assumption.
        unfold CL. auto using HMatch, IMatch.
    + inv H13. apply H5.
      exists (CR o0 o3). split; try assumption.
      unfold CR. auto using HMatch, IMatch.
Qed.

Lemma linsert_one_yield {L O} (pr : drules O)
    (l1 : L) (o1 : O) (t t' : parse_tree L O) :
  linsert_one pr l1 o1 t t' ->
  yield t' = inl l1 :: inr o1 :: yield t .
Proof.
  intros. induction H; simpl; auto.
  rewrite IHlinsert_one. reflexivity.
Qed.

Lemma linsert_one_exists {L O} (pr : drules O) `{drules_dec pr}
    (l : L) (o : O) (t : parse_tree L O) :
  exists t', linsert_one pr l o t t'.
Proof.
  induction t.
  - eexists. apply ANode_LInsert_One.
  - assert (Decision (conflict_pattern pr (CR o o0))). {
      auto using dec_conflict_pattern.
    }
    destruct IHt1, IHt2.
    destruct H.
    + eexists. eauto using INode_LInsert_One_2.
    + eexists. eauto using INode_LInsert_One_1.
Qed.

Lemma linsert_yield {L O} (pr : drules O)
    (o : O) (t1 t2 t' : parse_tree L O) :
  linsert pr t1 o t2 t' ->
  yield t' = yield t1 ++ inr o :: yield t2.
Proof.
  intro. induction H; simpl; eauto using linsert_one_yield.
  - rewrite IHlinsert2. rewrite IHlinsert1.
    simplify_list_eq. reflexivity.
Qed.

Lemma linsert_safe {L O} (pr : drules O) `{safety_props pr}
    (o : O) (t1 t2 t' : parse_tree L O) :
  conflict_free (conflict_pattern pr) t2 ->
  linsert pr t1 o t2 t' ->
  conflict_free (conflict_pattern pr) t'.
Proof.
  intros. induction H0; eauto using linsert_one_safe.
Qed.

Lemma linsert_exists {L O} (pr : drules O) `{drules_dec pr}
    (o : O) (t1 t2 : parse_tree L O) :
  exists t', linsert pr t1 o t2 t'.
Proof.
  revert o t2. induction t1; intros.
  - assert (exists t', linsert_one pr l o t2 t'). {
      auto using linsert_one_exists.
    }
    destruct H. eauto using ANode_LInsert.
  - specialize IHt1_2 with o0 t2. destruct IHt1_2.
    specialize IHt1_1 with o x. destruct IHt1_1.
    eauto using INode_LInsert.
Qed.

Theorem safety {L O} (pr : drules O) `{safety_props pr} `{drules_dec pr} (w : list (L + O)) :
  language w -> dlanguage pr w.
Proof.
  unfold language, dlanguage. intro. destruct H as [t].
  revert H. revert w. induction t; intros; simpl in *.
  - exists (ANode l); simpl in *. split.
    + assumption.
    + apply ANode_cfree.
  - specialize IHt2 with (yield t2). destruct IHt2 as [t2']. reflexivity. destruct H0.
    assert (exists t', linsert pr t1 o t2' t'). {
      auto using linsert_exists.
    }
    destruct H2 as [t']. exists t'. split.
    + rewrite <- H. rewrite <- H0.
      eauto using linsert_yield.
    + eauto using linsert_safe.
Qed.

End IGrammarSafety.
