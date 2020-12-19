Require Export IGrammar.
Require Import MyUtils.

Section IGrammarTheorems.

(* Search Decision. *)

Create HintDb IGrammar.
Hint Resolve CPrio1 : IGrammar.
Hint Resolve CPrio2 : IGrammar.
Hint Resolve CLeft : IGrammar.
Hint Resolve CRight : IGrammar.
Hint Resolve HMatch : IGrammar.
Hint Resolve IMatch : IGrammar.

Lemma is_conflict_pattern_true {O} (pr : drules O) q :
  conflict_pattern pr q <-> is_conflict_pattern pr q = true.
Proof.
  split; intro.
  - inv H; simpl; auto using decide_True, decide_False.
    + destruct (decide (prio pr o1 o2)); auto using decide_True, decide_False.
    + destruct (decide (prio pr o1 o2)); auto using decide_True, decide_False.
  - destruct q; inv H.
    destruct q1, q2; inv H1.
    + destruct q2_1, q2_2; inv H0.
      destruct (decide (prio pr o o0)); eauto with IGrammar.
      destruct (decide (left_a pr o o0)); eauto with IGrammar.
      inv H1.
    + destruct q1_1, q1_2; inv H0.
      destruct (decide (prio pr o o0)); eauto with IGrammar.
      destruct (decide (right_a pr o o0)); eauto with IGrammar.
      inv H1.
    + destruct q1_1, q1_2; inv H0.
Qed.

Lemma is_conflict_pattern_false {O} (pr : drules O) q :
  ~ conflict_pattern pr q <-> is_conflict_pattern pr q = false.
Proof.
  split; intro.
  - destruct (is_conflict_pattern pr q) eqn:E; auto.
    exfalso. destruct H. apply is_conflict_pattern_true.
    assumption.
  - intro. apply is_conflict_pattern_true in H0.
    rewrite H in H0. inv H0.
Qed.

(* This tactic can be used to rewrite to simplify a goal with a term
   [linsert_one pr l1 o1 (INode t1 o2 t2))], creating two cases: one
   where [CR o1 o2] is a conflict pattern and one where it is not a
   conflict pattern. *)
Ltac linsert_one_inode_destruct pr o1 o2 :=
    cbn [linsert_one] in *;
     destruct (is_conflict_pattern pr (CR o1 o2)) eqn:E;
     [apply is_conflict_pattern_true in E | apply is_conflict_pattern_false in E].

(* Yield Preservation Lemmas *)

Lemma linsert_one_yield_preserve {L O} (pr : drules O) (l1 : L) o1 t :
  yield (linsert_one pr l1 o1 t) = inl l1 :: inr o1 :: yield t.
Proof.
  induction t.
  - reflexivity.
  - linsert_one_inode_destruct pr o1 o; simpl; auto.
    rewrite IHt1. reflexivity.
Qed.
Hint Resolve linsert_one_yield_preserve : IGrammar.

Lemma linsert_yield_preserve {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  yield (linsert pr t1 o t2) = yield t1 ++ inr o :: yield t2.
Proof.
  revert o t2.
  induction t1; intros; simpl.
  - auto with IGrammar.
  - simplify_list_eq. rewrite <- IHt1_2. rewrite <- IHt1_1.
    reflexivity.
Qed.
Hint Resolve linsert_yield_preserve : IGrammar.

(* Fixing a parse tree preserves its yield. *)
Lemma repair_yield_preserve {L O} (pr : drules O) (t : parse_tree L O) :
  yield (repair pr t) = yield t.
Proof.
  induction t; simpl.
  - reflexivity.
  - rewrite <- IHt2. auto with IGrammar.
Qed.

(* For a safe disambiguation rules, it connot hold that both [CL o1 o2]
   and [CR o2 o1] conflict patterns. *)
Lemma safe_cl_cr {O} (o1 o2 : O) (pr : drules O) :
  safe_pr pr ->
  (conflict_pattern pr (CL o1 o2) /\ conflict_pattern pr (CR o2 o1)) -> False.
Proof.
  intros. destruct H0.
  inv H0; inv H1; eapply H; eauto.
Qed.

Lemma complete_cl_cr {O} (o1 o2 : O) (pr : drules O) :
  complete_pr pr ->
  (conflict_pattern pr (CL o1 o2) \/ conflict_pattern pr (CR o2 o1)).
Proof.
  intro. unfold complete_pr in H. specialize H with o2 o1.
  decompose [or] H; eauto with IGrammar.
Qed.

Lemma complete_neg_cl_cr {O} (o1 o2 : O) (pr : drules O) :
  complete_pr pr ->
  ~ conflict_pattern pr (CL o1 o2) ->
  conflict_pattern pr (CR o2 o1).
Proof.
  intros. apply complete_cl_cr with o1 o2 pr in H.
  destruct H; [contradiction|assumption].
Qed.

(* Conflict-Free Lemmas *)

(* The top operator of [linsert_one l o t] either is [o] or remains the same as [t] *)
Lemma linsert_one_top_operator_match {L O} (pr : drules O) (l : L) (o1 : O) (t : parse_tree L O) :
  matches (linsert_one pr l o1 t) (IPatt HPatt o1 HPatt) \/
  (exists o2, matches t (IPatt HPatt o2 HPatt) /\ matches (linsert_one pr l o1 t) (IPatt HPatt o2 HPatt)).
Proof.
  destruct t.
  - simpl. auto with IGrammar.
  - linsert_one_inode_destruct pr o1 o; eauto 6 with IGrammar.
Qed.

(* Simple Lemma that states that proving something holds for all conflict patterns [q],
   is the same as proving it holds for just conflict patterns of the form [CL] and [CR]. *)
Lemma conflict_pattern_cases {O} (pr : drules O) (q : tree_pattern O) (P : Prop) :
  (forall o1 o2, q = CL o1 o2 -> P) ->
  (forall o1 o2, q = CR o1 o2 -> P) ->
  (conflict_pattern pr q -> P).
Proof.
  intros. inv H1; eauto.
Qed.

(* This tactic applies the Lemma [conflict_pattern_cases] in a neat way. *)
Ltac cp_cases H := eapply conflict_pattern_cases in H; try eassumption; intros; subst.

(* A parse tree with just one infix node is always conflict-free *)
Lemma inode_single_cfree {L O} (pr : drules O) (l1 l2 : L) (o : O) :
  conflict_free (conflict_pattern pr) (INode (ANode l1) o (ANode l2)).
Proof.
  apply INode_cfree; auto using ANode_cfree.
  intro. destruct H as [q]. inv H. cp_cases H0.
  - inv H1. inv H3.
  - inv H1. inv H8.
Qed.

(* Assuming the set of disambiguation rules is safe, one-left-inserting in a
   conflict-free tree gives back also a conflict-free tree. *)
Lemma linsert_one_safe {L O} (pr : drules O) (l1 : L) (o1 : O) (t : parse_tree L O) :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) t ->
  conflict_free (conflict_pattern pr) (linsert_one pr l1 o1 t).
Proof.
  intros Hsafe Hcfree. induction t. apply inode_single_cfree.
  linsert_one_inode_destruct pr o1 o.
  - inv Hcfree. apply INode_cfree; auto. clear H3 H4.
    intro. destruct H as [q]. inv H.
    cp_cases H0.
    + inv H1. inv H4. clear H9 H5 H7.
      destruct (linsert_one_top_operator_match pr l1 o1 t1).
      * rewrite <- H in H1. inv H1.
        eauto using safe_cl_cr.
      * rewrite <- H in H1.
        inv H1. inv H3. inv H1. inv H4. clear H7 H9 H5 H12.
        destruct H2. eexists. eauto with IGrammar.
    + inv H1. inv H9. clear H4 H5 H7.
      destruct H2. eexists. eauto with IGrammar.
  - apply INode_cfree; auto using ANode_cfree.
    intro. destruct H as [q]. inv H.
    cp_cases H0.
    + inv H1. inv H3.
    + inv H1. inv H8. contradiction.
Qed.

Lemma linsert_safe {L O} (pr : drules O) (o : O) (t1 t2 : parse_tree L O) :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) t2 ->
  conflict_free (conflict_pattern pr) (linsert pr t1 o t2).
Proof.
  intro Hsafe. revert o t2.
  induction t1; eauto using linsert_one_safe.
Qed.

Lemma repair_safe {L O} (pr : drules O) (t : parse_tree L O) :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) (repair pr t).
Proof.
  intro. induction t.
  - apply ANode_cfree.
  - eauto using linsert_safe.
Qed.

(* Safety *)

Theorem safety {L O} (pr : drules O) (w : list (L + O)) :
  safe_pr pr ->
  language w -> dlanguage pr w.
Proof.
  intro Hsafe.
  unfold language, dlanguage. intro. destruct H as [t].
  rewrite <- H.
  exists (repair pr t).
  eauto using repair_yield_preserve, repair_safe.
Qed.


(* STUFF FOR COMPLETENESS HERE *)

Lemma linsert_one_simpleton_linsert_anode {L O} (pr : drules O) l1 o (t2 : parse_tree L O) :
  linsert_one pr l1 o t2 = simpleton_linsert pr (ANode l1) o t2.
Proof.
  induction t2; auto.
  simpl. rewrite IHt2_1. reflexivity.
Qed.

Lemma complete_pr_cr_trans {O} (pr : drules O) o1 o2 o3 :
  complete_pr pr ->
  conflict_pattern pr (CR o1 o2) ->
  conflict_pattern pr (CR o2 o3) ->
  conflict_pattern pr (CR o1 o3).
Admitted.

Ltac simpleton_linsert_inode_destruct pr o1 o2 :=
    cbn [simpleton_linsert] in *;
     destruct (is_conflict_pattern pr (CR o1 o2)) eqn:E;
     [apply is_conflict_pattern_true in E | apply is_conflict_pattern_false in E].

Lemma simpleton_linsert_assoc {L O} (pr : drules O) o o1 (t11 t12 t2 : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) (INode t11 o1 t12) ->
  ~ conflict_pattern pr (CL o o1) ->
  simpleton_linsert pr (INode t11 o1 t12) o t2 = simpleton_linsert pr t11 o1 (simpleton_linsert pr t12 o t2).
Proof.
  intros. induction t2.
  - simpleton_linsert_inode_destruct pr o1 o.
    + destruct t12 as [?|t121 o12 t122]; auto.
      rename E into E'.
      simpleton_linsert_inode_destruct pr o1 o12; auto.
      exfalso. inv H0. destruct H5.
      eexists. eauto with IGrammar.
    + apply complete_cl_cr with o o1 pr in H.
      destruct H; contradiction.
  - rename t2_1 into t21, o0 into o2, t2_2 into t22.
    simpleton_linsert_inode_destruct pr o o2.
    + rewrite IHt2_1.
      rename E into E'.
      simpleton_linsert_inode_destruct pr o1 o2; auto.
      exfalso. destruct E.
      eapply complete_pr_cr_trans; eauto.
      apply complete_cl_cr with o o1 pr in H.
      destruct H; [contradiction|assumption].
    + rename E into E'.
      simpleton_linsert_inode_destruct pr o1 o.
      * destruct t12 as [?|t121 o12 t122]; auto.
        rename E into E''.
        simpleton_linsert_inode_destruct pr o1 o12; auto.
        exfalso. inv H0. destruct H5.
        eexists. eauto with IGrammar.
      * exfalso. destruct E.
        apply complete_cl_cr with o o1 pr in H.
        destruct H; [contradiction|assumption].
Qed.

Lemma complete_pr_cr_cl_cr {O} (pr : drules O) o1 o2 o3 :
  complete_pr pr ->
  conflict_pattern pr (CR o1 o2) ->
  conflict_pattern pr (CL o2 o3) ->
  conflict_pattern pr (CR o1 o3).
Admitted.

Lemma linsert_simpleton_linsert {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) t1 ->
  (forall x1, matches t1 (IPatt HPatt x1 HPatt) -> ~ conflict_pattern pr (CL o x1)) ->
  linsert pr t1 o t2 = simpleton_linsert pr t1 o t2.
Proof.
  intro. intro. revert o t2.
  induction t1; intros; simpl; eauto using linsert_one_simpleton_linsert_anode.
  rename t1_1 into t11, o into o1, t1_2 into t12, o0 into o.
  rewrite IHt1_2.
    - rewrite IHt1_1.
      + symmetry. eauto using simpleton_linsert_assoc with IGrammar.
      + inv H0. assumption.
      + intros. intro. inv H2. inv H0. destruct H6.
        eexists. eauto with IGrammar.
    - inv H0. assumption.
    - intros. intro. inv H2. inv H0.
      destruct H6. exists (CR o1 x1). split; eauto with IGrammar.
      eapply complete_pr_cr_cl_cr; eauto.
      apply complete_cl_cr with o o1 pr in H.
      destruct H; eauto.
      exfalso. apply H1 with o1; eauto with IGrammar.
Qed.

Lemma simpleton_linsert_identity {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  conflict_free (conflict_pattern pr) (INode t1 o t2) ->
  simpleton_linsert pr t1 o t2 = INode t1 o t2.
Proof.
  intros. inv H.
  destruct t2; auto.
  simpleton_linsert_inode_destruct pr o o0; auto.
  exfalso. destruct H3.
  eexists. eauto with IGrammar.
Qed.

Lemma linsert_identity {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) (INode t1 o t2) ->
  linsert pr t1 o t2 = INode t1 o t2.
Proof.
  intros.
  rewrite linsert_simpleton_linsert; auto using simpleton_linsert_identity.
  - inv H0. assumption.
  - intros. intro. inv H1. inv H0. destruct H5.
    eexists. eauto with IGrammar.
Qed.

Lemma repair_identity {L O} (pr : drules O) (t : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) t ->
  repair pr t = t.
Proof.
  intros. induction t; simpl; auto.
  rewrite IHt2.
  - rewrite linsert_identity; auto.
  - inv H0. assumption.
Qed.

End IGrammarTheorems.
