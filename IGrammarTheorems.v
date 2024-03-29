Require Export IGrammar.
Require Import MyUtils.

Section IGrammarTheorems.

Create HintDb IGrammar.
Hint Resolve CPrio1 : IGrammar.
Hint Resolve CPrio2 : IGrammar.
Hint Resolve CLeft : IGrammar.
Hint Resolve CRight : IGrammar.
Hint Resolve HMatch : IGrammar.
Hint Resolve InfixMatch : IGrammar.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following two lemmas prove the correctness of the [is_conflict_pattern] function. *)

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

(* This tactic can be used to simplify a goal with a term
   [insert_in pr t1 o1 (InfixNode t21 o2 t22))], creating two cases: one
   where [CR o1 o2] is a conflict pattern and one where it is not a
   conflict pattern. *)
Ltac insert_in_inode_destruct pr o1 o2 :=
    cbn [insert_in] in *;
     destruct (is_conflict_pattern pr (CR o1 o2)) eqn:E;
     [apply is_conflict_pattern_true in E | apply is_conflict_pattern_false in E].

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas prove useful properties regardering the safety and completeness of [pr].
   In the definitions [safe_pr] and [complete_pr] we imposed restrictions on [pr] in terms of
   priority, left-associativity, and right-associativity. Here we prove properties that represent
   restrictions in terms of the conflict patterns [CL] and [CR]. *)

Lemma safe_cl_cr {O} (o1 o2 : O) (pr : drules O) :
  safe_pr pr ->
  (conflict_pattern pr (CL o1 o2) /\ conflict_pattern pr (CR o2 o1)) -> False.
Proof.
  intros. destruct H0.
  inv H0; inv H1; eapply H; eauto.
Qed.

Lemma complete_cl_or_cr {O} (o1 o2 : O) (pr : drules O) :
  complete_pr pr ->
  (conflict_pattern pr (CL o1 o2) \/ conflict_pattern pr (CR o2 o1)).
Proof.
  intro. destruct H. specialize complete_1 with o2 o1.
  decompose [or] complete_1; eauto with IGrammar.
Qed.

Lemma complete_neg_cl_cr {O} (o1 o2 : O) (pr : drules O) :
  complete_pr pr ->
  ~ conflict_pattern pr (CL o1 o2) ->
  conflict_pattern pr (CR o2 o1).
Proof.
  intros. apply complete_cl_or_cr with o1 o2 pr in H.
  destruct H; [contradiction|assumption].
Qed.

Lemma complete_pr_cr_trans {O} (pr : drules O) o1 o2 o3 :
  complete_pr pr ->
  conflict_pattern pr (CR o1 o2) ->
  conflict_pattern pr (CR o2 o3) ->
  conflict_pattern pr (CR o1 o3).
Proof.
  intros. destruct H.
  inv H0; inv H1; eauto with IGrammar.
Qed.

Lemma complete_pr_cr_cl_cr {O} (pr : drules O) o1 o2 o3 :
  complete_pr pr ->
  conflict_pattern pr (CR o1 o2) ->
  conflict_pattern pr (CL o2 o3) ->
  conflict_pattern pr (CR o1 o3).
Proof.
  intros. destruct H.
  inv H0; inv H1; eauto with IGrammar.
  exfalso. eauto.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas aim to prove that [repair] preserves the yield of the tree
   being repaired. This will be useful later when proving safety. *)

Lemma insert_in_yield_preserve {L O} (pr : drules O) (l1 : L) o t2 :
  yield (insert_in pr (AtomicNode l1) o t2) = inl l1 :: inr o :: yield t2.
Proof.
  induction t2.
  - reflexivity.
  - insert_in_inode_destruct pr o o0; simpl; auto.
    rewrite IHt2_1. reflexivity.
Qed.
Hint Resolve insert_in_yield_preserve : IGrammar.

Lemma repair_in_yield_preserve {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  yield (repair_in pr t1 o t2) = yield t1 ++ inr o :: yield t2.
Proof.
  revert o t2.
  induction t1; intros; simpl.
  - auto with IGrammar.
  - simplify_list_eq. rewrite <- IHt1_2. rewrite <- IHt1_1.
    reflexivity.
Qed.
Hint Resolve repair_in_yield_preserve : IGrammar.

Lemma repair_yield_preserve {L O} (pr : drules O) (t : parse_tree L O) :
  yield (repair pr t) = yield t.
Proof.
  induction t; simpl.
  - reflexivity.
  - rewrite <- IHt2. auto with IGrammar.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas aim to prove that [repair] ensures that the repaired tree
   is conflict-free, assuming the disambiguation rules are safe. *)


(* The top operator of [insert_in l1 o t2] either is [o] or remains the same as [t2] *)
Lemma insert_in_top_operator_match {L O} (pr : drules O) (l1 : L) (o : O) (t2 : parse_tree L O) :
  matches (insert_in pr (AtomicNode l1) o t2) (InfixPatt HPatt o HPatt) \/
  (exists o2, matches t2 (InfixPatt HPatt o2 HPatt) /\
              matches (insert_in pr (AtomicNode l1) o t2) (InfixPatt HPatt o2 HPatt)).
Proof.
  destruct t2.
  - simpl. auto with IGrammar.
  - insert_in_inode_destruct pr o o0; eauto 6 with IGrammar.
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
  conflict_free (conflict_pattern pr) (InfixNode (AtomicNode l1) o (AtomicNode l2)).
Proof.
  apply Infix_cf; auto using Atomic_cf.
  intro. destruct H as [q]. inv H. cp_cases H0.
  - inv H1. inv H3.
  - inv H1. inv H8.
Qed.

(* insert_in is safe. *)
Lemma insert_in_safe {L O} (pr : drules O) (l1 : L) (o : O) (t2 : parse_tree L O) :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) t2 ->
  conflict_free (conflict_pattern pr) (insert_in pr (AtomicNode l1) o t2).
Proof.
  (* By induction over [t2] *)
  intros Hsafe Hcfree. induction t2 as [l2|t21 ? o2 t22].
  (* Base case *)
  apply inode_single_cfree.
  (* Inductive case *)
  insert_in_inode_destruct pr o o2.
  - (* Case: [CR o o2] is a conflict pattern *)
    inv Hcfree. apply Infix_cf; auto. clear H3 H4.
    intro. destruct H as [q]. inv H.
    cp_cases H0.
    + (* Proving that our tree does not match arbitrary conflict pattern [CL x1 x2] *)
      rename o1 into x1, o0 into x2.
      inv H1. rename x1 into o2. clear H9. inv H4. clear H5 H7.
      (* Case analysis over the top operator of [insert_in pr l1 o t21]. *)
      destruct (insert_in_top_operator_match pr l1 o t21).
      * (* Case: top operator is [o] *)
        rewrite <- H in H1. inv H1.
        (* Contradiction: Both [CR o o2] and [CL o2 o] are conflict patterns. *)
        eauto using safe_cl_cr.
      * (* Case: top operator is [o21] *)
        destruct H1 as [o21].
        rewrite <- H in H1.
        inv H1. inv H3. inv H4. clear H H7 H9 H5 H12.
        (* Contradiction: It cannot conflict because our original tree has no conflicts. *)
        destruct H2. eexists. eauto with IGrammar.
    + (* Proving that our tree does not match arbitrary conflict pattern [CR x1 x2] *)
      rename o1 into x1, o0 into x2.
      inv H1. rename x1 into o2. inv H9. clear H4 H5 H7.
      (* Contradiction: It cannot conflict because our original tree has no conflicts. *)
      destruct H2. eexists. eauto with IGrammar.
  - (* Case: [CR o o2] is NOT a conflict pattern *)
    apply Infix_cf; auto using Atomic_cf.
    intro. destruct H as [q]. inv H.
    cp_cases H0.
    + inv H1. inv H3.
    + inv H1. inv H8. contradiction.
Qed.

(* repair_in is safe. *)
Lemma repair_in_safe {L O} (pr : drules O) (o : O) (t1 t2 : parse_tree L O) :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) t2 ->
  conflict_free (conflict_pattern pr) (repair_in pr t1 o t2).
Proof.
  intro Hsafe. revert o t2.
  induction t1; eauto using insert_in_safe.
Qed.

(* Repair is safe. *)
Lemma repair_safe {L O} (pr : drules O) (t : parse_tree L O) :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) (repair pr t).
Proof.
  intro. induction t.
  - apply Atomic_cf.
  - eauto using repair_in_safe.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* Safety proof *)

Theorem safety {L O} (pr : drules O) :
  safe_pr pr ->
  safe L pr.
Proof.
  intro Hsafe.
  unfold safe, language, dlanguage. intros. destruct H as [t].
  rewrite <- H.
  exists (repair pr t).
  eauto using repair_yield_preserve, repair_safe.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas aim to prove that [repair] is fully yield-dependent.
   Meaning that of two trees have equal yields, then they repair to the same
   tree. This will be useful for proving completeness later on.
   We prove this by showing that [repair] is the same as the [parse] function. *)

Lemma yield_struct_app {L O} (w1 : word L O) o w2 :
  yield_struct w1 →
  yield_struct w2 →
  yield_struct (w1 ++ inr o :: w2).
Proof.
  intro. induction H; intros; simpl; auto using LOYield.
Qed.

Lemma yield_is_yield_struct {L O} (t : parse_tree L O) :
  yield_struct (yield t).
Proof.
  induction t; simpl.
  - apply LYield.
  - auto using yield_struct_app.
Qed.

Lemma parse_yield_struct_some {L O} (pr : drules O) (w : word L O) :
  yield_struct w ->
  exists t, parse pr w = Some t.
Proof.
  intros. induction H; eauto.
  destruct IHyield_struct.
  eexists. simpl. rewrite H0. reflexivity.
Qed.

Lemma build_yield_some {L O} (pr : drules O) (t : parse_tree L O) :
  exists t', parse pr (yield t) = Some t'.
Proof.
  auto using yield_is_yield_struct, parse_yield_struct_some.
Qed.

Lemma parse_app {L O} (pr : drules O) (t1 t2 t2' : parse_tree L O) o :
  parse pr (yield t2) = Some t2' ->
  parse pr (yield t1 ++ inr o :: yield t2) = Some (repair_in pr t1 o t2').
Proof.
  revert t2 t2' o. induction t1; intros; simpl.
  - rewrite H. reflexivity.
  - simplify_list_eq. rename o into o1, o0 into o.
    destruct (build_yield_some pr t1_2).
    erewrite IHt1_1 with (t2 := (InfixNode t1_2 o t2)); auto.
    simpl. erewrite IHt1_2; auto.
Qed.

Lemma repair_parse {L O} (pr : drules O) (t : parse_tree L O) :
  parse pr (yield t) = Some (repair pr t).
Proof.
  induction t; simpl; auto.
  erewrite parse_app; eauto.
Qed.

Lemma repair_is_fully_yield_dependent {L O} (pr : drules O) (t1 t2 : parse_tree L O) :
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

(*
  ############################################## 
  ##############################################
  ##############################################
*)

(* The following lemmas aim to prove that [repair] preserves conflict-free trees
   (i.e. [repair t = t], if [t] is conflict-free), assuming the disambiguation rules are complete.

   This is done as follows: [repair] expands to [repair_in]. Proving that [repair_in]
   preserves conflict-free trees is difficult. Instead we show that [repair_in] is the same
   as [insert_in] for conflict-free trees. Showing that [insert_in] preserves
   conflict-free trees follows almost directly from the definition. *)


(* The usefulness of this lemma will become clear when we show that [repair_in] equals
   [insert_in] for conflict-free trees. *)
Lemma insert_in_assoc {L O} (pr : drules O) o o1 (t11 t12 t2 : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) (InfixNode t11 o1 t12) ->
  ~ conflict_pattern pr (CL o o1) ->
  insert_in pr (InfixNode t11 o1 t12) o t2 = insert_in pr t11 o1 (insert_in pr t12 o t2).
Proof.
  intros. induction t2.
  - insert_in_inode_destruct pr o1 o.
    + destruct t12 as [?|t121 o12 t122]; auto.
      rename E into E'.
      insert_in_inode_destruct pr o1 o12; auto.
      exfalso. inv H0. destruct H5.
      eexists. eauto with IGrammar.
    + apply complete_neg_cl_cr in H1; auto.
      contradiction.
  - rename t2_1 into t21, o0 into o2, t2_2 into t22.
    insert_in_inode_destruct pr o o2.
    + rewrite IHt2_1.
      rename E into E'.
      insert_in_inode_destruct pr o1 o2; auto.
      exfalso. destruct E.
      eapply complete_pr_cr_trans; eauto.
      apply complete_neg_cl_cr in H1; auto.
    + rename E into E'.
      insert_in_inode_destruct pr o1 o.
      * destruct t12 as [?|t121 o12 t122]; auto.
        rename E into E''.
        insert_in_inode_destruct pr o1 o12; auto.
        exfalso. inv H0. destruct H5.
        eexists. eauto with IGrammar.
      * exfalso. destruct E.
        apply complete_neg_cl_cr in H1; auto.
Qed.

(* [repair_in] equals [insert_in]. Note the premise of this lemma:
   We do not require the tree [InfixNode t1 o t2] to be conflict-free. Instead
   we just require that [t1] is conflict-free, and that [o] does not conflict
   with the top operator of [t1]. *)
Lemma repair_in_insert_in {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) t1 ->
  (forall x1, matches t1 (InfixPatt HPatt x1 HPatt) -> ~ conflict_pattern pr (CL o x1)) ->
  repair_in pr t1 o t2 = insert_in pr t1 o t2.
Proof.
  intro. intro. revert o t2.
  induction t1; intros; simpl; auto.
  rename t1_1 into t11, o into o1, t1_2 into t12, o0 into o.
  rewrite IHt1_2.
    - rewrite IHt1_1.
      + symmetry. eauto using insert_in_assoc with IGrammar.
      + inv H0. assumption.
      + intros. intro. inv H2. inv H0. destruct H6.
        eexists. eauto with IGrammar.
    - inv H0. assumption.
    - intros. intro. inv H2. inv H0.
      destruct H6. exists (CR o1 x1). split; eauto with IGrammar.
      eapply complete_pr_cr_cl_cr; eauto.
      apply complete_cl_or_cr with o o1 pr in H.
      destruct H; eauto.
      exfalso. apply H1 with o1; eauto with IGrammar.
Qed.

Lemma insert_in_complete {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  conflict_free (conflict_pattern pr) (InfixNode t1 o t2) ->
  insert_in pr t1 o t2 = InfixNode t1 o t2.
Proof.
  intros. inv H.
  destruct t2; auto.
  insert_in_inode_destruct pr o o0; auto.
  exfalso. destruct H3.
  eexists. eauto with IGrammar.
Qed.

Lemma repair_in_complete {L O} (pr : drules O) o (t1 t2 : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) (InfixNode t1 o t2) ->
  repair_in pr t1 o t2 = InfixNode t1 o t2.
Proof.
  intros.
  rewrite repair_in_insert_in; auto using insert_in_complete.
  - inv H0. assumption.
  - intros. intro. inv H1. inv H0. destruct H5.
    eexists. eauto with IGrammar.
Qed.

Lemma repair_complete {L O} (pr : drules O) (t : parse_tree L O) :
  complete_pr pr ->
  conflict_free (conflict_pattern pr) t ->
  repair pr t = t.
Proof.
  intros. induction t; simpl; auto.
  rewrite IHt2.
  - rewrite repair_in_complete; auto.
  - inv H0. assumption.
Qed.

(*
  ############################################## 
  ##############################################
  ##############################################
*)

Theorem completeness {L O} (pr : drules O) :
  complete_pr pr ->
  complete L pr.
Proof.
  intro. unfold complete. intros.
  apply repair_is_fully_yield_dependent with pr t1 t2 in H0.
  rewrite repair_complete in H0; auto.
  rewrite repair_complete in H0; auto.
Qed.

End IGrammarTheorems.
