Require Export IGrammar.
Require Import MyUtils.
Require Import IGrammarTheorems.

Section IGrammarBonusTheorems.

Create HintDb IGrammar.
Hint Resolve CPrio1 : IGrammar.
Hint Resolve CPrio2 : IGrammar.
Hint Resolve CLeft : IGrammar.
Hint Resolve CRight : IGrammar.
Hint Resolve HMatch : IGrammar.
Hint Resolve InfixMatch : IGrammar.

Definition safe_cpatterns {O} (pr : drules O) : Prop :=
  forall (o1 o2 : O), (conflict_pattern pr (CR o1 o2) /\ conflict_pattern pr (CL o2 o1) -> False).

Lemma safe_cpatterns_pr {O} (pr : drules O) :
  safe_cpatterns pr ->
  safe_pr pr.
Proof.
  unfold safe_cpatterns. unfold safe_pr. intros.
  destruct H0; destruct H1; eapply H; eauto with IGrammar.
Qed.

Lemma safe_filter_cpatterns {L O} (pr : drules O) :
  (exists (l : L), True) ->
  safe L pr ->
  safe_cpatterns pr.
Proof.
  unfold safe, safe_cpatterns. intros. destruct H as [l].
  inv H1.
  specialize H0 with [inl l; inr o1; inl l; inr o2; inl l].
  assert (language [inl l; inr o1; inl l; inr o2; inl l]). {
    unfold language. exists (InfixNode (InfixNode (AtomicNode l) o1 (AtomicNode l)) o2 (AtomicNode l)).
    reflexivity.
  }
  apply H0 in H1. unfold dlanguage in H1. destruct H1 as [t]. inv H1.
  destruct t; simplify_list_eq.
  destruct t1; simplify_list_eq.
  - destruct t2; simplify_list_eq.
    destruct t2_1; simplify_list_eq.
    + destruct t2_2; simplify_list_eq.
      * inv H5. destruct H7. eexists. eauto with IGrammar.
      * destruct (yield t2_2_1); simplify_list_eq. destruct w; simplify_list_eq.
    + destruct (yield t2_1_1); simplify_list_eq.
      destruct w; simplify_list_eq.
      * destruct (yield t2_1_2); simplify_list_eq.
        destruct w; simplify_list_eq.
      * destruct w; simplify_list_eq.
        destruct w; simplify_list_eq.
  - destruct t1_1; simplify_list_eq.
    + destruct t1_2; simplify_list_eq.
      * destruct t2; simplify_list_eq.
        **inv H5. destruct H7. eexists. eauto with IGrammar.
        **destruct (yield t2_1); simplify_list_eq.
          destruct w; simplify_list_eq.
      * destruct (yield t1_2_1); simplify_list_eq.
        destruct w; simplify_list_eq.
        **destruct (yield t1_2_2); simplify_list_eq.
          destruct w; simplify_list_eq.
        **destruct w; simplify_list_eq.
          destruct w; simplify_list_eq.
    + destruct (yield t1_1_1); simplify_list_eq.
      destruct w; simplify_list_eq.
      * destruct (yield t1_1_2); simplify_list_eq.
        destruct w; simplify_list_eq.
        **destruct (yield t1_2); simplify_list_eq.
          destruct w; simplify_list_eq.
        **destruct w; simplify_list_eq.
          destruct w; simplify_list_eq.
      * destruct w; simplify_list_eq.
        destruct w; simplify_list_eq.
        **destruct (yield t1_1_2); simplify_list_eq.
          destruct w; simplify_list_eq.
        **destruct w; simplify_list_eq.
          destruct w; simplify_list_eq.
Qed.

Record complete_cpatterns {O} (pr : drules O) := mkCompleteCpatterns {
  com1 : forall o1 o2, (conflict_pattern pr (CR o1 o2) \/ conflict_pattern pr (CL o2 o1));
  com2 : forall o1 o2 o3, conflict_pattern pr (CR o1 o2) ->
                          conflict_pattern pr (CR o2 o3) ->
                          conflict_pattern pr (CR o1 o3);
  com3 : forall o1 o2 o3, conflict_pattern pr (CL o1 o2) ->
                          conflict_pattern pr (CL o2 o3) ->
                          conflict_pattern pr (CL o1 o3)
}.

Record wf_drules {O} (pr : drules O) := mkWfDrules {
  wf_drules1 : forall o1 o2 : O, left_a pr o1 o2 /\ right_a pr o1 o2 -> False;
  wf_drules2 : forall o1 o2 : O, left_a pr o1 o2 /\ prio pr o1 o2 -> False;
  wf_drules3 : forall o1 o2 : O, prio pr o1 o2 /\ right_a pr o1 o2 -> False;
}.

Lemma complete_cpatterns_pr {O} (pr : drules O) :
  wf_drules pr ->
  safe_cpatterns pr ->
  complete_cpatterns pr ->
  complete_pr pr.
Proof.
  intros. apply mkComplete_pr; intros.
  - inv H1. specialize com4 with o1 o2. destruct com4.
    + inv H1; auto.
    + inv H1; auto.
  - inv H1. specialize com5 with o1 o2 o3. specialize com6 with o1 o2 o3.
    apply CPrio1 in H2 as ?. apply CPrio2 in H2 as ?. apply CPrio1 in H3 as ?. apply CPrio2 in H3 as ?.
    apply com5 in H4; auto. apply com6 in H1; auto.
    inv H1; auto. inv H4; auto.
    exfalso. eapply H; eauto.
  - apply CPrio1 in H2 as ?. apply CPrio2 in H2 as ?. apply CLeft in H3.
    inv H1. eapply com5 in H3 as ?; eauto.
    inv H1; eauto.
    specialize com4 with o3 o1. destruct com4.
    + eapply com5 in H1; eauto. exfalso. eapply H0; eauto.
    + inv H1; auto.
      exfalso. eapply H; eauto.
  - apply CPrio1 in H2 as ?. apply CPrio2 in H2 as ?. apply CRight in H3.
    inv H1. eapply com6 in H3 as ?; eauto.
    inv H1; eauto.
    specialize com4 with o1 o3. destruct com4.
    + inv H1; auto.
      exfalso. eapply H; eauto.
    + eapply com6 in H1; eauto. exfalso. eapply H0; eauto.
  - apply CLeft in H2. apply CPrio1 in H3 as ?. apply CPrio2 in H3.
    inv H1. eapply com5 in H3 as ?; eauto.
    inv H1; eauto.
    specialize com4 with o3 o1. destruct com4.
    + exfalso. eauto.
    + inv H1; eauto. exfalso. eapply H. eauto.
  - apply CLeft in H2 as ?. apply CLeft in H3 as ?. inv H1.
    eapply com5 in H5 as ?; eauto. inv H1; auto. apply CPrio1 in H7 as ?.
    exfalso.
    specialize com4 with o2 o1 as ?. destruct H6.
    + specialize com4 with o3 o2 as ?. destruct H8.
      * eapply com5 in H6; eauto.
      * inv H. inv H8; eauto.
    + inv H. inv H6; eauto.
  - apply CLeft in H2 as ?. apply CRight in H3 as ?.
    inv H1. specialize com4 with o1 o3 as ?. destruct H1; eauto.
    inv H. apply H0 with o2 o3. split; auto.
    + apply com5 with o1; auto.
      specialize com4 with o2 o1. destruct com4; auto. exfalso. inv H; eauto.
    + specialize com4 with o2 o3. destruct com4; auto. exfalso. inv H; eauto.
Qed.

Ltac cp_cases H := eapply conflict_pattern_cases in H; try eassumption; intros; subst.

Lemma complete_filter_cpatterns {L O} (pr : drules O) :
  safe_cpatterns pr ->
  (exists (l : L), True) ->
  complete L pr ->
  complete_cpatterns pr.
Proof.
  intros. destruct H0 as [l]. unfold complete in H1.
  apply mkCompleteCpatterns; intros.
  - specialize H1 with
      (InfixNode (AtomicNode l) o1 (InfixNode (AtomicNode l) o2 (AtomicNode l)))
      (InfixNode (InfixNode (AtomicNode l) o1 (AtomicNode l)) o2 (AtomicNode l)).
    simpl in H1.
    destruct (is_conflict_pattern pr (CR o1 o2)) eqn:E1; try apply is_conflict_pattern_true in E1; auto.
    apply is_conflict_pattern_false in E1.
    destruct (is_conflict_pattern pr (CL o2 o1)) eqn:E2; try apply is_conflict_pattern_true in E2; auto.
    apply is_conflict_pattern_false in E2.
    assert ([inl l; inr o1; inl l; inr o2; inl l] = [inl l; inr o1; inl l; inr o2; inl l]). {
      reflexivity.
    }
    apply H1 in H2.
    + inv H2.
    + apply Infix_cf; auto using Atomic_cf.
      * intro. inv H3. inv H4. cp_cases H3; inv H5.
        **inv H7.
        **inv H12. contradiction.
      * apply Infix_cf; auto using Atomic_cf.
        intro. inv H3. inv H4. cp_cases H3; inv H5.
        **inv H7.
        **inv H12.
    + apply Infix_cf; auto using Atomic_cf.
      * intro. inv H3. inv H4. cp_cases H3.
        **inv H5. inv H7. contradiction.
        **inv H5. inv H12.
      * apply Infix_cf; auto using Atomic_cf.
        intro. inv H3. inv H4. cp_cases H3; inv H5.
        **inv H7.
        **inv H12.
  - specialize H1 with
      (InfixNode (InfixNode (InfixNode (AtomicNode l) o1 (AtomicNode l)) o2 (AtomicNode l)) o3 (AtomicNode l))
      (InfixNode (AtomicNode l) o1 (InfixNode (InfixNode (AtomicNode l) o2 (AtomicNode l)) o3 (AtomicNode l))).
    simpl in H1.
    destruct (is_conflict_pattern pr (CR o1 o3)) eqn:E; try apply is_conflict_pattern_true in E; auto.
    apply is_conflict_pattern_false in E. exfalso.
    unfold safe_cpatterns in H.
    assert (~ conflict_pattern pr (CL o2 o1)); eauto.
    assert (~ conflict_pattern pr (CL o3 o2)); eauto.
    assert ([inl l; inr o1; inl l; inr o2; inl l; inr o3; inl l]
            = [inl l; inr o1; inl l; inr o2; inl l; inr o3; inl l]); auto.
    apply H1 in H6.
    + inv H6.
    + apply Infix_cf; auto using Atomic_cf.
      * intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. contradiction. inv H16.
      * apply Infix_cf; auto using Atomic_cf.
        **intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. contradiction. inv H16.
        **apply Infix_cf; auto using Atomic_cf.
          intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16.
    + apply Infix_cf; auto using Atomic_cf.
      * intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16. contradiction.
      * apply Infix_cf; auto using Atomic_cf.
        **intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. contradiction. inv H16.
        **apply Infix_cf; auto using Atomic_cf.
          intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16.
  - specialize H1 with
      (InfixNode (AtomicNode l) o3 (InfixNode (AtomicNode l) o2 (InfixNode (AtomicNode l) o1 (AtomicNode l))))
      (InfixNode (InfixNode (AtomicNode l) o3 (InfixNode (AtomicNode l) o2 (AtomicNode l))) o1 (AtomicNode l)).
    simpl in H1.
    destruct (is_conflict_pattern pr (CL o1 o3)) eqn:E; try apply is_conflict_pattern_true in E; auto.
    apply is_conflict_pattern_false in E. exfalso.
    unfold safe_cpatterns in H.
    assert (~ conflict_pattern pr (CR o2 o1)); eauto.
    assert (~ conflict_pattern pr (CR o3 o2)); eauto.
    assert ([inl l; inr o3; inl l; inr o2; inl l; inr o1; inl l]
            = [inl l; inr o3; inl l; inr o2; inl l; inr o1; inl l]); auto.
    apply H1 in H6.
    + inv H6.
    + apply Infix_cf; auto using Atomic_cf.
      * intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16. contradiction.
      * apply Infix_cf; auto using Atomic_cf.
        **intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16. contradiction.
        **apply Infix_cf; auto using Atomic_cf.
          intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16.
    + apply Infix_cf; auto using Atomic_cf.
      * intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. contradiction. inv H16.
      * apply Infix_cf; auto using Atomic_cf.
        **intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16. contradiction.
        **apply Infix_cf; auto using Atomic_cf.
          intro. inv H7. inv H8. cp_cases H7; inv H9. inv H11. inv H16.
Qed.

End IGrammarBonusTheorems.
