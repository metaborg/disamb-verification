From stdpp Require Export list.
From stdpp Require Export relations.
Load "Lib/StrongInduction".

Section Experiment7.

Ltac inv H := inversion H; clear H; subst.

Inductive production Terminal :=
  | AtomicProduction : Terminal → production Terminal
  | InfixProduction : option Terminal → production Terminal
  | PrefixProduction : Terminal → production Terminal
  | PostfixProduction : Terminal → production Terminal
  | ClosedProduction : Terminal → Terminal → production Terminal.

Global Arguments AtomicProduction {_} _.
Global Arguments InfixProduction {_} _.
Global Arguments PrefixProduction {_} _.
Global Arguments PostfixProduction {_} _.
Global Arguments ClosedProduction {_} _ _.

Record grammar := mkGrammar {
  Terminal : Type;
  Productions: production Terminal -> Prop;
}.

Context {g : grammar}.
Notation T := (Terminal g).
Implicit Types a b c o l : T.
Implicit Types oa ob : option T.
Notation P := (Productions g).
Implicit Types p : production T.
Notation AtomP a := (P (AtomicProduction a)).
Notation InP oa := (P (InfixProduction oa)).
Notation PreP a := (P (PrefixProduction a)).
Notation PostP a := (P (PostfixProduction a)).
Notation ClosedP a1 a2 := (P (ClosedProduction a1 a2)).


Definition word := list T.

Implicit Types w : word.

Inductive parse_tree :=
  | AtomicNode : T → parse_tree
  | InfixNode : parse_tree → option T → parse_tree → parse_tree
  | PrefixNode : T → parse_tree → parse_tree
  | PostfixNode : parse_tree → T → parse_tree
  | ClosedNode : T → parse_tree → T → parse_tree.

Notation PT := parse_tree.
Implicit Types t : PT.
Notation "'AN' a" := (AtomicNode a) (at level 3).
Notation "[ t1 ; oa ; t2 ]" := (InfixNode t1 oa t2).
Notation "[ a ; t2 ]" := (PrefixNode a t2).
Notation "[| t1 ; a ]" := (PostfixNode t1 a).
Notation "[( a1 ; t ; a2 )]" := (ClosedNode a1 t a2).

Inductive well_formed_parse_tree : PT → Prop :=
  | WellFormedAtomicNode a :
      AtomP a →
      well_formed_parse_tree (AN a)
  | WellFormedInfixNode t1 oa t2 :
      InP oa →
      well_formed_parse_tree t1 →
      well_formed_parse_tree t2 →
      well_formed_parse_tree [t1; oa; t2]
  | WellFormedPrefixNode a t2 :
      PreP a →
      well_formed_parse_tree t2 →
      well_formed_parse_tree [a; t2]
  | WellFormedPostfixNode t1 a :
      PostP a →
      well_formed_parse_tree t1 →
      well_formed_parse_tree [|t1; a]
  | WellFormedClosedNode a1 t a2 :
      ClosedP a1 a2 →
      well_formed_parse_tree t →
      well_formed_parse_tree [(a1; t; a2)].

Notation wf t := (well_formed_parse_tree t).

Fixpoint yield t : word :=
  match t with
  | AN a => [a]
  | [t1; (Some a); t2] => yield t1 ++ a :: yield t2
  | [t1; None; t2] => yield t1 ++ yield t2
  | [a; t2] => a :: yield t2
  | [|t1; a] => yield t1 ++ [a]
  | [(a1; t; a2)] => a1 :: yield t ++ [a2]
  end.

Inductive reorder_step : PT → PT → Prop :=
  | ReorderStepInfix t1 t2 t3 oa ob :
      reorder_step [[t1; oa; t2]; ob; t3] [t1; oa; [t2; ob; t3]]
  | ReorderStepInfixPrefix t1 t2 a ob :
      reorder_step [[a; t1]; ob; t2] [a; [t1; ob; t2]]
  | ReorderStepInfixPostfix t1 t2 oa b :
      reorder_step [t1; oa; [|t2; b]] [|[t1; oa; t2]; b]
  | ReorderStepPrefixPostfix t a b :
      reorder_step [a; [|t; b]] [|[a; t]; b]
  | ReorderStepInfixSubtree1 t1 oa t2 t1' :
      reorder_step t1 t1' →
      reorder_step [t1; oa; t2] [t1'; oa; t2]
  | ReorderStepInfixSubtree2 t1 oa t2 t2' :
      reorder_step t2 t2' →
      reorder_step [t1; oa; t2] [t1; oa; t2']
  | ReorderStepPrefixSubtree a t2 t2' :
      reorder_step t2 t2' →
      reorder_step [a; t2] [a; t2']
  | ReorderStepPostfixSubtree a t1 t1' :
      reorder_step t1 t1' →
      reorder_step [|t1; a] [|t1'; a]
  | ReorderStepClosedSubtree a1 t a2 t' :
      reorder_step t t' →
      reorder_step [(a1; t; a2)] [(a1; t'; a2)].

Notation "t1 ---> t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟶ t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟷ t2" := ((sc reorder_step) t1 t2) (at level 75).

Definition reorder := rtsc (reorder_step).

Notation "t1 <--->* t2" := (reorder t1 t2) (at level 76).
Notation "t1 ⟷* t2" := (reorder t1 t2) (at level 76).

Lemma reorder_infix_subtree1 t1 oa t2 t1' :
  t1 ⟷* t1' →
  [t1; oa; t2] ⟷* [t1'; oa; t2].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [y; oa; t2].
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree1. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree1. assumption.
    + assumption.
Qed.

Lemma reorder_infix_subtree2 t1 oa t2 t2' :
  t2 ⟷* t2' →
  [t1; oa; t2] ⟷* [t1; oa; t2'].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [t1; oa; y].
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree2. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree2. assumption.
    + assumption.
Qed.

Lemma reorder_prefix_subtree o t2 t2' :
  t2 ⟷* t2' →
  [o; t2] ⟷* [o; t2'].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [o; y].
    + inv H.
      * apply sc_lr. apply ReorderStepPrefixSubtree. assumption.
      * apply sc_rl. apply ReorderStepPrefixSubtree. assumption.
    + assumption.
Qed.

Lemma reorder_postfix_subtree t1 o t1' :
  t1 ⟷* t1' →
  [|t1; o] ⟷* [|t1'; o].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [|y; o].
    + inv H.
      * apply sc_lr. apply ReorderStepPostfixSubtree. assumption.
      * apply sc_rl. apply ReorderStepPostfixSubtree. assumption.
    + assumption.
Qed.

Lemma reorder_closed_subtree a1 t a2 t' :
  t ⟷* t' →
  [(a1; t; a2)] ⟷* [(a1; t'; a2)].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - eapply rtc_l.
    + inv H.
      * apply sc_lr. apply ReorderStepClosedSubtree. eassumption.
      * apply sc_rl. apply ReorderStepClosedSubtree. eassumption.
    + assumption.
Qed.

Inductive yield_struct : word → PT → Prop :=
  | AtomicYieldStruct  l w t :
      AtomP l →
      yield_some_struct (AN l) w t →
      yield_struct (l :: w) t
  | PrefixYieldStruct  o w t :
      PreP o →
      yield_struct w t →
      yield_struct (o :: w) [o; t]
  | ClosedYieldStruct a1 a2 w wt t t' :
      ClosedP a1 a2 →
      yield_struct w t →
      yield_some_struct [(a1; t; a2)] wt t' →
      yield_struct (a1 :: w ++ a2 :: wt) t'

with yield_some_struct : PT → word → PT → Prop :=
  | NilYieldStruct t :
      yield_some_struct t [] t
  | InfixSomeYieldStruct t1 o t2 w :
      InP (Some o) →
      yield_struct w t2 →
      yield_some_struct t1 (o :: w) [t1; Some o; t2]
  | InfixNoneYieldStruct t1 t2 w :
      InP None →
      yield_struct w t2 →
      yield_some_struct t1 w [t1; None; t2]
  | PostfixYieldStruct o w t1 t :
      PostP o →
      yield_some_struct [|t1; o] w t →
      yield_some_struct t1 (o :: w) t.

Notation ys w t := (yield_struct w t).
Notation yss t w u := (yield_some_struct t w u).

Inductive post_tree : PT → Prop :=
  | AtomicPostTree l :
      AtomP l →
      post_tree AN l
  | PostfixPostTree t a :
      PostP a →
      post_tree t →
      post_tree [|t; a].

Lemma yield_struct_infix_sound w1 t1 w2 t2 a :
  (ys w1 t1 → ys w2 t2 → InP (Some a) →
  ∃ t', ys (w1 ++ a :: w2) t' ∧ [t1; Some a; t2] ⟷* t')
  ∧
  (∀ ti, yss ti w1 t1 → ys w2 t2 → InP (Some a) →
  ∃ t', yss ti (w1 ++ a :: w2) t' ∧ [t1; Some a; t2] ⟷* t').
Proof.
  remember (length w1) as n. revert Heqn. revert w1 t1. strong induction n.
  intros. destruct w1 as [ | a0 w1]; split; intros.
  - inv H0.
  - inv H0.
    + simpl.
      exists [t1; Some a; t2]. split.
      * apply InfixSomeYieldStruct; assumption.
      * apply rtc_refl.
    + inv H4.
  - simpl in *.
    inv H0.
    + specialize H with (length w1) w1 t1. destruct H; auto.
      apply H0 in H7; auto.
      destruct H7 as [t']. destruct H3.
      exists t'. split; auto.
      apply AtomicYieldStruct; auto.
    + specialize H with (length w1) w1 t. destruct H; auto.
      apply H in H7; auto.
      destruct H7 as [t']. destruct H3.
      exists [a0; t']. split.
      * apply PrefixYieldStruct; auto.
      * apply rtc_l with [a0; [t; Some a; t2]].
        **apply sc_lr. apply ReorderStepInfixPrefix.
        **apply reorder_prefix_subtree. assumption.
    + simplify_list_eq. specialize H with (length wt) wt t1. destruct H; auto. {
        rewrite app_length. simpl. lia.
      }
      apply H0 in H8; auto. inv H8. inv H3.
      eexists. split; eauto.
      eapply ClosedYieldStruct; eauto.
  - simpl in *.
    inv H0.
    + specialize H with (length w1) w1 t3. destruct H; auto.
      apply H in H8; auto.
      destruct H8 as [t']. destruct H3.
      exists [ti; Some a0; t']. split.
      * apply InfixSomeYieldStruct; auto.
      * apply rtc_l with [ti; Some a0; [t3; Some a; t2]].
        **apply sc_lr. apply ReorderStepInfix.
        **apply reorder_infix_subtree2; assumption.
    + inv H4.
      * specialize H with (length w1) w1 t3. destruct H; auto.
        apply H0 in H8; auto.
        destruct H8 as [t']. destruct H4.
        exists [ti; None; t']. split.
        **apply InfixNoneYieldStruct; auto. apply AtomicYieldStruct; auto.
        **apply rtc_l with [ti; None; [t3; Some a; t2]].
          ***apply sc_lr. apply ReorderStepInfix.
          ***apply reorder_infix_subtree2; assumption.
      * specialize H with (length w1) w1 t. destruct H; auto.
        apply H in H8; auto.
        destruct H8. destruct H4.
        exists [ti; None; [a0; x]]. split.
        **apply InfixNoneYieldStruct; auto. apply PrefixYieldStruct; auto.
        **apply rtc_l with [ti; None; [[a0; t]; Some a; t2]].
          ***apply sc_lr. apply ReorderStepInfix.
          ***apply reorder_infix_subtree2.
            apply rtc_l with [a0; [t; Some a; t2]].
            ****apply sc_lr. apply ReorderStepInfixPrefix.
            ****apply reorder_prefix_subtree. assumption.
      * simplify_list_eq.
        specialize H with (length wt) wt t3. destruct H; auto. {
          rewrite app_length. simpl. lia.
        }
        apply H0 in H9; auto. inv H9. inv H4.
        eexists. split.
        **apply InfixNoneYieldStruct; auto. eapply ClosedYieldStruct; eauto.
        **eapply rtc_l.
          ***apply sc_lr. apply ReorderStepInfix.
          ***apply reorder_infix_subtree2. assumption.
    + specialize H with (length w1) w1 t1. destruct H; auto.
      apply H0 in H8; auto.
      destruct H8 as [t']. destruct H3.
      exists t'. split; auto.
      apply PostfixYieldStruct; auto.
Qed.

Lemma yield_struct_app_sound w1 t1 w2 t2 :
  (ys w1 t1 → ys w2 t2 → InP None →
  ∃ t', ys (w1 ++ w2) t' ∧ [t1; None; t2] ⟷* t')
  ∧
  (∀ ti, yss ti w1 t1 → ys w2 t2 → InP None →
  ∃ t', yss ti (w1 ++ w2) t' ∧ [t1; None; t2] ⟷* t').
Proof.
  remember (length w1) as n. revert Heqn. revert w1 t1. strong induction n.
  intros. destruct w1 as [ | a0 w1]; split; intros.
  - inv H0.
  - inv H0.
    + simpl.
      exists [t1; None; t2]. split.
      * apply InfixNoneYieldStruct; assumption.
      * apply rtc_refl.
    + inv H4.
  - simpl in *.
    inv H0.
    + specialize H with (length w1) w1 t1. destruct H; auto.
      apply H0 in H7; auto.
      destruct H7 as [t']. destruct H3.
      exists t'. split; auto.
      apply AtomicYieldStruct; auto.
    + specialize H with (length w1) w1 t. destruct H; auto.
      apply H in H7; auto.
      destruct H7 as [t']. destruct H3.
      exists [a0; t']. split.
      * apply PrefixYieldStruct; auto.
      * apply rtc_l with [a0; [t; None; t2]].
        **apply sc_lr. apply ReorderStepInfixPrefix.
        **apply reorder_prefix_subtree. assumption.
    + simplify_list_eq. specialize H with (length wt) wt t1. destruct H; auto. {
        rewrite app_length. simpl. lia.
      }
      apply H0 in H8; auto. inv H8. inv H3.
      eexists. split; eauto.
      eapply ClosedYieldStruct; eauto.
  - simpl in *.
    inv H0.
    + specialize H with (length w1) w1 t3. destruct H; auto.
      apply H in H8; auto.
      destruct H8 as [t']. destruct H3.
      exists [ti; Some a0; t']. split.
      * apply InfixSomeYieldStruct; auto.
      * apply rtc_l with [ti; Some a0; [t3; None; t2]].
        **apply sc_lr. apply ReorderStepInfix.
        **apply reorder_infix_subtree2; assumption.
    + inv H4.
      * specialize H with (length w1) w1 t3. destruct H; auto.
        apply H0 in H8; auto.
        destruct H8 as [t']. destruct H4.
        exists [ti; None; t']. split.
        **apply InfixNoneYieldStruct; auto. apply AtomicYieldStruct; auto.
        **apply rtc_l with [ti; None; [t3; None; t2]].
          ***apply sc_lr. apply ReorderStepInfix.
          ***apply reorder_infix_subtree2; assumption.
      * specialize H with (length w1) w1 t. destruct H; auto.
        apply H in H8; auto.
        destruct H8. destruct H4.
        exists [ti; None; [a0; x]]. split.
        **apply InfixNoneYieldStruct; auto. apply PrefixYieldStruct; auto.
        **apply rtc_l with [ti; None; [[a0; t]; None; t2]].
          ***apply sc_lr. apply ReorderStepInfix.
          ***apply reorder_infix_subtree2.
            apply rtc_l with [a0; [t; None; t2]].
            ****apply sc_lr. apply ReorderStepInfixPrefix.
            ****apply reorder_prefix_subtree. assumption.
      * simplify_list_eq.
        specialize H with (length wt) wt t3. destruct H; auto. {
          rewrite app_length. simpl. lia.
        }
        apply H0 in H9; auto. inv H9. inv H4.
        eexists. split.
        **apply InfixNoneYieldStruct; auto. eapply ClosedYieldStruct; eauto.
        **eapply rtc_l.
          ***apply sc_lr. apply ReorderStepInfix.
          ***apply reorder_infix_subtree2. assumption.
    + specialize H with (length w1) w1 t1. destruct H; auto.
      apply H0 in H8; auto.
      destruct H8 as [t']. destruct H3.
      exists t'. split; auto.
      apply PostfixYieldStruct; auto.
Qed.

Lemma yield_struct_postfix_sound w1 t1 a :
  (ys w1 t1 → PostP a →
  ∃ t', ys (w1 ++ [a]) t' ∧ [|t1; a] ⟷* t') ∧
  (∀ ti, yss ti w1 t1 → PostP a →
  ∃ t', yss ti (w1 ++ [a]) t' ∧ [|t1; a] ⟷* t').
Proof.
  remember (length w1) as n. revert Heqn. revert w1 t1. strong induction n.
  intros. destruct w1 as [ | a0 w1]; split; intros.
  - inv H0.
  - inv H0.
    + simpl.
      exists [|t1; a]. split.
      * apply PostfixYieldStruct; auto. apply NilYieldStruct.
      * apply rtc_refl.
    + inv H3.
  - simpl in *.
    inv H0.
    + specialize H with (length w1) w1 t1. destruct H; auto.
      apply H0 in H6; auto.
      destruct H6 as [t']. destruct H2.
      exists t'. split; auto.
      apply AtomicYieldStruct; auto.
    + specialize H with (length w1) w1 t. destruct H; auto.
      apply H in H6; auto.
      destruct H6 as [t']. destruct H2.
      exists [a0; t']. split.
      * apply PrefixYieldStruct; auto.
      * apply rtc_l with [a0; [|t; a]].
        **apply sc_rl. apply ReorderStepPrefixPostfix.
        **apply reorder_prefix_subtree. assumption.
    + simplify_list_eq. specialize H with (length wt) wt t1. destruct H; auto. {
        rewrite app_length. simpl. lia.
      }
      apply H0 in H7; auto. inv H7. inv H2.
      eexists. split; eauto.
      eapply ClosedYieldStruct; eauto.
  - simpl in *.
    inv H0.
    + specialize H with (length w1) w1 t2. destruct H; auto.
      apply H in H7; auto.
      destruct H7 as [t']. destruct H2.
      exists [ti; Some a0; t']. split.
      * apply InfixSomeYieldStruct; auto.
      * apply rtc_l with [ti; Some a0; [|t2; a]].
        **apply sc_rl. apply ReorderStepInfixPostfix.
        **apply reorder_infix_subtree2; assumption.
    + inv H3.
      * specialize H with (length w1) w1 t2. destruct H; auto.
        apply H0 in H7; auto.
        destruct H7 as [t']. destruct H3.
        exists [ti; None; t']. split.
        **apply InfixNoneYieldStruct; auto. apply AtomicYieldStruct; auto.
        **apply rtc_l with [ti; None; [|t2; a]].
          ***apply sc_rl. apply ReorderStepInfixPostfix.
          ***apply reorder_infix_subtree2; assumption.
      * specialize H with (length w1) w1 t. destruct H; auto.
        apply H in H7; auto.
        destruct H7. destruct H3.
        exists [ti; None; [a0; x]]. split.
        **apply InfixNoneYieldStruct; auto. apply PrefixYieldStruct; auto.
        **apply rtc_l with [ti; None; [|[a0; t]; a]].
          ***apply sc_rl. apply ReorderStepInfixPostfix.
          ***apply reorder_infix_subtree2.
            apply rtc_l with [a0; [|t; a]].
            ****apply sc_rl. apply ReorderStepPrefixPostfix.
            ****apply reorder_prefix_subtree. assumption.
      * simplify_list_eq.
        specialize H with (length wt) wt t2. destruct H; auto. {
          rewrite app_length. simpl. lia.
        }
        apply H0 in H8; auto. inv H8. inv H3.
        eexists. split.
        **apply InfixNoneYieldStruct; auto. eapply ClosedYieldStruct; eauto.
        **eapply rtc_l.
          ***apply sc_rl. apply ReorderStepInfixPostfix.
          ***apply reorder_infix_subtree2. assumption.
    + specialize H with (length w1) w1 t1. destruct H; auto.
      apply H0 in H7; auto.
      destruct H7 as [t']. destruct H2.
      exists t'. split; auto.
      apply PostfixYieldStruct; auto.
Qed.

Lemma yield_struct_sound t :
  wf t → exists t', ys (yield t) t' ∧ t ⟷* t'.
Proof.
  intro. induction H.
  - exists AN a. simpl. split.
    + apply AtomicYieldStruct; try assumption.
      apply NilYieldStruct.
    + apply rtc_refl.
  - simpl.
    destruct IHwell_formed_parse_tree1 as [t1']. destruct H2.
    destruct IHwell_formed_parse_tree2 as [t2']. destruct H4.
    destruct oa as [a|].
    + apply yield_struct_infix_sound with (yield t1) t1' (yield t2) t2' a in H2 as ?; auto.
      destruct H6 as [t]. destruct H6.
      exists t. split; auto.
      apply rtc_transitive with [t1'; Some a; t2].
      * apply reorder_infix_subtree1. assumption.
      * apply rtc_transitive with [t1'; Some a; t2']; auto.
        apply reorder_infix_subtree2. assumption.
    + apply yield_struct_app_sound with (yield t1) t1' (yield t2) t2' in H2 as ?; auto.
      destruct H6 as [t]. destruct H6.
      eexists. split; eauto.
      eapply rtc_transitive.
      * apply reorder_infix_subtree1. eassumption.
      * eapply rtc_transitive.
        **apply reorder_infix_subtree2. eassumption.
        **assumption.
  - destruct IHwell_formed_parse_tree as [t2']. destruct H1.
    simpl.
    exists [a; t2']. split.
    + apply PrefixYieldStruct; auto.
    + apply reorder_prefix_subtree. assumption.
  - destruct IHwell_formed_parse_tree as [t1']. destruct H1.
    simpl.
    apply yield_struct_postfix_sound with (yield t1) t1' a in H1; auto.
    destruct H1 as [t']. destruct H1.
    exists t'. split; auto.
    apply rtc_transitive with [|t1'; a]; auto.
    apply reorder_postfix_subtree. assumption.
  - destruct IHwell_formed_parse_tree as [t']. destruct H1.
    simpl.
    exists [(a1; t'; a2)]. split.
    + eapply ClosedYieldStruct; eauto.
      apply NilYieldStruct.
    + apply reorder_closed_subtree. assumption.
Qed.

Definition InfixSomeProduction a := InfixProduction (Some a).

Definition overlap (PType1 PType2 : T → production T) : Prop :=
  ∃ a, Productions g (PType1 a) ∧ Productions g (PType2 a).

Record harmless_overlap := mkHarmlessOverlap {
  harmless1 : overlap AtomicProduction PostfixProduction →
              overlap PostfixProduction InfixSomeProduction → False;
  harmless2 : overlap AtomicProduction PostfixProduction →
              overlap AtomicProduction PrefixProduction → False;
  harmless3 : overlap PrefixProduction InfixSomeProduction →
              overlap PostfixProduction InfixSomeProduction → False;
  harmless4 : overlap PrefixProduction InfixSomeProduction →
              overlap AtomicProduction PrefixProduction → False;
  harmless5 : Productions g (InfixProduction None) →
              overlap AtomicProduction InfixSomeProduction → False;
  harmless6 : Productions g (InfixProduction None) →
              overlap AtomicProduction PrefixProduction → False;
  harmless7 : Productions g (InfixProduction None) →
              overlap AtomicProduction PostfixProduction → False;
  harmless8 : Productions g (InfixProduction None) →
              overlap InfixSomeProduction PrefixProduction → False;
  harmless9 : Productions g (InfixProduction None) →
              overlap InfixSomeProduction PostfixProduction → False;
  harmless10 : Productions g (InfixProduction None) →
              overlap PrefixProduction PostfixProduction → False;
}.

Lemma yield_struct_closed_deterministic al ar w11 w12 w21 w22 t1 t2 :
  ClosedP al ar ->
  w11 ++ ar :: w12 = w21 ++ ar :: w22 ->
  (ys w11 t1 -> ys w21 t2 -> w11 = w21) /\
  (forall ti1 ti2, yss ti1 w11 t1 -> yss ti2 w21 t2 -> w11 = w21).
Proof.
  remember (length w11) as n. revert al ar w11 w12 w21 w22 t1 t2 Heqn.
  strong induction n. intros. split; intros.
  - inv H2.
    + inv H3; simpl in *.
      * inv H1. edestruct H with (n := length w); eauto.
        erewrite H3; eauto.
      * inv H1. admit (* overlap *).
      * inv H1. admit (* overlap *).
    + inv H3; simpl in *.
      * inv H1. admit (* overlap *).
      * inv H1. edestruct H with (n := length w); eauto.
        rewrite H1; eauto.
      * inv H1. admit (* overlap *).
    + inv H3; simpl in *.
      * inv H1. admit (* overlap *).
      * inv H1. admit (* overlap *).
      * inv H1. assert (a2 = a3). { admit (* overlap *). }
        subst. rewrite <- app_assoc in *. rewrite <- app_assoc in *. simpl in *.
        edestruct H with (n := (length w)); eauto. {
          rewrite app_length. lia.
        }
        assert (w = w0); eauto. subst.
        apply app_inj_1 in H10; auto. destruct H10. inv H10.
        edestruct H with (n := (length wt)) (al := al) (w11 := wt) (w21 := wt0); eauto. {
            rewrite app_length. simpl. lia.
        }
        erewrite H11; eauto.
  - inv H2; inv H3; simpl in *; auto.
    + inv H1. admit (* overlap *).
    + admit (* ignore empty infix op *).
    + inv H1. admit (* overlap *).
    + inv H1. admit (* overlap *).
    + inv H1. edestruct H with (n := length w); eauto.
      erewrite H1; eauto.
    + admit (* empty infix *).
    + inv H1. admit (*overlap*).
    + admit (* empty infix*).
    + admit (*empty infix*).
    + admit (*empty infix*).
    + admit (*empty infix*).
    + inv H1. admit (*overlap*).
    + inv H1. admit (*overlap*).
    + admit (*empty infix*).
    + inv H1.
      edestruct H with (n := length w); eauto.
      erewrite H3; eauto.
Admitted.

Lemma yield_struct_deterministic w t1 t2 :
  ys w t1 → ys w t2 → t1 = t2
with yield_some_struct_deterministic w t1 t2 ti :
  yss ti w t1 → yss ti w t2 → t1 = t2.
Proof.
  - intro. revert t2. induction H; intros.
    + inv H1; eauto.
      * admit. (* by overlap *)
      * admit. (* by overlap *)
    + inv H1.
      * admit (* by overlap *).
      * erewrite IHyield_struct; eauto.
      * admit. (* by overlap *)
    + inv H2.
      * admit. (* by overlap *)
      * admit. (* by overlap *)
      * assert (a2 = a3). { admit. (* by overlap *)  }
        subst. eapply yield_struct_closed_deterministic in H5; eauto.
        destruct H5. erewrite H2 in *; eauto.
        apply app_inj_1 in H4; auto. destruct H4. inv H5. clear H4 H2 H3.
        eapply yield_struct_deterministic in H0; eauto.
        subst.
        eauto.
  - intros. inv H; inv H0; auto.
    + admit (*empty infix*).
    + eapply yield_struct_deterministic in H2; eauto. subst. auto.
    + admit (*empty infix*).
    + admit (*overlap*).
    + admit (*empty infix*).
    + admit (*empty infix*).
    + admit (*empty infix*).
    + admit (*empty infix*).
    + admit (*overlap*).
    + admit (*empty infix*).
    + eapply yield_some_struct_deterministic; eauto.
Admitted.

Lemma rtsc_symmetry {A} (R : relation A) (x y : A) :
  rtsc R x y → rtsc R y x.
Proof.
  intros. induction H.
  - apply rtc_refl.
  - apply rtc_transitive with y.
    + assumption.
    + apply rtc_once. inv H.
      * apply sc_rl. assumption.
      * apply sc_lr. assumption.
Qed.

Lemma yield_reorder t1 t2 :
  harmless_overlap →
  wf t1 → wf t2 → yield t1 = yield t2 → t1 ⟷* t2.
Proof.
  intro Hharmless. intros.
  apply yield_struct_sound in H. destruct H as [t1']. destruct H.
  apply yield_struct_sound in H0. destruct H0 as [t2']. destruct H0.
  rewrite H1 in H. apply yield_struct_deterministic with (yield t2) t1' t2' in H; auto.
  subst.
  apply rtc_transitive with t2'; auto.
  apply rtsc_symmetry. assumption.
Qed.

End Experiment7.
