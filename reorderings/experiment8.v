From stdpp Require Export list.
From stdpp Require Export relations.
Load "Lib/StrongInduction".

Section Experiment8.

Ltac inv H := inversion H; clear H; subst.

Inductive production Terminal :=
  | ClosedProduction : Terminal → list Terminal → production Terminal
  | InfixProduction : Terminal → production Terminal
  | PrefixProduction : Terminal → production Terminal
  | PostfixProduction : Terminal → production Terminal.

Global Arguments ClosedProduction {_} _ _.
Global Arguments InfixProduction {_} _.
Global Arguments PrefixProduction {_} _.
Global Arguments PostfixProduction {_} _.

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
Notation ClosedP ahead acons := (P (ClosedProduction ahead acons)).
Notation InP a := (P (InfixProduction a)).
Notation PreP a := (P (PrefixProduction a)).
Notation PostP a := (P (PostfixProduction a)).


Definition word := list T.

Implicit Types w : word.

Inductive parse_tree :=
  | ClosedNode : T → parse_list → parse_tree
  | InfixNode : parse_tree → T → parse_tree → parse_tree
  | PrefixNode : T → parse_tree → parse_tree
  | PostfixNode : parse_tree → T → parse_tree
with parse_list :=
  | NilNode : parse_list
  | ConsNode : parse_tree → T → parse_list → parse_list.

Notation PT := parse_tree.
Implicit Types t : PT.
Notation PL := parse_list.
Implicit Types τ : PL.

Scheme parse_tree_list_rec := Induction for parse_tree Sort Prop
with parse_list_tree_rec := Induction for parse_list Sort Prop.

Notation CN := ClosedNode.
Notation IN := InfixNode.
Notation PeN := PrefixNode.
Notation PoN := PostfixNode.
Notation ϵ := NilNode.
Notation CoN := ConsNode.

Inductive well_formed_parse_tree : PT → Prop :=
  | WellFormedClosedNode ah ac τ :
      ClosedP ah ac →
      well_formed_parse_list ac τ →
      well_formed_parse_tree (CN ah τ)
  | WellFormedInfixNode t1 a t2 :
      InP a →
      well_formed_parse_tree t1 →
      well_formed_parse_tree t2 →
      well_formed_parse_tree (IN t1 a t2)
  | WellFormedPrefixNode a t2 :
      PreP a →
      well_formed_parse_tree t2 →
      well_formed_parse_tree (PeN a t2)
  | WellFormedPostfixNode t1 a :
      PostP a →
      well_formed_parse_tree t1 →
      well_formed_parse_tree (PoN t1 a)
with well_formed_parse_list : list T → PL → Prop :=
  | WellFormedNilNode :
      well_formed_parse_list [] ϵ
  | WellFormedConsNode a ac t τ :
      well_formed_parse_tree t →
      well_formed_parse_list ac τ →
      well_formed_parse_list (a :: ac) (CoN t a τ).

Scheme well_formed_parse_tree_list_rec := Induction for well_formed_parse_tree Sort Prop
with well_formed_parse_list_tree_rec := Induction for well_formed_parse_list Sort Prop.      

Notation wf t := (well_formed_parse_tree t).

Fixpoint yield t : word :=
  match t with
  | CN a τ => a :: yield_list τ
  | IN t1 a t2 => yield t1 ++ a :: yield t2
  | PeN a t => a :: yield t
  | PoN t a => yield t ++ [a]
  end
with yield_list τ : word :=
  match τ with
  | ϵ => []
  | CoN t a τ => yield t ++ a :: yield_list τ
  end.

Inductive reorder_step : PT → PT → Prop :=
  | ReorderStepInfix t1 t2 t3 a b :
      reorder_step (IN (IN t1 a t2) b t3) (IN t1 a (IN t2 b t3))
  | ReorderStepInfixPrefix t1 t2 a b :
      reorder_step (IN (PeN a t1) b t2) (PeN a (IN t1 b t2))
  | ReorderStepInfixPostfix t1 t2 a b :
      reorder_step (IN t1 a (PoN t2 b)) (PoN (IN t1 a t2) b)
  | ReorderStepPrefixPostfix t a b :
      reorder_step (PeN a (PoN t b)) (PoN (PeN a t) b)
  | ReorderStepInfixSubtree1 t1 a t2 t1' :
      reorder_step t1 t1' →
      reorder_step (IN t1 a t2) (IN t1' a t2)
  | ReorderStepInfixSubtree2 t1 a t2 t2' :
      reorder_step t2 t2' →
      reorder_step (IN t1 a t2) (IN t1 a t2')
  | ReorderStepPrefixSubtree a t2 t2' :
      reorder_step t2 t2' →
      reorder_step (PeN a t2) (PeN a t2')
  | ReorderStepPostfixSubtree a t1 t1' :
      reorder_step t1 t1' →
      reorder_step (PoN t1 a) (PoN t1' a)
  | ReorderStepClosedSubtree a τ τ' :
      reorder_step_list τ τ' →
      reorder_step (CN a τ) (CN a τ')
with reorder_step_list : PL → PL → Prop :=
  | ReorderStepConsSubtree1 t t' a τ :
      reorder_step t t' →
      reorder_step_list (CoN t a τ) (CoN t' a τ)
  | ReorderStepConsSubtree2 t a τ τ' :
      reorder_step_list τ τ' →
      reorder_step_list (CoN t a τ) (CoN t a τ').

Scheme reorder_step_tree_list_rec := Induction for reorder_step Sort Prop
with reorder_step_list_tree_rec := Induction for reorder_step_list Sort Prop.

Notation "t1 ---> t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟶ t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟷ t2" := ((sc reorder_step) t1 t2) (at level 75).

Definition reorder := rtsc (reorder_step).

Notation "t1 <--->* t2" := (reorder t1 t2) (at level 76).
Notation "t1 ⟷* t2" := (reorder t1 t2) (at level 76).

(* Lemma reorder_infix_subtree1 t1 oa t2 t1' :
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
Qed. *)

Inductive yield_struct : word → PT → Prop :=
  | ClosedYieldStruct :
      ClosedP ah ac →
      interleaving ac wi 
      yield_some_struct (AN l) w t →
      yield_struct (ah :: wi ++ wt) t'
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

Lemma yield_struct_closed_deterministic a b1 b2 v1 v2 w1 w2 tv tw (*tiv tv2*) :
  harmless_overlap →
  ClosedP a b1 → ClosedP a b2 → v1 ++ b1 :: v2 = w1 ++ b2 :: w2 → (* yss tiv v2 tv2 → *)
  (ys v1 tv → ys w1 tw → v1 = w1) ∧
  (∀ ti1 ti2, yss ti1 v1 tv → yss ti2 w1 tw → v1 = w1) ∧
  ((overlap PostfixProduction InfixSomeProduction ∨ overlap AtomicProduction PrefixProduction) →
      ∀ ti, ys v1 tv → yss ti w1 tw → False) ∧
  ((overlap PostfixProduction InfixSomeProduction ∨ overlap AtomicProduction PrefixProduction) →
      ∀ ti, yss ti v1 tv → ys w1 tw → False).
Proof.
  intro Hharmless. inv Hharmless. unfold overlap in *. unfold InfixSomeProduction in *.
  remember (length v1) as n. revert Heqn. revert a b1 b2 v1 v2 w1 w2 tv tw (*tiv tv2*). strong induction n.
  intros. (* rename H3 into Hv2 .*) split; try split; try split; intros.
  - inv H3; inv H4.
    + simplify_list_eq. edestruct H with (b1 := b1) (b2 := b2) (v1 := w) (w1 := w0); eauto. inv H8. erewrite H9; eauto.
    + simplify_list_eq. exfalso.
      edestruct H with (b1 := b1) (b2 := b2) (v1 := w) (w1 := w0); eauto. inv H8. inv H10. eauto.
    + simplify_list_eq. admit. (* TODO open closed + atomic overlap *)
    + simplify_list_eq. exfalso. 
      edestruct H with (b1 := b1) (b2 := b2) (v1 := w) (w1 := w0); eauto. inv H8. inv H10. eauto.
    + simplify_list_eq.
      edestruct H with (b1 := b1) (b2 := b2) (v1 := w) (w1 := w0); eauto. inv H8. erewrite H2; eauto.
    + simplify_list_eq. admit. (* TODO open closed + prefix overlap *)
    + simplify_list_eq. admit. (* TODO open closed + atomic overlap *)
    + simplify_list_eq. admit. (* TODO open closed + prefix overlap *)
    + simplify_list_eq.
      
      edestruct H with (n := length w) (b1 := a2) (b2 := a3) (v1 := w) (w1 := w0); eauto. {
        rewrite app_length. simpl. lia.
      }
      eapply H2 in H6; eauto. subst.
      simplify_list_eq.
      edestruct H with (length wt) a b1 b2 wt v2 wt0 w2 tv tw; auto. {
        rewrite app_length. simpl. lia.
      }
      inv H11. erewrite H12; eauto. 
  - inv H3; inv H4.
    + reflexivity.
    + simplify_list_eq. exfalso. admit. (* TODO close closed + infix overlap *)
    + simplify_list_eq. exfalso. inv H5.
      * simplify_list_eq. admit. (*TODO close closed + atomic overlap + infix none*)
      * simplify_list_eq. admit. (*TODO close closed + prefix overlap + infix none*)
      * simplify_list_eq. admit. (*TODO open closed + close closed + infix none*)
    + exfalso. simplify_list_eq. admit. (*TODO close closed + postfix*)
    + exfalso. simplify_list_eq. admit. (*TODO close closed + infix*)
    + simplify_list_eq.
      destruct H with (length w) a b1 b2 w v2 w0 w2 t2 t0; auto. rewrite H2; auto.
    + simpl in *. exfalso. inv H7.
      * simplify_list_eq.
        destruct H with (length w) a b1 b2 w v2 w0 w2 t2 t0; auto. inv H9. inv H11. eauto.
      * simplify_list_eq. eauto.
      * simplify_list_eq. admit. (*TODO open closed + infix + infix none*)
    + simplify_list_eq. exfalso.
      destruct H with (length w) a b1 b2 w v2 w0 w2 t2 tw; auto. inv H8. inv H10. eauto.
    + exfalso. simplify_list_eq. inv H6.
      * simplify_list_eq. admit. (*TODO close closed + atomic + infix none*)
      * simplify_list_eq. admit. (*TODO close closed + prefix + infix none*)
      * simplify_list_eq. admit. (*TODO open closed + close closed + infix none*)
    + exfalso. simplify_list_eq. inv H6.
      * simplify_list_eq. eauto.
      * simplify_list_eq. eauto.
      * simplify_list_eq. admit. (*TODO open close + infix + infix none*)
    + inv H6; inv H7; simplify_list_eq.
      * destruct H with (length w) a b1 b2 w v2 w0 w2 t2 t0; auto. inv H10.
        erewrite H11; eauto.
      * exfalso. eauto.
      * exfalso. admit. (*TODO open close + atomic + infix none*)
      * exfalso. eauto.
      * destruct H with (length w) a b1 b2 w v2 w0 w2 t t1; auto. rewrite H2; auto.
      * exfalso. admit. (*TODO: open close + prefix + infix none*)
      * exfalso. admit. (*TODO: open close + atomic + infix none*)
      * exfalso. admit. (*TODO: open close + prefix + infix none*)
      * edestruct H with (n := length w) (b1 := a2) (b2 := a3) (v1 := w) (w1 := w0); eauto. {
          rewrite app_length. simpl. lia.
        }
        eapply H2 in H8; eauto. subst. simplify_list_eq.
        edestruct H with (length wt) a b1 b2 wt v2 wt0 w2 t2 t0; auto. {
          rewrite app_length. simpl. lia.
        }
        inv H13. erewrite H14; eauto.
    + exfalso. inv H6; simplify_list_eq; eauto.
      admit. (*TODO open close + postfix + infix none*)
    + exfalso. simplify_list_eq. admit. (* TODO close closed + postfix *)
    + exfalso. simplify_list_eq.
      destruct H with (length w) a b1 b2 w v2 w0 w2 tv t2; auto.
      inv H8. inv H10. eauto.
    + exfalso. inv H7; simplify_list_eq; eauto.
      admit. (*TODO open closed + postfix + infix none*)
    + simplify_list_eq.
      destruct H with (length w) a b1 b2 w v2 w0 w2 tv tw; auto.
      inv H8. erewrite H9; eauto.
  - inv H4; inv H5; simplify_list_eq.
    + admit. (*TODO close closed + atomic*)
    + destruct H with (length w) a b1 b2 w v2 w0 w2 tv t2; auto.
      inv H9. inv H11. eauto.
    + inv H3; eauto. inv H5. inv H3. eauto.
    + inv H3; eauto.
    + admit. (*TODO close closed + prefix (+ assumptions)*)
    + inv H3; eauto.
    + inv H3; eauto. inv H5. inv H3; eauto.
    + destruct H with (length w) a b1 b2 w v2 w0 w2 t tw; auto.
      inv H9. inv H11. eauto.
    + admit. (*TODO open closed + close closed (+ assumptions)*)
    + admit. (*TODO open closed + infix (+ assumptions)*)
    + inv H3; eauto. inv H5. inv H3. eauto.
    + admit. (*TODO open closed + postfix (+ assumptions)*)
  - inv H4; inv H5; simplify_list_eq.
    + admit. (*TODO close closed + atomic (+ assumptions)*)
    + admit. (*TODO close closed + prefix (+ assumptions)*)
    + admit. (*TODO open closed + close closed (+ assumptions)*)
    + destruct H with (length w) a b1 b2 w v2 w0 w2 t2 tw; auto.
      inv H9. inv H11. eauto.
    + inv H3; eauto.
    + admit. (*TODO open closed + infix (+ assumptions)*)
    + inv H3; eauto. inv H5. inv H3; eauto.
    + inv H3; eauto. inv H5. inv H3; eauto.
    + inv H3; eauto. inv H5. inv H3; eauto.
    + inv H3; eauto.
    + destruct H with (length w) a b1 b2 w v2 w0 w2 tv t; auto.
      inv H9. inv H11. eauto.
    + admit. (*TODO open closed + postfix (+ assumptions)*)
Admitted.

Lemma yield_struct_deterministic w t1 t2 :
  harmless_overlap →
  (ys w t1 → ys w t2 → t1 = t2) ∧
  (∀ ti, yss ti w t1 → yss ti w t2 → t1 = t2) ∧
  ((overlap PostfixProduction InfixSomeProduction ∨ overlap AtomicProduction PrefixProduction) →
    ∀ ti, ys w t1 → yss ti w t2 → False).
Proof.
  intro Hharmless. assert (Hharmless' := Hharmless).
  inv Hharmless'. unfold overlap in *. unfold InfixSomeProduction in *.
  remember (length w) as n. revert Heqn. revert w t1 t2.
  strong induction n; intros. split; [intros|split; intros].
  - inv H0; inv H1; simpl in *.
    + specialize H with (length w0) w0 t1 t2.
      destruct H; auto. destruct H0. erewrite H0; eauto.
    + exfalso. specialize H with (length w0) w0 t t1.
      destruct H; auto. inv H0. eauto.
    + exfalso. admit. (* TODO open closed + atomic overlap *)
    + exfalso. specialize H with (length w0) w0 t t2.
      destruct H; auto. inv H0. eauto.
    + specialize H with (length w0) w0 t t0. destruct H; auto. rewrite H; auto.
    + exfalso. admit. (* TODO open closed + prefix overlap *)
    + exfalso. admit. (* TODO open closed + atomic overlap*)
    + exfalso. admit. (* TODO open closed + prefix overlap *)
    + eapply yield_struct_closed_deterministic in H5 as ?; eauto.
      inv H0. erewrite H1 in *; eauto. simplify_list_eq.
      clear H1 H8.
      destruct H with (length w0) w0 t t0; auto. {
        rewrite app_length. simpl. lia.
      }
      rewrite H0 in *; auto.
      clear H0 H1.
      destruct H with (length wt) wt t1 t2; auto. {
        rewrite app_length. simpl. lia.
      }
      inv H1. eapply H5; eauto.
  - inv H0; inv H1; simpl in *.
    + reflexivity.
    + inv H2.
    + destruct H with (length w0) w0 t3 t0; auto. rewrite H0; auto.
    + exfalso. inv H4; simpl in *.
      * eauto.
      * eauto.
      * admit. (*TODO open closed + infix + infix none*)
    + exfalso. destruct H with (length w0) w0 t3 t2; auto.
      inv H1. eauto.
    + inv H3.
    + exfalso. inv H3; simpl in *; eauto.
      admit. (*TODO open closed + infix + infix none*)
    + inv H3; inv H4; simpl in *.
      * destruct H with (length w0) w0 t3 t0; auto.
        inv H4. erewrite H6; eauto.
      * exfalso. eauto.
      * exfalso. admit. (*TODO open closed + atomic + infix none*)
      * exfalso. eauto.
      * destruct H with (length w0) w0 t t1; auto. rewrite H3; auto.
      * exfalso. admit. (*TODO open closed + prefix + infix none*)
      * exfalso. admit. (*TODO open closed + atomic + infix none*)
      * exfalso. admit. (*TODO open closed + prefix + infix none*)
      * eapply yield_struct_closed_deterministic in H7 as ?; eauto.
        inv H3. erewrite H4 in *; eauto. simplify_list_eq.
        clear H4 H10.
        destruct H with (length w0) w0 t t1; auto. {
          rewrite app_length. simpl. lia.
        }
        rewrite H3 in *; auto. clear H3 H4.
        destruct H with (length wt) wt t3 t0; auto. {
          rewrite app_length. simpl. lia.
        }
        inv H4. erewrite H7; eauto.
    + exfalso. inv H3; eauto.
      admit. (*TODO open closed + postfix + infix none*)
    + exfalso. destruct H with (length w0) w0 t3 t1; auto.
      inv H1. eauto.
    + exfalso. inv H4; eauto.
      admit. (*TODO open closed + postfix + infix none*)
    + destruct H with (length w0) w0 t1 t2; auto. inv H1. eapply H4; eauto.
  - inv H1; inv H2; simpl in *; eauto.
    + destruct H with (length w0) w0 t3 t1; auto. inv H2. eauto.
    + inv H0; eauto. inv H2. inv H0; eauto.
    + inv H0; eauto.
    + inv H0; eauto.
    + inv H0; eauto. inv H2. inv H0; eauto.
    + destruct H with (length w0) w0 t t2; auto. inv H2. eauto.
    + admit. (*TODO open closed + infix*)
    + inv H0; eauto. inv H2. inv H0; eauto.
    + admit. (*TODO open closed + postfix*)
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
