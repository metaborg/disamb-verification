From stdpp Require Export list.
From stdpp Require Export relations.
Require Import MyUtils.

Section Experiment3.


Inductive production Terminal :=
  | AtomicProduction : Terminal → production Terminal
  | InfixProduction : Terminal → production Terminal
  | PrefixProduction : Terminal → production Terminal
  | PostfixProduction : Terminal → production Terminal.

Global Arguments AtomicProduction {_} _.
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
Notation P := (Productions g).
Implicit Types p : production T.
Notation AtomP a := (P (AtomicProduction a)).
Notation InP a := (P (InfixProduction a)).
Notation PreP a := (P (PrefixProduction a)).
Notation PostP a := (P (PostfixProduction a)).


Definition word := list T.

Implicit Types w : word.

Inductive parse_tree :=
  | AtomicNode : T → parse_tree
  | InfixNode : parse_tree → T → parse_tree → parse_tree
  | PrefixNode : T → parse_tree → parse_tree
  | PostfixNode : parse_tree → T → parse_tree.

Notation PT := parse_tree.
Implicit Types t : PT.
Notation "'AN' a" := (AtomicNode a) (at level 3).
Notation "[ t1 ; a ; t2 ]" := (InfixNode t1 a t2).
Notation "[ a ; t2 ]" := (PrefixNode a t2).
Notation "[| t1 ; a ]" := (PostfixNode t1 a).

Inductive well_formed_parse_tree : PT → Prop :=
  | WellFormedAtomicNode a :
      AtomP a →
      well_formed_parse_tree (AN a)
  | WellFormedInfixNode t1 a t2 :
      InP a →
      well_formed_parse_tree t1 →
      well_formed_parse_tree t2 →
      well_formed_parse_tree [t1; a; t2]
  | WellFormedPrefixNode a t2 :
      PreP a →
      well_formed_parse_tree t2 →
      well_formed_parse_tree [a; t2]
  | WellFormedPostfixNode t1 a :
      PostP a →
      well_formed_parse_tree t1 →
      well_formed_parse_tree [|t1; a].

Notation wf t := (well_formed_parse_tree t).

Fixpoint yield t : word :=
  match t with
  | AN a => [a]
  | [t1; a; t2] => yield t1 ++ a :: yield t2
  | [a; t2] => a :: yield t2
  | [|t1; a] => yield t1 ++ [a]
  end.

Inductive reorder_step : PT → PT → Prop :=
  | ReorderStepInfix t1 t2 t3 a b :
      reorder_step [[t1; a; t2]; b; t3] [t1; a; [t2; b; t3]]
  | ReorderStepInfixPrefix t1 t2 a b :
      reorder_step [[a; t1]; b; t2] [a; [t1; b; t2]]
  | ReorderStepInfixPostfix t1 t2 a b :
      reorder_step [t1; a; [|t2; b]] [|[t1; a; t2]; b]
  | ReorderStepPrefixPostfix t a b :
      reorder_step [a; [|t; b]] [|[a; t]; b]
  | ReorderStepInfixSubtree1 t1 a t2 t1' :
      reorder_step t1 t1' →
      reorder_step [t1; a; t2] [t1'; a; t2]
  | ReorderStepInfixSubtree2 t1 a t2 t2' :
      reorder_step t2 t2' →
      reorder_step [t1; a; t2] [t1; a; t2']
  | ReorderStepPrefixSubtree a t2 t2' :
      reorder_step t2 t2' →
      reorder_step [a; t2] [a; t2']
  | ReorderStepPostfixSubtree a t1 t1' :
      reorder_step t1 t1' →
      reorder_step [|t1; a] [|t1'; a].

Notation "t1 ---> t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟶ t2" := (reorder_step t1 t2) (at level 75).

Definition reorder := rtsc (reorder_step).

Notation "t1 <--->* t2" := (reorder t1 t2) (at level 76).
Notation "t1 ⟷* t2" := (reorder t1 t2) (at level 76).

Inductive yield_struct : word → PT → Prop :=
  | AtomicYieldStruct l w t :
      AtomP l →
      yield_some_struct (AN l) w t →
      yield_struct (l :: w) t
  | PrefixYieldStruct o w t :
      PreP o →
      yield_struct w t →
      yield_struct (o :: w) [o; t]

with yield_some_struct : PT → word → PT → Prop :=
  | NilYieldStruct t :
      yield_some_struct t [] t
  | InfixYieldStruct t1 o t2 w :
      InP o →
      yield_struct w t2 →
      yield_some_struct t1 (o :: w) [t1; o; t2]
  | PostfixYieldStruct o w t1 t :
      PostP o →
      yield_some_struct [|t1; o] w t →
      yield_some_struct t1 (o :: w) t.

Notation "w 'Ψ' t" := (yield_struct w t) (at level 70).
Notation yss t w u := (yield_some_struct t w u).

Lemma reorder_infix_subtree1 t1 o t2 t1' :
  t1 ⟷* t1' →
  [t1; o; t2] ⟷* [t1'; o; t2].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [y; o; t2].
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree1. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree1. assumption.
    + assumption.
Qed.

Lemma reorder_infix_subtree2 t1 o t2 t2' :
  t2 ⟷* t2' →
  [t1; o; t2] ⟷* [t1; o; t2'].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [t1; o; y].
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

Inductive post_tree : PT → Prop :=
  | AtomicPostTree l :
      AtomP l →
      post_tree AN l
  | PostfixPostTree t a :
      PostP a →
      post_tree t →
      post_tree [|t; a].

Lemma yield_struct_app w1 t1 w2 t2 a :
  (w1 Ψ t1 → w2 Ψ t2 → InP a →
  ∃ t', (w1 ++ a :: w2) Ψ t' ∧ [t1; a; t2] ⟷* t')
  ∧
  (∀ ti, post_tree ti → yss ti w1 t1 → w2 Ψ t2 → InP a →
  ∃ t', yss ti (w1 ++ a :: w2) t' ∧ [t1; a; t2] ⟷* t').
Proof.
  revert t1. induction w1; intros; split; intros.
  - inv H.
  - inv H0.
    simpl.
    exists [t1; a; t2]. split.
    + apply InfixYieldStruct; assumption.
    + apply rtc_refl.
  - simpl.
    inv H.
    + specialize IHw1 with t1. destruct IHw1.
      apply H2 in H6; auto using AtomicPostTree.
      destruct H6 as [t']. destruct H3.
      exists t'. split; auto.
      apply AtomicYieldStruct; auto.
    + specialize IHw1 with t. destruct IHw1.
      apply H in H6; auto.
      destruct H6 as [t']. destruct H3.
      exists [a0; t']. split.
      * apply PrefixYieldStruct; auto.
      * apply rtc_l with [a0; [t; a; t2]].
        **apply sc_lr. apply ReorderStepInfixPrefix.
        **apply reorder_prefix_subtree. assumption.
  - simpl.
    inv H0.
    + specialize IHw1 with t3. destruct IHw1.
      apply H0 in H8; auto.
      destruct H8 as [t']. destruct H4.
      exists [ti; a0; t']. split.
      * apply InfixYieldStruct; auto.
      * apply rtc_l with [ti; a0; [t3; a; t2]].
        **apply sc_lr. apply ReorderStepInfix.
        **apply reorder_infix_subtree2; assumption.
    + specialize IHw1 with t1. destruct IHw1.
      apply H3 in H8; auto using PostfixPostTree.
      destruct H8 as [t']. destruct H4.
      exists t'. split; auto.
      apply PostfixYieldStruct; auto.
Qed.

Lemma yield_struct_tail w1 t1 a :
  (w1 Ψ t1 → PostP a →
  ∃ t', w1 ++ [a] Ψ t' ∧ [|t1; a] ⟷* t') ∧
  (∀ ti, post_tree ti → yss ti w1 t1 → PostP a →
  ∃ t', yss ti (w1 ++ [a]) t' ∧ [|t1; a] ⟷* t').
Proof.
  revert t1. induction w1; intros; split; intros.
  - inv H.
  - inv H0.
    simpl.
    exists [|t1; a]. split.
    + apply PostfixYieldStruct; auto. apply NilYieldStruct.
    + apply rtc_refl.
  - simpl.
    inv H.
    + specialize IHw1 with t1. destruct IHw1.
      apply H1 in H5; auto using AtomicPostTree.
      destruct H5 as [t']. destruct H2.
      exists t'. split; auto.
      apply AtomicYieldStruct; auto.
    + specialize IHw1 with t. destruct IHw1.
      apply H in H5; auto.
      destruct H5 as [t2']. destruct H2.
      exists [a0; t2']. split.
      * apply PrefixYieldStruct; auto.
      * apply rtc_l with [a0; [|t; a]].
        **apply sc_rl. apply ReorderStepPrefixPostfix.
        **apply reorder_prefix_subtree. assumption.
  - simpl.
    inv H0.
    + specialize IHw1 with t2. destruct IHw1.
      apply H0 in H7; auto.
      destruct H7 as [t2']. destruct H3.
      exists [ti; a0; t2']. split.
      * apply InfixYieldStruct; assumption.
      * apply rtc_l with [ti; a0; [|t2; a]].
        **apply sc_rl. apply ReorderStepInfixPostfix.
        **apply reorder_infix_subtree2. assumption.
    + specialize IHw1 with t1. destruct IHw1.
      apply H2 in H7; auto using PostfixPostTree.
      destruct H7 as [t']. destruct H3.
      exists t'. split; auto.
      apply PostfixYieldStruct; auto.
Qed.

Lemma yield_struct_sound t :
  wf t → exists t', yield t Ψ t' ∧ t ⟷* t'.
Proof.
  intro. induction H.
  - exists AN a. simpl. split.
    + apply AtomicYieldStruct; try assumption.
      apply NilYieldStruct.
    + apply rtc_refl.
  - simpl.
    destruct IHwell_formed_parse_tree1 as [t1']. destruct H2.
    destruct IHwell_formed_parse_tree2 as [t2']. destruct H4.
    apply yield_struct_app with (yield t1) t1' (yield t2) t2' a in H2 as ?; auto.
    destruct H6 as [t]. destruct H6.
    exists t. split; auto.
    apply rtc_transitive with [t1'; a; t2].
    + apply reorder_infix_subtree1. assumption.
    + apply rtc_transitive with [t1'; a; t2']; auto.
      apply reorder_infix_subtree2. assumption.
  - destruct IHwell_formed_parse_tree as [t2']. destruct H1.
    simpl.
    exists [a; t2']. split.
    + apply PrefixYieldStruct; auto.
    + apply reorder_prefix_subtree. assumption.
  - destruct IHwell_formed_parse_tree as [t1']. destruct H1.
    simpl.
    apply yield_struct_tail with (yield t1) t1' a in H1; auto.
    destruct H1 as [t']. destruct H1.
    exists t'. split; auto.
    apply rtc_transitive with [|t1'; a]; auto.
    apply reorder_postfix_subtree. assumption.
Qed.

Definition overlap (PType1 PType2 : T → production T) : Prop :=
  ∃ a, Productions g (PType1 a) ∧ Productions g (PType2 a).

Record harmless_overlap := mkHarmlessOverlap {
  harmless1 : overlap AtomicProduction PostfixProduction → overlap PostfixProduction InfixProduction → False;
  harmless2 : overlap AtomicProduction PostfixProduction → overlap AtomicProduction PrefixProduction → False;
  harmless3 : overlap PrefixProduction InfixProduction → overlap PostfixProduction InfixProduction → False;
  harmless4 : overlap PrefixProduction InfixProduction → overlap AtomicProduction PrefixProduction → False
}.

Lemma yield_struct_deterministic w t1 t2 :
  harmless_overlap →
  (w Ψ t1 → w Ψ t2 → t1 = t2) ∧
  (∀ ti, yss ti w t1 → yss ti w t2 → t1 = t2) ∧
  ((overlap PostfixProduction InfixProduction ∨ overlap AtomicProduction PrefixProduction) → 
    ∀ ti, w Ψ t1 → yss ti w t2 → False).
Proof.
  intro Hharmless. inv Hharmless. unfold overlap in *.
  revert t1 t2. induction w; intros; split; try split; intros.
  - inv H.
  - inv H. inv H0. reflexivity.
  - inv H0.
  - inv H.
    + inv H0.
      * specialize IHw with t1 t2. destruct IHw.
        eapply H0; eauto.
      * exfalso.
        specialize IHw with t t1. destruct IHw. destruct H0. eauto.
    + inv H0.
      * exfalso.
        specialize IHw with t t2. destruct IHw. destruct H0. eauto.
      * specialize IHw with t t0. destruct IHw.
        rewrite H; auto.
  - inv H.
    + inv H0.
      * specialize IHw with t3 t0. destruct IHw.
        rewrite H; auto.
      * exfalso.
        specialize IHw with t3 t2. destruct IHw. destruct H0. eauto.
    + inv H0.
      * exfalso.
        specialize IHw with t3 t1. destruct IHw. destruct H0. eauto.
      * specialize IHw with t1 t2. destruct IHw. destruct H0.
        eauto.
  - inv H0.
    + inv H1.
      * specialize IHw with t3 t1. destruct IHw. destruct H1. eauto.
      * destruct H; eauto.
    + inv H1.
      * destruct H; eauto.
      * specialize IHw with t t2. destruct IHw. destruct H1. eauto.
Qed.

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

End Experiment3.
