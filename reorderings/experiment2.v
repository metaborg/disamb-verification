From stdpp Require Export list.
From stdpp Require Export relations.
Require Import MyUtils.

Section Experiment2.


Inductive production Terminal :=
  | AtomicProduction : Terminal -> production Terminal
  | InfixProduction : Terminal -> production Terminal
  | PrefixProduction : Terminal -> production Terminal.

Global Arguments AtomicProduction {_} _.
Global Arguments InfixProduction {_} _.
Global Arguments PrefixProduction {_} _.

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


Definition word := list T.

Implicit Types w : word.

Inductive parse_tree :=
  | AtomicNode : T → parse_tree
  | InfixNode : parse_tree → T → parse_tree → parse_tree
  | PrefixNode : T → parse_tree → parse_tree.

Notation PT := parse_tree.
Implicit Types t : PT.
Notation "'AN' a" := (AtomicNode a) (at level 3).
Notation "[ t1 ; a ; t2 ]" := (InfixNode t1 a t2).
Notation "[ a ; t2 ]" := (PrefixNode a t2).

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
      well_formed_parse_tree [a; t2].

Notation wf t := (well_formed_parse_tree t).

Fixpoint yield t : word :=
  match t with
  | AN a => [a]
  | [t1; a; t2] => yield t1 ++ a :: yield t2
  | [a; t2] => a :: yield t2
  end.

Inductive reorder_step : PT → PT → Prop :=
  | ReorderStepInfix t1 t2 t3 a b :
      reorder_step [[t1; a; t2]; b; t3] [t1; a; [t2; b; t3]]
  | ReorderStepInfixPrefix t1 t2 a b :
      reorder_step [[a; t1]; b; t2] [a; [t1; b; t2]]
  | ReorderStepInfixSubtree1 t1 a t2 t1' :
      reorder_step t1 t1' →
      reorder_step [t1; a; t2] [t1'; a; t2]
  | ReorderStepInfixSubtree2 t1 a t2 t2' :
      reorder_step t2 t2' →
      reorder_step [t1; a; t2] [t1; a; t2']
  | ReorderStepPrefixSubtree a t2 t2' :
      reorder_step t2 t2' →
      reorder_step [a; t2] [a; t2'].

Notation "t1 ---> t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟶ t2" := (reorder_step t1 t2) (at level 75).

Definition reorder := rtsc (reorder_step).

Notation "t1 <--->* t2" := (reorder t1 t2) (at level 76).
Notation "t1 ⟷* t2" := (reorder t1 t2) (at level 76).

Inductive yield_struct : word -> PT -> Prop :=
  | AtomicYieldStruct l :
      AtomP l →
      yield_struct [l] (AN l)
  | InfixYieldStruct l o w t :
      AtomP l →
      InP o →
      yield_struct w t →
      yield_struct (l :: o :: w) [AN l; o; t]
  | PrefixYieldStruct o w t :
      PreP o →
      yield_struct w t →
      yield_struct (o :: w) [o; t].

Notation "w 'Ψ' t" := (yield_struct w t) (at level 70).

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

Lemma yield_struct_app w1 t1 w2 t2 a :
  w1 Ψ t1 → w2 Ψ t2 → InP a →
  ∃ t', w1 ++ a :: w2 Ψ t' ∧ [t1; a; t2] ⟷* t'.
Proof.
  intros. induction H.
  - simpl.
    exists [AN l; a; t2]. split.
    + apply InfixYieldStruct; assumption.
    + apply rtc_refl.
  - destruct IHyield_struct as [t2']. destruct H4.
    simpl.
    exists [AN l; o; t2']. split.
    + apply InfixYieldStruct; assumption.
    + apply rtc_l with [AN l; o; [t; a; t2]].
      * apply sc_lr. apply ReorderStepInfix.
      * apply reorder_infix_subtree2. assumption.
  - destruct IHyield_struct as [t2']. destruct H3.
    simpl.
    exists [o; t2']. split.
    + apply PrefixYieldStruct; assumption.
    + apply rtc_l with [o; [t; a; t2]].
      * apply sc_lr. apply ReorderStepInfixPrefix.
      * apply reorder_prefix_subtree. assumption.
Qed.

Lemma yield_struct_sound t :
  wf t → exists t', yield t Ψ t' ∧ t ⟷* t'.
Proof.
  intro. induction H.
  - exists AN a. simpl. split.
    + apply AtomicYieldStruct. assumption.
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
Qed.

Lemma yield_struct_deterministic w t1 t2 :
  w Ψ t1 → w Ψ t2 → t1 = t2.
Proof.
  intro. revert t2. induction H; intros.
  - inv H0.
    + reflexivity.
    + inv H5.
  - inv H2.
    + apply IHyield_struct in H9. rewrite H9. reflexivity.
    + exfalso. inv H7.
      * inv H1.
      * admit. (*Harmful overlap: l is in AtomP and PreP, o is in AtomP and InP*) 
      * admit. (*Harmful overlap: l is in AtomP and PreP, o is in PreP and InP*)
  - inv H1.
    + inv H0.
    + exfalso. inv H0.
      * inv H7.
      * admit. (*Harmful overlap: o is in AtomP and PreP, o0 is in AtomP and InP*)
      * admit. (*Harmful overlap: o is in AtomP and PreP, o0 is in PreP and InP*)
    + apply IHyield_struct in H6. subst. reflexivity.
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
  wf t1 → wf t2 → yield t1 = yield t2 → t1 ⟷* t2.
Proof.
  intros.
  apply yield_struct_sound in H. destruct H as [t1']. destruct H.
  apply yield_struct_sound in H0. destruct H0 as [t2']. destruct H0.
  rewrite H1 in H. apply yield_struct_deterministic with (yield t2) t1' t2' in H; auto.
  subst.
  apply rtc_transitive with t2'; auto.
  apply rtsc_symmetry. assumption.
Qed.

End Experiment2.
