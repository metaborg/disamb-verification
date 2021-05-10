From stdpp Require Export list.
From stdpp Require Export relations.
Require Import MyUtils.

Section Experiment.


Inductive production Terminal :=
  | AtomicProduction : Terminal -> production Terminal
  | InfixProduction : Terminal -> production Terminal.

Global Arguments AtomicProduction {_} _.
Global Arguments InfixProduction {_} _.

Record grammar := mkGrammar {
  Terminal : Type;
  Productions: production Terminal -> Prop;
}.

Context {g : grammar}.
Notation T := (Terminal g).
Implicit Types a b c : T.
Notation P := (Productions g).
Implicit Types p : production T.
Notation AP a := (P (AtomicProduction a)).
Notation IP a := (P (InfixProduction a)).


Definition word := list T.

Implicit Types w : word.

Inductive parse_tree :=
  | AtomicNode : T -> parse_tree
  | InfixNode : parse_tree -> T -> parse_tree -> parse_tree.

Notation PT := parse_tree.
Implicit Types t : PT.
Notation "'AN' a" := (AtomicNode a) (at level 3).
Notation "[ t1 ; a ; t2 ]" := (InfixNode t1 a t2).

Inductive well_formed_parse_tree : PT -> Prop :=
  | WellFormedAtomicNode a :
      AP a ->
      well_formed_parse_tree (AN a)
  | WellFormedInfixNode t1 a t2 :
      IP a ->
      well_formed_parse_tree t1 ->
      well_formed_parse_tree t2 ->
      well_formed_parse_tree [t1; a; t2].

Notation wf t := (well_formed_parse_tree t).

Fixpoint yield t : word :=
  match t with
  | AN a => [a]
  | [t1; a; t2] => yield t1 ++ a :: yield t2
  end.

Inductive reorder_step : PT -> PT -> Prop :=
  | ReorderStep1 t1 t2 t3 a b :
      reorder_step [[t1; a; t2]; b; t3] [t1; a; [t2; b; t3]]
  | ReorderStep2 t1 a t2 t1' :
      reorder_step t1 t1' ->
      reorder_step [t1; a; t2] [t1'; a; t2]
  | ReorderStep3 t1 a t2 t2' :
      reorder_step t2 t2' ->
      reorder_step [t1; a; t2] [t1; a; t2'].

Notation "t1 ---> t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟶ t2" := (reorder_step t1 t2) (at level 75).

Definition reorder := rtsc (reorder_step).

Notation "t1 <--->* t2" := (reorder t1 t2) (at level 76).
Notation "t1 ⟷* t2" := (reorder t1 t2) (at level 76).

Inductive yield_struct : word -> PT -> Prop :=
  | AtomicYieldStruct l :
      AP l ->
      yield_struct [l] (AN l)
  | InfixYieldStruct l o w t :
      AP l ->
      IP o ->
      yield_struct w t ->
      yield_struct (l :: o :: w) [AN l; o; t].

Notation "w 'Ψ' t" := (yield_struct w t) (at level 70).

Lemma reorder_subtree1 t1 o t2 t1' :
  t1 ⟷* t1' →
  [t1; o; t2] ⟷* [t1'; o; t2].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [y; o; t2].
    + inv H. 
      * apply sc_lr. apply ReorderStep2. assumption.
      * apply sc_rl. apply ReorderStep2. assumption.
    + assumption.
Qed.

Lemma reorder_subtree2 t1 o t2 t2' :
  t2 ⟷* t2' →
  [t1; o; t2] ⟷* [t1; o; t2'].
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with [t1; o; y].
    + inv H. 
      * apply sc_lr. apply ReorderStep3. assumption.
      * apply sc_rl. apply ReorderStep3. assumption.
    + assumption.
Qed.

Lemma yield_struct_app w1 t1 w2 t2 a :
  w1 Ψ t1 → w2 Ψ t2 → IP a →
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
      * apply sc_lr. apply ReorderStep1.
      * apply reorder_subtree2. assumption.
Qed.

Lemma yield_struct_sound t :
  wf t → exists t', yield t Ψ t' ∧ t <--->* t'.
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
    + apply reorder_subtree1. assumption.
    + apply rtc_transitive with [t1'; a; t2']; auto.
      apply reorder_subtree2. assumption.
Qed.

Lemma yield_struct_deterministic w t1 t2 :
  w Ψ t1 → w Ψ t2 → t1 = t2.
Proof.
  intro. revert t2. induction H; intros.
  - inv H0. reflexivity.
  - inv H2. apply IHyield_struct in H9. rewrite H9. reflexivity.
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

End Experiment.
