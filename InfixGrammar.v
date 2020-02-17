Require Import List.
Import ListNotations.
Load "Lib/StrongInduction".
Require Import Psatz.

Ltac inv H := inversion H; clear H; subst.

Definition word (L O : Type) := list (L + O).

Inductive parse_tree (L O : Type) :=
  | ANode : L -> parse_tree L O
  | INode : parse_tree L O -> O -> parse_tree L O -> parse_tree L O.

Arguments ANode {_ _} _.
Arguments INode {_ _} _ _ _.

Fixpoint yield {L O} (pt : parse_tree L O) : word L O :=
  match pt with
  | ANode lex => [inl lex]
  | INode pt1 op pt2 => yield pt1 ++ inr op :: yield pt2
  end.

Definition language {L O} (w : word L O) : Prop :=
  exists pt, yield pt = w. 

Inductive tree_pattern (O : Type) :=
  | NTPatt
  | IPatt : tree_pattern O -> O -> tree_pattern O -> tree_pattern O.

Arguments NTPatt {_}.
Arguments IPatt {_} _ _ _.

Inductive matches {L O} : tree_pattern O -> parse_tree L O -> Prop :=
  | NT_match pt :
      matches NTPatt pt
  | INode_match tp1 tp2 pt1 pt2 o :
      matches tp1 pt1 ->
      matches tp2 pt2 -> 
      matches (IPatt tp1 o tp2) (INode pt1 o pt2).

Inductive sub_matches {L O} : tree_pattern O -> parse_tree L O -> Prop :=
  | Refl_match tp pt :
      matches tp pt ->
      sub_matches tp pt
  | LSub_match tp pt1 o pt2 :
      sub_matches tp pt1 ->
      sub_matches tp (INode pt1 o pt2)
  | RSub_match tp pt1 o pt2 :
      sub_matches tp pt2 ->
      sub_matches tp (INode pt1 o pt2).

Record dgrammar (O : Type) := mkDgrammar {
  dleft : O -> O -> Prop
}.

Arguments dleft {_} _ _.

Definition valid_pt {L O} (g : dgrammar O) (pt : parse_tree L O) : Prop :=
  forall o1 o2, g.(dleft) o1 o2 ->
    ~ sub_matches (IPatt NTPatt o1 (IPatt NTPatt o2 NTPatt)) pt.

Definition dlanguage {L O} (g : dgrammar O) (w : word L O) : Prop :=
  exists pt,
    yield pt = w /\ valid_pt g pt.

Fixpoint size {L O} (pt : parse_tree L O) : nat :=
  match pt with
  | ANode _ => 0
  | INode pt1 _ pt2 => S (size pt1 + size pt2)
  end.

Section InfixGrammarTheorems.
Context {L O : Type}.
Implicit Types l : L.
Implicit Types g : dgrammar O.
Implicit Types pt : parse_tree L O.
Implicit Types w : word L O.

Lemma yield_infix_left pt1 pt1' pt2 o :
  yield pt1 = yield pt1' ->
  yield (INode pt1 o pt2) = yield (INode pt1' o pt2).
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma yield_infix_right pt1 pt2 pt2' o :
  yield pt2 = yield pt2' ->
  yield (INode pt1 o pt2) = yield (INode pt1 o pt2').
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma yield_infix pt1 pt2 pt1' pt2' o :
  yield pt1 = yield pt1' ->
  yield pt2 = yield pt2' ->
  yield (INode pt1 o pt2) = yield (INode pt1' o pt2').
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma yield_eq_nested_infix pt1 pt2 pt3 o1 o2 :
  yield (INode (INode pt1 o1 pt2) o2 pt3) = yield (INode pt1 o1 (INode pt2 o2 pt3)).
Proof.
  simpl.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma safety_atomic_pt g l :
  valid_pt g (ANode l).
Proof.
  unfold valid_pt.
  intros.
  intro N.
  inv N.
  inv H0.
Qed.

Lemma valid_pt_valid_st g pt1 pt2 o :
  valid_pt g (INode pt1 o pt2) -> valid_pt g pt1 /\ valid_pt g pt2.
Proof.
  unfold valid_pt.
  intros.
  split; intros; intro N; destruct H with (o1 := o1) (o2 := o2).
  - assumption.
  - apply LSub_match.
    assumption.
  - assumption.
  - apply RSub_match.
    assumption.
Qed.

Lemma safety_pt n g pt :
  size pt = n ->
  exists pt', size pt' = size pt /\ yield pt' = yield pt /\ valid_pt g pt'.
Proof.
  revert pt.
  strong induction n.

  intros.

  destruct pt as [lex|pt1 op1 pt2]; simpl in *. 
  - exists (ANode lex).
    split; [|split].
    + reflexivity.
    + reflexivity.
    + apply safety_atomic_pt.

  - destruct H with (n0 := size pt1) (pt := pt1) as (pt1'&[??]); [lia|reflexivity|].
    destruct H2.
    destruct H with (n0 := size pt2) (pt := pt2) as (pt2'&[??]); [lia|reflexivity|].
    destruct H5.
    destruct pt2' as [lex|pt2' op2 pt3']; simpl in *.
    + exists (INode pt1' op1 (ANode lex)).
      split; [|split].
      * simpl.
        lia.
      * simpl.
        rewrite H2.
        rewrite H5.
        reflexivity.
      * unfold valid_pt.
        intros.
        intro N.
        inv N.
        ** inv H8.
           inv H15.
        ** destruct H3 with (o1 := o1) (o2 := o2); assumption.
        ** inv H10.
           inv H0.

    + destruct H with (n0 := size (INode pt1' op1 pt2')) (pt := INode pt1' op1 pt2')
        as (pt1''&[??]). simpl. lia. reflexivity.
      
      destruct H8.
      simpl in *.

      exists (INode pt1'' op2 pt3').
      split; [|split].
      * simpl. lia.
      * simpl.
        rewrite <- H2.
        rewrite <- H5.
        rewrite H8.
        rewrite <- app_assoc.
        reflexivity.
      * unfold valid_pt.
        intros.
        intro N.
        apply valid_pt_valid_st in H6 as H11.
        destruct H11.
        inv N.
        ** inv H13.
           unfold valid_pt in H6.
           destruct H6 with (o1 := op2) (o2 := o2). assumption.
           apply Refl_match.
           apply INode_match.
           *** apply NT_match.
           *** assumption.
        ** unfold valid_pt in H9.
           destruct H9 with (o1 := o1) (o2 := o2). assumption.
           assumption.
        ** unfold valid_pt in H12.
           destruct H12 with (o1 := o1) (o2 := o2). assumption.
           assumption.
Qed.


Theorem safety g w :
  language w -> dlanguage g w.
Proof.
  unfold language.
  unfold dlanguage.
  intros.
  destruct H as [pt].
  rewrite <- H.
  specialize safety_pt with (n := size pt) (g := g) (pt := pt). intros.
  destruct H0. reflexivity.
  destruct H0. destruct H1.
  exists x. split; assumption.
Qed.

End InfixGrammarTheorems.