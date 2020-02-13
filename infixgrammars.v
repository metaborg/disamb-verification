Require Import List.
Import ListNotations.

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

Inductive ex_lex :=
  | A
  | B
  | C.

Inductive ex_op :=
  | o
  | p
  | q.

Example yield_simple_infix :
  yield (INode (ANode A) o (ANode B)) = [inl A; inr o; inl B].
Proof. reflexivity. Qed.

Example yield_large_nested_infix :
  yield (INode (INode (ANode B) p (ANode C)) o (INode (ANode A) q (INode (ANode C) o (ANode B)))) 
  = [inl B; inr p; inl C; inr o; inl A; inr q; inl C; inr o; inl B].
Proof. reflexivity. Qed.

Definition language {L O} (w : word L O) : Prop :=
  exists pt, yield pt = w.

Example simple_infix_in_language :
  language [inl A; inr o; inl B].
Proof.
  exists (INode (ANode A) o (ANode B)).
  apply yield_simple_infix.
Qed.

Example large_nested_infix_in_language :
  language [inl B; inr p; inl C; inr o; inl A; inr q; inl C; inr o; inl B].
Proof.
  exists (INode (INode (ANode B) p (ANode C)) o (INode (ANode A) q (INode (ANode C) o (ANode B)))).
  apply yield_large_nested_infix.
Qed.

Lemma list_length_two {A} (l1 : list A) l2 l3 e1 e2 e1' e2' :
  l1 ++ e1 :: l2 ++ e2 :: l3 = [e1'; e2'] ->
  e1 = e1' /\ e2 = e2'.
intros.
  destruct l1; simpl in H.
  - inv H.
    destruct l2; simpl in H2.
    + inv H2.
      split; reflexivity.
    + inv H2.
      destruct l2; discriminate H1.
  - inv H.
    destruct l1; simpl in H2.
    + inv H2.
      destruct l2; discriminate H1.
    + inv H2.
      destruct l1; discriminate H1.
Qed.

Example lex_op_not_in_language :
  ~ language [inl A; inr o].
Proof.
  intro H.
  inv H.
  destruct x; simpl in H0.
  - discriminate H0.
  - destruct x1; simpl in H0.
    + destruct x2; simpl in H0.
      * discriminate H0.
      * destruct (yield x2_1); discriminate H0.
    + rewrite <- app_assoc in H0.
      simpl in H0.
      apply list_length_two in H0.
      destruct H0.
      discriminate H.
Qed. 

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

Definition dlanguage {L O} (g : dgrammar O) (w : word L O) : Prop :=
  exists pt,
    yield pt = w /\
    (
      forall o1 o2, g.(dleft) o1 o2 ->
      ~ sub_matches (IPatt NTPatt o1 (IPatt NTPatt o2 NTPatt)) pt
    ).

