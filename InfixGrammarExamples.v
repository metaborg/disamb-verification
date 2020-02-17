Load InfixGrammar.

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
