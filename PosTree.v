Require Export InfixGrammar.
Require Import Utils.
From stdpp Require Import list.

Section PosTree.
Context {L O : Type}.

Inductive pos_tree :=
  | PANode : L -> nat -> pos_tree
  | PINode : pos_tree -> O -> nat -> pos_tree -> pos_tree.

Implicit Types pt : pos_tree.

Inductive wf_pos_tree : nat -> pos_tree -> nat -> Prop :=
  | Wfpos_PANode i l :
      wf_pos_tree i (PANode l i) (S i)
  | Wfpos_PINode i j k pt1 o pt2 :
      wf_pos_tree i pt1 j ->
      wf_pos_tree (S j) pt2 k ->
      wf_pos_tree i (PINode pt1 o j pt2) k.

Inductive nth_symbol n : (L + O) -> pos_tree -> Prop :=
  | L_nth l :
      nth_symbol n (inl l) (PANode l n)
  | O_nth o pt1 pt2 :
      nth_symbol n (inr o) (PINode pt1 o n pt2)
  | Symbol_nth1 s pt1 pt2 o i :
      nth_symbol n s pt1 ->
      nth_symbol n s (PINode pt1 o i pt2)
  | Symbol_nth2 s pt1 pt2 o i :
      nth_symbol n s pt2 ->
      nth_symbol n s (PINode pt1 o i pt2).

Fixpoint unpos pt : parse_tree :=
  match pt with
  | PANode l _ => ANode l
  | PINode pt1 o _ pt2 => INode (unpos pt1) o (unpos pt2)
  end.

Fixpoint pos t (n0 : nat) : (pos_tree * nat) :=
  match t with
  | ANode l => (PANode l n0, S n0)
  | INode t1 o t2 => 
      let (pt1, i) := pos t1 n0 in
      let (pt2, n) := pos t2 (S i) in
      (PINode pt1 o i pt2, n)
  end.

Definition pos_equivalent pt1 pt2 : Prop :=
  forall s i, nth_symbol i s pt1 <-> nth_symbol i s pt2.

End PosTree.
