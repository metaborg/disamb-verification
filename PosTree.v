Require Export InfixGrammar.

(* 
  In this section we define a pos_tree. Such a tree, which we can also call an indexed
  parse tree, or positional parse tree, is an extension to an ordinary parse_tree. Each
  lexical symbol and operand symbol gets assigned a natural number, representing the index
  of the symbol. The goal is that each index will also be the index of the symbol that ends
  up in the yield of the tree.
*)

Section PosTree.
Context {L O : Type}.

Inductive pos_tree :=
  | PANode : L -> nat -> pos_tree
  | PINode : pos_tree -> O -> nat -> pos_tree -> pos_tree.

Implicit Types pt : pos_tree.

(* Definition of what it means for a pos_tree to be well-formed between a number n0 and n.
   n0 is the start index (inclusive) and n is the final index (exclusive). *)
Inductive wf_pos_tree : nat -> pos_tree -> nat -> Prop :=
  | Wfpos_PANode i l :
      wf_pos_tree i (PANode l i) (S i)
  | Wfpos_PINode i j k pt1 o pt2 :
      wf_pos_tree i pt1 j ->
      wf_pos_tree (S j) pt2 k ->
      wf_pos_tree i (PINode pt1 o j pt2) k.

(* This function transforms a pos_tree into and ordinary parse_tree by removing all
   indices. *)
Fixpoint unpos pt : parse_tree :=
  match pt with
  | PANode l _ => ANode l
  | PINode pt1 o _ pt2 => INode (unpos pt1) o (unpos pt2)
  end.
 
(* This function transforms an ordinary parse_tree into a pos_tree pt and number n, given
   some start index n0, such that the pos_tree is well-formed between n0 and n. *)
Fixpoint pos t (n0 : nat) : (pos_tree * nat) :=
  match t with
  | ANode l => (PANode l n0, S n0)
  | INode t1 o t2 => 
      let (pt1, i) := pos t1 n0 in
      let (pt2, n) := pos t2 (S i) in
      (PINode pt1 o i pt2, n)
  end.

(* (ith_symbol i s pt) states that symbol s is in pt with index i. *)
Inductive ith_symbol i : (L + O) -> pos_tree -> Prop :=
  | L_ith l :
      ith_symbol i (inl l) (PANode l i)
  | O_ith o pt1 pt2 :
      ith_symbol i (inr o) (PINode pt1 o i pt2)
  | S_ith_l s pt1 pt2 o j :
      ith_symbol i s pt1 ->
      ith_symbol i s (PINode pt1 o j pt2)
  | S_ith_r s pt1 pt2 o j :
      ith_symbol i s pt2 ->
      ith_symbol i s (PINode pt1 o j pt2).

(* Two pos_trees are position equivalent if and only if they have the same symbols on the
   same indices. *)
Definition pos_equivalent pt1 pt2 : Prop :=
  forall s i, ith_symbol i s pt1 <-> ith_symbol i s pt2.

End PosTree.

Create HintDb pos_tree.
Hint Resolve Wfpos_PANode : pos_tree.
Hint Resolve Wfpos_PINode : pos_tree.
Hint Resolve L_ith : pos_tree.
Hint Resolve O_ith : pos_tree.
Hint Resolve S_ith_l : pos_tree.
Hint Resolve S_ith_r : pos_tree.
