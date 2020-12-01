From stdpp Require Export list.
From stdpp Require Export relations.

Section IGrammar.

(*
  An Infix Expression Grammar is a CFG where all productions have the following form:

  A = LEX       (atomic expressions)
  A = A op A    (infix expressions)

  A is the only nonterminal in the grammar. LEX and op are terminals, such that no operand
  symbol op, is LEX.

  In Coq, we define an infix expression grammar is as two types L (LEX) and O (op).
  Every possible instance l of L gives a production A = l. Similarly, every possible instance
  o of O gives a production A = A o A.
 *)


(* A word is a list of terminal symbols. *)
Definition word L O := list (L + O).

Inductive parse_tree L O :=
  (* Atomic Nodes for atomic expressions. The leaves of the parse tree. *)
  | ANode : L -> parse_tree L O
  (* Infix Nodes for infix expressions. *)
  | INode : parse_tree L O -> O -> parse_tree L O -> parse_tree L O.

Global Arguments ANode {_ _} _.
Global Arguments INode {_ _} _ _ _.

(* yield pt gives the left-to-right concatenation of all the leaves of pt. *)
Fixpoint yield {L O} t : word L O :=
  match t with
  | ANode lex => [inl lex]
  | INode t1 op t2 => yield t1 ++ inr op :: yield t2
  end.

(* language w states that w is a sentence in the language generated by the grammar. *)
Definition language {L O} (w : list (L + O)) : Prop :=
  exists (t : parse_tree L O), yield t = w.

Inductive tree_pattern O :=
  (* Nonterminal pattern node. *)
  | HPatt : tree_pattern O
  (* Infix pattern node. *)
  | IPatt : tree_pattern O -> O -> tree_pattern O -> tree_pattern O.

Global Arguments HPatt {_}.
Global Arguments IPatt {_} _ _ _.

(* matches t q states that parse tree t matches the tree pattern q. *)
Inductive matches {L O} : parse_tree L O -> tree_pattern O -> Prop :=
  (* Every parse tree matches the nonterminal pattern node. *)
  | HMatch t :
      matches t HPatt
  (* Infix nodes match the infix pattern node only if its subtrees match and the operand
     word is equal. *)
  | IMatch t1 t2 q1 q2 o :
      matches t1 q1 ->
      matches t2 q2 -> 
      matches (INode t1 o t2) (IPatt q1 o q2).

(* matches t qs states that parse tree t matches one of the tree patterns in qs. *)
Definition matches_set {L O} (t : parse_tree L O) (Q : tree_pattern O -> Prop) : Prop :=
  exists q : tree_pattern O, Q q /\ matches t q.

(* valid qs t states that a parse tree and all its subtrees should not match
   any patterns in qs. *)
Inductive conflict_free {L O} (Q : tree_pattern O -> Prop) : parse_tree L O -> Prop :=
  | ANode_cfree l :
      conflict_free Q (ANode l)
  | INode_cfree t1 o t2 :
      ~ matches_set (INode t1 o t2) Q ->
      conflict_free Q t1 ->
      conflict_free Q t2 ->
      conflict_free Q (INode t1 o t2).

Record drules (O : Type) := mkDrules {
  prio : O -> O -> Prop;
  left_a : O -> O -> Prop;
  right_a : O -> O -> Prop;

  prio_dec : RelDecision prio;
  left_a_dec : RelDecision left_a;
  right_a_dec : RelDecision right_a;
}.
Global Existing Instances prio_dec left_a_dec right_a_dec.

Global Arguments prio {_} _ _ _.
Global Arguments left_a {_} _ _ _.
Global Arguments right_a {_} _ _ _.

Definition CL {O} (o1 o2 : O) : tree_pattern O :=
  IPatt (IPatt HPatt o2 HPatt) o1 HPatt.
Definition CR {O} (o1 o2 : O) : tree_pattern O :=
  IPatt HPatt o1 (IPatt HPatt o2 HPatt).

Inductive conflict_pattern {O} (pr : drules O) : tree_pattern O -> Prop :=
  | CPrio1 (o1 o2 : O) :
      pr.(prio) o1 o2 ->
      conflict_pattern pr (CL o1 o2)
  | CPrio2 o1 o2 :
      pr.(prio) o1 o2 ->
      conflict_pattern pr (CR o1 o2)
  | CLeft o1 o2 : 
      pr.(left_a) o1 o2 ->
      conflict_pattern pr (CR o1 o2)
  | CRight o1 o2 : 
      pr.(right_a) o1 o2 ->
      conflict_pattern pr (CL o1 o2).

Definition dlanguage {L O} (pr : drules O) (w : list (L + O)) : Prop :=
  exists t : parse_tree L O, yield t = w /\ conflict_free (conflict_pattern pr) t.

Definition safe {L O} (pr : drules O) : Prop :=
  forall w : list (L + O), language w -> dlanguage pr w.

Definition safe_pr {O} (pr : drules O) : Prop :=
  forall o1 o2,
    (pr.(prio) o1 o2 \/ pr.(left_a) o1 o2) ->
    (pr.(prio) o2 o1 \/ pr.(right_a) o2 o1) ->
    False.

Definition complete_pr {O} (pr : drules O) : Prop :=
  forall o1 o2,
    pr.(prio) o1 o2 \/ pr.(left_a) o1 o2 \/
    pr.(prio) o2 o1 \/ pr.(right_a) o2 o1.

End IGrammar.


Section IGrammarFix.

Definition is_conflict_pattern {O} (pr : drules O) (q : tree_pattern O) :=
  match q with
  | IPatt (IPatt HPatt o2 HPatt) o1 HPatt =>
      if decide (pr.(prio) o1 o2) then true
      else if decide (pr.(right_a) o1 o2) then true
      else false
  | IPatt HPatt o1 (IPatt HPatt o2 HPatt) =>
      if decide (pr.(prio) o1 o2) then true
      else if decide (pr.(left_a) o1 o2) then true
      else false
  | _ => false
  end.

Fixpoint linsert_one {L O} (pr : drules O) l1 o1 t : parse_tree L O :=
  match t with
  | ANode l2 => INode (ANode l1) o1 (ANode l2)
  | INode t1 o2 t2 =>
      if is_conflict_pattern pr (CR o1 o2)
      then INode (linsert_one pr l1 o1 t1) o2 t2
      else INode (ANode l1) o1 (INode t1 o2 t2)
  end.

Fixpoint linsert {L O} (pr : drules O) t1 o t2 : parse_tree L O :=
  match t1 with
  | ANode l => linsert_one pr l o t2
  | INode t11 o1 t12 => linsert pr t11 o1 (linsert pr t12 o t2)
  end.

Fixpoint fix_tree {L O} (pr : drules O) t : parse_tree L O :=
  match t with
  | ANode l => ANode l
  | INode t1 o t2 => linsert pr t1 o (fix_tree pr t2)
  end.

Fixpoint simpleton_linsert {L O} (pr : drules O) t1 o t2 : parse_tree L O :=
  match t2 with
  | ANode l2 => INode t1 o (ANode l2)
  | INode t21 o2 t22 =>
      if is_conflict_pattern pr (CR o o2)
      then INode (simpleton_linsert pr t1 o t21) o2 t22
      else INode t1 o (INode t21 o2 t22)
  end.

Inductive complete_conflicts {O} (Q : tree_pattern O -> Prop) : tree_pattern O -> Prop :=
  | QSelf q :
      Q q ->
      complete_conflicts Q q
  | CR_CL o1 o2 :
      ~ Q (CR o1 o2) ->
      complete_conflicts Q (CL o2 o1)
  | CL_CR o1 o2 :
      ~ Q (CL o1 o2) ->
      complete_conflicts Q (CR o2 o1).

Definition complete_tree {L O} (Q : tree_pattern O -> Prop) (t : parse_tree L O) : Prop :=
  conflict_free (complete_conflicts Q) t.

Fixpoint tree_size {L O} (t : parse_tree L O) : nat :=
  match t with
  | ANode l => 0
  | INode t1 o t2 => S (tree_size t1 + tree_size t2)
  end.

End IGrammarFix.
