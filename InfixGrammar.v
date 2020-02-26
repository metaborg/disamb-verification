From stdpp Require Import list.
Require Import List.
Import ListNotations.
Require Import Psatz.
Load "Lib/StrongInduction".

Ltac inv H := inversion H; clear H; subst.


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
Definition word (L O : Type) := list (L + O).

Inductive parse_tree (L O : Type) :=
  (* Atomic Nodes for atomic expressions. The leaves of the parse tree. *)
  | ANode : L -> parse_tree L O
  (* Infix Nodes for infix expressions. *)
  | INode : parse_tree L O -> O -> parse_tree L O -> parse_tree L O.

Arguments ANode {_ _} _.
Arguments INode {_ _} _ _ _.

(* yield pt gives the left-to-right concatenation of all the leaves of pt. *)
Fixpoint yield {L O} (pt : parse_tree L O) : word L O :=
  match pt with
  | ANode lex => [inl lex]
  | INode pt1 op pt2 => yield pt1 ++ inr op :: yield pt2
  end.

(* language w states that w is a sentence in the language generated by the grammar. *)
Definition language {L O} (w : word L O) : Prop :=
  exists pt, yield pt = w. 

Inductive tree_pattern (O : Type) :=
  (* Nonterminal pattern node. *)
  | NTPatt
  (* Infix pattern node. *)
  | IPatt : tree_pattern O -> O -> tree_pattern O -> tree_pattern O.

Arguments NTPatt {_}.
Arguments IPatt {_} _ _ _.

(* matches pt tp states that parse tree pt matches the tree pattern tp. *)
Inductive matches {L O} : parse_tree L O -> tree_pattern O ->  Prop :=
  (* Every parse tree matches the nonterminal pattern node. *)
  | NT_match pt :
      matches pt NTPatt
  (* Infix nodes match the infix pattern node only if its subtrees match and the operand
     word is equal. *)
  | INode_match tp1 tp2 pt1 pt2 o :
      matches pt1 tp1 ->
      matches pt2 tp2 -> 
      matches (INode pt1 o pt2) (IPatt tp1 o tp2).

(* matches pt tps states that parse tree pt matches one of the tree patterns in tps. *)
Definition matches_set {L O} (pt : parse_tree L O) (tps : tree_pattern O -> Prop) :=
  exists tp, tps tp /\ matches pt tp.

(* valid_pt tps pt states that a parse tree and all its subtrees should not match
   any patterns in tps. *)
Inductive valid_pt {L O} (tps : tree_pattern O -> Prop) : parse_tree L O  -> Prop :=
  | ANode_valid lex :
      ~ matches_set (ANode lex) tps ->
      valid_pt tps (ANode lex)
  | INode_valid pt1 o pt2 :
      ~ matches_set (INode pt1 o pt2) tps ->
      valid_pt tps pt1 ->
      valid_pt tps pt2 ->
      valid_pt tps (INode pt1 o pt2).

(* Disambiguation rules for Infix Expression Grammars *)
Record dgrammar (O : Type) := mkDgrammar {
  left_assoc : O -> O -> Prop
}.

Arguments left_assoc {_} _ _.

(* dpattern g tp states that tp is a subtree exclusion pattern for the grammar g.
   a main usage is (dpattern g) to simply get the set of tree patterns tps. *)
Inductive dpattern {O} (g : dgrammar O) : tree_pattern O -> Prop :=
  | Left o1 o2 :
      g.(left_assoc) o1 o2 ->
      dpattern g (IPatt NTPatt o1 (IPatt NTPatt o2 NTPatt)).

(* dlanguage g w states that w is a sentence in the disambiguated language generated by g. *)
Definition dlanguage {L O} (g : dgrammar O) (w : word L O) : Prop := 
  exists pt,
    yield pt = w /\ valid_pt (dpattern g) pt.

(* size pt gives the number of infix nodes in the parse tree. *)
Fixpoint size {L O} (pt : parse_tree L O) : nat :=
  match pt with
  | ANode _ => 0
  | INode pt1 _ pt2 => S (size pt1 + size pt2)
  end.

Definition total {O} (g : dgrammar O) : Prop :=
  forall o1 o2, g.(left_assoc) o1 o2.

Create HintDb valid_pt.
Hint Resolve ANode_valid : valid_pt.
Hint Resolve INode_valid : valid_pt.
Hint Resolve NT_match : valid_pt.
Hint Resolve INode_match : valid_pt.
Hint Resolve Left : valid_pt.

Section InfixGrammarTheorems.
Context {L O : Type}.
Implicit Types l : L.
Implicit Types g : dgrammar O.
Implicit Types pt : parse_tree L O.
Implicit Types w : word L O.

(* Atomic nodes are always valid under subtree exclusion. *)
Lemma valid_anode (g : dgrammar O) (lex : L) :
  valid_pt (dpattern g) (ANode lex).
Proof.
  apply ANode_valid.
  intro. inv H. inv H0. inv H1. inv H.
Qed.

(* For every parse tree, we can construct a parse tree that is
    - valid under subtree exclusion
    - has the same yield
    - has the same size
  
  We are only interested in the yield and valid parse tree, but the lemma has been made
  stronger to allow for a better induction hypothesis.

  NOTATION: We write pt' with the prime to denote the 'transformed' parse trees.
*)
Lemma safety_pt n g pt :
  size pt = n ->
  exists pt', size pt' = size pt /\ yield pt' = yield pt /\ valid_pt (dpattern g) pt'.
Proof.
  (* Proof by (strong) induction over the size of the parse tree. *)
  revert pt.
  strong induction n. intros.

  destruct pt as [lex|pt1 op1 pt2]; simpl in *.
  
  (* BASE CASE: pt = ANode lex *)
  - exists (ANode lex).
    split. reflexivity. split. reflexivity.
    apply valid_anode.

  (* INDUCTIVE CASE: pt = INode pt1 pt2 *)
  - (* pt1' is the valid version of pt1 *)
    destruct H with (n0 := size pt1) (pt := pt1) as (pt1'&[??]); [lia|reflexivity|].
    destruct H2.
    (* pt2' is the valid version of pt2 *)
    destruct H with (n0 := size pt2) (pt := pt2) as (pt2'&[??]); [lia|reflexivity|].
    destruct H5.

    destruct pt2' as [lex|pt2' op2 pt3']; simpl in *.
    (* CASE: pt2' = ANode lex *)
    + exists (INode pt1' op1 (ANode lex)).
      split; [|split].
      * simpl.
        lia.
      * simpl.
        rewrite H2.
        rewrite H5.
        reflexivity.
      * apply INode_valid; [|assumption|apply valid_anode].
        intro.
        inv H7. inv H8. inv H0. inv H7. inv H15.

    (* CASE: pt2' = INode pt2' op2 pt3' *)
    + (* pt2' and pt3' are valid *)
      destruct H with (n0 := size (INode pt1' op1 pt2')) (pt := INode pt1' op1 pt2')
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
      * apply INode_valid.

        ** intro. destruct H10 as [tp]. destruct H10.

           inv H6. destruct H15.
           unfold matches_set.
           exists tp. split. assumption.
           inv H10. inv H11.
           eauto with valid_pt.

        ** assumption.
        ** inv H6. assumption.
Qed.

(* For every sentence in a language, that sentence will still exist in the disambiguated
   language. *)
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

(* Trivial helper lemma *)
Lemma list_length_one {A} (l1 l2 : list A) (a1 a2 : A) :
  [a1] = l1 ++ a2 :: l2 -> a1 = a2.
Proof.
  intros.
  destruct l1; simpl in H.
  - inv H. reflexivity.
  - destruct l1; inv H.
Qed.

(* If we have a total set of disambiguation rules, then our grammar is unambiguous
  (for every sentence in the language there exists exactly one corresponding parse tree). *)
Theorem completeness g pt1 pt2 :
  total g ->
  valid_pt (dpattern g) pt1 ->
  valid_pt (dpattern g) pt2 ->
  yield pt1 = yield pt2 ->
  pt1 = pt2.
Proof.
  intro HTotal. unfold total in HTotal.
  intro HValidPt1.
  revert pt2.
  induction HValidPt1 as [lex|pt1_1 o1 pt1_2].
  - intros.
    destruct pt2; simpl in H1.
    + inv H1. reflexivity.
    + apply list_length_one in H1. inv H1.
  
  - intros.

    destruct pt2 as [lex|pt2_1 o2 pt2_2]; simpl in H1.
    + symmetry in H1. apply list_length_one in H1.
      inv H1.
    + inv H0.
      destruct pt2_2, pt1_2; simpl in H1.
      * simplify_list_eq.
        destruct IHHValidPt1_1 with (pt2 := pt2_1); auto.
      * specialize HTotal with (o1 := o1) (o2 := o).
        destruct H.
        unfold matches_set.
        eauto 10 with valid_pt.
      * specialize HTotal with (o1 := o2) (o2 := o).
        destruct H5.
        unfold matches_set.
        eauto 10 with valid_pt.
      * specialize HTotal with (o1 := o2) (o2 := o).
        destruct H5.
        unfold matches_set.
        eauto 10 with valid_pt.
Qed.

End InfixGrammarTheorems.
