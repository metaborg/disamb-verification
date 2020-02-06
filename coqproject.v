Require Import List.
Import ListNotations.

Ltac inv H := inversion H; clear H; subst.

Record grammar (L O : Type) := mkGrammar {
  c_p : O -> O -> Prop;
  i_p : O -> Prop
}.

Arguments c_p {_ _} _ _ _.
Arguments i_p {_ _} _ _.

Definition word (L O : Type) := list (L + O).

(* Big-step derivation to a word *)
Inductive derives_big {L O} (g : grammar L O): word L O -> Prop :=
  | Atomic_der_big (lex : L) :
      derives_big g [inl lex]
  | Closed_der_big op1 op2 w :
      g.(c_p) op1 op2 ->
      derives_big g w ->
      derives_big g (inr op1 :: w ++ [inr op2])
  | Infix_der_big op w1 w2 :
      g.(i_p) op ->
      derives_big g w1 ->
      derives_big g w2 ->
      derives_big g (w1 ++ inr op :: w2).

Inductive parse_tree (L O : Type) :=
  | ANode : L -> parse_tree L O
  | CNode : O -> parse_tree L O -> O -> parse_tree L O
  | INode : parse_tree L O -> O -> parse_tree L O -> parse_tree L O.

Arguments ANode {_ _} _.
Arguments CNode {_ _} _ _ _.
Arguments INode {_ _} _ _ _.

Fixpoint yield {L O} (pt : parse_tree L O) : word L O :=
  match pt with
  | ANode lex => [inl lex]
  | CNode op1 pt op2  => inr op1 :: yield pt ++ [inr op2]
  | INode pt1 op pt2 => yield pt1 ++ inr op :: yield pt2
  end.

(* Well-formed parse trees *)
Inductive wf_tree {L O} (g : grammar L O) : parse_tree L O -> Prop := 
  | ANode_wf lex :
      wf_tree g (ANode lex)
  | CNode_wf op1 pt op2 :
      g.(c_p) op1 op2 ->
      wf_tree g pt ->
      wf_tree g (CNode op1 pt op2)
  | INode_wf pt1 op pt2 :
      g.(i_p) op ->
      wf_tree g pt1 ->
      wf_tree g pt2 ->
      wf_tree g (INode pt1 op pt2).

Inductive nonterminal :=
  | NT.
(* Sentential form *)
Definition sform (L O : Type) := list (L + O + nonterminal).

(* One-step derivation *)
Inductive derives_one {L O} (g : grammar L O) : sform L O -> sform L O -> Prop :=
  | Atomic_der_one lex s_l s_r:
      derives_one g
        (s_l ++ inr NT :: s_r)
        (s_l ++ inl lex :: s_r)
  | Closed_der_one op1 op2 s_l s_r :
      g.(c_p) op1 op2 ->
      derives_one g
        (s_l ++ inr NT :: s_r)
        (s_l ++ inl (inr op1) :: inr NT :: inl (inr op2) :: s_r)
  | Infix_der_one op s_l s_r :
      g.(i_p) op ->
      derives_one g
        (s_l ++ inr NT :: s_r)
        (s_l ++ inr NT :: inl (inr op) :: inr NT :: s_r).

(* Small-step derivation (reflexive and transitive closure of one-step) *)
Inductive derives_small {L O} (g : grammar L O) : sform L O -> sform L O -> Prop :=
  | Refl_der s :
      derives_small g s s
  | Trans_der s s' s'':
      derives_one g s s' ->
      derives_small g s' s'' ->
      derives_small g s s''.

Fixpoint word_to_sform {L O} (w : word L O) : sform L O :=
  match w with
  | [] => []
  | sym :: w => inl sym :: word_to_sform w
  end.


  (* 
    THEOREMS THEOREMS THEOREMS THEOREMS THEOREMS THEOREMS THEOREMS
    THEOREMS THEOREMS THEOREMS THEOREMS THEOREMS THEOREMS THEOREMS
   *)

Section grammar_theorems.
Context {L O : Type}.
Implicit Types g : grammar L O.
Implicit Types pt : parse_tree L O.
Implicit Types w : word L O.
Implicit Types s : sform L O.

(* If a tree is well-formed, then the grammar big-derives its yield *)
Theorem wf_tree_yield_derives_big g pt :
  wf_tree g pt -> derives_big g (yield pt).
Proof.
  intros.
  induction H.
  - eapply Atomic_der_big.
  - eapply Closed_der_big.
    + assumption.
    + assumption.
  - eapply Infix_der_big.
    + assumption.
    + assumption.
    + assumption.
Qed.

(* If a grammar big-derives a word w, 
then there is a well-formed tree with yield w *)
Theorem derives_big_wf_tree_yield g w :
  derives_big g w -> exists pt, wf_tree g pt /\ yield pt = w.
Proof.
  intros.
  induction H.
  - exists (ANode lex).
    split.
    + apply ANode_wf.
    + reflexivity.
  - destruct IHderives_big as [pt].
    exists (CNode op1 pt op2).
    destruct H1.
    split.
    + apply CNode_wf; assumption.
    + simpl.
      rewrite H2.
      reflexivity.
  - destruct IHderives_big1 as [pt1].
    destruct IHderives_big2 as [pt2].
    destruct H2.
    destruct H3.
    exists (INode pt1 op pt2).
    split.
    + apply INode_wf; assumption.
    + simpl.
      rewrite H4.
      rewrite H5.
      reflexivity.
Qed.

(* Concatenating two word then transforming it to an sentential form, is the same
  as concatenating the sentential forms corresponding to the two words. *)
Lemma word_to_sform_concat w1 w2 :
  word_to_sform (w1 ++ w2) = word_to_sform w1 ++ word_to_sform w2.
Proof.
  induction w1.
  - reflexivity.
  - simpl.
    rewrite IHw1.
    reflexivity.
Qed.

(* If beta => beta', then alpha beta => alpha beta' *)
Lemma derives_one_prefix g s s' s_l :
  derives_one g s s' ->
  derives_one g (s_l ++ s) (s_l ++ s').
Proof.
  intros.
  destruct H.
  - rewrite app_assoc.
    rewrite app_assoc.
    apply Atomic_der_one.
  - simpl.
    rewrite app_assoc.
    rewrite app_assoc.
    apply Closed_der_one.
    assumption.
  - rewrite app_assoc.
    rewrite app_assoc.
    apply Infix_der_one.
    assumption.
Qed.

(* If beta *=> beta', then alpha beta *=> alpha beta' *)
Lemma derives_small_prefix g s s' s_l:
  derives_small g s s' ->
  derives_small g (s_l ++ s) (s_l ++ s').
Proof.
  intros.
  revert s_l.
  induction H.
  - intros.
    apply Refl_der.
  - intros.
    apply Trans_der with (s'0 := s_l ++ s').
    + apply derives_one_prefix.
      assumption.
    + apply IHderives_small.
Qed.

(* If beta => beta', then beta gamma => beta' gamma *)
Lemma derives_one_postfix g s s' s_r :
  derives_one g s s' ->
  derives_one g (s ++ s_r) (s' ++ s_r).
Proof.
  intros.
  destruct H.
  - rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    apply Atomic_der_one.
  - rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    apply Closed_der_one.
    assumption.
  - rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    apply Infix_der_one.
    assumption.
Qed.

(* If beta *=> beta', then beta gamma *=> beta' gamma *)
Lemma derives_small_postfix g s s' s_r:
  derives_small g s s' ->
  derives_small g (s ++ s_r) (s' ++ s_r).
Proof.
  intros.
  revert s_r.
  induction H.
  - intros.
    apply Refl_der.
  - intros.
    apply Trans_der with (s'0 := s' ++ s_r).
    + apply derives_one_postfix.
      assumption.
    + apply IHderives_small.
Qed.

(* If beta *=> beta', then alpha beta gamma *=> alpha beta' gamma *)
Lemma derives_small_closed g s s' s_l s_r :
  derives_small g s s' ->
  derives_small g (s_l ++ s ++ s_r) (s_l ++ s' ++ s_r).
Proof.
  intros.
  apply derives_small_prefix.
  apply derives_small_postfix.
  assumption.
Qed.

(* If alpha *=> beta and beta *=> gamma, then alpha *=> gamma *)
Lemma derives_small_transitive g s s' s'' :
  derives_small g s s' ->
  derives_small g s' s'' ->
  derives_small g s s''.
Proof.
  intros H.
  induction H.
  - intros.
    assumption.
  - intros.
    apply Trans_der with (s'0 := s').
    + assumption.
    + apply IHderives_small.
      assumption.
Qed.

(* If alpha *=> alpha' and gamma *=> gamma',
  then alpha beta gamme *=> alpha' beta gamma' *)
Lemma derives_small_infix g s_l s_r s_l' s_r' s :
  derives_small g s_l s_l' ->
  derives_small g s_r s_r' ->
  derives_small g (s_l ++ s ++ s_r) (s_l' ++ s ++ s_r').
Proof.
  intros.
  apply derives_small_transitive with (s' := s_l' ++ s ++ s_r).
  - apply derives_small_postfix.
    assumption.
  - rewrite app_assoc.
    rewrite app_assoc.
    apply derives_small_prefix.
    assumption.
Qed.

(* If a grammar big-derives a word w, then A *=> w *)
Theorem derives_big_derives_small g w :
  derives_big g w -> derives_small g [inr NT] (word_to_sform w).
Proof.
  intros.
  (* This assertion is often used to rewrite grammars
  to be able to use the lemmas above *)
  assert (R1: forall (a : L + O + nonterminal) (b : sform L O),
                derives_one g [a] b = derives_one g ([] ++ [a]) ([] ++ b)
         ). { reflexivity. }
  induction H.
  - apply Trans_der with (s' := [inl (inl lex)]).
    + rewrite R1.
      apply Atomic_der_one.
    + apply Refl_der.
  - simpl.
    rewrite word_to_sform_concat.
    simpl.
    apply Trans_der with (s' := [inl (inr op1); inr NT; inl (inr op2)]).
    + rewrite R1.
      apply Closed_der_one.
      assumption.
    + assert (R2:
        derives_small g [inl (inr op1); inr NT; inl (inr op2)]
          (inl (inr op1) :: word_to_sform w ++ [inl (inr op2)])
        =
        derives_small g ([inl (inr op1)] ++ [inr NT] ++ [inl (inr op2)])
          ([inl (inr op1)] ++ word_to_sform w ++ [inl (inr op2)])
      ). { reflexivity. }
      rewrite R2.
      apply derives_small_closed.
      assumption.
  - rewrite word_to_sform_concat.
    simpl.
    apply Trans_der with (s' := [inr NT; inl (inr op); inr NT]).
    + rewrite R1.
      apply Infix_der_one.
      assumption.
    + assert (R2:
        derives_small g [inr NT; inl (inr op); inr NT]
          (word_to_sform w1 ++ inl (inr op) :: word_to_sform w2)
        =
        derives_small g ([inr NT] ++ [inl (inr op)] ++ [inr NT])
          (word_to_sform w1 ++ [inl (inr op)] ++ word_to_sform w2)
      ). { reflexivity. }
      rewrite R2.
      apply derives_small_infix.
      * assumption.
      * assumption.
Qed.
