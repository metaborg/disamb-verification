Require Export PosTree.
From stdpp Require Export relations.

Section Reordering.

Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types pt : @pos_tree L O.

Inductive reorder_step : parse_tree -> parse_tree -> Prop :=
  | RI_LR t11 o1 t12 o t2 :
      reorder_step (INode (INode t11 o1 t12) o t2)
                   (INode t11 o1 (INode t12 o t2))
  | RI_RL t1 o t21 o2 t22 :
      reorder_step (INode t1 o (INode t21 o2 t22))
                   (INode (INode t1 o t21) o2 t22)
  | RI_t1 t1 o t2 t1' :
      reorder_step t1 t1' ->
      reorder_step (INode t1 o t2) (INode t1' o t2)
  | RI_t2 t1 o t2 t2' :
      reorder_step t2 t2' ->
      reorder_step (INode t1 o t2) (INode t1 o t2').

Definition reorder := rtc reorder_step.

Ltac super_simpl := try simpl in *; try simplify_list_eq; try reflexivity.

Lemma reorder_step_preserves_yields t t' :
  reorder_step t t' -> yield t = yield t'.
Proof.
  intros. induction H; super_simpl.
  - rewrite IHreorder_step. reflexivity.
  - rewrite IHreorder_step. reflexivity.
Qed.

Lemma reorder_preserves_yield t t' :
  reorder t t' -> yield t = yield t'.
Proof.
  unfold reorder. intros.
  induction H.
  - reflexivity.
  - rewrite <- IHrtc.
    apply reorder_step_preserves_yields.
    assumption.
Qed.

Inductive reorder_step_pos : pos_tree -> pos_tree -> Prop :=
  | PRI_LR pt11 o1 i1 pt12 o i pt2 :
      reorder_step_pos (PINode (PINode pt11 o1 i1 pt12) o i pt2)
                       (PINode pt11 o1 i1 (PINode pt12 o i pt2))
  | PRI_RL pt1 o i pt21 o2 i2 pt22 :
      reorder_step_pos (PINode pt1 o i (PINode pt21 o2 i2 pt22))
                      (PINode (PINode pt1 o i pt21) o2 i2 pt22)
  | PRI_pt1 pt1 o i pt2 pt1' :
      reorder_step_pos pt1 pt1' ->
      reorder_step_pos (PINode pt1 o i pt2) (PINode pt1' o i pt2)
  | PRI_pt2 pt1 o i pt2 pt2' :
      reorder_step_pos pt2 pt2' ->
      reorder_step_pos (PINode pt1 o i pt2) (PINode pt1 o i pt2').

Definition reorder_pos := rtc reorder_step_pos.

End Reordering.


