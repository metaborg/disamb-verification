From stdpp Require Export relations.
From disamb Require Export MixfixGrammar.
From disamb Require Import MyUtils.

Inductive reorder_forest_left_up {T} (p1 : list (symbol T)) (ts1 : parse_forest T) : 
                                      parse_forest T → parse_forest T → Prop :=
  | reorder_left_up_last p3 ts3 :
      reorder_forest_left_up p1 ts1 (cons_forest (node p3 ts3) nil_forest)
        (cons_forest (node p1 (cons_forest (node p3 ts3) ts1)) nil_forest)
  | reorder_left_up_cons t2 ts2 ts2' :
      reorder_forest_left_up p1 ts1 ts2 ts2' →
      reorder_forest_left_up p1 ts1 (cons_forest t2 ts2) (cons_forest t2 ts2').

Inductive reorder_step_tree {T} : parse_tree T → parse_tree T → Prop :=
  | reorder_left_up p1 ts1 p2 ts2 ts2' :
      reorder_forest_left_up p1 ts1 ts2 ts2' →
      reorder_step_tree (node p1 (cons_forest (node p2 ts2) ts1)) (node p2 ts2')
  | reorder_subtree p ts ts' :
      reorder_step_forest ts ts' →
      reorder_step_tree (node p ts) (node p ts')

with reorder_step_forest {T} : parse_forest T → parse_forest T → Prop :=
  | reorder_head t ts t' :
      reorder_step_tree t t' →
      reorder_step_forest (cons_forest t ts) (cons_forest t' ts)
  | reorder_tail t ts ts' :
      reorder_step_forest ts ts' →
      reorder_step_forest (cons_forest t ts) (cons_forest t ts').

Scheme reorder_step_tree_forest_rec := Induction for reorder_step_tree Sort Prop
with reorder_step_forest_tree_rec := Induction for reorder_step_forest Sort Prop.

Definition reorder_tree {T} := rtsc (@reorder_step_tree T).
Definition reorder_forest {T} := rtsc (@reorder_step_forest T).

Inductive left_reorderable {T} : production T → production T → Prop :=
  | left_reorderable_one p :
      left_reorderable [E] (E :: p)
  | left_reorderable_cons X p1 p2 :
      left_reorderable p1 p2 →
      left_reorderable (X :: p1) p2.

Global Instance left_reorderable_decidable {T} (p1 p2 : production T) :
  Decision (left_reorderable p1 p2).
Proof.
  induction p1 as [|X p1].
  - right. intro. inv H.
  - destruct IHp1.
    + left. constructor. assumption.
    + destruct X.
      * right. intro. inv H. contradiction.
      * destruct p1 as [|X p1].
        **destruct p2 as [|X p2].
          ***right. intro. inv H. inv H3.
          ***destruct X.
            ****right. intro. inv H. inv H3.
            ****left. constructor.
        **right. intro. inv H. contradiction.
Qed.
