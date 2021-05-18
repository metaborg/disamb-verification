From stdpp Require Export relations.
From disamb Require Export MixfixGrammar.

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
