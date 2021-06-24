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

Inductive left_dangling {T} : production T → Prop :=
  | left_dangling_intro p :
      left_dangling (E :: p).

Inductive right_dangling {T} : production T → Prop :=
  | right_dangling_one :
      right_dangling [E]
  | right_dangling_cons X p :
      right_dangling p →
      right_dangling (X :: p).

Global Instance left_dangling_decidable {T} (p : production T) : Decision (left_dangling p).
Proof.
  destruct p.
  - right. intro. inv H.
  - destruct s.
    + right. intro. inv H.
    + left. constructor.
Qed.

Global Instance right_dangling_decidable {T} (p : production T) : Decision (right_dangling p).
Proof.
  induction p.
  - right. intro. inv H.
  - destruct IHp.
    + left. constructor. assumption.
    + destruct p.
      * destruct a.
        **right. intro. inv H. inv H1.
        **left. constructor.
      * right. intro. inv H. contradiction.
Qed.

Inductive left_branching_forest {T} : parse_forest T → Prop :=
  | left_branching_forest_intro p1 t1s ts :
      left_branching_forest (cons_forest (node p1 t1s) ts).

Inductive left_branching {T} : parse_tree T → Prop :=
  | left_branching_intro p ts :
      left_branching_forest ts →
      left_branching (node p ts).

Inductive right_branching_forest {T} : parse_forest T → Prop :=
  | right_branching_forest_last pn tns :
      right_branching_forest (cons_forest (node pn tns) nil_forest)
  | right_branching_forest_cons t ts :
      right_branching_forest ts →
      right_branching_forest (cons_forest t ts).

Inductive right_branching {T} : parse_tree T → Prop :=
  | right_branching_intro p ts :
      right_branching_forest ts →
      right_branching (node p ts).
