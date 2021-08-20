From stdpp Require Export relations.
From disamb Require Export MixfixGrammar2.
From disamb Require Import MyUtils.


Inductive reorder_step {T} : parse_tree T → parse_tree T → Prop :=
  | reorder_step_intro p1 t11 τ1 p2 t21 τ2 t22 :
      is_node t21 →
      reorder_step (large_node p1 t11 τ1 (large_node p2 t21 τ2 t22))
                   (large_node p2 (large_node p1 t11 τ1 t21) τ2 t22)
  | reorder_step_sub1 p t1 t1' τ tn :
      reorder_step t1 t1' →
      reorder_step (large_node p t1 τ tn) (large_node p t1' τ tn)
  | reorder_step_subτ p t1 τ τ' tn :
      reorder_step_list τ τ' →
      reorder_step (large_node p t1 τ tn) (large_node p t1 τ' tn)
  | reorder_step_subn p t1 τ tn tn' :
      reorder_step tn tn' →
      reorder_step (large_node p t1 τ tn) (large_node p t1 τ tn')

with reorder_step_list {T} : parse_list T → parse_list T → Prop :=
  | reorder_step_head t ts t' :
      reorder_step t t' →
      reorder_step_list (parse_cons t ts) (parse_cons t' ts)
  | reorder_step_tail t ts ts' :
      reorder_step_list ts ts' →
      reorder_step_list (parse_cons t ts) (parse_cons t ts').

Scheme reorder_step_tree_list_rec := Induction for reorder_step Sort Prop
with reorder_step_list_tree_rec := Induction for reorder_step_list Sort Prop.

Definition reorder {T} := rtsc (@reorder_step T).
Definition reorder_list {T} := rtsc (@reorder_step_list T).

Inductive left_dangling {T} : production T → Prop :=
  | left_dangling_intro σ Xn :
      left_dangling (large_production E σ Xn).

Inductive right_dangling {T} : production T → Prop :=
  | right_dangling_intro X1 σ :
      right_dangling (large_production X1 σ E).

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
  destruct p.
  - right. intro. inv H.
  - destruct s0.
    + right. intro. inv H.
    + left. constructor.
Qed.

Inductive left_branching {T} : parse_tree T → Prop :=
  | left_branching_intro p t1 τ tn :
      is_node t1 →
      left_branching (large_node p t1 τ tn).

Inductive right_branching {T} : parse_tree T → Prop :=
  | right_branching_intro p t1 τ tn :
      is_node tn →
      right_branching (large_node p t1 τ tn).
