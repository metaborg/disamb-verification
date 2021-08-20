From disamb Require Import MyUtils.
From disamb Require Export MixfixReorder2.

Record disambiguation_rules (T : Type) := mkDisambiguation_rules {
  priority : production T → production T → Prop;
  left_associativity : production T → production T → Prop;
  right_associativity : production T → production T → Prop;
  priority_decidable : RelDecision priority;
  left_associativity_decidable : RelDecision left_associativity;
  right_associativity_decidable : RelDecision right_associativity;
}.

Notation drules := disambiguation_rules.

Global Arguments priority {_} _ _ _.
Global Arguments left_associativity {_} _ _ _.
Global Arguments right_associativity {_} _ _ _.
Global Arguments priority_decidable {_} _.
Global Arguments left_associativity_decidable {_} _.
Global Arguments right_associativity_decidable {_} _.

Global Existing Instances priority_decidable left_associativity_decidable right_associativity_decidable. 

Notation "p1 'lefta' p2 '∠' PR" := (left_associativity PR p1 p2) (at level 50).
Notation "p1 'righta' p2 '∠' PR" := (right_associativity PR p1 p2) (at level 51).
Notation "p1 '>>' p2 '∠' PR" := (priority PR p1 p2) (at level 52).

Definition safe_drules {T} (PR : drules T) : Prop :=
  ∀ p1 p2, ¬ ((p1 >> p2 ∠ PR ∨ p1 lefta p2 ∠ PR) ∧ (p2 >> p1 ∠ PR ∨ p2 righta p1 ∠ PR)).

Record conflict_rules (T : Type) := mk_conflict_rules {
  conflict_left : production T → production T → Prop;
  conflict_right : production T → production T → Prop;
  conflict_left_decidable : RelDecision conflict_left;
  conflict_right_decidable : RelDecision conflict_right;
  conflict_left_well_formed : ∀ p1 p2, conflict_left p1 p2 → left_dangling p1 ∧ right_dangling p2;
  conflict_right_well_formed : ∀ p1 p2, conflict_right p1 p2 → right_dangling p1 ∧ left_dangling p2;
}.

Global Arguments conflict_left {_} _ _ _.
Global Arguments conflict_right {_} _ _ _.
Global Existing Instances conflict_left_decidable.
Global Existing Instances conflict_right_decidable.


Notation crules := conflict_rules.

Notation "p1 'CL' p2 '∠' Q" := (Q.(conflict_left) p1 p2) (at level 54).
Notation "p1 'CR' p2 '∠' Q" := (Q.(conflict_right) p1 p2) (at level 53).

Definition safe_crules {T} (Q : crules T) : Prop := ∀ p1 p2, ¬ (p1 CL p2 ∠ Q ∧ p2 CR p1 ∠ Q).
Definition complete_crules {T} (Q : crules T) : Prop := ∀ p1 p2,
  left_dangling p1 → right_dangling p2 → p1 CL p2 ∠ Q ∨ p2 CR p1 ∠ Q.

Inductive in_rightmost_branch {T} (p : production T) : parse_tree T → Prop :=
  | in_rightmost_branch_root t1 τ tn :
      in_rightmost_branch p (large_node p t1 τ tn)
      (*Note: We don't check for small_nodes, because disambiguation rules involving them are nonsensical.*)
  | in_rightmost_branch_sub p0 t1 τ tn :
      in_rightmost_branch p tn →
      in_rightmost_branch p (large_node p0 t1 τ tn).

Inductive in_leftmost_branch {T} (p : production T) : parse_tree T → Prop :=
  | in_leftmost_branch_root t1 τ tn :
      in_leftmost_branch p (large_node p t1 τ tn)
      (*Note: We don't check for small_nodes, because disambiguation rules involving them are nonsensical.*)
  | in_leftmost_branch_sub p0 t1 τ tn :
      in_leftmost_branch p t1 →
      in_leftmost_branch p (large_node p0 t1 τ tn).

Notation "p 'LM' t" := (in_leftmost_branch p t) (at level 55).
Notation "p 'RM' t" := (in_rightmost_branch p t) (at level 56).

Inductive in_left_neighborhood {T} (p : production T) : parse_tree T → Prop :=
  | in_left_neighborhood_intro p0 t1 τ tn :
      in_rightmost_branch p t1 →
      in_left_neighborhood p (large_node p0 t1 τ tn).

Inductive in_right_neighborhood {T} (p : production T) : parse_tree T → Prop :=
  | in_right_neighborhood_intro p0 t1 τ tn :
      in_leftmost_branch p tn →
      in_right_neighborhood p (large_node p0 t1 τ tn).

Notation "p 'LN' t" := (in_left_neighborhood p t) (at level 57).
Notation "p 'RN' t" := (in_right_neighborhood p t) (at level 58).

Definition left_neighborhood_conflict_free {T} (Q : conflict_rules T) p1 t1 τ tn : Prop :=
  ∀ p2, p1 CL p2 ∠ Q → ¬ p2 LN (large_node p1 t1 τ tn).

Definition right_neighborhood_conflict_free {T} (Q : conflict_rules T) p1 t1 τ tn : Prop :=
  ∀ p2, p1 CR p2 ∠ Q → ¬ p2 RN (large_node p1 t1 τ tn).

Notation lncf := left_neighborhood_conflict_free.
Notation rncf := right_neighborhood_conflict_free.

Inductive conflict_free {T} (Q : conflict_rules T) : parse_tree T → Prop :=
  | conflict_free_leaf a :
      conflict_free Q (leaf a)
  | conflict_free_small_node p opt_a :
      conflict_free Q (small_node p opt_a)
  | conflict_free_large_node p t1 τ tn :
      lncf Q p t1 τ tn →
      rncf Q p t1 τ tn →
      conflict_free Q t1 →
      conflict_free_list Q τ →
      conflict_free Q tn →
      conflict_free Q (large_node p t1 τ tn)

with conflict_free_list {T} (Q : conflict_rules T) : parse_list T → Prop :=
  | conflict_free_nil :
      conflict_free_list Q parse_nil
  | conflict_free__cons t ts :
      conflict_free Q t →
      conflict_free_list Q ts →
      conflict_free_list Q (parse_cons t ts).

Notation cf := conflict_free.
Notation cfl := conflict_free_list.

Scheme conflict_free_tree_list := Induction for conflict_free Sort Prop
with conflict_free_list_tree := Induction for conflict_free_list Sort Prop.

Definition crules_sentence {T} (g : mixfixgrammar T) (Q : crules T) w :=
  ∃ t, wft g E t ∧ cf Q t ∧ yt t = w.

Inductive as_conflict_right_rule {T} (PR : drules T) : production T → production T → Prop :=
  | priority_pattern_right p1 p2 :
      p1 >> p2 ∠ PR →
      right_dangling p1 →
      left_dangling p2 →
      as_conflict_right_rule PR p1 p2
  | left_associativity_right p1 p2 :
      p1 lefta p2 ∠ PR →
      right_dangling p1 →
      left_dangling p2 →
      as_conflict_right_rule PR p1 p2.

Inductive as_conflict_left_rule {T} (PR : drules T) : production T → production T → Prop :=
  | priority_pattern_left p1 p2 :
      p1 >> p2 ∠ PR →
      left_dangling p1 →
      right_dangling p2 →
      as_conflict_left_rule PR p1 p2
  | right_associativity_left p1 p2 :
      p1 righta p2 ∠ PR →
      left_dangling p1 →
      right_dangling p2 →
      as_conflict_left_rule PR p1 p2.

Global Instance as_conflict_right_rule_decidable {T} (PR : drules T) : RelDecision (as_conflict_right_rule PR).
Proof.
  intros p1 p2.
  destruct (decide (right_dangling p1)) as [Hrd|Hnrd].
  - destruct (decide (left_dangling p2)) as [Hld|Hnld].
    + destruct (decide (p1 >> p2 ∠ PR)) as [Hprio|Hnprio].
      * left. auto using priority_pattern_right.
      * destruct (decide (p1 lefta p2 ∠ PR)) as [Hlefta|Hnlefta].
        **left. auto using left_associativity_right.
        **right. intro. inv H; auto.
    + right. intro. inv H; auto.
  - right. intro. inv H; auto.
Qed.

Global Instance as_conflict_left_rule_decidable {T} (PR : drules T) : RelDecision (as_conflict_left_rule PR).
Proof.
  intros p1 p2.
  destruct (decide (left_dangling p1)) as [Hld|Hnld].
  - destruct (decide (right_dangling p2)) as [Hrd|Hnrd].
    + destruct (decide (p1 >> p2 ∠ PR)) as [Hprio|Hnprio].
      * left. auto using priority_pattern_left.
      * destruct (decide (p1 righta p2 ∠ PR)) as [Hrighta|Hnrighta].
        **left. auto using right_associativity_left.
        **right. intro. inv H; auto.
    + right. intro. inv H; auto.
  - right. intro. inv H; auto.
Qed.

Lemma as_conflict_right_rule_well_formed {T} (PR : drules T) :
  ∀ p1 p2, as_conflict_right_rule PR p1 p2 → right_dangling p1 ∧ left_dangling p2.
Proof.
  intros. inv H; auto.
Qed.

Lemma as_conflict_left_rule_well_formed {T} (PR : drules T) :
  ∀ p1 p2, as_conflict_left_rule PR p1 p2 → left_dangling p1 ∧ right_dangling p2.
Proof.
  intros. inv H; auto.
Qed.

Definition drules_to_crules {T} (PR : drules T) : crules T := mk_conflict_rules T
  (as_conflict_left_rule PR)
  (as_conflict_right_rule PR)
  (as_conflict_left_rule_decidable PR)
  (as_conflict_right_rule_decidable PR)
  (as_conflict_left_rule_well_formed PR)
  (as_conflict_right_rule_well_formed PR).

Notation drules_sentence g PR w := (crules_sentence g (drules_to_crules PR) w).
