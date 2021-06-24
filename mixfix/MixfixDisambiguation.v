From disamb Require Import MyUtils.
From disamb Require Export MixfixReorder.

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

Inductive in_rightmost_branch {T} (p : production T) : parse_tree T → Prop :=
  | in_rightmost_branch_root ts :
      in_rightmost_branch p (node p ts)
  | in_rightmost_branch_sub p0 ts :
      in_rightmost_branch_forest p ts →
      in_rightmost_branch p (node p0 ts)

with in_rightmost_branch_forest {T} (p : production T) : parse_forest T → Prop :=
  | in_rightmost_branch_forest_last t :
      in_rightmost_branch p t →
      in_rightmost_branch_forest p (cons_forest t nil_forest)
  | in_rightmost_branch_forest_cons t ts :
      in_rightmost_branch_forest p ts →
      in_rightmost_branch_forest p (cons_forest t ts).

Scheme in_rightmost_branch_tree_forest := Induction for in_rightmost_branch Sort Prop
with in_rightmost_branch_forest_tree := Induction for in_rightmost_branch_forest Sort Prop.

Inductive in_leftmost_branch {T} (p : production T) : parse_tree T → Prop :=
  | in_leftmost_branch_root ts :
      in_leftmost_branch p (node p ts)
  | in_leftmost_branch_sub p0 t ts :
      in_leftmost_branch p t →
      in_leftmost_branch p (node p0 (cons_forest t ts)).

Notation "p 'LM' t" := (in_leftmost_branch p t) (at level 55).
Notation "p 'RM' t" := (in_rightmost_branch p t) (at level 56).
Notation "p 'RMf' ts" := (in_rightmost_branch_forest p ts) (at level 56).

Inductive in_left_neighborhood {T} (p : production T) : parse_tree T → Prop :=
  | in_left_neighborhood_intro p0 t ts :
      in_rightmost_branch p t →
      in_left_neighborhood p (node p0 (cons_forest t ts)).

Inductive in_right_neighborhood_forest {T} (p : production T) : parse_forest T → Prop :=
  | in_right_neighborhood_forest_last t :
      in_leftmost_branch p t →
      in_right_neighborhood_forest p (cons_forest t nil_forest)
  | in_right_neighborhood_forest_cons t ts :
      in_right_neighborhood_forest p ts →
      in_right_neighborhood_forest p (cons_forest t ts).

Inductive in_right_neighborhood {T} (p : production T) : parse_tree T → Prop :=
  | in_right_neighborhood_intro p0 ts :
      in_right_neighborhood_forest p ts →
      in_right_neighborhood p (node p0 ts).

Notation "p 'NL' t" := (in_left_neighborhood p t) (at level 57).
Notation "p 'NR' t" := (in_right_neighborhood p t) (at level 58).
Notation "p 'NRf' ts" := (in_right_neighborhood_forest p ts) (at level 58).

Inductive conflict_free {T} (Q : conflict_rules T) : parse_tree T → Prop :=
  | conflict_free_leaf a :
      conflict_free Q (leaf a)
  | conflict_free_node p1 ts :
      (∀ p2, p1 CL p2 ∠ Q → ¬ p2 NL (node p1 ts)) →
      (∀ p2, p1 CR p2 ∠ Q → ¬ p2 NR (node p1 ts)) →
      conflict_free_forest Q ts →
      conflict_free Q (node p1 ts)

with conflict_free_forest {T} (Q : conflict_rules T) : parse_forest T → Prop :=
  | conflict_free_forest_nil :
      conflict_free_forest Q nil_forest
  | conflict_free_forest_cons t ts :
      conflict_free Q t →
      conflict_free_forest Q ts →
      conflict_free_forest Q (cons_forest t ts).

Notation cf := conflict_free.
Notation cff := conflict_free_forest.

Scheme conflict_free_tree_forest := Induction for conflict_free Sort Prop
with conflict_free_forest_tree := Induction for conflict_free_forest Sort Prop.

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
