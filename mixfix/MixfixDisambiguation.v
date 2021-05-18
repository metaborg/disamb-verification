From disamb Require Import MyUtils.
From disamb Require Export MixfixGrammar.

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

Inductive disambiguation_pattern (T : Type) :=
  | left_pattern (p1 p2 : production T)
  | right_pattern (p1 p2 : production T).

Global Arguments left_pattern {_} _ _ .
Global Arguments right_pattern {_} _ _.

Record disambiguation_patterns (T : Type) := mk_disambiguation_patterns {
  patterns : disambiguation_pattern T → Prop;
  patterns_decidable : ∀ q, Decision (patterns q);
}.

Global Arguments patterns {_} _ _.
Global Arguments patterns_decidable {_} _.

Notation dpatts := disambiguation_patterns.

Notation "'∠' q Q" := (Q.(patterns) q) (at level 52).
Notation "p1 'CL' p2 '∠' Q" := (Q.(patterns) (left_pattern p1 p2)) (at level 54).
Notation "p1 'CR' p2 '∠' Q" := (Q.(patterns) (right_pattern p1 p2)) (at level 53).

Inductive leftmost_match {T} (p : production T) : parse_tree T → Prop :=
  | leftmost_match_id ts :
      leftmost_match p (node p ts)
  | leftmost_match_deep p0 t ts :
      leftmost_match p t →
      leftmost_match p (node p0 (cons_forest t ts)).

Notation "t 'Mlm' p" := (leftmost_match p t) (at level 55).

Inductive rightmost_match {T} (p : production T) : parse_tree T → Prop :=
  | rightmost_match_id ts :
      rightmost_match p (node p ts)
  | rightmost_match_deep p0 ts :
      rightmost_match_forest p ts →
      rightmost_match p (node p0 ts)

with rightmost_match_forest {T} (p : production T) : parse_forest T → Prop :=
  | rightmost_match_forest_last t :
      rightmost_match p t →
      rightmost_match_forest p (cons_forest t nil_forest)
  | rightmost_match_forest_cons t ts :
      rightmost_match_forest p ts →
      rightmost_match_forest p (cons_forest t ts).

Scheme rightmost_match_tree_forest := Induction for rightmost_match Sort Prop
with rightmost_match_forest_tree := Induction for rightmost_match_forest Sort Prop.

Notation "t 'Mrm' p" := (rightmost_match p t) (at level 56).
Notation "ts 'Mrmf' p" := (rightmost_match_forest p ts) (at level 57).

Inductive conflict_right_forest {T} (p : production T) : parse_forest T → Prop :=
  | conflict_right_forest_last t :
      t Mlm p →
      conflict_right_forest p (cons_forest t nil_forest)
  | conflict_right_forest_cons t ts :
      conflict_right_forest p ts →
      conflict_right_forest p (cons_forest t ts).

Notation crf := conflict_right_forest.

Inductive conflict {T} (Q : dpatts T) : parse_tree T → Prop :=
  | conflict_left p1 p2 t ts :
      p1 CL p2 ∠ Q →
      t Mrm p2 →
      conflict Q (node p1 (cons_forest t ts))
  | conflict_right p1 p2 ts :
      p1 CR p2 ∠ Q →
      conflict_right_forest p2 ts →
      conflict Q (node p1 ts).

Notation c := conflict.

Inductive conflict_free_tree {T} (Q : dpatts T) : parse_tree T → Prop :=
  | conflict_free_leaf a :
      conflict_free_tree Q (leaf a)
  | conflict_free_node p ts :
      ¬ conflict Q (node p ts) →
      conflict_free_forest Q ts →
      conflict_free_tree Q (node p ts)

with conflict_free_forest {T} (Q : dpatts T) : parse_forest T → Prop :=
  | conflict_free_nil_forest :
      conflict_free_forest Q nil_forest
  | conflict_free_cons_forest t ts :
      conflict_free_tree Q t →
      conflict_free_forest Q ts →
      conflict_free_forest Q (cons_forest t ts).

Scheme conflict_free_tree_forest := Induction for conflict_free_tree Sort Prop
with conflict_free_forest_tree := Induction for conflict_free_forest Sort Prop.

Notation cft := conflict_free_tree.
Notation cfts := conflict_free_forest.

Inductive disambiguation_rules_to_patterns {T} (PR : drules T) : disambiguation_pattern T → Prop :=
  | priority_pattern_right p1 p2 :
      p1 >> p2 ∠ PR →
      disambiguation_rules_to_patterns PR (right_pattern p1 p2)
  | priority_pattern_left p1 p2 :
      p1 >> p2 ∠ PR →
      disambiguation_rules_to_patterns PR (left_pattern p1 p2)
  | left_associativity_pattern p1 p2 :
      p1 lefta p2 ∠ PR →
      disambiguation_rules_to_patterns PR (right_pattern p1 p2)
  | right_associativity_pattern p1 p2 :
      p1 righta p2 ∠ PR →
      disambiguation_rules_to_patterns PR (left_pattern p1 p2).

Global Instance disambiguation_rules_to_patterns_decidable {T} (PR : drules T) :
  ∀ q, Decision (disambiguation_rules_to_patterns PR q).
Proof.
  intro q. destruct q as [p1 p2|p1 p2]; destruct (decide (p1 >> p2 ∠ PR)) as [Hprio|Hnotprio].
  - left. auto using priority_pattern_left.
  - destruct (decide (p1 righta p2 ∠ PR)) as [Hrighta|Hnotrighta].
    + left. auto using right_associativity_pattern.
    + right. intro Hleftpattern.
      inv Hleftpattern; contradiction.
  - left. auto using priority_pattern_right.
  - destruct (decide (p1 lefta p2 ∠ PR)) as [Hlefta|Hnotlefta].
    + left. auto using left_associativity_pattern.
    + right. intro Hrightpattern.
      inv Hrightpattern; contradiction.
Qed.

Definition drules_to_dpatts {T} (PR : drules T) : dpatts T := mk_disambiguation_patterns T
  (disambiguation_rules_to_patterns PR)
  (disambiguation_rules_to_patterns_decidable PR).
