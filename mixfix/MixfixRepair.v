From disamb Require Export MixfixDisambiguation.
From disamb Require Import MyUtils.

Fixpoint repair_cl {T} (Q : dpatts T) (p : production T) (t1 : parse_tree T) (ts : parse_forest T)
      : parse_tree T * bool :=
  match t1 with
  | leaf a => (node p (cons_forest t1 ts), false)
  | node p1 t1s =>
      let (t1s', b) := repair_cl_forest Q p t1s ts in
      if decide (b = true ∨ p CL p1 ∠ Q) then (node p1 t1s', true)
      else (node p (cons_forest t1 ts), false)
  end

with repair_cl_forest {T} (Q : dpatts T) (p : production T) (t1s ts : parse_forest T)
      : parse_forest T * bool :=
  match t1s with
  | nil_forest => (nil_forest, false)
  | cons_forest t1n nil_forest =>
      let (t1n', b) := repair_cl Q p t1n ts in
      (cons_forest t1n' nil_forest, b)
  | cons_forest t11 t1s =>
      let (t1s', b) := repair_cl_forest Q p t1s ts in
      (cons_forest t11 t1s', b)
  end.

Definition rcl {T} (Q : dpatts T) (t : parse_tree T) :=
  match t with
  | leaf a => t
  | node p nil_forest => t
  | node p (cons_forest t1 ts) => let (t', _) := repair_cl Q p t1 ts in t'
  end.

Fixpoint add_last {T} (ts : parse_forest T) (tn : parse_tree T) :=
  match ts with
  | nil_forest => cons_forest tn nil_forest
  | cons_forest t ts => cons_forest t (add_last ts tn)
  end.

Fixpoint repair_cr {T} (Q : dpatts T) (p : production T) (ts : parse_forest T) (tn : parse_tree T) :=
  match tn with
  | leaf a => (node p (add_last ts tn), false)
  | node pn nil_forest => (node p (add_last ts tn), false)
  | node pn (cons_forest tn1 tns) =>
      let (tn1', b) := repair_cr Q p ts tn1 in
      if decide (b = true ∨ p CR pn ∠ Q) then (node pn (cons_forest tn1' tns), true)
      else (node p (add_last ts tn), false)
  end.

Fixpoint split_last {T} (t : parse_tree T) (ts : parse_forest T) :=
  match ts with
  | nil_forest => (nil_forest, t)
  | cons_forest t2 ts =>
      let (ts', t') := split_last t ts in (cons_forest t2 ts', t')
  end.
  
Definition rcr {T} (Q : dpatts T) (t : parse_tree T) :=
  match t with
  | leaf a => t
  | node p nil_forest => t
  | node p (cons_forest t ts) =>
      let (ts, tn) := split_last t ts in
      let (t', _) := repair_cr Q p ts tn in t'
  end.

Fixpoint repair {T} (Q : dpatts T) (t : parse_tree T) :=
  match t with
  | leaf a => leaf a
  | node p ts => rcr Q (rcl Q (node p (repair_forest Q ts)))
  end

with repair_forest {T} (Q : dpatts T) (ts : parse_forest T) :=
  match ts with
  | nil_forest => nil_forest
  | cons_forest t ts => cons_forest (repair Q t) (repair_forest Q ts)
  end.
