From disamb Require Export MixfixDisambiguation.
From disamb Require Export MixfixUtils.

Fixpoint repair_cr {T} (Q : crules T) (p : production T) (ts : parse_forest T) (tn : parse_tree T) :=
  match tn with
  | leaf a => (node p (add_last ts tn), false)
  | node pn tns => repair_cr_forest Q p pn ts tns
  end

with repair_cr_forest {T} (Q : crules T) (p pn : production T) (ts tns : parse_forest T) :=
  match tns with
  | nil_forest => (node p (add_last ts (node pn tns)), false)
  | cons_forest tn1 tns =>
      let (tn1', b) := repair_cr Q p ts tn1 in
      if decide (b = true ∨ p CR pn ∠ Q) then (node pn (cons_forest tn1' tns), true)
      else (node p (add_last ts (node pn (cons_forest tn1 tns))), false)
  end.
  
Definition repair_cr_start {T} (Q : crules T) (t : parse_tree T) :=
  match t with
  | leaf a => t
  | node p nil_forest => t
  | node p (cons_forest t ts) =>
      let (ts, tn) := split_last t ts in
      let (t', _) := repair_cr Q p ts tn in t'
  end.

Fixpoint repair_cl {T} (Q : crules T) (p : production T) (t1 : parse_tree T) (ts : parse_forest T) :=
  match t1 with
  | leaf a => repair_cr_start Q (node p (cons_forest t1 ts))
  | node p1 t1s => repair_cl_forest1 Q p p1 t1s ts
  end

with repair_cl_forest1 {T} (Q : crules T) (p p1 : production T) (t1s ts : parse_forest T) :=
  match t1s with
  | nil_forest => repair_cr_start Q (node p (cons_forest (node p1 t1s) ts))
  | cons_forest t11 t1s =>
      match (repair_cl_forest2 Q p p1 ts t1s) with
      | None => repair_cr_start Q (node p (cons_forest (node p1 (cons_forest t11 t1s)) ts))
      | Some ts' => repair_cl Q p1 t11 ts'
      end
  end

with repair_cl_forest2 {T} (Q : crules T) (p p1 : production T) (ts t1s : parse_forest T) : option (parse_forest T) :=
  match t1s with
  | nil_forest => None
  | cons_forest t1i t1s =>
      match t1s with
      | nil_forest => 
          match t1i with
          | leaf a => None
          | node p1n t1ns => Some (cons_forest (repair_cl Q p t1i ts) nil_forest)
          end
      | _ =>
          match (repair_cl_forest2 Q p p1 ts t1s) with
          | None => None
          | Some t1s' => Some (cons_forest t1i t1s')
          end
      end
  end.

Definition repair_cl_start {T} (Q : crules T) (p : production T) (ts : parse_forest T) :=
  match ts with
  | nil_forest => node p ts
  | cons_forest t1 ts => repair_cl Q p t1 ts
  end.

Fixpoint repair {T} (Q : crules T) (t : parse_tree T) :=
  match t with
  | leaf a => leaf a
  | node p ts => repair_cl_start Q p (repair_forest Q ts)
  end

with repair_forest {T} (Q : crules T) (ts : parse_forest T) :=
  match ts with
  | nil_forest => nil_forest
  | cons_forest t ts => cons_forest (repair Q t) (repair_forest Q ts)
  end.
