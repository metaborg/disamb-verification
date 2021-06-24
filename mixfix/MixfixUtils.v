From disamb Require Export MixfixGrammar.

Fixpoint add_last {T} (ts : parse_forest T) (tn : parse_tree T) :=
  match ts with
  | nil_forest => cons_forest tn nil_forest
  | cons_forest t ts => cons_forest t (add_last ts tn)
  end.

Fixpoint split_last {T} (t : parse_tree T) (ts : parse_forest T) :=
  match ts with
  | nil_forest => (nil_forest, t)
  | cons_forest t2 ts =>
      let (ts', t') := split_last t2 ts in (cons_forest t ts', t')
  end.
