From stdpp Require Export list.

Inductive symbol (T : Type) :=
  | terminal (a : T)
  | nonterminal.

Global Arguments terminal {_} _.
Global Arguments nonterminal {_}.

Notation E := nonterminal.

Definition production (T : Type) := list (symbol T).

Record mixfixgrammar (T : Type) := mkMixfixgrammar {
  productions : production T → Prop;
  acyclic_productions : ¬ productions [E];
}.

Global Arguments productions {_} _ _.
Global Arguments acyclic_productions {_} _.

Notation prod := productions.

Definition word (T : Type) := list T.

Inductive parse_tree (T : Type) :=
  | leaf : T → parse_tree T
  | node : production T → parse_forest T → parse_tree T

with parse_forest (T : Type) :=
  | nil_forest : parse_forest T
  | cons_forest : parse_tree T → parse_forest T → parse_forest T.

Global Arguments leaf {_} _.
Global Arguments node {_} _ _.
Global Arguments nil_forest {_}.
Global Arguments cons_forest {_} _ _.

Scheme parse_tree_forest_rec := Induction for parse_tree Sort Prop
with parse_forest_tree_rec := Induction for parse_forest Sort Prop.

Scheme parse_tree_forest_rec_set := Induction for parse_tree Sort Set
with parse_forest_tree_rec_set := Induction for parse_forest Sort Set.

Inductive well_formed_parse_tree {T} (g : mixfixgrammar T) : symbol T → parse_tree T → Prop :=
  | well_formed_leaf a :
      well_formed_parse_tree g (terminal a) (leaf a)
  | well_formed_node p ts :
      prod g p →
      well_formed_parse_forest g p ts →
      well_formed_parse_tree g E (node p ts) 

with well_formed_parse_forest {T} (g : mixfixgrammar T) : list (symbol T) → parse_forest T → Prop :=
  | well_formed_nil_forest :
      well_formed_parse_forest g [] nil_forest
  | well_formed_cons_forest X Xs t ts :
      well_formed_parse_tree g X t →
      well_formed_parse_forest g Xs ts →
      well_formed_parse_forest g (X :: Xs) (cons_forest t ts).

Scheme well_formed_parse_tree_forest_rec := Induction for well_formed_parse_tree Sort Prop
with well_formed_parse_forest_tree_rec := Induction for well_formed_parse_forest Sort Prop.

Notation wft g X t := (well_formed_parse_tree g X t).
Notation wfts g Xs ts := (well_formed_parse_forest g Xs ts).

Fixpoint yield_tree {T} t : word T :=
  match t with
  | leaf a => [a]
  | node p ts => yield_forest ts
  end

with yield_forest {T} ts : word T :=
  match ts with
  | nil_forest => []
  | cons_forest t ts => yield_tree t ++ yield_forest ts
  end.

Notation yt t := (yield_tree t).
Notation yts ts := (yield_forest ts).

Definition sentence {T} (g : mixfixgrammar T) w := ∃ t, wft g E t ∧ yt t = w.

Create HintDb mixfix.
Hint Resolve well_formed_leaf well_formed_node well_formed_nil_forest well_formed_cons_forest : mixfix.
