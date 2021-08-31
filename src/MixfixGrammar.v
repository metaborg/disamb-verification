From stdpp Require Export list.

Inductive symbol (T : Type) :=
  | terminal (a : T)
  | nonterminal.

Global Arguments terminal {_} _.
Global Arguments nonterminal {_}.

Notation E := nonterminal.

Inductive production (T : Type) :=
  | small_production : option T → production T
  | large_production : symbol T → list (symbol T) → symbol T → production T.

Global Arguments small_production {_} _.
Global Arguments large_production {_} _ _ _.

Definition mixfixgrammar (T : Type) := production T → Prop.

Definition word (T : Type) := list T.

Inductive parse_tree (T : Type) :=
  | leaf : T → parse_tree T
  | small_node : production T → option T → parse_tree T
  | large_node : production T → parse_tree T → parse_list T → parse_tree T → parse_tree T

with parse_list (T : Type) :=
  | parse_nil : parse_list T
  | parse_cons : parse_tree T → parse_list T → parse_list T.

Global Arguments leaf {_} _.
Global Arguments small_node {_} _ _.
Global Arguments large_node {_} _ _ _ _.
Global Arguments parse_nil {_}.
Global Arguments parse_cons {_} _ _.

Scheme parse_tree_list_rec := Induction for parse_tree Sort Prop
with parse_list_tree_rec := Induction for parse_list Sort Prop.

Scheme parse_tree_list_rec_set := Induction for parse_tree Sort Set
with parse_list_tree_rec_set := Induction for parse_list Sort Set.

Inductive is_node {T} : parse_tree T → Prop :=
  | is_small_node p opt_a :
      is_node (small_node p opt_a)
  | is_large_node p t1 τ tn :
      is_node (large_node p t1 τ tn).

Inductive well_formed_parse_tree {T} (g : mixfixgrammar T) : symbol T → parse_tree T → Prop :=
  | well_formed_leaf a :
      well_formed_parse_tree g (terminal a) (leaf a)
  | well_formed_small_node opt_a :
      g (small_production opt_a) →
      well_formed_parse_tree g E (small_node (small_production opt_a) opt_a)
  | well_formed_large_node X1 σ Xn t1 τ tn :
      g (large_production X1 σ Xn) →
      well_formed_parse_tree g X1 t1 →
      well_formed_parse_list g σ τ →
      well_formed_parse_tree g Xn tn →
      well_formed_parse_tree g E (large_node (large_production X1 σ Xn) t1 τ tn) 

with well_formed_parse_list {T} (g : mixfixgrammar T) : list (symbol T) → parse_list T → Prop :=
  | well_formed_parse_nil :
      well_formed_parse_list g [] parse_nil
  | well_formed_parse_cons X Xs t ts :
      well_formed_parse_tree g X t →
      well_formed_parse_list g Xs ts →
      well_formed_parse_list g (X :: Xs) (parse_cons t ts).

Scheme well_formed_parse_tree_list_rec := Induction for well_formed_parse_tree Sort Prop
with well_formed_parse_list_tree_rec := Induction for well_formed_parse_list Sort Prop.

Notation wft g X t := (well_formed_parse_tree g X t).
Notation wfτ g σ ts := (well_formed_parse_list g σ ts).

Fixpoint yield_tree {T} t : word T :=
  match t with
  | leaf a => [a]
  | small_node p opt_a =>
      match opt_a with
      | None => []
      | Some a => [a]
      end
  | large_node p t1 τ tn => yield_tree t1 ++ yield_list τ ++ yield_tree tn 
  end

with yield_list {T} τ : word T :=
  match τ with
  | parse_nil => []
  | parse_cons t ts => yield_tree t ++ yield_list ts
  end.

Notation yt t := (yield_tree t).
Notation yts ts := (yield_list ts).

Definition sentence {T} (g : mixfixgrammar T) w := ∃ t, wft g E t ∧ yt t = w.
