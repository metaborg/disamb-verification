From stdpp Require Export list.

Section IPGrammar.

Inductive prod OP :=
  | InfixProd : OP -> prod OP
  | PrefixProd : OP -> prod OP.

Global Arguments InfixProd {_} _.
Global Arguments PrefixProd {_} _.

Record ipg := mkIpgrammar {
  LEX : Type;
  OP : Type;
  prods: prod OP -> Prop
}.

Definition word g := list (LEX g + OP g).

Inductive parse_tree (g : ipg) :=
  | AtomicNode : LEX g -> parse_tree g
  | InfixNode : parse_tree g -> OP g -> parse_tree g -> parse_tree g
  | PrefixNode : OP g -> parse_tree g -> parse_tree g.

Global Arguments AtomicNode {_} _.
Global Arguments InfixNode {_} _ _ _.
Global Arguments PrefixNode {_} _ _.

Inductive wf_parse_tree g : parse_tree g -> Prop :=
  | Atomic_wf l :
      wf_parse_tree g (AtomicNode l)
  | Infix_wf t1 o t2 :
      g.(prods) (InfixProd o) ->
      wf_parse_tree g t1 ->
      wf_parse_tree g t2 ->
      wf_parse_tree g (InfixNode t1 o t2)
  | Prefix_wf o t :
      g.(prods) (PrefixProd o) ->
      wf_parse_tree g t ->
      wf_parse_tree g (PrefixNode o t).

Fixpoint yield {g} t : word g :=
  match t with
  | AtomicNode l => [inl l]
  | InfixNode t1 o t2 => yield t1 ++ inr o :: yield t2
  | PrefixNode o t => inr o :: yield t
  end.

Definition language {g} w : Prop :=
  exists (t : parse_tree g), wf_parse_tree g t /\ yield t = w.

Inductive tree_pattern g :=
  | HPatt : tree_pattern g
  | InfixPatt : tree_pattern g -> OP g -> tree_pattern g -> tree_pattern g
  | PrefixPatt : OP g -> tree_pattern g -> tree_pattern g.

Global Arguments HPatt {_}.
Global Arguments InfixPatt {_} _ _ _.
Global Arguments PrefixPatt {_} _ _.

Inductive matches {g} : parse_tree g -> tree_pattern g -> Prop :=
  | HMatch t :
      matches t HPatt
  | InfixMatch t1 t2 q1 q2 o :
      matches t1 q1 ->
      matches t2 q2 -> 
      matches (InfixNode t1 o t2) (InfixPatt q1 o q2)
  | PrefixMatch t q o :
      matches t q ->
      matches (PrefixNode o t) (PrefixPatt o q).

Definition matches_set {g} t (Q : tree_pattern g -> Prop) : Prop :=
  exists q, Q q /\ matches t q.

Inductive i_conflict_free {g} (Q : tree_pattern g -> Prop) : parse_tree g -> Prop :=
  | Atomic_cf l :
      i_conflict_free Q (AtomicNode l)
  | Infix_cf t1 o t2 :
      ~ matches_set (InfixNode t1 o t2) Q ->
      i_conflict_free Q t1 ->
      i_conflict_free Q t2 ->
      i_conflict_free Q (InfixNode t1 o t2)
  | Prefix_cf t o :
      ~ matches_set (PrefixNode o t) Q ->
      i_conflict_free Q t ->
      i_conflict_free Q (PrefixNode o t).

Inductive matches_rm {g} : parse_tree g -> tree_pattern g -> Prop :=
  | Match_rm t q :
      matches t q ->
      matches_rm t q
  | InfixMatch_rm t1 o t2 q :
      matches_rm t2 q ->
      matches_rm (InfixNode t1 o t2) q
  | PrefixMatch_rm o t q :
      matches_rm t q ->
      matches_rm (PrefixNode o t) q.

Inductive matches_drm {g} : parse_tree g -> tree_pattern g -> Prop :=
  | InfixMatch_drm t1 t2 q1 q2 o :
      matches_rm t1 q1 ->
      matches_rm t2 q2 ->
      matches_drm (InfixNode t1 o t2) (InfixPatt q1 o q2)
  | PrefixMatch_drm t q o : 
      matches_rm t q ->
      matches_drm (PrefixNode o t) (PrefixPatt o q).

Definition matches_drm_set {g} t (Q : tree_pattern g -> Prop) : Prop :=
  exists q, Q q /\ matches_drm t q.

Inductive drm_conflict_free {g} (Q : tree_pattern g -> Prop) : parse_tree g -> Prop :=
  | Atomic_drmcf l :
      drm_conflict_free Q (AtomicNode l)
  | Infix_drmcf t1 o t2 :
      ~ matches_drm_set (InfixNode t1 o t2) Q ->
      drm_conflict_free Q t1 ->
      drm_conflict_free Q t2 ->
      drm_conflict_free Q (InfixNode t1 o t2)
  | Prefix_drmcf t o :
      ~ matches_drm_set (PrefixNode o t) Q ->
      drm_conflict_free Q t ->
      drm_conflict_free Q (PrefixNode o t).

Definition conflict_free {g} (Qi Qrm : tree_pattern g -> Prop) t :=
  i_conflict_free Qi t /\ drm_conflict_free Qrm t.

Record drules g := mkDrules {
  prio : prod g.(OP) -> prod g.(OP) -> Prop;
  left_a : prod g.(OP) -> prod g.(OP) -> Prop;
  right_a : prod g.(OP) -> prod g.(OP) -> Prop;

  prio_dec : RelDecision prio;
  left_a_dec : RelDecision left_a;
  right_a_dec : RelDecision right_a;
}.
Global Existing Instances prio_dec left_a_dec right_a_dec.

Global Arguments prio {_} _ _ _.
Global Arguments left_a {_} _ _ _.
Global Arguments right_a {_} _ _ _.

Definition CL_infix_infix {g} o1 o2 : tree_pattern g :=
  InfixPatt (InfixPatt HPatt o2 HPatt) o1 HPatt.
Definition CL_infix_prefix {g} o1 o2 : tree_pattern g :=
  InfixPatt (PrefixPatt o2 HPatt) o1 HPatt.
Definition CR_infix_infix {g} o1 o2 : tree_pattern g :=
  InfixPatt HPatt o1 (InfixPatt HPatt o2 HPatt).
Definition CR_prefix_infix {g} o1 o2 : tree_pattern g :=
  PrefixPatt o1 (InfixPatt HPatt o2 HPatt).

Inductive i_conflict_pattern {g} (pr : drules g) : tree_pattern g -> Prop :=
  | CLeft o1 o2 : 
      pr.(left_a) (InfixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CR_infix_infix o1 o2)
  | CRight o1 o2 : 
      pr.(right_a) (InfixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CL_infix_infix o1 o2)
  | CPrio_infix_infix_1 o1 o2 :
      pr.(prio) (InfixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CL_infix_infix o1 o2)
  | CPrio_infix_infix_2 o1 o2 :
      pr.(prio) (InfixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CR_infix_infix o1 o2)
  | CPrio_prefix_infix o1 o2 :
      pr.(prio) (PrefixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CR_prefix_infix o1 o2).

Inductive rm_conflict_pattern {g} (pr : drules g) : tree_pattern g -> Prop :=
  | CPrio_infix_prefix o1 o2 :
      pr.(prio) (InfixProd o1) (PrefixProd o2) ->
      rm_conflict_pattern pr (CL_infix_prefix o1 o2).

Definition dlanguage {g} (pr : drules g) w : Prop :=
  exists t, wf_parse_tree g t /\ yield t = w /\
    conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) t.

Definition safe {g} (pr : drules g) : Prop :=
  forall w, language w -> dlanguage pr w.

Definition complete {g} (pr : drules g) : Prop :=
  forall t1 t2,
    yield t1 = yield t2 ->
    conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) t1 ->
    conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) t2 ->
    t1 = t2.

Definition safe_pr {g} (pr : drules g) : Prop :=
  forall p1 p2,
    (pr.(prio) p1 p2 \/ (pr.(left_a)) p1 p2) ->
    (pr.(prio) p2 p1 \/ (pr.(right_a)) p2 p1) ->
    False.

Definition is_i_conflict_pattern {g} (pr : drules g) (q : tree_pattern g) :=
  match q with
  | InfixPatt (InfixPatt HPatt o2 HPatt) o1 HPatt =>
      if decide (pr.(prio) (InfixProd o1) (InfixProd o2)) then true
      else if decide (pr.(right_a) (InfixProd o1) (InfixProd o2)) then true
      else false
  | InfixPatt HPatt o1 (InfixPatt HPatt o2 HPatt) =>
      if decide (pr.(prio) (InfixProd o1) (InfixProd o2)) then true
      else if decide (pr.(left_a) (InfixProd o1) (InfixProd o2)) then true
      else false
  | PrefixPatt o1 (InfixPatt HPatt o2 HPatt) =>
      if decide (pr.(prio) (PrefixProd o1) (InfixProd o2)) then true
      else false
  | _ => false
  end.

Definition is_rm_conflict_pattern {g} (pr : drules g) (q : tree_pattern g) :=
  match q with
  | InfixPatt (PrefixPatt o2 HPatt) o1 HPatt =>
      if decide (pr.(prio) (InfixProd o1) (PrefixProd o2)) then true
      else false
  | _ => false
  end.

Fixpoint linsert_lo {g} (pr : drules g) l1 o t2 : parse_tree g :=
  match t2 with
  | InfixNode t21 o2 t22 =>
      if is_i_conflict_pattern pr (CR_infix_infix o o2)
      then InfixNode (linsert_lo pr l1 o t21) o2 t22
      else InfixNode (AtomicNode l1) o t2
  | _ => InfixNode (AtomicNode l1) o t2
  end.

Fixpoint linsert_o {g} (pr : drules g) o t2 : parse_tree g :=
  match t2 with
  | InfixNode t21 o2 t22 =>
      if is_i_conflict_pattern pr (CR_prefix_infix o o2)
      then InfixNode (linsert_o pr o t21) o2 t22
      else PrefixNode o t2
  | _ => PrefixNode o t2
  end.

Fixpoint linsert_to {g} (pr : drules g) t1 o t2 : parse_tree g :=
  match t1 with
  | AtomicNode l1 => linsert_lo pr l1 o t2
  | InfixNode t11 o1 t12 => linsert_to pr t11 o1 (linsert_to pr t12 o t2)
  | PrefixNode o1 t12 => linsert_o pr o1 (linsert_to pr t12 o t2)
  end.

Fixpoint repair {g} (pr : drules g) t : parse_tree g :=
  match t with
  | AtomicNode l => AtomicNode l
  | InfixNode t1 o t2 => linsert_to pr t1 o (repair pr t2)
  | PrefixNode o t2 => linsert_o pr o (repair pr t2)
  end.

Fixpoint slinsert_to {g} (pr : drules g) t1 o t2 : parse_tree g :=
  match t2 with
  | InfixNode t21 o2 t22 =>
      if is_i_conflict_pattern pr (CR_infix_infix o o2)
      then InfixNode (slinsert_to pr t1 o t21) o2 t22
      else InfixNode t1 o t2
  | _ => InfixNode t1 o t2
  end.

Fixpoint parse {g} (pr : drules g) (w : word g) : option (parse_tree g) :=
  match w with
  | [inl l] => Some (AtomicNode l)
  | inl l :: inr o :: w =>
      match (parse pr w) with
      | None => None
      | Some t => Some (linsert_lo pr l o t)
      end
  | inr o :: w =>
      match (parse pr w) with
      | None => None
      | Some t => Some (linsert_o pr o t)
      end
  | _ => None
  end.

Inductive yield_struct {g} : word g -> Prop :=
  | LYield l :
      yield_struct [inl l]
  | LOYield l o w :
      yield_struct w ->
      yield_struct (inl l :: inr o :: w)
  | OYield o w :
      yield_struct w ->
      yield_struct (inr o :: w).

End IPGrammar.
