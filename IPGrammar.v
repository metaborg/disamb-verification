From stdpp Require Export list.

Section IPGrammar.

Inductive prod OP :=
  | InfixProd : OP -> prod OP
  | PrefixProd : OP -> prod OP.

Arguments InfixProd {_} _.
Arguments PrefixProd {_} _.

Record ippg := mkIppgrammar {
  LEX : Type;
  OP : Type;
  prods: prod OP -> Prop
}.

Definition word g := list (LEX g + OP g).

Inductive parse_tree (g : ippg) :=
  | AtomicNode : LEX g -> parse_tree g
  | InfixNode : parse_tree g -> OP g -> parse_tree g -> parse_tree g
  | PrefixNode : OP g -> parse_tree g -> parse_tree g.

Arguments AtomicNode {_} _.
Arguments InfixNode {_} _ _ _.
Arguments PrefixNode {_} _ _.

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

Arguments HPatt {_}.
Arguments InfixPatt {_} _ _ _.
Arguments PrefixPatt {_} _ _.

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
  right_a : prod g.(OP) -> prod g.(OP) -> Prop
}.

Arguments prio {_} _ _ _.
Arguments left_a {_} _ _ _.
Arguments right_a {_} _ _ _.

Record drules_dec {g} (pr : drules g) := mkDrules_dec {
  dec_prio : forall p1 p2, Decision (pr.(prio) p1 p2);
  dec_left_a : forall p1 p2, Decision (pr.(left_a) p1 p2);
  dec_right_a : forall p1 p2, Decision (pr.(right_a) p1 p2)
}.

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

Definition safe_pr {g} (pr : drules g) : Prop :=
  forall p1 p2,
    (pr.(prio) p1 p2 \/ (pr.(left_a)) p1 p2) ->
    (pr.(prio) p2 p1 \/ (pr.(right_a)) p2 p1) ->
    False.

Inductive linsert_one {g} (pr : drules g) (l1 : LEX g) (o1 : OP g) : 
      parse_tree g -> parse_tree g -> Prop :=
  | Atomic_LInsert_One l2 :
      linsert_one pr l1 o1 (AtomicNode l2)
        (InfixNode (AtomicNode l1) o1 (AtomicNode l2))
  | Infix_LInsert_One_1 t1 o2 t2 :
      ~ i_conflict_pattern pr (CR_infix_infix o1 o2) ->
      linsert_one pr l1 o1 (InfixNode t1 o2 t2)
        (InfixNode (AtomicNode l1) o1 (InfixNode t1 o2 t2))
  | Infix_LInsert_One_2 t1 o2 t2 t1' :
      i_conflict_pattern pr (CR_infix_infix o1 o2) ->
      linsert_one pr l1 o1 t1 t1' ->
      linsert_one pr l1 o1 (InfixNode t1 o2 t2)
        (InfixNode t1' o2 t2)
  | Prefix_LInsert_One o2 t :
      linsert_one pr l1 o1 (PrefixNode o2 t)
        (InfixNode (AtomicNode l1) o1 (PrefixNode o2 t)).

Inductive linsert_op {g} (pr : drules g) o1 :
      parse_tree g -> parse_tree g -> Prop :=
  | Atomic_LInsert_Op l :
      linsert_op pr o1 (AtomicNode l)
        (PrefixNode o1 (AtomicNode l))
  | Infix_LInsert_Op_1 t1 o2 t2 :
      ~ i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
      linsert_op pr o1 (InfixNode t1 o2 t2)
        (PrefixNode o1 (InfixNode t1 o2 t2))
  | Infix_LInsert_Op_2 t1 o2 t2 t1' :
      i_conflict_pattern pr (CR_prefix_infix o1 o2) ->
      linsert_op pr o1 t1 t1' ->
      linsert_op pr o1 (InfixNode t1 o2 t2)
        (InfixNode t1' o2 t2)
  | Prefix_LInsert_Op o2 t :
      linsert_op pr o1 (PrefixNode o2 t)
        (PrefixNode o1 (PrefixNode o2 t)).

Inductive linsert {g} (pr : drules g) :
      parse_tree g -> OP g -> parse_tree g -> parse_tree g -> Prop :=
  | Atomic_LInsert l o t t' :
      linsert_one pr l o t t' ->
      linsert pr (AtomicNode l) o t t'
  | Infix_LInsert t1 o1 t2 o2 t t' t'' :
      linsert pr t2 o2 t t' ->
      linsert pr t1 o1 t' t'' ->
      linsert pr (InfixNode t1 o1 t2) o2 t t''
  | Prefix_LInsert o1 t1 o2 t t' t'':
      linsert pr t1 o2 t t' ->
      linsert_op pr o1 t' t'' ->
      linsert pr (PrefixNode o1 t1) o2 t t''.

Inductive fix_tree {g} (pr : drules g) : parse_tree g -> parse_tree g -> Prop :=
  | Atomic_fix l :
      fix_tree pr (AtomicNode l) (AtomicNode l)
  | Infix_fix t1 o t2 t2' t' :
      fix_tree pr t2 t2' ->
      linsert pr t1 o t2' t' ->
      fix_tree pr (InfixNode t1 o t2) t'
  | Prefix_fix o t1 t1' t' :
      fix_tree pr t1 t1' ->
      linsert_op pr o t1' t' ->
      fix_tree pr (PrefixNode o t1) t'.

End IPGrammar.
