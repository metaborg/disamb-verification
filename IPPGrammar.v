From stdpp Require Export list.
Require Import MyUtils.

Section IPPGrammar.

Inductive prod OP :=
  | InfixProd : OP -> prod OP
  | PrefixProd : OP -> prod OP
  | PostfixProd : OP -> prod OP.

Global Arguments InfixProd {_} _.
Global Arguments PrefixProd {_} _.
Global Arguments PostfixProd {_} _.

Record ipg := mkIpgrammar {
  LEX : Type;
  OPinpre : Type; (* We allow overlap between infix and prefix operators *)
  OPpost : Type;
  prods: prod (OPinpre + OPpost) -> Prop
}.

Definition OP g := OPinpre g + OPpost g : Type.

Definition word g := list (LEX g + OP g).

Inductive parse_tree (g : ipg) :=
  | AtomicNode : LEX g -> parse_tree g
  | InfixNode : parse_tree g -> OP g -> parse_tree g -> parse_tree g
  | PrefixNode : OP g -> parse_tree g -> parse_tree g
  | PostfixNode : parse_tree g -> OP g -> parse_tree g.

Global Arguments AtomicNode {_} _.
Global Arguments InfixNode {_} _ _ _.
Global Arguments PrefixNode {_} _ _.
Global Arguments PostfixNode {_} _ _.

Inductive wf_parse_tree g : parse_tree g -> Prop :=
  | Atomic_wf l :
      wf_parse_tree g (AtomicNode l)
  | Infix_wf t1 o t2 :
      g.(prods) (InfixProd (inl o)) ->
      wf_parse_tree g t1 ->
      wf_parse_tree g t2 ->
      wf_parse_tree g (InfixNode t1 (inl o) t2)
  | Prefix_wf o t :
      g.(prods) (PrefixProd (inl o)) ->
      wf_parse_tree g t ->
      wf_parse_tree g (PrefixNode (inl o) t)
  | Postfix_wf o t :
      g.(prods) (PostfixProd (inr o)) ->
      wf_parse_tree g t ->
      wf_parse_tree g (PostfixNode t (inr o)).

Fixpoint yield {g} t : word g :=
  match t with
  | AtomicNode l => [inl l]
  | InfixNode t1 o t2 => yield t1 ++ inr o :: yield t2
  | PrefixNode o t => inr o :: yield t
  | PostfixNode t o => yield t ++ [inr o]
  end.

Definition language {g} w : Prop :=
  exists (t : parse_tree g), wf_parse_tree g t /\ yield t = w.

Inductive tree_pattern g :=
  | HPatt : tree_pattern g
  | InfixPatt : tree_pattern g -> OP g -> tree_pattern g -> tree_pattern g
  | PrefixPatt : OP g -> tree_pattern g -> tree_pattern g
  | PostfixPatt : tree_pattern g -> OP g -> tree_pattern g.

Global Arguments HPatt {_}.
Global Arguments InfixPatt {_} _ _ _.
Global Arguments PrefixPatt {_} _ _.
Global Arguments PostfixPatt {_} _ _.

Inductive matches {g} : parse_tree g -> tree_pattern g -> Prop :=
  | HMatch t :
      matches t HPatt
  | InfixMatch t1 t2 q1 q2 o :
      matches t1 q1 ->
      matches t2 q2 -> 
      matches (InfixNode t1 o t2) (InfixPatt q1 o q2)
  | PrefixMatch t q o :
      matches t q ->
      matches (PrefixNode o t) (PrefixPatt o q)
  | PostfixMatch t q o :
      matches t q ->
      matches (PostfixNode t o) (PostfixPatt q o).

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
      i_conflict_free Q (PrefixNode o t)
  | Postfix_cf t o :
      ~ matches_set (PostfixNode t o) Q ->
      i_conflict_free Q t ->
      i_conflict_free Q (PostfixNode t o).

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
      matches_drm (PrefixNode o t) (PrefixPatt o q)
  | PostfixMatch_drm t o q :
      matches_rm t q ->
      matches_drm (PostfixNode t o) (PostfixPatt q o).

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
      drm_conflict_free Q (PrefixNode o t)
  | Postfix_drmcf t o :
      ~ matches_drm_set (PostfixNode t o) Q ->
      drm_conflict_free Q t ->
      drm_conflict_free Q (PostfixNode t o).

Inductive matches_lm {g} : parse_tree g -> tree_pattern g -> Prop :=
  | Match_lm t q :
      matches t q ->
      matches_lm t q
  | InfixMatch_lm t1 o t2 q :
      matches_lm t1 q ->
      matches_lm (InfixNode t1 o t2) q
  | PostfixMatch_lm o t q :
      matches_lm t q ->
      matches_lm (PostfixNode t o) q.

Inductive matches_dlm {g} : parse_tree g -> tree_pattern g -> Prop :=
  | InfixMatch_dlm t1 t2 q1 q2 o :
      matches_lm t1 q1 ->
      matches_lm t2 q2 ->
      matches_dlm (InfixNode t1 o t2) (InfixPatt q1 o q2)
  | PrefixMatch_dlm t q o : 
      matches_lm t q ->
      matches_dlm (PrefixNode o t) (PrefixPatt o q)
  | PostfixMatch_dlm t o q :
      matches_lm t q ->
      matches_dlm (PostfixNode t o) (PostfixPatt q o).

Definition matches_dlm_set {g} t (Q : tree_pattern g -> Prop) : Prop :=
  exists q, Q q /\ matches_dlm t q.

Inductive dlm_conflict_free {g} (Q : tree_pattern g -> Prop) : parse_tree g -> Prop :=
  | Atomic_dlmcf l :
      dlm_conflict_free Q (AtomicNode l)
  | Infix_dlmcf t1 o t2 :
      ~ matches_dlm_set (InfixNode t1 o t2) Q ->
      dlm_conflict_free Q t1 ->
      dlm_conflict_free Q t2 ->
      dlm_conflict_free Q (InfixNode t1 o t2)
  | Prefix_dlmcf t o :
      ~ matches_dlm_set (PrefixNode o t) Q ->
      dlm_conflict_free Q t ->
      dlm_conflict_free Q (PrefixNode o t)
  | Postfix_dlmcf t o :
      ~ matches_dlm_set (PostfixNode t o) Q ->
      dlm_conflict_free Q t ->
      dlm_conflict_free Q (PostfixNode t o).

Definition conflict_free {g} (Qi Qrm Qlm : tree_pattern g -> Prop) t :=
  i_conflict_free Qi t /\ drm_conflict_free Qrm t /\ dlm_conflict_free Qlm t.

Record drules g := mkDrules {
  prio : prod (OP g) -> prod (OP g) -> Prop;
  left_a : prod (OP g) -> prod (OP g) -> Prop;
  right_a : prod (OP g) -> prod (OP g) -> Prop;

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
Definition CR_infix_infix {g} o1 o2 : tree_pattern g :=
  InfixPatt HPatt o1 (InfixPatt HPatt o2 HPatt).
Definition CL_infix_prefix {g} o1 o2 : tree_pattern g :=
  InfixPatt (PrefixPatt o2 HPatt) o1 HPatt.
Definition CR_infix_postfix {g} o1 o2 : tree_pattern g :=
  InfixPatt HPatt o1 (PostfixPatt HPatt o2).
Definition CR_prefix_infix {g} o1 o2 : tree_pattern g :=
  PrefixPatt o1 (InfixPatt HPatt o2 HPatt).
Definition CL_postfix_infix {g} o1 o2 : tree_pattern g :=
  PostfixPatt (InfixPatt HPatt o2 HPatt) o1.
Definition CR_prefix_postfix {g} o1 o2 : tree_pattern g :=
  PrefixPatt o1 (PostfixPatt HPatt o2).
Definition CL_postfix_prefix {g} o1 o2 : tree_pattern g :=
  PostfixPatt (PrefixPatt o2 HPatt) o1.

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
      i_conflict_pattern pr (CR_prefix_infix o1 o2)
  | CLeft_prefix_infix o1 o2 :
      pr.(left_a) (PrefixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CR_prefix_infix o1 o2)
  | CPrio_postfix_infix o1 o2 :
      pr.(prio) (PostfixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CL_postfix_infix o1 o2)
  | CRight_postfix_infix o1 o2 :
      pr.(right_a) (PostfixProd o1) (InfixProd o2) ->
      i_conflict_pattern pr (CL_postfix_infix o1 o2).

Inductive rm_conflict_pattern {g} (pr : drules g) : tree_pattern g -> Prop :=
  | CPrio_infix_prefix o1 o2 :
      pr.(prio) (InfixProd o1) (PrefixProd o2) ->
      rm_conflict_pattern pr (CL_infix_prefix o1 o2)
  | CRight_infix_prefix o1 o2 :
      pr.(right_a) (InfixProd o1) (PrefixProd o2) ->
      rm_conflict_pattern pr (CL_infix_prefix o1 o2)
  | CPrio_postfix_prefix o1 o2 :
      pr.(prio) (PostfixProd o1) (PrefixProd o2) ->
      rm_conflict_pattern pr (CL_postfix_prefix o1 o2)
  | CRight_postfix_prefix o1 o2 :
      pr.(right_a) (PostfixProd o1) (PrefixProd o2) ->
      rm_conflict_pattern pr (CL_postfix_prefix o1 o2).

Inductive lm_conflict_pattern {g} (pr : drules g) : tree_pattern g -> Prop :=
  | CPrio_infix_postfix o1 o2 :
      pr.(prio) (InfixProd o1) (PostfixProd o2) ->
      lm_conflict_pattern pr (CR_infix_postfix o1 o2)
  | CLeft_infix_postfix o1 o2 :
      pr.(left_a) (InfixProd o1) (PostfixProd o2) ->
      lm_conflict_pattern pr (CR_infix_postfix o1 o2)
  | CPrio_prefix_postfix o1 o2 :
      pr.(prio) (PrefixProd o1) (PostfixProd o2) ->
      lm_conflict_pattern pr (CR_prefix_postfix o1 o2)
  | CLeft_prefix_postfix o1 o2 :
      pr.(left_a) (PrefixProd o1) (PostfixProd o2) ->
      lm_conflict_pattern pr (CR_prefix_postfix o1 o2).

Definition cfree {g} (pr : drules g) t : Prop :=
  conflict_free (i_conflict_pattern pr) (rm_conflict_pattern pr) (lm_conflict_pattern pr) t.

Definition dlanguage {g} (pr : drules g) w : Prop :=
  exists t, wf_parse_tree g t /\ yield t = w /\
    cfree pr t.

Definition safe {g} (pr : drules g) : Prop :=
  forall w, language w -> dlanguage pr w.

Definition complete {g} (pr : drules g) : Prop :=
  forall t1 t2,
    yield t1 = yield t2 ->
    cfree pr t1 ->
    cfree pr t2 ->
    t1 = t2.

Definition safe_pr {g} (pr : drules g) : Prop :=
  forall p1 p2,
    (pr.(prio) p1 p2 \/ (pr.(left_a)) p1 p2) ->
    (pr.(prio) p2 p1 \/ (pr.(right_a)) p2 p1) ->
    False.

Record complete_pr {g} (pr : drules g) := mkComplete_pr {
  complete_1 : forall o1 o2,
    pr.(prio) o1 o2 \/ pr.(left_a) o1 o2 \/
    pr.(prio) o2 o1 \/ pr.(right_a) o2 o1;

  complete_2 : forall o1 o2 o3,
    pr.(prio) o1 o2 -> pr.(prio) o2 o3 -> pr.(prio) o1 o3;

  complete_3 : forall o1 o2 o3,
    pr.(prio) o1 o2 -> pr.(prio) o2 o3 -> pr.(prio) o1 o3;
  complete_4 : forall o1 o2 o3,
    pr.(prio) o1 o2 -> pr.(left_a) o2 o3 -> pr.(prio) o1 o3;
  complete_5 : forall o1 o2 o3,
    pr.(prio) o1 o2 -> pr.(right_a) o2 o3 -> pr.(prio) o1 o3;
  complete_6 : forall o1 o2 o3,
    pr.(left_a) o1 o2 -> pr.(prio) o2 o3 -> pr.(prio) o1 o3;
  complete_7 : forall o1 o2 o3,
    pr.(right_a) o1 o2 -> pr.(prio) o2 o3 -> pr.(prio) o1 o3;

  complete_8 : forall o1 o2 o3,
    pr.(left_a) o1 o2 -> pr.(left_a) o2 o3 -> pr.(left_a) o1 o3;
  complete_9 : forall o1 o2 o3,
    pr.(right_a) o1 o2 -> pr.(right_a) o2 o3 -> pr.(right_a) o1 o3;

  complete_10 : forall o1 o2 o3,
    pr.(left_a) o1 o2 -> pr.(right_a) o2 o3 -> False;
  complete_11 : forall o1 o2 o3,
    pr.(right_a) o1 o2 -> pr.(left_a) o2 o3 -> False;
}.

End IPPGrammar.

Section IPPGrammarRepair.

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
      else if decide (pr.(left_a) (PrefixProd o1) (InfixProd o2)) then true
      else false
  | PostfixPatt (InfixPatt HPatt o2 HPatt) o1 =>
      if decide (pr.(prio) (PostfixProd o1) (InfixProd o2)) then true
      else if decide (pr.(right_a) (PostfixProd o1) (InfixProd o2)) then true
      else false
  | _ => false
  end.

Definition is_lm_conflict_pattern {g} (pr : drules g) (q : tree_pattern g) :=
  match q with
  | InfixPatt HPatt o1 (PostfixPatt HPatt o2) =>
      if decide (pr.(prio) (InfixProd o1) (PostfixProd o2)) then true
      else if decide (pr.(left_a) (InfixProd o1) (PostfixProd o2)) then true
      else false
  | PrefixPatt o1 (PostfixPatt HPatt o2) =>
      if decide (pr.(prio) (PrefixProd o1) (PostfixProd o2)) then true
      else if decide (pr.(left_a) (PrefixProd o1) (PostfixProd o2)) then true
      else false
  | _ => false
  end.

Fixpoint has_infix_lm_conflicts {g} (pr : drules g) o t2 : bool :=
  match t2 with
  | PostfixNode t21 o2 =>
      if is_lm_conflict_pattern pr (CR_infix_postfix o o2) then true
      else has_infix_lm_conflicts pr o t21
  | InfixNode t21 o2 t22 => has_infix_lm_conflicts pr o t21
  | _ => false
  end.

Fixpoint has_prefix_lm_conflicts {g} (pr : drules g) o t2 : bool :=
  match t2 with
  | PostfixNode t21 o2 =>
      if is_lm_conflict_pattern pr (CR_prefix_postfix o o2) then true
      else has_prefix_lm_conflicts pr o t21
  | InfixNode t21 o2 t22 => has_prefix_lm_conflicts pr o t21
  | _ => false
  end.

Fixpoint has_postfix_rm_conflicts {g} (pr : drules g) t1 o : bool :=
  match t1 with
  | PrefixNode o1 t12 =>
      if decide (pr.(prio) (PostfixProd o) (PrefixProd o1)) then true
      else if decide (pr.(right_a) (PostfixProd o) (PrefixProd o1)) then true
      else has_postfix_rm_conflicts pr t12 o
  | InfixNode t11 o1 t12 => has_postfix_rm_conflicts pr t12 o
  | _ => false
  end.

Fixpoint insert_pre {g} (pr : drules g) o t2 : parse_tree g :=
  match t2 with
  | InfixNode t21 o2 t22 =>
      if is_i_conflict_pattern pr (CR_prefix_infix o o2)
      then InfixNode (insert_pre pr o t21) o2 t22
      else if has_prefix_lm_conflicts pr o t2
      then InfixNode (insert_pre pr o t21) o2 t22
      else PrefixNode o t2
  | PostfixNode t21 o2 =>
      if has_prefix_lm_conflicts pr o t2
      then PostfixNode (insert_pre pr o t21) o2
      else PrefixNode o t2
  | _ => PrefixNode o t2
  end.

Fixpoint insert_post {g} (pr : drules g) t1 o : parse_tree g :=
  match t1 with
  | InfixNode t11 o1 t12 =>
      if is_i_conflict_pattern pr (CL_postfix_infix o o1)
      then InfixNode t11 o1 (insert_post pr t12 o)
      else if has_postfix_rm_conflicts pr t1 o
      then InfixNode t11 o1 (insert_post pr t12 o)
      else PostfixNode t1 o
  | PrefixNode o1 t12 =>
      if has_postfix_rm_conflicts pr t1 o
      then PrefixNode o1 (insert_post pr t12 o)
      else PostfixNode t1 o
  | _ => PostfixNode t1 o
  end.

Fixpoint insert_in {g} (pr : drules g) t1 o t2 : parse_tree g :=
  match t2 with
  | InfixNode t21 o2 t22 =>
      if is_i_conflict_pattern pr (CR_infix_infix o o2)
      then InfixNode (insert_in pr t1 o t21) o2 t22
      else if has_infix_lm_conflicts pr o t2
      then InfixNode (insert_in pr t1 o t21) o2 t22
      else InfixNode t1 o t2
  | PostfixNode t21 o2 =>
      if has_infix_lm_conflicts pr o t2
      then PostfixNode (insert_in pr t1 o t21) o2
      else InfixNode t1 o t2
  | _ => InfixNode t1 o t2
  end.

Fixpoint repair_in {g} (pr : drules g) t1 o t2 : parse_tree g :=
  match t1 with
  | InfixNode t11 o1 t12 => repair_in pr t11 o1 (repair_in pr t12 o t2)
  | PrefixNode o1 t12 => insert_pre pr o1 (repair_in pr t12 o t2)
  | _ => insert_in pr t1 o t2
  end.


Fixpoint repair {g} (pr : drules g) t : parse_tree g :=
  match t with
  | AtomicNode l => AtomicNode l
  | InfixNode t1 o t2 => repair_in pr (repair pr t1) o (repair pr t2)
  | PrefixNode o t2 => insert_pre pr o (repair pr t2)
  | PostfixNode t1 o => insert_post pr (repair pr t1) o
  end.

End IPPGrammarRepair.
