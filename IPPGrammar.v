From stdpp Require Export list.

Section IPPGrammar.

Inductive prod OP :=
  | InfixProd : OP -> prod OP
  | PrefixProd : OP -> prod OP.
  (* | PostfixProd : OP -> prod OP. *)

Arguments InfixProd {_} _.
Arguments PrefixProd {_} _.
(* Arguments PostfixProd {_} _. *)

Record ippg := mkIppgrammar {
  LEX : Type;
  OP : Type;
  prods: prod OP -> Prop
}.

Definition word (g : ippg) := list (LEX g + OP g).

Inductive parse_tree (g : ippg) :=
  | AtomicNode : LEX g -> parse_tree g
  | InfixNode : parse_tree g -> OP g -> parse_tree g -> parse_tree g
  | PrefixNode : OP g -> parse_tree g -> parse_tree g.
  (* | PostfixNode : parse_tree g -> OP g -> parse_tree g. *)

Arguments AtomicNode {_} _.
Arguments InfixNode {_} _ _ _.
Arguments PrefixNode {_} _ _.
(* Arguments PostfixNode {_} _ _. *)

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
  (* | PostfixNode_wf t o :
      g.(prods) (PostfixProd o) ->
      wf_parse_tree g t ->
      wf_parse_tree g (PostfixNode t o). *)

Fixpoint yield {g} t : word g :=
  match t with
  | AtomicNode l => [inl l]
  | InfixNode t1 o t2 => yield t1 ++ inr o :: yield t2
  | PrefixNode o t => inr o :: yield t
  (* | PostfixNode t o => yield t ++ [inr o] *)
  end.

Definition language {g} w : Prop :=
  exists (t : parse_tree g), wf_parse_tree g t /\ yield t = w.

Inductive tree_pattern g :=
  | HPatt : tree_pattern g
  | InfixPatt : tree_pattern g -> OP g -> tree_pattern g -> tree_pattern g
  | PrefixPatt : OP g -> tree_pattern g -> tree_pattern g.
  (* | PostfixPatt : tree_pattern g -> OP g -> tree_pattern g. *)

Arguments HPatt {_}.
Arguments InfixPatt {_} _ _ _.
Arguments PrefixPatt {_} _ _.
(* Arguments PostfixPatt {_} _ _. *)

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
  (* | PostfixMatch t q o :
      matches t q ->
      matches (PostfixNode t o) (PostfixPatt q o). *)

Definition matches_set {g} t (Q : tree_pattern g -> Prop) : Prop :=
  exists q, Q q /\ matches t q.

Inductive conflict_free {g} (Q : tree_pattern g -> Prop) : parse_tree g -> Prop :=
  | Atomic_cf l :
      conflict_free Q (AtomicNode l)
  | Infix_cf t1 o t2 :
      ~ matches_set (InfixNode t1 o t2) Q ->
      conflict_free Q t1 ->
      conflict_free Q t2 ->
      conflict_free Q (InfixNode t1 o t2)
  | Prefix_cf t o :
      ~ matches_set (PrefixNode o t) Q ->
      conflict_free Q t ->
      conflict_free Q (PrefixNode o t).
  (* | PostfixNode_cf t o :
      ~ matches_set (PostfixNode t o) Q ->
      conflict_free Q t ->
      conflict_free Q (PostfixNode t o). *)

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

Inductive conflict_pattern {g} (pr : drules g) : tree_pattern g -> Prop :=
  | CLeft o1 o2 : 
      pr.(left_a) (InfixProd o1) (InfixProd o2) ->
      conflict_pattern pr (CR_infix_infix o1 o2)
  | CRight o1 o2 : 
      pr.(right_a) (InfixProd o1) (InfixProd o2) ->
      conflict_pattern pr (CL_infix_infix o1 o2)
  | CPrio_infix_infix_1 o1 o2 :
      pr.(prio) (InfixProd o1) (InfixProd o2) ->
      conflict_pattern pr (CL_infix_infix o1 o2)
  | CPrio_infix_infix_2 o1 o2 :
      pr.(prio) (InfixProd o1) (InfixProd o2) ->
      conflict_pattern pr (CR_infix_infix o1 o2)
  | CPrio_infix_prefix o1 o2 :
      pr.(prio) (InfixProd o1) (PrefixProd o2) ->
      conflict_pattern pr (CL_infix_prefix o1 o2)
  | CPrio_prefix_infix o1 o2 :
      pr.(prio) (PrefixProd o1) (InfixProd o2) ->
      conflict_pattern pr (CR_prefix_infix o1 o2).

Require Import MyUtils.

Lemma dec_conflict_pattern {g} (pr : drules g) `{drules_dec pr} (q : tree_pattern g) :
  Decision (conflict_pattern pr q).
Proof.
  destruct drules_dec0.
  unfold Decision. destruct q.
  - right. intro. inv H.
  - destruct q1, q2.
    + right. intro. inv H.
    + destruct q2_1. destruct q2_2.
      * replace (InfixPatt HPatt o (InfixPatt HPatt o0 HPatt)) with (CR_infix_infix o o0); try reflexivity.
        specialize dec_prio0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        specialize dec_left_a0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        destruct dec_prio0, dec_left_a0; auto using CPrio_infix_infix_2, CLeft.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
    + destruct q1_1. destruct q1_2.
      * replace (InfixPatt (InfixPatt HPatt o0 HPatt) o HPatt) with (CL_infix_infix o o0); try reflexivity.
        specialize dec_prio0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        specialize dec_right_a0 with (p1 := InfixProd o) (p2 := InfixProd o0).
        destruct dec_prio0, dec_right_a0; auto using CPrio_infix_infix_1, CRight.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
    + right. intro. inv H.
    + destruct q1.
      * replace (InfixPatt (PrefixPatt o0 HPatt) o HPatt) with (CL_infix_prefix o o0); try reflexivity.
        specialize dec_prio0 with (p1 := InfixProd o) (p2 := PrefixProd o0).
        destruct dec_prio0; auto using CPrio_infix_prefix.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
    + right. intro. inv H.
  - destruct q.
    + right. intro. inv H.
    + destruct q1, q2.
      * replace (PrefixPatt o (InfixPatt HPatt o0 HPatt)) with (CR_prefix_infix o o0); try reflexivity.
        specialize dec_prio0 with (p1 := PrefixProd o) (p2 := InfixProd o0).
        destruct dec_prio0; auto using CPrio_prefix_infix.
        right. intro. inv H; contradiction.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
      * right. intro. inv H.
    + right. intro. inv H.
Qed.

Definition dlanguage {g} (pr : drules g) w : Prop :=
  exists t, wf_parse_tree g t /\ yield t = w /\ conflict_free (conflict_pattern pr) t.

Definition safe {g} (pr : drules g) : Prop :=
  forall w, language w -> dlanguage pr w.

Definition safe_pr {g} (pr : drules g) : Prop :=
  forall p1 p2,
    (pr.(prio) p1 p2 \/ (pr.(left_a)) p1 p2) ->
    (pr.(prio) p2 p1 \/ (pr.(right_a)) p2 p1) ->
    False.

Lemma safe_infix_infix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  conflict_pattern pr (CL_infix_infix o1 o2) ->
  conflict_pattern pr (CR_infix_infix o2 o1) ->
  False.
Proof.
  intros H_safe H_CL H_CR. unfold safe_pr in H_safe.
  inv H_CL; inv H_CR; eauto.
Qed.

Lemma safe_infix_prefix {g} (pr : drules g) o1 o2 :
  safe_pr pr ->
  conflict_pattern pr (CL_infix_prefix o1 o2) ->
  conflict_pattern pr (CR_prefix_infix o2 o1) ->
  False.
Proof.
  intros. unfold safe_pr in H.
  inv H0; inv H1; eauto.
Qed.

Inductive linsert_one {g} (pr : drules g) (l1 : LEX g) (o1 : OP g) : 
      parse_tree g -> parse_tree g -> Prop :=
  | Atomic_LInsert_One l2 :
      linsert_one pr l1 o1 (AtomicNode l2)
        (InfixNode (AtomicNode l1) o1 (AtomicNode l2))
  | Infix_LInsert_One_1 t1 o2 t2 :
      ~ conflict_pattern pr (CR_infix_infix o1 o2) ->
      linsert_one pr l1 o1 (InfixNode t1 o2 t2)
        (InfixNode (AtomicNode l1) o1 (InfixNode t1 o2 t2))
  | Infix_LInsert_One_2 t1 o2 t2 t1' :
      conflict_pattern pr (CR_infix_infix o1 o2) ->
      linsert_one pr l1 o1 t1 t1' ->
      linsert_one pr l1 o1 (InfixNode t1 o2 t2)
        (InfixNode t1' o2 t2)
  | Prefix_LInsert_One o2 t :
      linsert_one pr l1 o1 (PrefixNode o2 t)
        (InfixNode (AtomicNode l1) o1 (PrefixNode o2 t)).

Lemma linsert_one_match {g} (pr : drules g) l o1 t t' :
  linsert_one pr l o1 t t' ->
  matches t' (InfixPatt HPatt o1 HPatt) \/
  (exists o2, matches t (InfixPatt HPatt o2 HPatt) /\ matches t' (InfixPatt HPatt o2 HPatt)).
Proof.
  intros. inv H.
  - left. apply InfixMatch; apply HMatch.
  - left. apply InfixMatch; apply HMatch.
  - right. exists o2. split; apply InfixMatch; apply HMatch.
  - left. apply InfixMatch; apply HMatch.
Qed.

Lemma conflict_pattern_cases {O} (pr : drules O) (q : tree_pattern O) (P : Prop) :
  (forall o1 o2, q = CL_infix_infix o1 o2 -> P) ->
  (forall o1 o2, q = CR_infix_infix o1 o2 -> P) ->
  (forall o1 o2, q = CL_infix_prefix o1 o2 -> P) ->
  (forall o1 o2, q = CR_prefix_infix o1 o2 -> P) ->
  (conflict_pattern pr q -> P).
Proof.
  intros. inv H3; eauto.
Qed.

Lemma linsert_one_safe {g} (pr : drules g) l1 o1 t t' :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) t ->
  linsert_one pr l1 o1 t t' ->
  conflict_free (conflict_pattern pr) t'.
Proof.
  intro H_safe. intros. induction H0.
  - apply Infix_cf; auto using Atomic_cf.
    intro. inv H0. inv H1. inv H0; inv H2.
    inv H9. inv H4. inv H4. inv H9. inv H4.
  - apply Infix_cf; auto using Atomic_cf.
    intro. destruct H0. destruct H1 as [q]. inv H0.
    inv H2. inv H1. inv H7; inv H6; inv H1.
    auto using CLeft. auto using CPrio_infix_infix_2.
  - inv H. apply Infix_cf; auto. clear H6 H7.
    intro. destruct H as [q]. inv H.
    eapply conflict_pattern_cases; try eassumption; intros; subst; inv H3.
    + apply linsert_one_match in H1. destruct H1.
      * inv H. inv H6. eauto using safe_infix_infix.
      * destruct H5.
        inv H. inv H1. inv H. inv H3. inv H6.
        exists (CL_infix_infix o0 o3). split; auto.
        unfold CL_infix_infix. auto using HMatch, InfixMatch.
    + inv H11. destruct H5.
      exists (CR_infix_infix o0 o3). split; auto.
      unfold CR_infix_infix. auto using HMatch, InfixMatch.
    + inv H6. inv H1.
  - apply Infix_cf; auto using Atomic_cf.
    intro. destruct H0 as [q]. inv H0.
    inv H2. inv H1. inv H7; inv H6; inv H1.
Qed.

Lemma linsert_one_yield {g} (pr : drules g) l1 o1 t t' :
  linsert_one pr l1 o1 t t' ->
  yield t' = inl l1 :: inr o1 :: yield t.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHlinsert_one. reflexivity.
Qed.

Lemma linsert_one_wf {g} (pr : drules g) l o t t' :
  wf_parse_tree g t ->
  g.(prods) (InfixProd o) ->
  linsert_one pr l o t t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H1.
  - auto using Infix_wf, Atomic_wf.
  - auto using Infix_wf, Atomic_wf.
  - inv H. auto using Infix_wf.
  - auto using Infix_wf, Atomic_wf, Prefix_wf.
Qed.

Lemma linsert_one_exists {g} (pr : drules g) `{drules_dec pr} l o t :
  exists t', linsert_one pr l o t t'.
Proof.
  induction t.
  - eauto using Atomic_LInsert_One.
  - assert (Decision (conflict_pattern pr (CR_infix_infix o o0))). {
      auto using dec_conflict_pattern.
    }
    destruct IHt1, IHt2.
    destruct H.
    + eauto using Infix_LInsert_One_2.
    + eauto using Infix_LInsert_One_1.
  - eauto using Prefix_LInsert_One.
Qed.

Inductive linsert_op {g} (pr : drules g) o1 :
      parse_tree g -> parse_tree g -> Prop :=
  | Atomic_LInsert_Op l :
      linsert_op pr o1 (AtomicNode l)
        (PrefixNode o1 (AtomicNode l))
  | Infix_LInsert_Op_1 t1 o2 t2 :
      ~ conflict_pattern pr (CR_prefix_infix o1 o2) ->
      linsert_op pr o1 (InfixNode t1 o2 t2)
        (PrefixNode o1 (InfixNode t1 o2 t2))
  | Infix_LInsert_Op_2 t1 o2 t2 t1' :
      conflict_pattern pr (CR_prefix_infix o1 o2) ->
      linsert_op pr o1 t1 t1' ->
      linsert_op pr o1 (InfixNode t1 o2 t2)
        (InfixNode t1' o2 t2)
  | Prefix_LInsert_Op o2 t :
      linsert_op pr o1 (PrefixNode o2 t)
        (PrefixNode o1 (PrefixNode o2 t)).

Lemma linsert_op_match {g} (pr : drules g) o1 t t' :
  linsert_op pr o1 t t' ->
  matches t' (PrefixPatt o1 HPatt) \/
  (exists o2, matches t (InfixPatt HPatt o2 HPatt) /\ matches t' (InfixPatt HPatt o2 HPatt)).
Proof.
  intros. inv H; auto using PrefixMatch, HMatch.
  right. exists o2. auto using InfixMatch, HMatch.
Qed. 

Lemma linsert_op_safe {g} (pr : drules g) o1 t t' :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) t ->
  linsert_op pr o1 t t' ->
  conflict_free (conflict_pattern pr) t'.
Proof.
  intro H_safe. intros. induction H0.
  - apply Prefix_cf; auto using Atomic_cf.
    intro. inv H0. inv H1. inv H0; inv H2.
    inv H3.
  - apply Prefix_cf; auto.
    intro. destruct H0.
    destruct H1 as [q]. inv H0. inv H1; inv H2.
    inv H3. auto using CPrio_prefix_infix.
  - inv H. apply Infix_cf; auto.
    intro. destruct H5. destruct H as [q]. inv H.
    eapply conflict_pattern_cases; try eassumption; intros; subst; inv H3.
    + apply linsert_op_match in H1. destruct H1.
      * inv H. inv H5.
      * inv H. inv H1. inv H. inv H5. inv H3.
        eexists. split. eassumption.
        unfold CL_infix_infix. auto using InfixMatch, HMatch.
    + inv H12.
      eexists. split. eassumption.
      unfold CR_infix_infix. auto using InfixMatch, HMatch.
    + apply linsert_op_match in H1. destruct H1.
      * exfalso. inv H5. inv H. eauto using safe_infix_prefix.
      * inv H. inv H1. inv H5. inv H3.
  - apply Prefix_cf; auto.
    intro. inv H0. inv H1. inv H0; inv H2. inv H3.
Qed.

Lemma linsert_op_yield {g} (pr : drules g) o1 t t' :
  linsert_op pr o1 t t' ->
  yield t' = inr o1 :: yield t.
Proof.
  intros. induction H; simpl; auto.
  rewrite IHlinsert_op. reflexivity.
Qed.

Lemma linsert_op_wf {g} (pr : drules g) o1 t t' :
  wf_parse_tree g t ->
  g.(prods) (PrefixProd o1) ->
  linsert_op pr o1 t t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H1.
  - auto using Prefix_wf, Atomic_wf.
  - auto using Prefix_wf, Infix_wf.
  - inv H. auto using Infix_wf.
  - auto using Prefix_wf.
Qed.

Lemma linsert_op_exists {g} (pr : drules g) `{drules_dec pr} o t :
  exists t', linsert_op pr o t t'.
Proof.
  induction t.
  - eauto using Atomic_LInsert_Op.
  - assert (Decision (conflict_pattern pr (CR_prefix_infix o o0))). {
      auto using dec_conflict_pattern.
    }
    destruct IHt1, IHt2.
    destruct H.
    + eauto using Infix_LInsert_Op_2.
    + eauto using Infix_LInsert_Op_1.
  - eauto using Prefix_LInsert_Op.
Qed.

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

Lemma linsert_yield {g} (pr : drules g) o t1 t2 t' :
  linsert pr t1 o t2 t' ->
  yield t' = yield t1 ++ inr o :: yield t2.
Proof.
  intro. induction H; simpl; eauto using linsert_one_yield.
  - rewrite IHlinsert2. rewrite IHlinsert1.
    simplify_list_eq. reflexivity.
  - apply linsert_op_yield in H0.
    rewrite H0. rewrite IHlinsert.
    reflexivity.
Qed.

Lemma linsert_safe {g} (pr : drules g) o t1 t2 t' :
  safe_pr pr ->
  conflict_free (conflict_pattern pr) t2 ->
  linsert pr t1 o t2 t' ->
  conflict_free (conflict_pattern pr) t'.
Proof.
  intros. induction H1; eauto using linsert_one_safe, linsert_op_safe.
Qed.

Lemma linsert_wf {g} (pr : drules g) o t1 t2 t' :
  wf_parse_tree g t1 ->
  g.(prods) (InfixProd o) ->
  wf_parse_tree g t2 ->
  linsert pr t1 o t2 t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H2.
  - eauto using linsert_one_wf.
  - inv H. auto.
  - inv H. eauto using linsert_op_wf.
Qed.

Lemma linsert_exists {g} (pr : drules g) `{drules_dec pr} o t1 t2 :
  exists t', linsert pr t1 o t2 t'.
Proof.
  revert o t2. induction t1; intros.
  - assert (exists t', linsert_one pr l o t2 t'). {
      auto using linsert_one_exists.
    }
    destruct H. eauto using Atomic_LInsert.
  - specialize IHt1_2 with o0 t2. destruct IHt1_2.
    specialize IHt1_1 with o x. destruct IHt1_1.
    eauto using Infix_LInsert.
  - specialize IHt1 with o0 t2. destruct IHt1.
    assert (exists t', linsert_op pr o x t'). {
      auto using linsert_op_exists.
    }
    destruct H0.
    eauto using Prefix_LInsert.
Qed.

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

Lemma fix_tree_safe {g} (pr : drules g) t t' :
  safe_pr pr ->
  fix_tree pr t t' ->
  conflict_free (conflict_pattern pr) t'.
Proof.
  intros. induction H0.
  - apply Atomic_cf.
  - eauto using linsert_safe.
  - eauto using linsert_op_safe.
Qed.

Lemma fix_tree_yield {g} (pr : drules g) t t' :
  fix_tree pr t t' ->
  yield t' = yield t.
Proof.
  intros. induction H; simpl.
  - reflexivity.
  - apply linsert_yield in H0. rewrite H0.
    rewrite IHfix_tree.
    reflexivity.
  - apply linsert_op_yield in H0. rewrite H0.
    rewrite IHfix_tree.
    reflexivity.
Qed.

Lemma fix_tree_wf {g} (pr : drules g) t t' :
  wf_parse_tree g t ->
  fix_tree pr t t' ->
  wf_parse_tree g t'.
Proof.
  intros. induction H0.
  - apply Atomic_wf.
  - inv H. eauto using linsert_wf.
  - inv H. eauto using linsert_op_wf.
Qed.

Lemma fix_tree_exists {g} (pr : drules g) `{drules_dec pr} t :
  exists t', fix_tree pr t t'.
Proof.
  induction t.
  - eauto using Atomic_fix.
  - destruct IHt2.
    assert (exists t', linsert pr t1 o x t'). {
      auto using linsert_exists.
    }
    destruct H0.
    eauto using Infix_fix.
  - destruct IHt.
    assert (exists t', linsert_op pr o x t'). {
      auto using linsert_op_exists.
    }
    destruct H0.
    eauto using Prefix_fix.
Qed.

Theorem safety {g} (pr : drules g) `{drules_dec pr} w :
  safe_pr pr ->
  language w -> dlanguage pr w.
Proof.
  unfold language, dlanguage. intros.
  destruct H0 as [t]. inv H0.
  assert (exists t', fix_tree pr t t'). {
    auto using fix_tree_exists.
  }
  destruct H0 as [t'].
  exists t'.
  split; try split.
  - eauto using fix_tree_wf.
  - eauto using fix_tree_yield.
  - eauto using fix_tree_safe.
Qed.
