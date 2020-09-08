Require Export PosTree.

Require Import MyUtils.

Section PosTreeTheorems.
Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types pt : @pos_tree L O.

(* If a pos_tree is well-formed between n0 and n, then its size is n - n0. *)
Lemma wf_pos_tree_size n0 n pt : 
  wf_pos_tree n0 pt n -> n = n0 + length (yield (unpos pt)). 
Proof.
  intros.
  induction H; simpl.
  - lia.
  - rewrite app_length.
    simpl.
    lia.
Qed.

(* If a symbol is in a well-formed pos_tree between n0 and n in i, then n0 <= i < n. *)
Lemma symbol_between_indices n0 pt n i s :
  wf_pos_tree n0 pt n -> ith_symbol i s pt -> le n0 i /\ i < n.
Proof.
  intro.
  induction H; intros.
  (* CASE: pt = (l, n0) *)
  - inv H.
    lia.
  (* CASE: pt = [pt1 (o, j) pt2] *)
  - apply wf_pos_tree_size in H as ?.
    apply wf_pos_tree_size in H0 as ?.
    inv H1.
    (* CASE: s = o *)
    + lia.
    (* CASE: s is in pt1 *)
    + apply IHwf_pos_tree1 in H6.
      lia.
    (* CASE: s is in pt2 *)
    + apply IHwf_pos_tree2 in H6.
      lia.
Qed.

(* If a symbol s is in a well-formed pos_tree between n0 and n in i, then s in the
   (i - n0)th position of the yield. *)
Lemma pos_yield pt n0 n s i :
  wf_pos_tree n0 pt n ->
  ith_symbol i s pt -> (yield (unpos pt)) !! (i - n0) = Some s.
Proof.
  (* By induction over well-formedness of pt *)
  intros. induction H.
  (* CASE: pt = (l, n0) and yield(pt) = l *)
  - inv H0.
    replace (i0 - i0) with 0; [|lia].
    reflexivity.
  (* CASE: pt = [pt1 (o, j) pt2] and yield(pt) = yield(pt1) o yield(pt2). *)
  - simpl.
    apply wf_pos_tree_size in H as ?.
    apply wf_pos_tree_size in H1 as ?.
    inv H0.
    (* CASE: s = o and i = j *)
    + apply list_lookup_middle.
      lia.
    (* CASE: s is in pt1 *)
    + apply lookup_app_l_Some.
      auto.
    (* CASE: s is in pt2 *)
    + eapply symbol_between_indices in H6 as ?; [|eassumption].
      apply wf_pos_tree_size in H.
      apply wf_pos_tree_size in H1.
      apply IHwf_pos_tree2 in H6.
      rewrite <- H6.
      rewrite cons_middle.
      rewrite app_assoc.
      replace (i - S (i0 + length (yield (unpos pt1))))
        with (i - i0 - length (yield (unpos pt1) ++ [inr o])).
      apply lookup_app_r.
      rewrite app_length.
      simpl.
      lia.
      rewrite app_length.
      simpl.
      lia.
Qed.

(* If a symbol s is in the i-th position of the yield of a well-formed pos_tree pt between
   n0 and n, then s is the (n0 + i)th position of the tree. *)
Lemma yield_pos pt n0 n s i :
  wf_pos_tree n0 pt n ->
  (yield (unpos pt)) !! i = Some s -> ith_symbol (n0 + i) s pt.
Proof.
  intro. revert i.
  induction H; intros; simpl in *; simplify_list_eq.
  (* CASE: pt = (l, n0) *)
  - replace (i + 0) with i; [|lia].
    apply L_ith.
  (* CASE: pt = [pt1 (o, j) pt2] *)
  - apply wf_pos_tree_size in H as ?.
    apply wf_pos_tree_size in H0 as ?.
    apply lookup_app_Some in H1.
    destruct H1.
    (* CASE: s is in yield(pt1) *)
    + auto with pos_tree.
    + destruct H1.
      destruct (i0 - length (yield (unpos pt1))) eqn:E; simplify_list_eq.
    (* CASE: s = o *)
      * replace i0 with (length (yield (unpos pt1))); [|lia].
        apply O_ith.
    (* CASE: s is in yield(pt2) *)
      * apply S_ith_r.
        apply IHwf_pos_tree2 in H4.
        replace (i + i0) with (S (i + length (yield (unpos pt1)) + n)); [auto|lia].
Qed.

(* Two pos_trees are position equivalent if and only if they have equal yields. *)
Lemma pos_equivalence_yields pt1 pt2 n0 n :
  wf_pos_tree n0 pt1 n -> wf_pos_tree n0 pt2 n ->
  (pos_equivalent pt1 pt2 <-> yield (unpos pt1) = yield (unpos pt2)).
Proof.
  (* Simple proof by Lemmas pos_yield and yield_pos. *)
  intros.
  split.
  - intros.
    unfold pos_equivalent in H1.
    apply lookup_some_equality.
    intros.
    split.
    + intros.
      eapply yield_pos in H2; [|eassumption].
      apply H1 in H2.
      eapply pos_yield in H2; [|eassumption].
      replace (n0 + i - n0) with i in H2; [|lia].
      assumption.
    + intros.
      eapply yield_pos in H2; [|eassumption].
      apply H1 in H2.
      eapply pos_yield in H2; [|eassumption].
      replace (n0 + i - n0) with i in H2; [|lia].
      assumption.
  - unfold pos_equivalent.
    intros.
    split; intros.
    + eapply symbol_between_indices in H2 as ?; [|eassumption].
      destruct H3.
      eapply pos_yield in H2; [|eassumption].
      rewrite H1 in H2.
      eapply yield_pos in H2; [|eassumption].
      replace (n0 + (i - n0)) with i in H2; [|lia].
      assumption.
    + eapply symbol_between_indices in H2 as ?; [|eassumption].
      destruct H3.
      eapply pos_yield in H2; [|eassumption].
      rewrite <- H1 in H2.
      eapply yield_pos in H2; [|eassumption].
      replace (n0 + (i - n0)) with i in H2; [|lia].
      assumption.
Qed.

(* The pos function actually gives back a well-formed pos_tree. *)
Lemma pos_wf_pos_tree t pt n0 n :
  pos t n0 = (pt, n) -> wf_pos_tree n0 pt n.
Proof.
  revert pt n0 n.
  induction t; intros; simpl in H.
  - inv H.
    apply Wfpos_PANode. 
  - destruct (pos t1 n0) eqn:E1.
    destruct (pos t2 (S n1)) eqn:E2.
    inv H.
    apply Wfpos_PINode; auto.
Qed.

(* Unpos is the injective function of pos. *)
Lemma pos_unpos t n0 p n :
  pos t n0 = (p, n) -> unpos p = t.
Proof.
  revert n0 p n.
  induction t; intros; simpl in H.
  - inv H. reflexivity.
  - destruct (pos t1 n0) eqn:E1.
    destruct (pos t2 (S n1)) eqn:E2.
    inv H.
    apply IHt1 in E1.
    apply IHt2 in E2.
    simpl.
    rewrite E1.
    rewrite E2.
    reflexivity.
Qed.

(* Suppose we have a pos_tree [pt1 (o, j) pt2]. If a symbol is in the i-th position of
   the tree and i < j, then the symbol must be in pt1. *)
Lemma symbol_ith_subtree_l n0 n i j s o pt1 pt2 :
  wf_pos_tree n0 (PINode pt1 o j pt2) n ->
  ith_symbol i s (PINode pt1 o j pt2) ->
  i < j ->
  ith_symbol i s pt1.
Proof.
  intros.
  inv H.
  inv H0.
  - lia.
  - assumption.
  - eapply symbol_between_indices in H3; [|eassumption].
    destruct H3.
    lia.
Qed.

(* Suppose we have a pos_tree [pt1 (o, j) pt2]. If a symbol is in the i-th position of
   the tree and i > j, then the symbol must be in pt2. *)
Lemma symbol_ith_subtree_r n0 n i j s o pt1 pt2 :
  wf_pos_tree n0 (PINode pt1 o j pt2) n ->
  ith_symbol i s (PINode pt1 o j pt2) ->
  i > j ->
  ith_symbol i s pt2.
Proof.
  intros.
  inv H.
  inv H0.
  - lia.
  - eapply symbol_between_indices in H3; [|eassumption].
    destruct H3.
    lia.
  - assumption.
Qed.

(* For two pos_trees where the top operator and index is (o, i). *)
Lemma pos_equivalent_subtrees pt1 pt1_1 pt1_2 pt2 pt2_1 pt2_2 o i n0 n :
  pt1 = PINode pt1_1 o i pt1_2 ->
  pt2 = PINode pt2_1 o i pt2_2 ->
  wf_pos_tree n0 pt1 n ->
  wf_pos_tree n0 pt2 n ->
  pos_equivalent pt1 pt2 ->
  pos_equivalent pt1_1 pt2_1 /\ pos_equivalent pt1_2 pt2_2.
Proof.
  (* By the two above Lemmas. *)
  intros. subst.
  unfold pos_equivalent in *.
  split; intros.
  - specialize H3 with (s := s) (i0 := i0).
    destruct H3.
    split; intros.
    + assert (H1' := H1).
      inv H1'.
      eapply symbol_between_indices in H3 as ?; [|eassumption].
      destruct H4.
      assert (ith_symbol i0 s (PINode pt1_1 o i pt1_2)). {
        auto with pos_tree.
      }
      apply H in H6.
      eauto using symbol_ith_subtree_l.
    + assert (H2' := H2).
      inv H2'.
      eapply symbol_between_indices in H3 as ?; [|eassumption].
      destruct H4.
      assert (ith_symbol i0 s (PINode pt2_1 o i pt2_2)). {
        auto with pos_tree.
      }
      apply H0 in H6.
      eauto using symbol_ith_subtree_l.
  - specialize H3 with (s := s) (i0 := i0).
    destruct H3.
    split; intros.
    + assert (H1' := H1).
      inv H1'.
      eapply symbol_between_indices in H3 as ?; [|eassumption].
      destruct H4.
      assert (ith_symbol i0 s (PINode pt1_1 o i pt1_2)). {
        auto with pos_tree.
      }
      apply H in H6.
      eauto using symbol_ith_subtree_r.
    + assert (H2' := H2).
      inv H2'.
      eapply symbol_between_indices in H3 as ?; [|eassumption].
      destruct H4.
      assert (ith_symbol i0 s (PINode pt2_1 o i pt2_2)). {
        auto with pos_tree.
      }
      apply H0 in H6.
      eauto using symbol_ith_subtree_r.
Qed.

(* Position eequivalence is a transitive relation. *)
Lemma pos_equivalent_transitive pt1 pt2 pt3 :
  pos_equivalent pt1 pt2 -> pos_equivalent pt2 pt3 -> pos_equivalent pt1 pt3.
Proof.
  unfold pos_equivalent.
  intros.
  split; intros.
  - apply H0. apply H.
    assumption.
  - apply H. apply H0.
    assumption.
Qed.

End PosTreeTheorems.
