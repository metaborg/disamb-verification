Require Import PosTree.
Require Import MyUtils.
From stdpp Require Import list.

Section PosTreeTheorems.
Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types pt : @pos_tree L O.

Lemma wf_pos_tree_size i j pt : 
  wf_pos_tree i pt j -> j = i + length (yield (unpos pt)). 
Proof.
  intros.
  induction H; simpl.
  - lia.
  - rewrite app_length.
    simpl.
    lia.
Qed.

Lemma symbol_between_indices i0 pt n i s :
  wf_pos_tree i0 pt n -> nth_symbol i s pt -> le i0 i /\ i < n.
Proof.
  revert i0 i n.
  induction pt; intros.
  - inv H.
    inv H0.
    lia.
  - inv H.
    apply wf_pos_tree_size in H7 as ?.
    apply wf_pos_tree_size in H8 as ?.
    inv H0.
    + split; lia.
    + eapply IHpt1 in H7; [|eassumption].
      destruct H7.
      split; lia.
    + eapply IHpt2 in H8; [|eassumption].
      destruct H8.
      split; lia.
Qed.

Lemma pos_yield pt n0 n s i :
  wf_pos_tree n0 pt n ->
  nth_symbol i s pt -> (yield (unpos pt)) !! (i - n0) = Some s.
Proof.
  intros. induction H.
  - inv H0.
    replace (i0 - i0) with 0; [|lia].
    reflexivity.
  - simpl.
    inv H0.
    + apply wf_pos_tree_size in H.
      apply list_lookup_middle.
      lia.
    + apply lookup_app_l_Some.
      auto.
    + eapply symbol_between_indices in H4 as ?; [|eassumption].
      destruct H0.
      apply wf_pos_tree_size in H.
      apply wf_pos_tree_size in H1.
      apply IHwf_pos_tree2 in H4.
      rewrite <- H4.
      rewrite cons_middle.
      rewrite app_assoc.
      replace (i - S j) with (i - i0 - length (yield (unpos pt1) ++ [inr o])).
      apply lookup_app_r.
      rewrite app_length.
      simpl.
      lia.
      rewrite app_length.
      simpl.
      lia.
Qed.

Lemma yield_pos pt n0 n s i :
  wf_pos_tree n0 pt n ->
  (yield (unpos pt)) !! i = Some s -> nth_symbol (n0 + i) s pt.
Proof.
  intro. revert i.
  induction H; intros; simpl in *; simplify_list_eq.
  - replace (i + 0) with i; [|lia].
    apply L_nth.

  - apply wf_pos_tree_size in H as ?.
    apply wf_pos_tree_size in H0 as ?.

    apply lookup_app_Some in H1.
    destruct H1.
    + apply Symbol_nth1.
      apply IHwf_pos_tree1.
      assumption.
    + destruct H1.
      destruct (i0 - length (yield (unpos pt1))) eqn:E.
      * simplify_list_eq.
        replace i0 with (length (yield (unpos pt1))); [|lia].
        apply O_nth.
      * simplify_list_eq.
        apply Symbol_nth2.
        apply IHwf_pos_tree2 in H4.
        replace (i + i0) with (S (i + length (yield (unpos pt1)) + n)).
        assumption.
        lia.
Qed.

Lemma pos_equivalence_yields pt1 pt2 n0 n :
  wf_pos_tree n0 pt1 n -> wf_pos_tree n0 pt2 n ->
  (pos_equivalent pt1 pt2 <-> yield (unpos pt1) = yield (unpos pt2)).
Proof.
  intros.
  split.

  - intros.
    unfold pos_equivalent in H1.
    apply nth_error_equality.
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

Lemma pos_tree_parse_tree (P : @parse_tree L O -> Prop) :
  (forall n0 pt n, wf_pos_tree n0 pt n -> P (unpos pt)) -> forall t, P t.
Proof.
  intros.
  remember (pos t 0) as x.
  destruct x.
  specialize H with (n0 := 0) (pt := p) (n := n).
  symmetry in Heqx.
  apply pos_wf_pos_tree in Heqx as ?.
  apply H in H0.
  apply pos_unpos in Heqx.
  rewrite Heqx in H0.
  assumption.
Qed.

Lemma symbol_nth_subtree_l n0 n i j s o pt1 pt2 :
  wf_pos_tree n0 (PINode pt1 o i pt2) n ->
  nth_symbol j s (PINode pt1 o i pt2) ->
  j < i ->
  nth_symbol j s pt1.
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

Lemma symbol_nth_subtree_r n0 n i j s o pt1 pt2 :
  wf_pos_tree n0 (PINode pt1 o i pt2) n ->
  nth_symbol j s (PINode pt1 o i pt2) ->
  j > i ->
  nth_symbol j s pt2.
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

Lemma pos_equivalent_subtrees pt1 pt1_1 pt1_2 pt2 pt2_1 pt2_2 o i n0 n :
  pt1 = PINode pt1_1 o i pt1_2 ->
  pt2 = PINode pt2_1 o i pt2_2 ->
  wf_pos_tree n0 pt1 n ->
  wf_pos_tree n0 pt2 n ->
  pos_equivalent pt1 pt2 ->
  pos_equivalent pt1_1 pt2_1 /\ pos_equivalent pt1_2 pt2_2.
Proof.
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
      assert (nth_symbol i0 s (PINode pt1_1 o i pt1_2)). {
        apply Symbol_nth1.
        assumption.
      }
      apply H in H6.
      eauto using symbol_nth_subtree_l.
    + assert (H2' := H2).
      inv H2'.
      eapply symbol_between_indices in H3 as ?; [|eassumption].
      destruct H4.
      assert (nth_symbol i0 s (PINode pt2_1 o i pt2_2)). {
        apply Symbol_nth1.
        assumption.
      }
      apply H0 in H6.
      eauto using symbol_nth_subtree_l.
  - specialize H3 with (s := s) (i0 := i0).
    destruct H3.
    split; intros.
    + assert (H1' := H1).
      inv H1'.
      eapply symbol_between_indices in H3 as ?; [|eassumption].
      destruct H4.
      assert (nth_symbol i0 s (PINode pt1_1 o i pt1_2)). {
        apply Symbol_nth2.
        assumption.
      }
      apply H in H6.
      eauto using symbol_nth_subtree_r.
    + assert (H2' := H2).
      inv H2'.
      eapply symbol_between_indices in H3 as ?; [|eassumption].
      destruct H4.
      assert (nth_symbol i0 s (PINode pt2_1 o i pt2_2)). {
        apply Symbol_nth2.
        assumption.
      }
      apply H0 in H6.
      eauto using symbol_nth_subtree_r.
Qed.

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
