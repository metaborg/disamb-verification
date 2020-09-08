From stdpp Require Import relations sets.
From stdpp Require Import list.

Require Export PosTreeTheorems.
Require Import MyUtils.

Section GloballyFiniteReorderings.

Context {L O : Type}.

Implicit Types o : O.
Implicit Types l : L.
Implicit Types t : @parse_tree L O.
Implicit Types pt : @pos_tree L O.
Implicit Types w : @word L O.
Implicit Types s : L + O.

Fixpoint fill_right_trees (o : O) tl (trs : list (@parse_tree L O)) : list parse_tree :=
  match trs with
  | [] => []
  | tr :: trs => (INode tl o tr) :: (fill_right_trees o tl trs)
  end.

Lemma tree_fills_right o tl tr trs :
  tr ∈ trs → INode tl o tr ∈ fill_right_trees o tl trs.
Proof.
  intros. induction H as [tr|tr e]; simpl.
  - apply elem_of_list_here.
  - auto using elem_of_list_further.
Qed. 

Fixpoint fill_trees (o : O) (tls : list (@parse_tree L O)) (trs : list (@parse_tree L O)) : list parse_tree :=
  match tls with
  | [] => []
  | tl :: tls => (fill_right_trees o tl trs) ++ (fill_trees o tls trs)
  end.

Lemma tree_fills o tl tls tr trs :
  tl ∈ tls → tr ∈ trs → INode tl o tr ∈ fill_trees o tls trs.
Proof.
  intros. induction H as [tl tls|tl e]; simpl.
  - apply elem_of_app. left. auto using tree_fills_right.
  - apply elem_of_app. auto.
Qed.

Fixpoint build_reorderings_h wl wr (fuel : nat) : list parse_tree :=
  match fuel with
  | 0 => []
  | S fuel =>
    match wr with
    | [] => []
    | s :: wr =>
      match s with
      | inl l => (ANode l) :: (build_reorderings_h (wl ++ [s]) wr fuel)
      | inr o => (fill_trees o (build_reorderings_h [] wl fuel) (build_reorderings_h [] wr fuel))
                 ++ (build_reorderings_h (wl ++ [s]) wr fuel)
      end
    end
  end.

Definition build_reorderings w := build_reorderings_h [] w (length w * length w + length w).

Lemma zero_times_zero n :
  n * n = 0 -> n = 0.
Proof.
  intros. destruct n; lia.
Qed.

Lemma yield_non_empty t :
  yield t ≠ [].
Proof.
  intro. destruct t; simpl in H. inv H. destruct (yield t1); inv H.
Qed.

Fixpoint tree_top t : L + O :=
  match t with
  | ANode l => inl l
  | INode _ o _ => inr o
  end.

Lemma tree_top_in_yield t :
  tree_top t ∈ yield t.
Proof.
  destruct t; simpl.
  - apply elem_of_list_singleton. reflexivity.
  - apply elem_of_app. right. apply elem_of_list_here.
Qed.

Fixpoint tree_top_index pt : nat :=
  match pt with
  | PANode _ n => n
  | PINode _ _ n _ => n
  end.

Lemma tree_top_index_gt_start_index pt n0 n :
  wf_pos_tree n0 pt n → tree_top_index pt ≥ n0.
Proof.
  intros. induction H; simpl.
  - lia.
  - apply wf_pos_tree_size in H. lia.
Qed.

Lemma build_reorderings_h_correct fuel wl wr pt n0 n :
  (length wl + length wr) * (length wl + length wr) + length wr ≤ fuel →
  wf_pos_tree n0 pt n →
  yield (unpos pt) = wl ++ wr →
  tree_top_index pt ≥ length wl + n0 →
  unpos pt ∈ build_reorderings_h wl wr fuel.
Proof.
  revert wl wr pt n0 n. induction fuel; intros.

  (* If fuel = 0, show that this cannot happen because that causes a contradiction. *)
  - exfalso.
    assert (length wr * length wr = 0). lia. apply zero_times_zero in H3.
    apply nil_length_inv in H3. subst. destruct pt; simplify_list_eq. lia.
    rewrite app_length in *. simpl in *. lia.

  - (* First showing that wr cannot be empty using the fact that the top operator has to be in wr. *)
    destruct wr; simpl in *. exfalso. destruct pt; simplify_list_eq. inv H0. lia.
    rewrite app_length in *. simpl in *. inv H0. apply wf_pos_tree_size in H8. lia.

    destruct s; simpl in *.
    (* Case: Next element in wr is a lexeme *)
    + (* If pt is just a lexeme, then it must be equal to that element from wr and we're done. *)
      destruct pt. simpl in *. destruct wl; simplify_list_eq. apply elem_of_list_here.
      destruct wl; simplify_list_eq.

      (* If pt is not a lexeme, then the result must be somewhere in the tail of wr. *)
      apply elem_of_list_further. apply IHfuel with (n0 := n0) (n := n).
      * rewrite app_length. simpl. lia.
      * assumption.
      * simplify_list_eq. assumption.
      * simpl in *. rewrite app_length. simpl. inv H0.
        apply wf_pos_tree_size in H9. rewrite H9. simplify_list_eq. inv H2. 
        ** assert (length wl = length (yield (unpos pt1))). lia. simplify_list_eq.
        ** lia.

    (* Case: Next element in wr is an operand symbol. *)
    + (* pt cannot be a lexeme because its yield gives an operand symbol. *)
      destruct pt. simpl in *. destruct wl; simplify_list_eq. destruct wl; simplify_list_eq.
      rename o0 into o_top.

      inv H2.
      * simpl in *. apply elem_of_app. left.
        inv H0. apply wf_pos_tree_size in H9 as ?.
        assert (length wl = length (yield (unpos pt1))). lia. simplify_list_eq.
        apply tree_fills.

        eapply IHfuel.
        simpl. lia.
        eassumption.
        reflexivity.
        simpl. eapply tree_top_index_gt_start_index. eassumption.

        eapply IHfuel.
        simpl. lia.
        eassumption.
        reflexivity.
        simpl. eapply tree_top_index_gt_start_index. eassumption.

      * apply elem_of_app. right.

        eapply IHfuel.
        rewrite app_length. simpl. lia.
        eassumption.
        simplify_list_eq. assumption.
        rewrite app_length. simpl. inv H0. apply wf_pos_tree_size in H10. simplify_list_eq. lia.
Qed.

Lemma build_reorderings_correct t :
  t ∈ build_reorderings (yield t).
Proof.
  unfold build_reorderings.
  remember (pos t 0) as x. destruct x.
  symmetry in Heqx.
  apply pos_unpos in Heqx as ?.
  apply pos_wf_pos_tree in Heqx as ?.
  rewrite <- H.
  eapply build_reorderings_h_correct.
  - simpl. lia.
  - eassumption.
  - reflexivity.
  - simpl. lia.
Qed.

Definition reorder_rel (R : relation (@parse_tree L O)) : Prop :=
  ∀ t t', R t t' → yield t = yield t'.

Lemma reorder_rel_transitive R :
  reorder_rel R → reorder_rel (tc R).
Proof.
  intros.
  intro. intros. induction H0.
  - apply H. assumption.
  - rewrite <- IHtc.
    apply H. assumption.
Qed.

Theorem reorder_rel_globally_finite R t :
  reorder_rel R → pred_finite (tc R t).
Proof.
  intros. exists (build_reorderings (yield t)).
  intros. apply reorder_rel_transitive in H.
  apply H in H0. rewrite H0.
  apply build_reorderings_correct.
Qed.

End GloballyFiniteReorderings.
