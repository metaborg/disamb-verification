From disamb Require Export MixfixRepair.
From disamb Require Export MixfixReorder.
From disamb Require Import MixfixReorderTheorems.
From disamb Require Import MyUtils.

Section MixfixRepairReorder.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)) (b : bool).

Lemma repair_cl_reorder g Q p t1 ts t' b :
  wft g E t1 →
  repair_cl Q p t1 ts = (t', b) → reorder_tree (node p (cons_forest t1 ts)) t'.
Proof.
  intro Hwf. revert t' ts b. induction Hwf using well_formed_parse_tree_forest_rec
    with (P0 := fun p1 t1s Hwfts => ∀ ts ts' b, (b = true ∨ p CL p1 ∠ Q) →
                            repair_cl_forest Q p t1s ts = (ts', b) →
                            reorder_tree (node p (cons_forest (node p1 t1s) ts)) (node p1 ts'));
    intros.
  - simpl in *. inv H. apply rtc_refl.
  - simpl in *. destruct (repair_cl_forest Q p ts ts0) eqn:E.
    destruct (decide (b0 = true ∨ p CL p0 ∠ Q)).
    + inv H.
      eapply IHHwf; eauto.
    + inv H. apply rtc_refl.
  - simpl in *. exfalso.
    destruct H.
    + subst. inv H0.
    + destruct Q.
      apply left_pattern_well_formed in H.
      eapply left_reorderable_nil_false. eassumption.
  - destruct ts.
    + destruct (repair_cl Q p t ts0) eqn:F. inv H0.
      inv w.
      inv Hwf.
      * exfalso.
        simpl in F. inv F.
        destruct H; try inv H.
        destruct Q.
        apply left_pattern_well_formed in H.
        eapply left_reorder_terminal_false. eassumption.
      * eapply rtc_l.
        **repeat constructor.
        **apply IHHwf in F.
          apply reorder_forest_reorder_tree.
          apply reorder_head_tree_reorder_forest.
          assumption.
    + destruct (repair_cl_forest Q p (cons_forest p0 ts) ts0) eqn:F. inv H0.
      simpl in *.


Lemma rcl_reorder Q t :
  reorder_tree t (rcl Q t).
Proof.
  induction t.
  - simpl. apply rtc_refl.
  - simpl. destruct p0.
    + apply rtc_refl.
    + destruct (repair_cl Q p p0 p1) eqn:E.


Theorem repair_reorder Q t :
  reorder_tree t (repair Q t).
Proof.
  induction t using parse_tree_forest_rec
    with (P0 := fun ts => reorder_forest ts (repair_forest Q ts)).
  - simpl. apply rtc_refl.
  - cbn [repair]. destruct (repair_forest Q p0) eqn:E.
    + simpl. apply reorder_forest_reorder_tree. assumption.
    + 
