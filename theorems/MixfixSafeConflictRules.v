From disamb Require Export MixfixDisambiguation.
From disamb Require Import MyUtils.

Section MixfixSafeConflictRules.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ β γ : list (symbol T)) (b : bool) (Q : crules T).

Lemma atomic_symbol_list_to_atomic_parse_list_correct g σ :
  atomic_symbol_list σ →
  ∃ τ, atomic_symbol_list_to_atomic_parse_list σ = Some τ ∧ wfτ g σ τ ∧ atomic_parse_list τ.
Proof.
  intro. induction H; simpl.
  - eexists. split; eauto. split; constructor.
  - destruct IHatomic_symbol_list as [τ2]. inv H0. inv H2.
    eexists. rewrite H1. split; eauto. split; repeat constructor; auto.
Qed.

Lemma atomic_production_to_atomic_parse_tree_correct g p :
  g p → atomic_production p →
  ∃ t, atomic_production_to_atomic_parse_tree p = Some t ∧ wft g E t ∧ atomic_parse_tree t.
Proof.
  intros. inv H0; simpl.
  - eexists. split; eauto. split.
    + constructor. assumption.
    + constructor.
  - apply atomic_symbol_list_to_atomic_parse_list_correct with (g := g) in H1.
    destruct H1 as [τ]. inv H0. inv H2. rewrite H1.
    eexists. split; eauto. split; repeat constructor; auto.
Qed.

Lemma inject_tree_in_symbol_well_formed g X t :
  wft g E t → wft g X (inject_tree_in_symbol X t).
Proof.
  intro. destruct X; simpl; repeat constructor; auto.
Qed.

Lemma inject_tree_in_symbol_list_well_formed g σ t :
  wft g E t → wfτ g σ (inject_tree_in_symbol_list σ t).
Proof.
  intro. induction σ; simpl; constructor; auto using inject_tree_in_symbol_well_formed.
Qed.

Lemma atomic_list_non_reorderable τ_atom τ :
  atomic_parse_list τ_atom →
  ¬ reorder_step_list τ_atom τ.
Proof.
  intro. revert τ. induction H; intros ??.
  - inv H.
  - inv H0.
    + inv H4.
    + eapply IHatomic_parse_list; eauto.
Qed.

Lemma atomic_list_non_reorderable_2 τ_atom τ :
  atomic_parse_list τ_atom →
  ¬ reorder_step_list τ τ_atom.
Proof.
  intro. revert τ. induction H; intros ??.
  - inv H.
  - inv H0.
    + inv H3.
    + eapply IHatomic_parse_list; eauto.
Qed.

Lemma atomic_tree_non_reorderable t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step t_atom t.
Proof.
  intros ??. inv H.
  - inv H0.
  - inv H0.
    + inv H6.
    + eapply atomic_list_non_reorderable; eauto.
    + inv H6.
Qed.

Lemma atomic_tree_non_reorderable_2 t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step t t_atom.
Proof.
  intros ??. inv H.
  - inv H0.
  - inv H0.
    + inv H3.
    + eapply atomic_list_non_reorderable_2; eauto.
    + inv H3.
Qed.

Lemma inject_atomic_tree_in_symbol_non_reorderable X t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step (inject_tree_in_symbol X t_atom) t.
Proof.
  intros ??. destruct X as [a|]; simpl in H0; inv H0.
  - inv H.
  - inv H. inv H1.
  - inv H. eapply atomic_list_non_reorderable; eauto.
  - inv H. inv H1.
Qed.

Lemma inject_atomic_tree_in_symbol_non_reorderable_2 X t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step t (inject_tree_in_symbol X t_atom).
Proof.
  intros ??. destruct X as [a|]; simpl in H0; inv H0.
  - inv H.
  - inv H. inv H1.
  - inv H. eapply atomic_list_non_reorderable_2; eauto.
  - inv H. inv H1.
Qed.

Lemma inject_atomic_tree_in_symbol_list_non_reorderable t_atom σ τ :
  atomic_parse_tree t_atom →
  ¬ reorder_step_list (inject_tree_in_symbol_list σ t_atom) τ.
Proof.
  intro. revert τ. induction σ; simpl; intros ??.
  - inv H0.
  - inv H0.
    + eapply inject_atomic_tree_in_symbol_non_reorderable; eauto.
    + eapply IHσ; eauto.
Qed.

Lemma inject_atomic_tree_in_symbol_list_non_reorderable_2 t_atom σ τ :
  atomic_parse_tree t_atom →
  ¬ reorder_step_list τ (inject_tree_in_symbol_list σ t_atom).
Proof.
  intro. revert τ. induction σ; simpl; intros ??.
  - inv H0.
  - inv H0.
    + eapply inject_atomic_tree_in_symbol_non_reorderable_2; eauto.
    + eapply IHσ; eauto.
Qed.

Lemma special_atomic_injection_non_reorderable_1 β (Xn : symbol T) X1 γ t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step
      (large_node (large_production X1 γ E) (inject_tree_in_symbol X1 t_atom)
          (inject_tree_in_symbol_list γ t_atom) t_atom) t.
Proof.
  intros ??. inv H0.
  - inv H. inv H6.
  - eapply inject_atomic_tree_in_symbol_non_reorderable; eauto.
  - eapply inject_atomic_tree_in_symbol_list_non_reorderable; eauto.
  - eapply atomic_tree_non_reorderable; eauto.
Qed.

Lemma special_atomic_injection_non_reorderable_2 β (Xn : symbol T) X1 γ t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step
      t
      (large_node (large_production X1 γ E) (inject_tree_in_symbol X1 t_atom)
          (inject_tree_in_symbol_list γ t_atom) t_atom).
Proof.
  intros ??. inv H0.
  - destruct X1; simpl in H4; inv H4. inv H. inv H3.
  - eapply inject_atomic_tree_in_symbol_non_reorderable_2; eauto.
  - eapply inject_atomic_tree_in_symbol_list_non_reorderable_2; eauto.
  - eapply atomic_tree_non_reorderable_2; eauto. 
Qed.

Lemma special_atomic_injection_non_reorderable_3 β (Xn : symbol T) X1 γ t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step
      (large_node (large_production E β Xn) t_atom (inject_tree_in_symbol_list β t_atom)
          (inject_tree_in_symbol Xn t_atom)) t.
Proof.
  intros ??. inv H0.
  - destruct Xn; simpl in H5; inv H5. inv H. inv H6.
  - eapply atomic_tree_non_reorderable; eauto.
  - eapply inject_atomic_tree_in_symbol_list_non_reorderable; eauto.
  - eapply inject_atomic_tree_in_symbol_non_reorderable; eauto.
Qed.

Lemma special_atomic_injection_non_reorderable_4 β (Xn : symbol T) X1 γ t_atom t :
  atomic_parse_tree t_atom →
  ¬ reorder_step
      t
      (large_node (large_production E β Xn) t_atom (inject_tree_in_symbol_list β t_atom)
          (inject_tree_in_symbol Xn t_atom)).
Proof.
  intros ??. inv H0.
  - inv H. inv H3.
  - eapply atomic_tree_non_reorderable_2; eauto.
  - eapply inject_atomic_tree_in_symbol_list_non_reorderable_2; eauto.
  - eapply inject_atomic_tree_in_symbol_non_reorderable_2; eauto.
Qed.

Lemma reorder_simple_tree β Xn X1 γ t_atom t1 t2 :
  atomic_parse_tree t_atom →
  reorder t1 t2
  →
  t1 = (large_node (large_production E β Xn)
          (large_node (large_production X1 γ E)
             (inject_tree_in_symbol X1 t_atom)
             (inject_tree_in_symbol_list γ t_atom)
              t_atom
          )
          (inject_tree_in_symbol_list β t_atom)
          (inject_tree_in_symbol Xn t_atom)
       )
  ∨
  t1 = (large_node (large_production X1 γ E)
          (inject_tree_in_symbol X1 t_atom)
          (inject_tree_in_symbol_list γ t_atom)
          (large_node (large_production E β Xn)
             t_atom
             (inject_tree_in_symbol_list β t_atom)
             (inject_tree_in_symbol Xn t_atom)
          )
       )
  →
  t2 = (large_node (large_production E β Xn)
          (large_node (large_production X1 γ E)
             (inject_tree_in_symbol X1 t_atom)
             (inject_tree_in_symbol_list γ t_atom)
              t_atom
          )
          (inject_tree_in_symbol_list β t_atom)
          (inject_tree_in_symbol Xn t_atom)
       )
  ∨
  t2 = (large_node (large_production X1 γ E)
          (inject_tree_in_symbol X1 t_atom)
          (inject_tree_in_symbol_list γ t_atom)
          (large_node (large_production E β Xn)
             t_atom
             (inject_tree_in_symbol_list β t_atom)
             (inject_tree_in_symbol Xn t_atom)
          )
       ).
Proof.
  intros. induction H0.
  - destruct H1; auto.
  - destruct H1.
    + subst. inv H0.
      * exfalso. inv H1.
        **destruct Xn; simpl in H6; inv H6; inv H; inv H7.
        **eapply special_atomic_injection_non_reorderable_1; eauto.
        **eapply inject_atomic_tree_in_symbol_list_non_reorderable; eauto.
        **eapply inject_atomic_tree_in_symbol_non_reorderable; eauto.
      * inv H1.
        **auto.
        **exfalso. eapply special_atomic_injection_non_reorderable_2; eauto.
        **exfalso. eapply inject_atomic_tree_in_symbol_list_non_reorderable_2; eauto.
        **exfalso. eapply inject_atomic_tree_in_symbol_non_reorderable_2; eauto.
    + subst. inv H0.
      * inv H1.
        **auto.
        **exfalso. eapply inject_atomic_tree_in_symbol_non_reorderable; eauto.
        **exfalso. eapply inject_atomic_tree_in_symbol_list_non_reorderable; eauto.
        **exfalso. eapply special_atomic_injection_non_reorderable_3; eauto.
      * exfalso. inv H1.
        **destruct X1; simpl in H5; inv H5; inv H; inv H4.
        **eapply inject_atomic_tree_in_symbol_non_reorderable_2; eauto.
        **eapply inject_atomic_tree_in_symbol_list_non_reorderable_2; eauto.
        **eapply special_atomic_injection_non_reorderable_4; eauto.
Qed.

Lemma reorder_safety_safe_crules g Q :
  subset_crules g Q → (∃ p, g p ∧ atomic_production p) →
  (∀ X t, wft g X t → ∃ t', reorder t t' ∧ cf Q t') → safe_crules Q.
Proof.
  intros ??????. destruct H0 as [p_atom]. inv H0. inv H2.
  apply atomic_production_to_atomic_parse_tree_correct in H3; auto.
  destruct H3 as [t_atom]. inv H2. inv H6.
  apply conflict_left_well_formed in H0 as ?. inv H6.
  inv H8. inv H9. rename σ into β, σ0 into γ.
  specialize H1 with E
    (large_node (large_production E β Xn)
      (large_node (large_production X1 γ E)
        (inject_tree_in_symbol X1 t_atom)
        (inject_tree_in_symbol_list γ t_atom)
        t_atom
      )
      (inject_tree_in_symbol_list β t_atom)
      (inject_tree_in_symbol Xn t_atom)
    ).
  destruct H1 as [t']. {
    eapply conflict_left_productions in H0; eauto. inv H0.
    constructor; auto.
    - constructor; auto.
      + auto using inject_tree_in_symbol_well_formed.
      + auto using inject_tree_in_symbol_list_well_formed.
    - auto using inject_tree_in_symbol_list_well_formed.
    - auto using inject_tree_in_symbol_well_formed.
  }
  inv H1.
  eapply reorder_simple_tree in H6; eauto.
  destruct H6; subst.
  - inv H8. eapply H11; eauto. repeat constructor.
  - inv H8. eapply H12; eauto. repeat constructor.
Qed.

End MixfixSafeConflictRules.
