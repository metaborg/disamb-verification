From disamb Require Export MixfixRepair3.
From disamb Require Import MyUtils.

Section MixfixRepairWellformed.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool) (Q : crules T).

Lemma repair_cr_well_formed g X Q p t1 τ tn :
  wft g X (large_node p t1 τ tn) → wft g X (repair_cr Q p t1 τ tn).
Proof.
  intro. inv H. revert H5 H6 H7. revert X1 σ t1 τ. induction H8; simpl; intros.
  - constructor; auto. constructor.
  - constructor; auto. constructor; auto.
  - destruct (decide (rncf Q (large_production X0 σ0 E) t0 τ0 (large_node (large_production X1 σ Xn) t1 τ tn))).
    + constructor; auto. constructor; auto.
    + constructor; auto. inv H8_; auto. exfalso. apply n. intros ???. inv H2. inv H4.
      * apply conflict_right_well_formed in H1. inv H1. inv H3.
      * inv H3.
Qed.

Lemma repair_top_well_formed g X Q p t1 τ t2 :
  wft g X (large_node p t1 τ t2) → wft g X (repair_top Q p t1 τ t2).
Proof.
  intro. inv H. revert H7 H8 H5. revert σ τ t2 Xn. induction H6; intros; simpl.
  - apply repair_cr_well_formed. constructor; auto. constructor.
  - apply repair_cr_well_formed. constructor; auto. constructor; auto.
  - destruct (decide (lncf Q (large_production E σ0 Xn0) (large_node (large_production X1 σ Xn) t1 τ tn) τ0 t2)).
    + apply repair_cr_well_formed. constructor; auto. constructor; auto.
    + apply IHwell_formed_parse_tree1; auto. inv H6_0; auto. exfalso. apply n.
      intros ???. inv H2. inv H4.
      * apply conflict_left_well_formed in H1. inv H1. inv H3.
      * inv H3.
Qed.

Lemma repair_well_formed g X Q t :
  wft g X t → wft g X (repair Q t).
Proof.
  intro. induction H using well_formed_parse_tree_list_rec with
      (P0 := fun σ τ H => wfτ g σ (repair_list Q τ)); simpl.
  - constructor.
  - constructor. assumption.
  - apply repair_top_well_formed. constructor; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma repair_list_well_formed g σ Q τ :
  wfτ g σ τ → wfτ g σ (repair_list Q τ).
Proof.
  intro. induction H using well_formed_parse_list_tree_rec with
      (P := fun X t H => wft g X (repair Q t)); simpl.
  - constructor.
  - constructor. assumption.
  - apply repair_top_well_formed. constructor; auto.
  - constructor.
  - constructor; auto.
Qed.

End MixfixRepairWellformed.
