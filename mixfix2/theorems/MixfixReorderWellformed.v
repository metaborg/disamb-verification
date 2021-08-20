From disamb Require Export MixfixReorder2.
From disamb Require Import MyUtils.

Section MixfixReorderWellformed.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool).

Lemma reorder_step_well_formed g X t1 t2 :
  wft g X t1 → reorder_step t1 t2 → wft g X t2.
Proof.
  intros. revert H. revert X. induction H0 using reorder_step_tree_list_rec with
    (P0 := fun τ τ' H => ∀ σ, wfτ g σ τ → wfτ g σ τ'); intros.
  - inv H. inv H8. constructor; auto.
    assert (X0 = E). { inv H9; inv i; auto. } subst.
    constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
Qed.

Lemma reorder_step_well_formed_2 g X t1 t2 :
  wft g X t2 → reorder_step t1 t2 → wft g X t1.
Proof.
  intros. revert H. revert X. induction H0 using reorder_step_tree_list_rec with
    (P0 := fun τ1 τ2 H => ∀ σ, wfτ g σ τ2 → wfτ g σ τ1); intros.
  - inv H. inv H6. constructor; auto.
    assert (Xn0 = E). { inv H11; inv i; auto. } subst.
    constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
  - inv H. constructor; auto.
Qed.

End MixfixReorderWellformed.
