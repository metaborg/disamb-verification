From disamb Require Export MixfixRepair.
From disamb Require Import MyUtils MixfixRepairReorder MixfixRepairConflictFree
                           MixfixReorderWellformed MixfixReorderYield.

Section MixfixReorderSafety.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool) (Q : crules T).

Theorem reorder_safety g X t Q :
  safe_crules Q → wft g X t → ∃ t', reorder t t' ∧ cf Q t'.
Proof.
  intros. exists (repair Q t). split.
  - eapply repair_reorder; eauto.
  - apply repair_conflict_free; auto.
Qed.

Corollary safety g w Q :
  safe_crules Q → sentence g w → crules_sentence g Q w.
Proof.
  intros. unfold sentence in H0. destruct H0 as [t]. inv H0.
  apply reorder_safety with (Q := Q) in H1 as ?; auto. inv H0. inv H2.
  exists x. split; [|split].
  - eapply reorder_well_formed; eauto.
  - assumption.
  - apply reorder_yield. symmetry. assumption.
Qed.

End MixfixReorderSafety.
