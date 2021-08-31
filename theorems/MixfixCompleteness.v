From disamb Require Export MixfixRepair.
From disamb Require Import MyUtils.
From disamb Require Import MixfixReorderRepair.
From disamb Require Import MixfixConflictFreeRepair.

Section MixfixReorderCompleteness.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool) (Q : crules T).

Theorem reorder_completeness g X1 X2 Q t1 t2 :
  complete_crules Q →
  wft g X1 t1 → wft g X2 t2 → reorder t1 t2 → cf Q t1 → cf Q t2 → t1 = t2.
Proof.
  intros. eapply reorder_repair in H2; eauto.
  rewrite conflict_free_repair in H2; auto.
  rewrite conflict_free_repair in H2; auto.
Qed.

End MixfixReorderCompleteness.
