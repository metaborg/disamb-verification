From disamb Require Export MixfixDisambiguation.
From disamb Require Import MixfixRepairReorder.
From disamb Require Import MixfixRepairConflictFree.
From disamb Require Import MyUtils.

Section MixfixSafety.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)) (b : bool) (Q : crules T) (PR : drules T).

Lemma safe_drules_safe_crules PR :
  safe_drules PR → safe_crules (drules_to_crules PR).
Proof.
  intros ????. destruct H0. unfold safe_drules in H.
  inv H0; inv H1; eapply H; eauto.
Qed.

Theorem safety g PR w :
  safe_drules PR →
  sentence g w → drules_sentence g PR w.
Proof.
  intro Hsafe.
  unfold sentence, drules_sentence.
  intro. destruct H as [t]. destruct H.
  exists (repair (drules_to_crules PR) t). split; [|split].
  - auto using repair_wf.
  - eapply repair_conflict_free; eauto. auto using safe_drules_safe_crules.
  - rewrite <- H0. erewrite <- repair_preserves_yield; eauto.
Qed.

End MixfixSafety.
