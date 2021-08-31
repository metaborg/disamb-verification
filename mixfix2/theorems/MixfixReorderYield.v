From disamb Require Export MixfixReorder2.
From disamb Require Import MyUtils.

Section MixfixReorderYield.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool).

Lemma reorder_step_yield t1 t2 :
  reorder_step t1 t2 → yt t1 = yt t2.
Proof.
  intro. induction H using reorder_step_tree_list_rec with
      (P0 := fun τ1 τ2 H => yts τ1 = yts τ2); simplify_list_eq.
  - reflexivity.
  - rewrite IHreorder_step. reflexivity.
  - rewrite IHreorder_step. reflexivity.
  - rewrite IHreorder_step. reflexivity.
  - rewrite IHreorder_step. reflexivity.
  - rewrite IHreorder_step. reflexivity.
Qed.

Lemma reorder_yield t1 t2 :
  reorder t1 t2 → yt t1 = yt t2.
Proof.
  intro. induction H; auto.
  inv H.
  - rewrite <- IHrtc. apply reorder_step_yield. assumption.
  - rewrite <- IHrtc. symmetry. apply reorder_step_yield. assumption.
Qed.

End MixfixReorderYield.
