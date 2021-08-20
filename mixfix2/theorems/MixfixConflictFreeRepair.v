From disamb Require Export MixfixRepair3.
From disamb Require Import MyUtils.

Section MixfixConflictFreeRepair.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts τ : parse_list T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs σ : list (symbol T)) (b : bool) (Q : crules T).

Lemma conflict_free_repair_cr Q p t1 τ tn :
  cf Q (large_node p t1 τ tn) → repair_cr Q p t1 τ tn = large_node p t1 τ tn.
Proof.
  intro. destruct tn as [an1|pn opt_an1|pn tn1 τn tnn]; simpl.
  - destruct (decide (rncf Q p t1 τ (leaf an1))); auto.
  - destruct (decide (rncf Q p t1 τ (small_node pn opt_an1))); auto.
  - destruct (decide (rncf Q p t1 τ (large_node pn tn1 τn tnn))); auto.
    destruct n. inv H. assumption.
Qed.

Lemma conflict_free_repair_top Q p t1 τ tn :
  cf Q (large_node p t1 τ tn) → repair_top Q p t1 τ tn = large_node p t1 τ tn.
Proof.
  intro. destruct t1 as [a11|p1 opt_a11|p1 t11 τ1 t1n]; simpl.
  - destruct (decide (lncf Q p (leaf a11) τ tn)); auto using conflict_free_repair_cr.
  - destruct (decide (lncf Q p (small_node p1 opt_a11) τ tn)); auto using conflict_free_repair_cr.
  - destruct (decide (lncf Q p (large_node p1 t11 τ1 t1n) τ tn)); auto using conflict_free_repair_cr.
    destruct n. inv H. assumption.
Qed.

Lemma conflict_free_repair Q t :
  cf Q t → repair Q t = t.
Proof.
  intro. induction H using conflict_free_tree_list with
    (P0 := fun τ H => repair_list Q τ = τ); auto; simpl.
  - rewrite IHconflict_free1. rewrite IHconflict_free2. rewrite IHconflict_free3.
    apply conflict_free_repair_top. constructor; auto.
  - rewrite IHconflict_free. rewrite IHconflict_free0. reflexivity.
Qed.

End MixfixConflictFreeRepair.
