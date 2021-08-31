From disamb Require Export MixfixUtils.
From disamb Require Import MyUtils.

Section MixfixUtilsTheorems.

Context {T : Type}.
Implicit Types (t : parse_tree T) (ts : parse_forest T) (p : production T) (X : symbol T)
  (g : mixfixgrammar T) (Xs : list (symbol T)).

Lemma split_last_wf g X t Xs ts ts1 tn :
  wft g X t → wfts g Xs ts → split_last t ts = (ts1, tn) → ∃ Xn, wft g Xn tn.
Proof.
  intros Hwft Hwfts.
  revert Hwft. revert X t ts1.
  induction Hwfts; simpl; intros.
  - inv H.
    eauto.
  - destruct (split_last t ts) eqn:E.
    inv H0.
    eapply IHHwfts.
    apply H.
    apply E.
Qed.

Lemma split_last_add_last t ts tsh tn :
  split_last t ts = (tsh, tn) → add_last tsh tn = cons_forest t ts.
Proof.
  revert t tsh.
  induction ts; simpl; intros t tsh Hsplit.
  - inv Hsplit.
    simpl.
    reflexivity.
  - destruct (split_last p ts) eqn:E.
    inv Hsplit.
    simpl.
    erewrite IHts; eauto.
Qed.

End MixfixUtilsTheorems.
