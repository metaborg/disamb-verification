From stdpp Require Import relations sets.
From stdpp Require Import list.

Definition globally_finite {A} (R : relation A) (x : A) :=
  pred_finite (tc R x).
  
Lemma globally_finite_sn {A} (R : relation A) x :
  Irreflexive (tc R) → globally_finite R x → sn R x.
Proof.
  intros Hirr [xs Hfin]. remember (length xs) as n eqn:Hn.
  revert x xs Hn Hfin.
  induction (lt_wf n) as [n _ IH].
  intros x xs -> Hfin.
  apply Acc_intro. intros. simpl in H.
  assert (Hy: y ∈ xs). {
    apply Hfin. apply tc_once. assumption.
  }
  apply elem_of_Permutation in Hy as Hxs. destruct Hxs as [xs'].
  apply IH with (y := length xs') (xs := xs').
  - apply Permutation_length in H0. simpl in H0. lia.
  - reflexivity.
  - intros z Hyz.
    assert (Hz: z ∈ xs). {
      apply Hfin. eapply tc_l; eassumption.
    }
    apply elem_of_list_In in Hz.
    Search Permutation. eapply Permutation_in in Hz; eauto.
    inversion Hz.
    + subst. destruct Hirr with (x := z). assumption.
    + apply elem_of_list_In. assumption.
Qed.
