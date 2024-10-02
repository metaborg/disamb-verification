From disamb Require Export MixfixDisambiguation.
From disamb Require Import MyUtils.

Global Instance right_neighborhood_conflict_free_decidable {T} (Q : crules T) p t :
  Decision (rncf Q p t).
Proof.
  unfold rncf.
  induction t.
  - left. intros ???. inv H0.
  - left. intros ???. inv H0.
  - destruct (decide (p CR p0 ∠ Q)).
    + right. intro. eapply H; eauto. constructor.
    + destruct IHt1.
      * destruct IHt2.
        **left. intros ???. inv H0.
          ***contradiction.
          ***eapply n0; eauto.
          ***eapply n1; eauto.
        **right. intro. apply n1. intros ???. eapply H; eauto.
          apply in_neighborhood_right. assumption.
      * right. intro. apply n0. intros ???. eapply H; eauto.
          apply in_neighborhood_left. assumption.
Qed.

Fixpoint repair_cr {T} (Q : crules T) (p : production T)
    (t1 : parse_tree T) (τ : parse_list T) (tn : parse_tree T) :=
  match tn with
  | large_node pn tn1 τn tnn =>
      if decide (rncf Q p tn)
      then large_node p t1 τ tn
      else large_node pn (repair_cr Q p t1 τ tn1) τn tnn
  | _ => (large_node p t1 τ tn)
  end.

Global Instance left_neighborhood_conflict_free_decidable {T} (Q : crules T) p t :
  Decision (lncf Q p t).
Proof.
  unfold lncf.
  induction t.
  - left. intros ???. inv H0.
  - left. intros ???. inv H0.
  - destruct (decide (p CL p0 ∠ Q)).
    + right. intro. eapply H; eauto. constructor.
    + destruct IHt1.
      * destruct IHt2.
        **left. intros ???. inv H0.
          ***contradiction.
          ***eapply n0; eauto.
          ***eapply n1; eauto.
        **right. intro. apply n1. intros ???. eapply H; eauto.
          apply in_neighborhood_right. assumption.
      * right. intro. apply n0. intros ???. eapply H; eauto.
          apply in_neighborhood_left. assumption.
Qed.

Fixpoint repair_top {T} (Q : crules T) (p : production T)
    (t1 : parse_tree T) (τ : parse_list T) (tn: parse_tree T) :=
  match t1 with
  | large_node p1 t11 τ1 t1n =>
      if decide (lncf Q p t1)
      then repair_cr Q p t1 τ tn
      else repair_top Q p1 t11 τ1 (repair_top Q p t1n τ tn)
  | _ => repair_cr Q p t1 τ tn
  end.

Fixpoint repair {T} (Q : crules T) (t : parse_tree T) :=
  match t with  
  | large_node p t1 τ tn => repair_top Q p (repair Q t1) (repair_list Q τ) (repair Q tn)
  | _ => t
  end

with repair_list {T} (Q : crules T) (τ : parse_list T) :=
  match τ with
  | parse_nil => parse_nil
  | parse_cons t ts => parse_cons (repair Q t) (repair_list Q ts)
  end.
