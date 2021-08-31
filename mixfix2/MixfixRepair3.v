From disamb Require Export MixfixDisambiguation2.
From disamb Require Import MyUtils.

Global Instance right_neighborhood_conflict_free_decidable {T} (Q : crules T) p t1 τ tn :
  Decision (rncf Q p t1 τ tn).
Proof.
  unfold rncf.
  assert (Decision (∀ p2, p CR p2 ∠ Q → ¬ p2 LM tn)). {
    clear t1 τ. induction tn.
    - left. intros ???. inv H0.
    - left. intros ???. inv H0.
    - destruct (decide (p CR p0 ∠ Q)).
      + right. intro. eapply H; eauto. constructor.
      + destruct (decide (∀ p2, p CR p2 ∠ Q → ¬ p2 LM tn1)).
        * left. intros ???. inv H0. contradiction. eapply n0; eauto.
        * right. intro. apply n0. intros ???. eapply H; eauto. constructor. assumption. 
  }
  destruct (decide (∀ p2 : production T, p CR p2 ∠ Q → ¬ p2 LM tn)).
  - left. intros ???. inv H1. eapply n; eauto.
  - right. intro. apply n. intros ???. eapply H0; eauto. constructor. assumption.
Qed.

Fixpoint repair_cr {T} (Q : crules T) (p : production T)
    (t1 : parse_tree T) (τ : parse_list T) (tn : parse_tree T) :=
  match tn with
  | large_node pn tn1 τn tnn =>
      if decide (rncf Q p t1 τ tn)
      then large_node p t1 τ tn
      else large_node pn (repair_cr Q p t1 τ tn1) τn tnn
  | _ => (large_node p t1 τ tn)
  end.

Global Instance left_neighborhood_conflict_free_decidable {T} (Q : crules T) p t1 τ tn :
  Decision (lncf Q p t1 τ tn).
Proof.
  unfold lncf.
  assert (Decision (∀ p2, p CL p2 ∠ Q → ¬ p2 RM t1)). {
    clear tn τ. induction t1.
    - left. intros ???. inv H0.
    - left. intros ???. inv H0.
    - destruct (decide (p CL p0 ∠ Q)).
      + right. intro. eapply H; eauto. constructor.
      + destruct (decide (∀ p2 : production T, p CL p2 ∠ Q → ¬ p2 RM t1_2)).
        * left. intros ???. inv H0. contradiction. eapply n0; eauto.
        * right. intro. apply n0. intros ???. eapply H; eauto. constructor. assumption. 
  }
  destruct (decide (∀ p2 : production T, p CL p2 ∠ Q → ¬ p2 RM t1)).
  - left. intros ???. inv H1. eapply n; eauto.
  - right. intro. apply n. intros ???. eapply H0; eauto. constructor. assumption.
Qed.

Fixpoint repair_top {T} (Q : crules T) (p : production T)
    (t1 : parse_tree T) (τ : parse_list T) (tn: parse_tree T) :=
  match t1 with
  | large_node p1 t11 τ1 t1n =>
      if decide (lncf Q p t1 τ tn)
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
