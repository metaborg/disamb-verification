Require Export ReductionOrder.
From stdpp Require Export relations.

Require Import ReorderingTheorems.
Require Import MyUtils.

Section ReductionOrderTheorems.

Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types g : @dgrammar O.

(* Lemma gtp_gtp_trans g t t' :
  gtp g t t' → gtp_trans g t t'.
Proof.
  intros. induction H.
  - auto using OPT1.
  - auto using OPT2.
  - auto using OPT3.
Qed. *)

Lemma gtp_trans g t t' t'' :
  gtp g t t' → gtp g t' t'' → gtp g t t''.
Proof.
  intro. revert t''. induction H; intros.
  - inv H0; eauto using OP1, g.(priority_trans).
  - inv H0; auto using OP1, OP2, OP4.
  - inv H0; auto using OP1, OP3, OP4.
  - inv H1; auto using OP1, OP4.
Qed. 

(* Lemma gtp_gtp_trans_trans g t t' t'' :
  gtp g t t' → gtp_trans g t' t'' → gtp_trans g t t''.
Proof.
  intro. revert t''. induction H; intros.
  - eapply gtp_trans_trans; eauto using OPT1.
  - eapply gtp_trans_trans; eauto using OPT2, gtp_gtp_trans.
  - eapply gtp_trans_trans; eauto using OPT3, gtp_gtp_trans.
Qed.

Lemma gtp_trans_complete g t t' :
  (tc (gtp g)) t t' → gtp_trans g t t'.
Proof.
  intros. induction H.
  - auto using gtp_gtp_trans.
  - eauto using gtp_gtp_trans_trans.
Qed. *)

Lemma gtp_irreflexive g t t' :
  gtp g t t' → t ≠ t'.
Proof.
  intro. induction H.
  - intro. inv H0. apply g.(priority_irefl) in H. apply H.
  - intro. inv H0. contradiction.
  - intro. inv H0. contradiction.
  - intro. inv H1. contradiction.
Qed. 

(* Lemma gtp_acyclic g :
  Irreflexive (tc (@gtp L O g)).
Proof.
  intro. intro. apply gtp_trans_complete in H. apply gtp_trans_irreflexive in H. contradiction.
Qed. *)

Create HintDb gtl.
Hint Resolve OLC1 : gtl.
Hint Resolve OLC2 : gtl.
Hint Resolve OLC3 : gtl.
Hint Resolve OL1 : gtl.
Hint Resolve OL2 : gtl.
Hint Resolve OL3 : gtl.
Hint Resolve OL4 : gtl.
Hint Resolve left_assoc_sym : gtl.
Hint Resolve left_assoc_trans : gtl.

Lemma gtlc_trans g oc1 oc2 oc3 t t' t'' :
  gtlc g oc1 t t' → gtlc g oc2 t' t'' →
  g.(rel) oc1 oc2 = Some Left_assoc → g.(rel) oc2 oc3 = Some Left_assoc →
  gtlc g oc3 t t''.
Proof.
  intro. revert t'' oc2 oc3. induction H; intros.
  - inv H0.
  - assert (rel g o oc3 = Some Left_assoc). {
      eapply g.(left_assoc_trans). apply g.(left_assoc_sym). eassumption.
      eapply g.(left_assoc_trans); eassumption.
    }
    apply g.(left_assoc_sym) in H4 as ?.
    inv H1; eauto with gtl.
  - assert (rel g o oc3 = Some Left_assoc). {
      eapply g.(left_assoc_trans). apply g.(left_assoc_sym). eassumption.
      eapply g.(left_assoc_trans); eassumption.
    }
    apply g.(left_assoc_sym) in H5 as ?.
    inv H2; eauto with gtl.
Qed.

Hint Resolve gtlc_trans : gtl.

Lemma olc2_gtl_gtlc g t t1 t2 u u1 u2 (v : @parse_tree L O) o p oc :
  u = INode u1 p u2 → t = INode t1 o t2 →
  g.(rel) oc o = Some Left_assoc → g.(rel) o p ≠ Some Left_assoc →
  gtl g u v → gtlc g oc t v.
Proof.
  intros. inv H3.
  - inv H6. rename o' into q. rename t'1 into v1. rename t'2 into v2.
    apply OLC2. assumption.
    intro. destruct H2.
    eauto with gtl.
  - inv H5. apply OLC2. assumption.
    intro. destruct H2.
    eauto with gtl.
  - inv H5. apply OLC2. assumption.
    intro. destruct H2.
    eauto with gtl.
  - inv H6. apply OLC2. assumption.
    intro. destruct H2.
    eauto with gtl.
Qed.

Lemma gtlc_gtl_gtlc g o t u v :
  gtlc g o t u → gtl g u v → gtlc g o t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0.
  - eauto using olc2_gtl_gtlc with gtl.
  - inv H2; eauto with gtl.
Qed.

Lemma gtl_gtlc_gtlc g oc t u v :
  gtl g t u → gtlc g oc u v → gtlc g oc t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0. contradiction.
    inv H1.
    + eauto with gtl.
    + apply OLC2. eauto with gtl.
      intro. destruct H7. eauto with gtl.
    + apply OLC3; eauto with gtl.
      eauto 10 with gtl.
  - inv H0; eauto with gtl.
  - inv H0; eauto with gtl.
  - inv H1; eauto with gtl.
Qed.

Lemma glt_trans g t t' t'' :
  gtl g t t' → gtl g t' t'' → gtl g t t''.
Proof.
  intro. revert t''. induction H; intros.
  - inv H1.
    + eauto with gtl.
    + inv H0; eauto with gtl.
    + inv H0; eauto using gtlc_gtl_gtlc with gtl.
    + inv H0; eauto using gtlc_gtl_gtlc with gtl.
  - inv H0; eauto with gtl.
    inv H6; eauto with gtl.
  - inv H0; eauto with gtl.
    inv H6; eauto using gtl_gtlc_gtlc with gtl.
  - inv H1; eauto with gtl.
    inv H7; eauto using gtl_gtlc_gtlc with gtl.
Qed.

Lemma gtlc_irreflexive g oc t t' :
  gtlc g oc t t' → t ≠ t'.
Proof.
  intro. induction H; intro.
  - inv H0.
  - inv H1. contradiction.
  - inv H2. contradiction.
Qed.

Lemma gtl_irreflexive g t t' :
  gtl g t t' → t ≠ t'.
Proof.
  intro. induction H; intro.
  - inv H0. contradiction. inv H1.
    apply gtlc_irreflexive in H10. contradiction.
  - inv H0. contradiction.
  - inv H0. contradiction.
  - inv H1. contradiction.
Qed.

Create HintDb gtr.
Hint Resolve ORC1 : gtr.
Hint Resolve ORC2 : gtr.
Hint Resolve ORC3 : gtr.
Hint Resolve OR1 : gtr.
Hint Resolve OR2 : gtr.
Hint Resolve OR3 : gtr.
Hint Resolve OR4 : gtr.
Hint Resolve right_assoc_sym : gtr.
Hint Resolve right_assoc_trans : gtr.

Lemma gtrc_trans g oc1 oc2 oc3 t t' t'' :
  gtrc g oc1 t t' → gtrc g oc2 t' t'' →
  g.(rel) oc1 oc2 = Some Right_assoc → g.(rel) oc2 oc3 = Some Right_assoc →
  gtrc g oc3 t t''.
Proof.
  intro. revert t'' oc2 oc3. induction H; intros.
  - inv H0.
  - assert (rel g o oc3 = Some Right_assoc). { eauto with gtr. }
    apply g.(right_assoc_sym) in H4 as ?.
    inv H1; eauto with gtr.
  - assert (rel g o oc3 = Some Right_assoc). { eauto with gtr. }
    apply g.(right_assoc_sym) in H5 as ?.
    inv H2; eauto with gtr.
Qed.

Hint Resolve gtrc_trans : gtr.

Lemma orc2_gtr_gtrc g t t1 t2 u u1 u2 (v : @parse_tree L O) o p oc :
  u = INode u1 p u2 → t = INode t1 o t2 →
  g.(rel) oc o = Some Right_assoc → g.(rel) o p ≠ Some Right_assoc →
  gtr g u v → gtrc g oc t v.
Proof.
  intros. inv H3.
  - inv H6. rename o' into q. rename t'1 into v1. rename t'2 into v2.
    apply ORC2. assumption.
    intro. destruct H2.
    eauto with gtr.
  - inv H5. apply ORC2. assumption.
    intro. destruct H2.
    eauto with gtr.
  - inv H5. apply ORC2. assumption.
    intro. destruct H2.
    eauto with gtr.
  - inv H6. apply ORC2. assumption.
    intro. destruct H2.
    eauto with gtr.
Qed.

Lemma gtrc_gtr_gtrc g o t u v :
  gtrc g o t u → gtr g u v → gtrc g o t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0.
  - eauto using orc2_gtr_gtrc with gtr.
  - inv H2; eauto with gtr.
Qed.

Lemma gtr_gtrc_gtrc g oc t u v :
  gtr g t u → gtrc g oc u v → gtrc g oc t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0. contradiction.
    inv H1.
    + eauto with gtr.
    + apply ORC2. eauto with gtr.
      intro. destruct H7. eauto with gtr.
    + apply ORC3; eauto with gtr.
      eauto 10 with gtr.
  - inv H0; eauto with gtr.
  - inv H0; eauto with gtr.
  - inv H1; eauto with gtr.
Qed.

Lemma glr_trans g t t' t'' :
  gtr g t t' → gtr g t' t'' → gtr g t t''.
Proof.
  intro. revert t''. induction H; intros.
  - inv H1.
    + eauto with gtr.
    + inv H0; eauto using gtrc_gtr_gtrc with gtr.
    + inv H0; eauto with gtr.
    + inv H0; eauto using gtrc_gtr_gtrc with gtr.
  - inv H0; eauto with gtr.
    inv H6; eauto using gtr_gtrc_gtrc with gtr.
  - inv H0; eauto with gtr.
    inv H6; eauto with gtr.
  - inv H1; eauto with gtr.
    inv H7; eauto using gtr_gtrc_gtrc with gtr.
Qed.

Lemma gtrc_irreflexive g oc t t' :
  gtrc g oc t t' → t ≠ t'.
Proof.
  intro. induction H; intro.
  - inv H0.
  - inv H1. contradiction.
  - inv H2. contradiction.
Qed.

Inductive gtp_or_gtl g : parse_tree → parse_tree → Prop :=
  | ULeft t u :
      gtp g t u → gtp_or_gtl g t u
  | URight t u :
      gtl g t u → gtp_or_gtl g t u.

Lemma asdfgh g t1 o t2 u1 p u2 u1' t1' :
  g.(rel) o p = Some Left_assoc → gtlc g o t2 u2 →
  yield (INode t1 o t2) = yield (INode u1 p u2) → yield u1 = yield u1' →
  gtp g u1 u1' →
  ∃ t1', gtp g t1 t1' ∧ yield t1 = yield t1'.
Proof.
  intros. apply yield_equivalence_are_reorderings in H1.
  apply yield_equivalence_are_reorderings in H2.
  induction H2; intros.

  apply gtp_irreflexive in H3. contradiction.

  
  
  subst. inv Hequ.
  apply gtlc_irreflexive in H0. contradiction.

  
  

Lemma gtp_commutes_gtl g t u v :
  gtl g t u → gtp g u v → ∃ w, gtp g t w ∧ (rtc (gtp_or_gtl g)) w v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0. contradiction. clear H9.
    rename t'1 into u1. rename o' into p. rename t'2 into u2.
    inv H1.
    + rename t'1 into v1, o' into q, t'2 into v2.
      exists (INode v1 q v2). split.
      apply OP1.
      eapply priority_group_left_2. eassumption. eauto using left_assoc_sym.
      apply rtc_refl.
    + rename t1' into u1'.
    
    
    
    
  (* AAAAAAAAAAAAAAAAAAAAA *)

Lemma gtlc_gtr_gtlc g oc t u v :
  (* g.(rel) oc oc' = Some Left_assoc → *)
  gtlc g oc t u → gtr g u v → gtlc g oc t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0.
  - rename t'1 into u1, o' into p, t'2 into u2.
    inv H1; eauto with gtl.
    rename t'1 into v1, o' into q, t'2 into v2.
    inv H7. contradiction.
    apply OLC2. assumption.
    apply g.(right_assoc_sym) in H6.
    apply g.(right_assoc_group) with (o3 := oc) in H6.
    intro. apply H6.
    apply g.(left_assoc_sym). assumption.
  - rename t'1 into u1, o' into p, t'2 into u2.
    inv H2; eauto with gtl.
    rename t'1 into v1, o' into q, t'2 into v2.
    apply g.(right_assoc_sym) in H7.
    apply g.(right_assoc_group) with (o3 := oc) in H7.
    eauto with gtl.
Qed.

Lemma gtl_gtrc_gtrc g oc t u v :
  gtl g t u → gtrc g oc u v → gtrc g oc t v.
Proof.
  intro. revert v. induction H; intros.
  - rename t'1 into u1, o' into p, t'2 into u2.
    assert (g.(rel) oc p = Some Right_assoc). {inv H1; assumption. }
    apply g.(right_assoc_sym) in H2.
    apply g.(right_assoc_group) with (o3 := o) in H2.
    destruct H2.
    eauto with gtl.
  - inv H0; eauto with gtr.
  - inv H0; eauto with gtr.
  - inv H1; eauto with gtr.
Qed.

Create HintDb rel.
Hint Resolve left_assoc_sym : rel.
Hint Resolve right_assoc_sym : rel.
Hint Resolve left_assoc_trans : rel.
Hint Resolve right_assoc_trans : rel.
Hint Resolve priority_trans : rel.
Hint Resolve priority_group_left_1 : rel.
(* Hint Resolve priority_group_left_2 : rel. *)
Hint Resolve priority_group_right_1 : rel.
(* Hint Resolve priority_group_right_2 : rel. *)

(* Lemma gtlc_gtpr_gtlc g oc t u v :
  gtlc g oc t u → gtpr g u v → gtlc g oc t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0.
  - rename t'1 into u1, o' into p, t'2 into u2.
    inv H1.
    + rename u0 into v1, p0 into q, u3 into v2.
      destruct (g.(rel) o q) eqn:E. destruct d.
      * apply OLC3; eauto with rel. *)
        

Lemma gtlc_gtpr_gtpr g oc t u v :
  gtlc g oc t u → gtpr g u v → gtpr g t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0.
  - rename t'1 into u1, o' into p, t'2 into u2.
    inv H1.
    + rename u0 into v1, p0 into q, u3 into v2.
      

Lemma gtpr_trans g t u v :
  gtpr g t u → gtpr g u v → gtpr g t v.
Proof.
  intro. revert v. induction H; intros.
  - inv H0; eauto using GTPR_Priority with rel.
  - inv H0. contradiction.
    inv H1.
    + rename u0 into v1, p0 into q, u3 into v2.
      apply GTPR_Priority.
      eauto using g.(priority_group_left_2) with rel.
    + rename u0 into v1, p0 into q, u3 into v2.
      inv H7. contradiction.
      apply GTPR_LAssoc.
      eauto with rel.
      apply OLC3; eauto using gtlc_trans with rel.
    + rename u0 into v1, p0 into q, u3 into v2.
      exfalso.
      apply g.(right_assoc_group) with (o3 := o) in H5.
      apply H5. auto with rel.
    + rename t1' into u1'.
      apply GTPR_LAssoc. assumption.
      apply OLC3; assumption.
    + (* POSSIBLE CHEAT HERE *)
      rename t2' into u2'.
      eapply GTPR_Temp. assumption.
      apply OLC3; eassumption.
      assumption.
    + (* POSSIBLE CHEAT HERE *)
      rename t1' into u1', t2' into u2'.
      eapply GTPR_Temp. assumption.
      apply OLC3; try eassumption.
      assumption.
    + (* CHEAT CASE *)
      rename u0 into v1, p0 into q, u3 into v2.
      rename u2' into v2'.
      eapply GTPR_Temp. eauto with rel.
      apply OLC3; eauto with rel.
      inv H7. contradiction.


Lemma gtl_gtr_cotrans g t u v :
  gtl g t u → gtr g u v → gtl g t v ∨ gtr g t v.
Proof.
  intro. revert v. induction H; intros.
  - rename t'1 into u1. rename o' into p. rename t'2 into u2.
    inv H1.
    + apply g.(left_assoc_sym) in H.
      apply g.(left_assoc_group) with (o3 := o') in H.
      contradiction.
    + left. apply OL1. assumption.
      apply OLC3; eauto with gtl.
      inv H0. contradiction. assumption.
    + rename t2' into u2'. inv H0. contradiction.
      left. apply OL1. assumption.
      apply OLC3; eauto with gtl.
      eauto using gtlc_gtr_gtlc.
    + rename t1' into u1', t2' into u2'. inv H0. contradiction.
      left. apply OL1. assumption.
      apply OLC3; eauto with gtl.
      eauto using gtlc_gtr_gtlc.
  - inv H0.
    + rename t'1 into v1, o' into q, t'2 into v2.
      inv H6. contradiction.
      right. apply OR1. assumption.
      apply ORC3; auto.
      eauto using gtl_gtrc_gtrc.
    + rename t1'0 into t1''.
      apply IHgtl in H5. destruct H5; auto with gtl gtr.
    + left. (* FUCKING KUUUUT*)

