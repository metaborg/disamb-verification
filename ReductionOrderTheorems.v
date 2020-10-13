Require Export ReductionOrder.
From stdpp Require Export relations.

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
  gtrc g oc1 t t' → gtlc g oc2 t' t'' →
  g.(rel) oc1 oc2 = Some Right_assoc → g.(rel) oc2 oc3 = Some Right_assoc →
  gtrc g oc3 t t''.
Proof.
  intro. revert t'' oc2 oc3. induction H; intros.
  - inv H0.
  - assert (rel g o oc3 = Some Right_assoc). { eauto using gtr. }
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
