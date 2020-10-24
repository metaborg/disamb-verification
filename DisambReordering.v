Require Export InfixGrammar.
From stdpp Require Export relations.

Require Import MyUtils.

Section DisambReordering.

Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.

Record cgrammar := mkCgrammar {
  ldr : O → O → Prop;
  rdl : O → O → Prop;

  ldr_not_rdl o p : ldr o p → ¬ rdl p o;
  rdl_not_ldr o p : rdl o p → ¬ ldr p o
}.

Implicit Types g : cgrammar.

Inductive disamb g : parse_tree → parse_tree → Prop :=
  | D_RDL o p t1 t2 t3 :
      g.(rdl) o p →
      disamb g (INode (INode t1 p t2) o t3)
               (INode t1 p (INode t2 o t3))
  | D_LDR o p t1 t2 t3 :
      g.(ldr) o p →
      disamb g (INode t1 o (INode t2 p t3))
               (INode (INode t1 o t2) p t3)
  | D_Sub_Left o t1 t1' t2 :
      disamb g t1 t1' →
      disamb g (INode t1 o t2) (INode t1' o t2)
  | D_Sub_Right o t1 t2 t2' :
      disamb g t2 t2' →
      disamb g (INode t1 o t2) (INode t1 o t2').

Lemma nonsense_equality t t1 o :
  t ≠ INode t1 o t.
Proof.
  revert o t1. induction t; intros.
  - intro. inv H.
  - intro. inv H.
    specialize IHt2 with (o := o0) (t1 := t0).
    contradiction.
Qed.

Lemma disamb_irreflexive g t t' :
  disamb g t t' → t ≠ t'.
Proof.
  intro. induction H.
  - intro. inv H0.
    eapply nonsense_equality. eauto.
  - intro. inv H0.
    eapply nonsense_equality. eauto.
  - intro. inv H0.
    apply IHdisamb. reflexivity.
  - intro. inv H0.
    apply IHdisamb. reflexivity.
Qed.

Lemma sub_must_reorder g t1 o t2 t1' :
  tc (disamb g) (INode t1 o t2) (INode t1' o t2) →
  tc (disamb g) t1 t1'.
Proof.
  remember (INode t1 o t2) as t. remember (INode t1' o t2) as t'.
  intro. revert Heqt Heqt'. revert t1 t1' o t2. induction H; intros.
  - subst.
    inv H.
    + exfalso. eapply nonsense_equality. eauto.
    + exfalso. eapply nonsense_equality. eassumption.
    + apply tc_once. assumption.
    + exfalso. eapply disamb_irreflexive; eauto.
  - subst.
    inv H.
    + 
    eapply tc_l.

    eapply IHtc.


