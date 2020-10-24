Require Export InfixGrammar.
Require Import MyUtils.

Load "Lib/StrongInduction".

Section ReductionOrderTheorems.

Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types g : @dgrammar O.
Implicit Types q : @tree_pattern O.
Implicit Types qs : @tree_pattern O -> Prop.

Inductive CRelation :=
  | Up
  | Down.

Definition crel := O → O → option CRelation.

Implicit Types cg : crel.

Inductive ccpatterns cg : tree_pattern → Prop :=
  | CUp o1 o2 :
      cg o1 o2 = Some Up →
      ccpatterns cg (IPatt NTPatt o1 (IPatt NTPatt o2 NTPatt))
  | CDown o1 o2 :
      cg o1 o2 = Some Down →
      ccpatterns cg (IPatt (IPatt NTPatt o1 NTPatt) o2 NTPatt).

Fixpoint interleave_left cg l o t :=
  match t with
  | ANode l2 => INode (ANode l) o t
  | INode t1 p t2 =>
      match (cg o p) with
      | Some Up => INode (interleave_left cg l o t1) p t2
      | _ => INode (ANode l) o t
      end
  end.

Lemma anode_valid cg l :
  valid (ccpatterns cg) (ANode l).
Proof.
  apply ANode_valid.
  intro. inv H. destruct H0.
  inv H; inv H0.
Qed.

Definition left_top t : option O :=
  match t with
  | INode (INode _ o _) _ _ => Some o
  | _ => None
  end.

Lemma interleave_left_is_left cg l o1 t1 t2 o2 :
  cg o1 o2 = Some Up →
  matches (interleave_left cg l o1 (INode t1 o2 t2)) (IPatt (IPatt NTPatt o1 NTPatt) o2 NTPatt)
  ∨ (exists o3, matches t1 (IPatt NTPatt o3 NTPatt) ∧
    matches (interleave_left cg l o1 (INode t1 o2 t2)) (IPatt (IPatt NTPatt o3 NTPatt) o2 NTPatt)
  ).
Proof.
  intros. simpl. rewrite H.
  destruct t1; simpl.
  - left. auto using INode_match, NT_match.
  - destruct (cg o1 o) eqn:E.
  
    + destruct c.
      * right. exists o. split;
        auto using INode_match, NT_match.
      * left. auto using INode_match, NT_match.
    + left. auto using INode_match, NT_match.
Qed.


Lemma interleave_left_safe cg l o t :
  valid (ccpatterns cg) t → valid (ccpatterns cg) (interleave_left cg l o t).
Proof.
  intros. induction H.
  - simpl in *.
    clear H.
    apply INode_valid.
    intro. inv H. destruct H0.
    inv H. inv H0. inv H8. inv H0. inv H3.
    apply anode_valid.
    apply anode_valid.
  - rename o0 into p. destruct (cg o p) eqn:E.
    + destruct c.
      * apply interleave_left_is_left with (l := l) (t1 := t1) (t2 := t2) in E as ?.
        destruct H2.
        **inv H2. inv H6. rewrite E in H3. inv H3.
          simpl. rewrite E.

          apply INode_valid; auto.
           
          intro. inv H2. destruct H3. assert (H2' := H2). inv H2'.

          inv H3. inv H16.
          apply H. eexists; eauto using INode_match, NT_match.

          rewrite <- H4 in H3. inv H3. inv H11.
          rewrite E in H5. inv H5.

        **destruct H2. destruct H2. inv H2.
          simpl. rewrite E. apply INode_valid; auto.
          intro.
          inv H2. destruct H4. assert (H2' := H2). inv H2'.

          inv H4. inv H15. apply H.
          eexists; eauto using INode_match, NT_match.

          simpl in H3. rewrite E in H3.
          inv H3. inv H10. clear H14 H11 H13 H7 H9.
          inv H4. inv H8. rewrite <- H3 in H4. inv H4.
          apply H.
          eexists; eauto using INode_match, NT_match.

      * simpl.
        rewrite E.
        apply INode_valid.
        **intro. inv H2. destruct H3.
          assert (H2' := H2). inv H2'.
          inv H3. inv H12.
          rewrite E in H4. inv H4.
        
          inv H3. inv H7.

        ** apply anode_valid.
        ** apply INode_valid; auto.
    + simpl.
      rewrite E.
      apply INode_valid.
      * intro. inv H2. destruct H3.
        assert (H2' := H2). inv H2'.
        inv H3. inv H12.
        rewrite E in H4. inv H4.
    
        inv H3. inv H7.

      * apply anode_valid.
      * apply INode_valid; auto.
Qed.

Lemma interleave_yield gc l o t :
  yield (interleave_left gc l o t) = inl l :: inr o :: yield t.
Proof.
  induction t; simpl in *.
  - reflexivity.
  - destruct (gc o o0).
    + destruct c.
      * simpl. rewrite IHt1. reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

Fixpoint build_safe_tree gc w : option parse_tree :=
  match w with
  | [inl l] => Some (ANode l)
  | inl l :: inr o :: w =>
    match (build_safe_tree gc w) with
    | None => None
    | Some t => Some (interleave_left gc l o t)
    end
  | _ => None
  end.

Inductive yield_struct : word → Prop :=
  | Lsingle l :
      yield_struct [inl l]
  | LOstruct l o w :
      yield_struct w →
      yield_struct (inl l :: inr o :: w).

Lemma yield_struct_app w1 o w2 :
  yield_struct w1 →
  yield_struct w2 →
  yield_struct (w1 ++ inr o :: w2).
Proof.
  intro. induction H; intros.
  - simpl. apply LOstruct. assumption.
  - simpl. apply LOstruct. auto.
Qed.

Lemma yield_is_yield_struct t :
  yield_struct (yield t).
Proof.
  induction t; simpl.
  - apply Lsingle.
  - auto using yield_struct_app.
Qed.

Lemma build_safe_tree_correct gc w :
  yield_struct w →
  ∃ t, (build_safe_tree gc w) = Some t ∧ valid (ccpatterns gc) t ∧ yield t = w.
Proof.
  intro. induction H.
  - eexists. simpl. split. reflexivity.
    split. apply anode_valid.
    reflexivity.
  - destruct IHyield_struct as [t]. destruct H0. destruct H1.
    eexists. simpl. rewrite H0. split. reflexivity.
    split. apply interleave_left_safe. assumption.
    rewrite interleave_yield. rewrite H2. reflexivity.
Qed.

Lemma csafety gc w :
  language w → exists t, yield t = w ∧ valid (ccpatterns gc) t.
Proof.
  intro. unfold language in H. destruct H as [t]. subst.
  assert (yield_struct (yield t)). {
    apply yield_is_yield_struct.
  }
  apply build_safe_tree_correct with (gc := gc) in H.
  destruct H. destruct H. destruct H0.
  exists x. auto.
Qed.

(* Definition construct_gc g o1 o2 : option CRelation :=
  match (g.(rel) o1 o2) with
  | Some Left_assoc => Some Up
  | Some Right_assoc => Some Down
  | Some Priority => Some Up
  | None =>
      match (g.(rel) o2 o1) with
      | Some Priority => Some Down
      | _ => None
      end
  end. *)
