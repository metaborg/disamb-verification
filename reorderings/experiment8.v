From stdpp Require Export list.
From stdpp Require Export relations.
Load "Lib/StrongInduction".

Section Experiment8.

Ltac inv H := inversion H; clear H; subst.

Inductive production Terminal :=
  | ClosedProduction : Terminal → list Terminal → production Terminal
  | InfixProduction : Terminal → production Terminal
  | PrefixProduction : Terminal → production Terminal
  | PostfixProduction : Terminal → production Terminal.

Global Arguments ClosedProduction {_} _ _.
Global Arguments InfixProduction {_} _.
Global Arguments PrefixProduction {_} _.
Global Arguments PostfixProduction {_} _.

Record grammar := mkGrammar {
  Terminal : Type;
  Productions: production Terminal -> Prop;
}.

Context {g : grammar}.
Notation T := (Terminal g).
Implicit Types a b c o l : T.
Implicit Types oa ob : option T.
Notation P := (Productions g).
Implicit Types p : production T.
Notation ClosedP ahead acons := (P (ClosedProduction ahead acons)).
Notation InP a := (P (InfixProduction a)).
Notation PreP a := (P (PrefixProduction a)).
Notation PostP a := (P (PostfixProduction a)).


Definition word := list T.

Implicit Types w : word.

Inductive parse_tree :=
  | ClosedNode : T → parse_list → parse_tree
  | InfixNode : parse_tree → T → parse_tree → parse_tree
  | PrefixNode : T → parse_tree → parse_tree
  | PostfixNode : parse_tree → T → parse_tree
with parse_list :=
  | NilNode : parse_list
  | ConsNode : parse_tree → T → parse_list → parse_list.

Notation PT := parse_tree.
Implicit Types t : PT.
Notation PL := parse_list.
Implicit Types τ : PL.

Scheme parse_tree_list_rec := Induction for parse_tree Sort Prop
with parse_list_tree_rec := Induction for parse_list Sort Prop.

Notation CN := ClosedNode.
Notation IN := InfixNode.
Notation PeN := PrefixNode.
Notation PoN := PostfixNode.
Notation ϵ := NilNode.
Notation CoN := ConsNode.

Inductive well_formed_parse_tree : PT → Prop :=
  | WellFormedClosedNode ah ac τ :
      ClosedP ah ac →
      well_formed_parse_list ac τ →
      well_formed_parse_tree (CN ah τ)
  | WellFormedInfixNode t1 a t2 :
      InP a →
      well_formed_parse_tree t1 →
      well_formed_parse_tree t2 →
      well_formed_parse_tree (IN t1 a t2)
  | WellFormedPrefixNode a t2 :
      PreP a →
      well_formed_parse_tree t2 →
      well_formed_parse_tree (PeN a t2)
  | WellFormedPostfixNode t1 a :
      PostP a →
      well_formed_parse_tree t1 →
      well_formed_parse_tree (PoN t1 a)
with well_formed_parse_list : list T → PL → Prop :=
  | WellFormedNilNode :
      well_formed_parse_list [] ϵ
  | WellFormedConsNode a ac t τ :
      well_formed_parse_tree t →
      well_formed_parse_list ac τ →
      well_formed_parse_list (a :: ac) (CoN t a τ).

Scheme well_formed_parse_tree_list_rec := Induction for well_formed_parse_tree Sort Prop
with well_formed_parse_list_tree_rec := Induction for well_formed_parse_list Sort Prop.      

Notation wf t := (well_formed_parse_tree t).
Notation wfl := well_formed_parse_list.

Fixpoint yield t : word :=
  match t with
  | CN a τ => a :: yield_list τ
  | IN t1 a t2 => yield t1 ++ a :: yield t2
  | PeN a t => a :: yield t
  | PoN t a => yield t ++ [a]
  end
with yield_list τ : word :=
  match τ with
  | ϵ => []
  | CoN t a τ => yield t ++ a :: yield_list τ
  end.

Inductive reorder_step : PT → PT → Prop :=
  | ReorderStepInfix t1 t2 t3 a b :
      reorder_step (IN (IN t1 a t2) b t3) (IN t1 a (IN t2 b t3))
  | ReorderStepInfixPrefix t1 t2 a b :
      reorder_step (IN (PeN a t1) b t2) (PeN a (IN t1 b t2))
  | ReorderStepInfixPostfix t1 t2 a b :
      reorder_step (IN t1 a (PoN t2 b)) (PoN (IN t1 a t2) b)
  | ReorderStepPrefixPostfix t a b :
      reorder_step (PeN a (PoN t b)) (PoN (PeN a t) b)
  | ReorderStepInfixSubtree1 t1 a t2 t1' :
      reorder_step t1 t1' →
      reorder_step (IN t1 a t2) (IN t1' a t2)
  | ReorderStepInfixSubtree2 t1 a t2 t2' :
      reorder_step t2 t2' →
      reorder_step (IN t1 a t2) (IN t1 a t2')
  | ReorderStepPrefixSubtree a t2 t2' :
      reorder_step t2 t2' →
      reorder_step (PeN a t2) (PeN a t2')
  | ReorderStepPostfixSubtree a t1 t1' :
      reorder_step t1 t1' →
      reorder_step (PoN t1 a) (PoN t1' a)
  | ReorderStepClosedSubtree a τ τ' :
      reorder_step_list τ τ' →
      reorder_step (CN a τ) (CN a τ')
with reorder_step_list : PL → PL → Prop :=
  | ReorderStepConsSubtree1 t t' a τ :
      reorder_step t t' →
      reorder_step_list (CoN t a τ) (CoN t' a τ)
  | ReorderStepConsSubtree2 t a τ τ' :
      reorder_step_list τ τ' →
      reorder_step_list (CoN t a τ) (CoN t a τ').

Scheme reorder_step_tree_list_rec := Induction for reorder_step Sort Prop
with reorder_step_list_tree_rec := Induction for reorder_step_list Sort Prop.

Notation "t1 ---> t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟶ t2" := (reorder_step t1 t2) (at level 75).
Notation "t1 ⟷ t2" := ((sc reorder_step) t1 t2) (at level 75).

Definition reorder := rtsc (reorder_step).

Notation "t1 <--->* t2" := (reorder t1 t2) (at level 76).
Notation "t1 ⟷* t2" := (reorder t1 t2) (at level 76).

Notation "τ1 ----> τ2" := (reorder_step_list τ1 τ2) (at level 75).

Definition reorder_list := rtsc (reorder_step_list).

Notation "τ1 ---->* τ2" := (reorder_list τ1 τ2) (at level 76).

Lemma reorder_infix_subtree1 t1 a t2 t1' :
  t1 ⟷* t1' →
  (IN t1 a t2) ⟷* (IN t1' a t2).
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (IN y a t2).
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree1. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree1. assumption.
    + assumption.
Qed.

Lemma reorder_infix_subtree2 t1 a t2 t2' :
  t2 ⟷* t2' →
  (IN t1 a t2) ⟷* (IN t1 a t2').
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (IN t1 a y).
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree2. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree2. assumption.
    + assumption.
Qed.

Lemma reorder_prefix_subtree o t2 t2' :
  t2 ⟷* t2' →
  (PeN o t2) ⟷* (PeN o t2').
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (PeN o y).
    + inv H.
      * apply sc_lr. apply ReorderStepPrefixSubtree. assumption.
      * apply sc_rl. apply ReorderStepPrefixSubtree. assumption.
    + assumption.
Qed.

Lemma reorder_postfix_subtree t1 o t1' :
  t1 ⟷* t1' →
  (PoN t1 o) ⟷* (PoN t1' o).
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (PoN y o).
    + inv H.
      * apply sc_lr. apply ReorderStepPostfixSubtree. assumption.
      * apply sc_rl. apply ReorderStepPostfixSubtree. assumption.
    + assumption.
Qed.

(* Lemma reorder_closed_subtree a1 t a2 t' :
  t ⟷* t' →
  (CN a1 t a2) ⟷* (CN a1 t' a2).
Proof.
  intro. induction H.
  - apply rtc_refl.
  - eapply rtc_l.
    + inv H.
      * apply sc_lr. apply ReorderStepClosedSubtree. eassumption.
      * apply sc_rl. apply ReorderStepClosedSubtree. eassumption.
    + assumption.
Qed. *)

Inductive yield_struct : word → PT → Prop :=
  | ClosedYieldStruct ah ac wi τ wt t :
      ClosedP ah ac →
      interleaving ac wi τ →
      yield_some_struct (CN ah τ) wt t →
      yield_struct (ah :: wi ++ wt) t
  | PrefixYieldStruct o w t :
      PreP o →
      yield_struct w t →
      yield_struct (o :: w) (PeN o t)

with interleaving : list T → word → PL → Prop :=
  | NilInterleave :
      interleaving [] [] ϵ
  | ConsInterleave w1 t ac τ ah w2 :
      yield_struct w1 t →
      interleaving ac w2 τ →
      interleaving (ah :: ac) (w1 ++ ah :: w2) (CoN t ah τ)

with yield_some_struct : PT → word → PT → Prop :=
  | NilYieldStruct t :
      yield_some_struct t [] t
  | InfixYieldStruct t1 o t2 w :
      InP o →
      yield_struct w t2 →
      yield_some_struct t1 (o :: w) (IN t1 o t2)
  | PostfixYieldStruct o w t1 t :
      PostP o →
      yield_some_struct (PoN t1 o) w t →
      yield_some_struct t1 (o :: w) t.

Notation ys := yield_struct.
Notation yss := yield_some_struct.
Notation il := interleaving.

Inductive post_tree : PT → Prop :=
  | ClosedPostTree a τ :
      post_tree (CN a τ)
  | PostfixPostTree t a :
      post_tree t →
      post_tree (PoN t a).


Lemma yield_struct_infix_sound w1 t1 w2 t2 a :
  ys w1 t1 → ys w2 t2 → InP a →
  ∃ t', ys (w1 ++ a :: w2) t' ∧ (IN t1 a t2) ⟷* t'
with
  yield_some_struct_infix_sound ti w1 t1 w2 t2 a :
  yss ti w1 t1 → ys w2 t2 → InP a →
  ∃ t', yss ti (w1 ++ a :: w2) t' ∧ (IN t1 a t2) ⟷* t'.
Proof.
  - intros. inv H.
    + simplify_list_eq. edestruct yield_some_struct_infix_sound; eauto.
      rename x into t'. destruct H.
      exists t'. split; eauto. eapply ClosedYieldStruct; eauto.
    + simpl. specialize yield_struct_infix_sound with w t w2 t2 a.
      destruct yield_struct_infix_sound; auto. rename x into t'.
      exists (PeN o t'). inv H. split.
      * apply PrefixYieldStruct; auto.
      * eapply rtc_l.
        **apply sc_lr. apply ReorderStepInfixPrefix.
        **apply reorder_prefix_subtree. assumption.
  - intros. inv H.
    + simpl. exists (IN t1 a t2). split.
      * apply InfixYieldStruct; auto.
      * apply rtc_refl.
    + simpl. specialize yield_struct_infix_sound with w t3 w2 t2 a.
      destruct yield_struct_infix_sound; eauto. rename x into t'. inv H.
      exists (IN ti o t'). split.
      * apply InfixYieldStruct; auto.
      * eapply rtc_l.
        **apply sc_lr. apply ReorderStepInfix.
        **apply reorder_infix_subtree2. assumption.
    + simpl. edestruct yield_some_struct_infix_sound; eauto. inv H.
      rename x into t'. exists t'. split; auto. apply PostfixYieldStruct; auto.
Qed.

Lemma yield_struct_postfix_sound w1 t1 a :
  ys w1 t1 → PostP a →
  ∃ t', ys (w1 ++ [a]) t' ∧ (PoN t1 a) ⟷* t'
with yield_some_struct_postfix_sound ti w1 t1 a :
  yss ti w1 t1 → PostP a →
  ∃ t', yss ti (w1 ++ [a]) t' ∧ (PoN t1 a) ⟷* t'.
Proof.
  - intros. inv H.
    + simplify_list_eq. edestruct yield_some_struct_postfix_sound; eauto.
      rename x into t'. inv H. exists t'. split; eauto. eapply ClosedYieldStruct; eauto.
    + simpl. edestruct yield_struct_postfix_sound; eauto. inv H.
      rename x into t'. exists (PeN o t'). split.
      * apply PrefixYieldStruct; auto.
      * (* [[o t] a] ---> [o [t a]] ---> [o t'] *) admit.
  - intros. inv H.
    + simpl. exists (PoN t1 a). split.
      * apply PostfixYieldStruct; auto. apply NilYieldStruct.
      * apply rtc_refl.
    + simpl. edestruct yield_struct_postfix_sound; eauto. inv H. rename x into t'.
      exists (IN ti o t'). split.
      * apply InfixYieldStruct; auto.
      * (* [[ti o t2] a]  ---> [ti o [t2 a]]  ---> [ti o t'] *) admit. 
    + simpl. specialize yield_some_struct_postfix_sound with (PoN ti o) w t1 a.
      destruct yield_some_struct_postfix_sound; auto. inv H. rename x into t'.
      exists t'. split; auto. apply PostfixYieldStruct; auto.
Admitted.

Lemma yield_struct_sound t :
  wf t → exists t', ys (yield t) t' ∧ t ⟷* t'
with interleave_sound ac τ :
  wfl ac τ → exists τ', il ac (yield_list τ) τ' ∧ τ ---->* τ'.
Proof.
  - intros. inv H.
    + simpl. apply interleave_sound in H1. destruct H1 as [τ']. inv H.
      exists (CN ah τ'). split.
      * assert (yield_list τ = yield_list τ ++ []). {
          simplify_list_eq. reflexivity.
        }
        rewrite H. eapply ClosedYieldStruct; eauto. apply NilYieldStruct.
      *(* Trivial reordering *) admit.
    + simpl. apply yield_struct_sound in H1. apply yield_struct_sound in H2.
      destruct H1 as [t1']. destruct H2 as [t2'].
      inv H. inv H1.
      apply yield_struct_infix_sound with (yield t1) t1' (yield t2) t2' a in H2; auto.
      destruct H2 as [t]. inv H1.
      exists t. split; auto.
      (* Trivial reordering *) admit.
    + simpl. apply yield_struct_sound in H1. destruct H1 as [t2']. inv H.
      exists (PeN a t2'). split.
      * apply PrefixYieldStruct; auto.
      * (* Trivial reordering*) admit.
    + simpl. apply yield_struct_sound in H1. destruct H1 as [t1']. inv H.
      apply yield_struct_postfix_sound with (yield t1) t1' a in H1; auto.
      destruct H1 as [t']. inv H.
      exists t'. split; auto. (*Trivial reordering*) admit.
  - intros. inv H.
    + simpl. exists ϵ. split.
      * apply NilInterleave.
      * apply rtc_refl.
    + simpl. edestruct yield_struct_sound; eauto. rename x into t'. inv H.
      edestruct interleave_sound; eauto. rename x into τ'. inv H.
      exists (CoN t' a τ'). split.
      * apply ConsInterleave; auto.
      * (* Trivial reordering*) admit.
Admitted.

Inductive closed_op a : Prop :=
  | ClosedOpHead ac :
      ClosedP a ac →
      closed_op a
  | ClosedOpTail ah ac :
      ClosedP ah ac →
      a ∈ ac →
      closed_op a.

Inductive tail ac : list T → Prop :=
  | TailHead :
      tail ac ac
  | TailTail a ac1 :
      tail ac ac1 →
      tail ac (a :: ac1).

Inductive closed_tail ac : Prop :=
  | ClosedTail ah ac2 :
      ClosedP ah ac2 →
      tail ac ac2 →
      closed_tail ac.

Lemma tail_subset a ac1 ac2 :
  a ∈ ac1 → tail ac1 ac2 → a ∈ ac2.
Proof.
  intros. induction H0; auto.
  right. auto.
Qed.

Lemma tail_cons a ac1 ac2 :
  tail (a :: ac1) ac2 → tail ac1 ac2.
Proof.
  intro. induction H.
  - apply TailTail. apply TailHead.
  - apply TailTail. assumption.
Qed.

Lemma tail_trans ac1 ac2 ac3 :
  tail ac1 ac2 → tail ac2 ac3 → tail ac1 ac3.
Proof.
  intro. revert ac3. induction H; intros; auto.
  apply IHtail. eapply tail_cons; eauto.
Qed.

Record noOverlap := mkNoOverlap {
  overlap1 : ∀ a ac1 ac2, ClosedP a ac1 → ClosedP a ac2 → ac1 = ac2;
  overlap2 : ∀ a, closed_op a → InP a → False;
  overlap3 : ∀ a, closed_op a → PreP a → False;
  overlap4 : ∀ a, closed_op a → PostP a → False;
  overlap5 : ∀ a, InP a → PreP a → False;
  overlap6 : ∀ a, InP a → PostP a → False;
  overlap7 : ∀ a, PreP a → PostP a → False;
}.

Hypothesis NO : noOverlap.

Lemma ys_closed_deterministic w11 w12 w21 w22 a t1 t2 :
  closed_op a →
  w11 ++ a :: w12 = w21 ++ a :: w22 →
  ys w11 t1 →
  ys w21 t2 →
  w11 = w21
with yss_closed_deterministic w11 w12 w21 w22 a t1 t2 ti1 ti2 :
  closed_op a →
  w11 ++ a :: w12 = w21 ++ a :: w22 →
  yss ti1 w11 t1 →
  yss ti2 w21 t2 →
  w11 = w21
with il_closed_deterministic w11 w12 w21 w22 ac τ1 τ2 :
  closed_tail ac →
  w11 ++ w12 = w21 ++ w22 →
  il ac w11 τ1 →
  il ac w21 τ2 →
  w11 = w21.
Proof.
  - intros HC. intros. inv H0; inv H1.
    + eapply overlap1 in H2; eauto. subst.
      rewrite <- app_assoc in H1. rewrite <- app_assoc in H1.
      eapply il_closed_deterministic with (w11 := wi) (w21 := wi0) in H3 as ?;
      eauto using ClosedTail, TailHead.
      subst. inv H1.
      eapply yss_closed_deterministic with (w11 := wt) (w21 := wt0) in H4; eauto.
      subst. auto. 
    + exfalso. eapply overlap3 with (a := o); eauto.
      eapply ClosedOpHead; eauto.
    + exfalso. eapply overlap3 with (a := ah); eauto.
      eapply ClosedOpHead; eauto.
    + eapply ys_closed_deterministic with (w11 := w) (w21 := w0) in H3; eauto.
      subst. auto.
  - intros. inv H1; inv H2; auto.
    + exfalso. eauto using overlap2. 
    + exfalso. eauto using overlap4.
    + exfalso. eauto using overlap2.
    + eapply ys_closed_deterministic with (w11 := w) (w21 := w0) in H4; eauto.
      subst. auto.
    + exfalso. eauto using overlap6.
    + exfalso. eauto using overlap4.
    + exfalso. eauto using overlap6.
    + eapply yss_closed_deterministic with (w11 := w) (w21 := w0) in H4; eauto.
      subst. auto.
  - intros. inv H1; inv H2; auto.
    rewrite <- app_assoc in H0. rewrite <- app_assoc in H0. simpl in H0.
    assert (closed_op ah). {
      inv H.
      eapply ClosedOpTail; eauto.
      eapply tail_subset; eauto.
      left.
    }
    eapply ys_closed_deterministic with (w11 := w1) (w21 := w0) in H3; eauto.
    subst. inv H0.
    assert (closed_tail ac0). {
      inv H.
      eapply ClosedTail; eauto.
      eapply tail_cons; eauto.
    }
    eapply il_closed_deterministic with (w11 := w2) (w21 := w3) in H4; eauto.
    subst. auto.
Qed.

Lemma ys_deterministic w t1 t2 :
  ys w t1 → ys w t2 → t1 = t2
with yss_deterministic ti w t1 t2 :
  yss ti w t1 → yss ti w t2 → t1 = t2
with il_deterministic ac w τ1 τ2 :
  closed_tail ac → il ac w τ1 → il ac w τ2 → τ1 = τ2. 
Proof.
  - intros. inv H; inv H0.
    + eapply overlap1 in H1; eauto. subst.
      assert (closed_tail ac). { eapply ClosedTail; eauto. apply TailHead. }
      eapply il_closed_deterministic in H2 as ?; eauto. subst.
      inv H4.
      eapply il_deterministic in H2 as ?; eauto. subst.
      eapply yss_deterministic in H3; eauto.
    + exfalso. eauto using overlap3, ClosedOpHead.
    + exfalso. eauto using overlap3, ClosedOpHead.
    + eapply ys_deterministic in H2; eauto. subst. auto.
  - intros. inv H; inv H0.
    + auto.
    + eapply ys_deterministic in H2; eauto. subst. auto.
    + exfalso. eauto using overlap6.
    + exfalso. eauto using overlap6.
    + eapply yss_deterministic with (t2 := t2) in H2; assumption.
  - intros. inv H0; inv H1; auto.
    assert (closed_op ah). {
      inv H. eapply ClosedOpTail; eauto.
      eapply tail_subset; eauto. left.
    }
    eapply ys_closed_deterministic in H2 as ?; eauto. subst.
    inv H5.
    eapply ys_deterministic in H2; eauto. subst.
    assert (closed_tail ac0). {
      inv H. eapply ClosedTail; eauto using tail_cons.
    }
    eapply il_deterministic in H3; eauto. subst. auto.
Qed.

Lemma rtsc_symmetry {A} (R : relation A) (x y : A) :
  rtsc R x y → rtsc R y x.
Proof.
  intros. induction H.
  - apply rtc_refl.
  - apply rtc_transitive with y.
    + assumption.
    + apply rtc_once. inv H.
      * apply sc_rl. assumption.
      * apply sc_lr. assumption.
Qed.

Lemma yield_reorder t1 t2 :
  ¬ overlap →
  wf t1 → wf t2 → yield t1 = yield t2 → t1 ⟷* t2.
Proof.
  intro HOverlap. intros.
  apply yield_struct_sound in H. destruct H as [t1']. destruct H.
  apply yield_struct_sound in H0. destruct H0 as [t2']. destruct H0.
  rewrite H1 in H. apply ys_deterministic with (yield t2) t1' t2' in H; auto.
  subst.
  apply rtc_transitive with t2'; auto.
  apply rtsc_symmetry. assumption.
Qed.

End Experiment8.
