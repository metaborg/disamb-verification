From stdpp Require Export list.
From stdpp Require Export relations.

Section Experiment9.

Ltac inv H := inversion H; clear H; subst.

Inductive production Terminal :=
  | ClosedProduction : Terminal → list Terminal → production Terminal
  | InfixProduction : Terminal → list Terminal → production Terminal
  | PrefixProduction : Terminal → production Terminal
  | PostfixProduction : Terminal → production Terminal.

Global Arguments ClosedProduction {_} _ _.
Global Arguments InfixProduction {_} _ _.
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
Notation InP ah ac := (P (InfixProduction ah ac)).
Notation PreP a := (P (PrefixProduction a)).
Notation PostP a := (P (PostfixProduction a)).


Definition word := list T.

Implicit Types w : word.

Inductive parse_tree :=
  | ClosedNode : T → parse_list → parse_tree
  | InfixNode : parse_tree → T → parse_list → parse_tree → parse_tree
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
  | WellFormedInfixNode t1 a ac τ t2 :
      InP a ac →
      well_formed_parse_tree t1 →
      well_formed_parse_list ac τ →
      well_formed_parse_tree t2 →
      well_formed_parse_tree (IN t1 a τ t2)
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
  | IN t1 a τ t2 => yield t1 ++ a :: yield_list τ ++ yield t2
  | PeN a t => a :: yield t
  | PoN t a => yield t ++ [a]
  end
with yield_list τ : word :=
  match τ with
  | ϵ => []
  | CoN t a τ => yield t ++ a :: yield_list τ
  end.

Inductive reorder_step : PT → PT → Prop :=
  | ReorderStepInfix t1 t2 t3 τ1 τ2 a b :
      reorder_step (IN (IN t1 a τ1 t2) b τ2 t3) (IN t1 a τ1 (IN t2 b τ2 t3))
  | ReorderStepInfixPrefix t1 t2 τ a b :
      reorder_step (IN (PeN a t1) b τ t2) (PeN a (IN t1 b τ t2))
  | ReorderStepInfixPostfix t1 t2 τ a b :
      reorder_step (IN t1 a τ (PoN t2 b)) (PoN (IN t1 a τ t2) b)
  | ReorderStepPrefixPostfix t a b :
      reorder_step (PeN a (PoN t b)) (PoN (PeN a t) b)
  | ReorderStepInfixSubtree1 t1 a τ t2 t1' :
      reorder_step t1 t1' →
      reorder_step (IN t1 a τ t2) (IN t1' a τ t2)
  | ReorderStepInfixSubtree2 t1 a τ t2 t2' :
      reorder_step t2 t2' →
      reorder_step (IN t1 a τ t2) (IN t1 a τ t2')
  | ReorderStepInfixSubtree3 t1 a τ t2 τ' :
      reorder_step_list τ τ' →
      reorder_step (IN t1 a τ t2) (IN t1 a τ' t2)
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

Notation "τ1 <---->* τ2" := (reorder_list τ1 τ2) (at level 76).

Lemma reorder_infix_subtree1 t1 a τ t2 t1' :
  t1 ⟷* t1' →
  (IN t1 a τ t2) ⟷* (IN t1' a τ t2).
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (IN y a τ t2).
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree1. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree1. assumption.
    + assumption.
Qed.

Lemma reorder_infix_subtree2 t1 a τ t2 t2' :
  t2 ⟷* t2' →
  (IN t1 a τ t2) ⟷* (IN t1 a τ t2').
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (IN t1 a τ y).
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree2. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree2. assumption.
    + assumption.
Qed.

Lemma reorder_infix_subtree3 t1 a τ t2 τ' :
  τ <---->* τ' →
  (IN t1 a τ t2) ⟷* (IN t1 a τ' t2).
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (IN t1 a y t2).
    + inv H. 
      * apply sc_lr. apply ReorderStepInfixSubtree3. assumption.
      * apply sc_rl. apply ReorderStepInfixSubtree3. assumption.
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

Lemma reorder_closed_subtree a τ τ' :
  τ <---->* τ' →
  (CN a τ) ⟷* (CN a τ').
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (CN a y).
    + inv H.
      * apply sc_lr. apply ReorderStepClosedSubtree. assumption.
      * apply sc_rl. apply ReorderStepClosedSubtree. assumption.
    + assumption.
Qed.

Lemma reorder_cons_subtree1 t t' a τ :
  t ⟷* t' →
  (CoN t a τ) <---->* (CoN t' a τ).
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (CoN y a τ).
    + inv H.
      * apply sc_lr. apply ReorderStepConsSubtree1. assumption.
      * apply sc_rl. apply ReorderStepConsSubtree1. assumption.
    + assumption.
Qed.

Lemma reorder_cons_subtree2 t a τ τ' :
  τ <---->* τ' →
  (CoN t a τ) <---->* (CoN t a τ').
Proof.
  intro. induction H.
  - apply rtc_refl.
  - apply rtc_l with (CoN t a y).
    + inv H.
      * apply sc_lr. apply ReorderStepConsSubtree2. assumption.
      * apply sc_rl. apply ReorderStepConsSubtree2. assumption.
    + assumption.
Qed.

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
  | InfixYieldStruct a t1 ac wi τ wt t2 :
      InP a ac →
      interleaving ac wi τ →
      yield_struct wt t2 →
      yield_some_struct t1 (a :: wi ++ wt) (IN t1 a τ t2)
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


Lemma yield_struct_infix_sound w1 t1 wi τ w2 t2 a ac :
  ys w1 t1 → il ac wi τ → ys w2 t2 → InP a ac →
  ∃ t', ys (w1 ++ a :: wi ++ w2) t' ∧ (IN t1 a τ t2) ⟷* t'
with
  yield_some_struct_infix_sound ti w1 t1 wi τ w2 t2 a ac :
  yss ti w1 t1 → il ac wi τ → ys w2 t2 → InP a ac →
  ∃ t', yss ti (w1 ++ a :: wi ++ w2) t' ∧ (IN t1 a τ t2) ⟷* t'.
Proof.
  - intros. inv H.
    + simpl. rewrite <- app_assoc.
      edestruct yield_some_struct_infix_sound with (a := a) (ac := ac); eauto.
      rename x into t'. destruct H.
      exists t'. split; eauto. eapply ClosedYieldStruct; eauto.
    + simpl. specialize yield_struct_infix_sound with w t wi τ w2 t2 a ac.
      destruct yield_struct_infix_sound; auto. rename x into t'.
      exists (PeN o t'). inv H. split.
      * apply PrefixYieldStruct; auto.
      * eapply rtc_l.
        **apply sc_lr. apply ReorderStepInfixPrefix.
        **apply reorder_prefix_subtree. assumption.
  - intros. inv H.
    + simpl. exists (IN t1 a τ t2). split.
      * eapply InfixYieldStruct; eauto.
      * apply rtc_refl.
    + simpl. rewrite <- app_assoc.
      specialize yield_struct_infix_sound with wt t3 wi τ w2 t2 a ac.
      destruct yield_struct_infix_sound; eauto. rename x into t'. inv H.
      exists (IN ti a0 τ0 t'). split.
      * eapply InfixYieldStruct; eauto.
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
    + simpl. rewrite <- app_assoc. edestruct yield_some_struct_postfix_sound; eauto.
      rename x into t'. inv H. exists t'. split; eauto. eapply ClosedYieldStruct; eauto.
    + simpl. edestruct yield_struct_postfix_sound; eauto. inv H.
      rename x into t'. exists (PeN o t'). split.
      * apply PrefixYieldStruct; auto.
      * eapply rtc_transitive. apply rtc_once.
        apply sc_rl. apply ReorderStepPrefixPostfix.
        apply reorder_prefix_subtree. assumption.
  - intros. inv H.
    + simpl. exists (PoN t1 a). split.
      * apply PostfixYieldStruct; auto. apply NilYieldStruct.
      * apply rtc_refl.
    + simpl. rewrite <- app_assoc.
      edestruct yield_struct_postfix_sound; eauto. inv H. rename x into t'.
      exists (IN ti a0 τ t'). split.
      * eapply InfixYieldStruct; eauto.
      * eapply rtc_transitive. apply rtc_once.
        apply sc_rl. apply ReorderStepInfixPostfix.
        apply reorder_infix_subtree2. assumption.
    + simpl. specialize yield_some_struct_postfix_sound with (PoN ti o) w t1 a.
      destruct yield_some_struct_postfix_sound; auto. inv H. rename x into t'.
      exists t'. split; auto. apply PostfixYieldStruct; auto.
Qed.

Lemma yield_struct_sound t :
  wf t → exists t', ys (yield t) t' ∧ t ⟷* t'
with interleave_sound ac τ :
  wfl ac τ → exists τ', il ac (yield_list τ) τ' ∧ τ <---->* τ'.
Proof.
  - intros. inv H.
    + simpl. apply interleave_sound in H1. destruct H1 as [τ']. inv H.
      exists (CN ah τ'). split.
      * assert (yield_list τ = yield_list τ ++ []). {
          rewrite app_nil_r. reflexivity.
        }
        rewrite H. eapply ClosedYieldStruct; eauto. apply NilYieldStruct.
      * apply reorder_closed_subtree. assumption.
    + simpl. apply yield_struct_sound in H1. apply yield_struct_sound in H3.
      apply interleave_sound in H2.
      destruct H1 as [t1']. destruct H2 as [τ']. destruct H3 as [t2'].
      inv H. inv H1. inv H2.
      apply yield_struct_infix_sound with (yield t1) t1' (yield_list τ) τ' (yield t2) t2' a ac in H3; auto.
      destruct H3 as [t]. inv H2.
      exists t. split; auto.
      eapply rtc_transitive.
      apply reorder_infix_subtree1; eauto.
      eapply rtc_transitive.
      apply reorder_infix_subtree2; eauto.
      eapply rtc_transitive.
      apply reorder_infix_subtree3; eauto.
      assumption.
    + simpl. apply yield_struct_sound in H1. destruct H1 as [t2']. inv H.
      exists (PeN a t2'). split.
      * apply PrefixYieldStruct; auto.
      * eauto using reorder_prefix_subtree.
    + simpl. apply yield_struct_sound in H1. destruct H1 as [t1']. inv H.
      apply yield_struct_postfix_sound with (yield t1) t1' a in H1; auto.
      destruct H1 as [t']. inv H.
      exists t'. split; auto.
      eapply rtc_transitive.
      eapply reorder_postfix_subtree; eauto.
      assumption.
  - intros. inv H.
    + simpl. exists ϵ. split.
      * apply NilInterleave.
      * apply rtc_refl.
    + simpl. edestruct yield_struct_sound; eauto. rename x into t'. inv H.
      edestruct interleave_sound; eauto. rename x into τ'. inv H.
      exists (CoN t' a τ'). split.
      * apply ConsInterleave; auto.
      * eapply rtc_transitive.
        eapply reorder_cons_subtree1; eauto.
        eapply reorder_cons_subtree2; eauto.
Qed.

Inductive closed_op a : Prop :=
  (* | ClosedOpHead ac :
      ClosedP a ac →
      closed_op a *)
  | ClosedOpTail ah ac :
      ClosedP ah ac →
      a ∈ ac →
      closed_op a.

Inductive infix_op a : Prop :=
  (* | InfixOpHead ac :
      InP a ac →
      infix_op a *)
  | InfixOpTail ah ac :
      InP ah ac →
      a ∈ ac →
      infix_op a.

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

Inductive infix_tail ac : Prop :=
  | InfixTail ah ac2 :
      InP ah ac2 →
      tail ac ac2 →
      infix_tail ac.

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

Inductive mixfix_op a : Prop :=
  | MixfixOpClosed :
      closed_op a →
      mixfix_op a
  | MixfixOpInfix :
      infix_op a →
      mixfix_op a.

Inductive mixfix_tail ac : Prop :=
  | MixfixTailClosed :
      closed_tail ac →
      mixfix_tail ac
  | MixfixTailInfix :
      infix_tail ac →
      mixfix_tail ac.

Create HintDb ops.
Hint Constructors closed_op infix_op tail closed_tail infix_tail mixfix_op mixfix_tail : ops.


Record noOverlap := mkNoOverlap {
  overlap1 : ∀ a ac1 ac2, ClosedP a ac1 → ClosedP a ac2 → ac1 = ac2;
  overlap2 : ∀ a ac1 ac2, ClosedP a ac1 → InP a ac2 → False;
  overlap3 : ∀ a ac, ClosedP a ac → PreP a → False;
  overlap4 : ∀ a ac, ClosedP a ac → PostP a → False;
  overlap5 : ∀ a ac, closed_op a → InP a ac → False; 
  overlap6 : ∀ a, closed_op a → infix_op a → False;
  overlap7 : ∀ a, closed_op a → PreP a → False;
  overlap8 : ∀ a, closed_op a → PostP a → False;
  overlap9 : ∀ a ac1 ac2, InP a ac1 → InP a ac2 → ac1 = ac2;
  overlap10 : ∀ a ac, InP a ac → infix_op a → False;
  overlap11 : ∀ a ac, InP a ac → PreP a → False;
  overlap12 : ∀ a ac, InP a ac → PostP a → False;
  overlap13 : ∀ a, infix_op a → PreP a → False;
  overlap14 : ∀ a, infix_op a → PostP a → False;
  overlap15 : ∀ a, PreP a → PostP a → False;
}.

Create HintDb overlap.
Hint Resolve overlap1 overlap2 overlap3 overlap4 overlap5 overlap6 overlap7 overlap8
  overlap9 overlap10 overlap11 overlap12 overlap13 overlap14 overlap15 : overlap.

Hypothesis NO : noOverlap.

Lemma ys_closed_deterministic w11 w12 w21 w22 a t1 t2 :
  mixfix_op a →
  w11 ++ a :: w12 = w21 ++ a :: w22 →
  ys w11 t1 →
  ys w21 t2 →
  w11 = w21
with yss_closed_deterministic w11 w12 w21 w22 a t1 t2 ti1 ti2 :
  mixfix_op a →
  w11 ++ a :: w12 = w21 ++ a :: w22 →
  yss ti1 w11 t1 →
  yss ti2 w21 t2 →
  w11 = w21
with il_closed_deterministic w11 w12 w21 w22 ac τ1 τ2 :
  mixfix_tail ac →
  w11 ++ w12 = w21 ++ w22 →
  il ac w11 τ1 →
  il ac w21 τ2 →
  w11 = w21.
Proof.
  - intros HM. intros. inv H0; inv H1.
    + eapply overlap1 in H2 as ?; eauto. subst.
      rewrite <- app_assoc in H1. rewrite <- app_assoc in H1.
      eapply il_closed_deterministic with (w11 := wi) (w21 := wi0) in H3 as ?;
      eauto; [|inv HM; eauto with ops].
      subst. inv H1.
      eapply yss_closed_deterministic with (w11 := wt) (w21 := wt0) in H4; eauto.
      subst. auto. 
    + exfalso. eauto with overlap.
    + exfalso. eauto with overlap.
    + eapply ys_closed_deterministic with (w11 := w) (w21 := w0) in H3; eauto.
      subst. auto.
  - intros. inv H1; inv H2; auto.
    + exfalso. inv H; eauto with overlap. 
    + exfalso. inv H; eauto with overlap.
    + exfalso. inv H; eauto with overlap.
    + repeat rewrite <- app_assoc in H2.
      eapply overlap9 in H3 as ?; eauto. subst.
      eapply il_closed_deterministic with (w11 := wi) (w21 := wi0) in H4 as ?; eauto with ops.
      subst. inv H2.
      eapply ys_closed_deterministic with (w11 := wt) (w21 := wt0) in H5 as ?; eauto.
      subst. reflexivity.
    + exfalso. eauto with overlap.
    + exfalso. inv H; eauto with overlap.
    + exfalso. eauto with overlap.
    + eapply yss_closed_deterministic with (w11 := w) (w21 := w0) in H4; eauto.
      subst. reflexivity.
  - intros. inv H1; inv H2; auto.
    rewrite <- app_assoc in H0. rewrite <- app_assoc in H0. simpl in H0.
    assert (mixfix_op ah). {
      inv H.
      - inv H1. eapply MixfixOpClosed.
        eapply ClosedOpTail; eauto.
        eapply tail_subset; eauto.
        left.
      - inv H1. eapply MixfixOpInfix.
        eapply InfixOpTail; eauto.
        eapply tail_subset; eauto.
        left.
    }
    eapply ys_closed_deterministic with (w11 := w1) (w21 := w0) in H3; eauto.
    subst. inv H0.
    assert (mixfix_tail ac0). {
      inv H.
      - inv H0; eauto using tail_cons with ops.
      - inv H0; eauto using tail_cons with ops.
    }
    eapply il_closed_deterministic with (w11 := w2) (w21 := w3) in H4; eauto.
    subst. auto.
Qed.

Lemma ys_deterministic w t1 t2 :
  ys w t1 → ys w t2 → t1 = t2
with yss_deterministic ti w t1 t2 :
  yss ti w t1 → yss ti w t2 → t1 = t2
with il_deterministic ac w τ1 τ2 :
  mixfix_tail ac → il ac w τ1 → il ac w τ2 → τ1 = τ2. 
Proof.
  - intros. inv H; inv H0.
    + eapply overlap1 in H1 as ?; eauto. subst.
      assert (mixfix_tail ac). { eauto with ops. }
      eapply il_closed_deterministic in H2 as ?; eauto. subst.
      inv H4.
      eapply il_deterministic with (τ2 := τ0) in H2 as ?; eauto. subst.
      eapply yss_deterministic with (t2 := t2) in H3; eauto.
    + exfalso. eauto with overlap.
    + exfalso. eauto with overlap.
    + eapply ys_deterministic with (t2 := t0) in H2; eauto. subst. auto.
  - intros. inv H; inv H0.
    + auto.
    + eapply overlap9 in H1 as ?; eauto. subst.
      eapply il_closed_deterministic in H4 as ?; eauto with ops.
      subst. inv H4.
      eapply il_deterministic with (τ2 := τ0) in H2 as ?; eauto with ops.
      subst.
      eapply ys_deterministic with (t2 := t0) in H3; eauto.
      subst. reflexivity.
    + exfalso. eauto with overlap.
    + exfalso. eauto with overlap.
    + eapply yss_deterministic with (t2 := t2) in H2; assumption.
  - intros. inv H0; inv H1; auto.
    assert (mixfix_op ah). {
      inv H.
      - inv H0. apply MixfixOpClosed.
        eapply ClosedOpTail; eauto.
        eapply tail_subset; eauto. left.
      - inv H0. apply MixfixOpInfix.
        eapply InfixOpTail; eauto.
        eapply tail_subset; eauto. left.
    }
    eapply ys_closed_deterministic in H2 as ?; eauto. subst.
    inv H5.
    eapply ys_deterministic with (t2 := t0) in H2; eauto. subst.
    assert (mixfix_tail ac0). {
      inv H.
      - inv H1. eauto using tail_cons with ops.
      - inv H1. eauto using tail_cons with ops. 
    }
    eapply il_deterministic with (τ2 := τ0) in H3; eauto. subst. auto.
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
  wf t1 → wf t2 → yield t1 = yield t2 → t1 ⟷* t2.
Proof.
  intros.
  apply yield_struct_sound in H. destruct H as [t1']. destruct H.
  apply yield_struct_sound in H0. destruct H0 as [t2']. destruct H0.
  rewrite H1 in H. apply ys_deterministic with (yield t2) t1' t2' in H; auto.
  subst.
  apply rtc_transitive with t2'; auto.
  apply rtsc_symmetry. assumption.
Qed.

End Experiment9.
