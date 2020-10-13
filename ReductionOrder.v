Require Export InfixGrammar.

Section ReductionOrder.

Context {L O : Type}.
Implicit Types l : L.
Implicit Types o : O.
Implicit Types s : L + O.
Implicit Types t : @parse_tree L O.
Implicit Types g : @dgrammar O.

(* Inductive gtp g : parse_tree → parse_tree → Prop :=
  | OP1 o o' t1 t2 t'1 t'2 :
      g.(rel) o o' = Some Priority →
      gtp g (INode t1 o t2) (INode t'1 o' t'2)
  | OP2 o t1 t2 t1' :
      gtp g t1 t1' →
      gtp g (INode t1 o t2) (INode t1' o t2)
  | OP3 o t1 t2 t2' :
      gtp g t2 t2' →
      gtp g (INode t1 o t2) (INode t1 o t2'). *)

Inductive gtp g : parse_tree → parse_tree → Prop :=
  | OP1 o o' t1 t2 t'1 t'2 :
    g.(rel) o o' = Some Priority →
    gtp g (INode t1 o t2) (INode t'1 o' t'2)
  | OP2 o t1 t2 t1' :
    gtp g t1 t1' →
    gtp g (INode t1 o t2) (INode t1' o t2)
  | OP3 o t1 t2 t2' :
    gtp g t2 t2' →
    gtp g (INode t1 o t2) (INode t1 o t2')
  | OP4 o t1 t2 t1' t2' :
    gtp g t1 t1' →
    gtp g t2 t2' →
    gtp g (INode t1 o t2) (INode t1' o t2').

Definition r_gtp g t t' := yield t = yield t' ∧ gtp g t t'.

Inductive gtlc g oc : parse_tree → parse_tree → Prop :=
  | OLC1 l o t1 t2 :
      g.(rel) oc o = Some Left_assoc →
      gtlc g oc (INode t1 o t2) (ANode l)
  | OLC2 o o' t1 t2 t'1 t'2 :
      g.(rel) oc o = Some Left_assoc →
      g.(rel) oc o' ≠ Some Left_assoc →
      gtlc g oc (INode t1 o t2) (INode t'1 o' t'2)
  | OLC3 o o' t1 t2 t'1 t'2 :
      g.(rel) oc o = Some Left_assoc →
      g.(rel) oc o' = Some Left_assoc →
      gtlc g oc t2 t'2 →
      gtlc g oc (INode t1 o t2) (INode t'1 o' t'2).

(* Inductive gtl g : parse_tree → parse_tree → Prop :=
  | OL1 o o' t1 t2 t'1 t'2 :
      g.(rel) o o' = Some Left_assoc →
      gtlc g o (INode t1 o t2) (INode t'1 o' t'2) →
      gtl g (INode t1 o t2) (INode t'1 o' t'2)
  | OL2 o t1 t2 t1' :
      gtl g t1 t1' →
      gtl g (INode t1 o t2) (INode t1' o t2)
  | OL3 o t1 t2 t2' :
      gtl g t2 t2' →
      gtl g (INode t1 o t2) (INode t1 o t2'). *)

Inductive gtl g : parse_tree → parse_tree → Prop :=
  | OL1 o o' t1 t2 t'1 t'2 :
      g.(rel) o o' = Some Left_assoc →
      gtlc g o (INode t1 o t2) (INode t'1 o' t'2) →
      gtl g (INode t1 o t2) (INode t'1 o' t'2)
  | OL2 o t1 t2 t1' :
      gtl g t1 t1' →
      gtl g (INode t1 o t2) (INode t1' o t2)
  | OL3 o t1 t2 t2' :
      gtl g t2 t2' →
      gtl g (INode t1 o t2) (INode t1 o t2')
  | OL4 o t1 t2 t1' t2' :
      gtl g t1 t1' →
      gtl g t2 t2' →
      gtl g (INode t1 o t2) (INode t1' o t2').

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

Definition r_gtl g t t' := yield t = yield t' ∧ gtl g t t'.

Inductive gtrc g oc : parse_tree → parse_tree → Prop :=
  | ORC1 l o t1 t2 :
      g.(rel) oc o = Some Right_assoc →
      gtrc g oc (INode t1 o t2) (ANode l)
  | ORC2 o o' t1 t2 t'1 t'2 :
      g.(rel) oc o = Some Right_assoc →
      g.(rel) oc o' ≠ Some Right_assoc →
      gtrc g oc (INode t1 o t2) (INode t'1 o' t'2)
  | ORC3 o o' t1 t2 t'1 t'2 :
      g.(rel) oc o = Some Right_assoc →
      g.(rel) oc o' = Some Right_assoc →
      gtrc g oc t1 t'1 →
      gtrc g oc (INode t1 o t2) (INode t'1 o' t'2).

(* Inductive gtr g : parse_tree → parse_tree → Prop :=
  | OR1 o o' t1 t2 t'1 t'2 :
      g.(rel) o o' = Some Right_assoc →
      gtrc g o (INode t1 o t2) (INode t'1 o' t'2) →
      gtr g (INode t1 o t2) (INode t'1 o' t'2)
  | OR2 o t1 t2 t1' :
      gtr g t1 t1' →
      gtr g (INode t1 o t2) (INode t1' o t2)
  | OR3 o t1 t2 t2' :
      gtr g t2 t2' →
      gtr g (INode t1 o t2) (INode t1 o t2'). *)

Inductive gtr g : parse_tree → parse_tree → Prop :=
  | OR1 o o' t1 t2 t'1 t'2 :
      g.(rel) o o' = Some Right_assoc →
      gtrc g o (INode t1 o t2) (INode t'1 o' t'2) →
      gtr g (INode t1 o t2) (INode t'1 o' t'2)
  | OR2 o t1 t2 t1' :
      gtr g t1 t1' →
      gtr g (INode t1 o t2) (INode t1' o t2)
  | OR3 o t1 t2 t2' :
      gtr g t2 t2' →
      gtr g (INode t1 o t2) (INode t1 o t2')
  | OR4 o t1 t1' t2 t2' :
      gtr g t1 t1' →
      gtr g t2 t2' →
      gtr g (INode t1 o t2) (INode t1' o t2').

Definition r_gtr g t t' := yield t = yield t' ∧ gtr g t t'.

End ReductionOrder.
