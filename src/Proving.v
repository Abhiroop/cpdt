Require Import Bool Arith List Cpdt.CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Fail Inductive List M A :=
| nil : List M A
| cons : M A -> M (List M A) -> List M A.

Fail Inductive NonStrictlyPos := con : (NonStrictlyPos -> nat) -> NonStrictlyPos.

Fail Inductive Mu A := mu : (Mu A -> A) -> Mu A.

Definition Cont R A := (A -> R) -> R.

Fail Inductive ListC R A :=
| nilC  : ListC R A
| consC : ((A -> R) -> R) -> ((ListC R A -> R) -> R) -> ListC R A.

Fail Inductive Free (F : Type -> Type) (A : Type) :=
| pure   : Free F A
| impure : F (Free F A) -> Free F A.

Inductive Void := .

(* defining type synonym but with phantom type params *)

Definition Zero (A : Type) := Void.

Definition One  (A : Type) := unit. (* inhabited by tt *)

Fail Inductive FixF F := fixF : F (FixF F) -> FixF F.

Inductive Ext (Shape : Type) (Pos : Shape -> Type) A :=
  ext : forall s, (Pos s -> A) -> Ext Shape Pos A.

Arguments ext {_} {_} {_} s pf.
Set Implicit Arguments.

Definition Shape_One := unit.

Definition Pos_One (s : Shape_One) := Void.

Definition Ext_One A := Ext Shape_One Pos_One A.

Definition to_One (A : Type) (ext : Ext_One A) : One A := tt.

Definition from_One (A : Type) (z : One A) : Ext_One A :=
  ext tt (fun (p : Pos_One _) => match p with end).

Lemma to_from_One : forall A (ox : One A), to_One (from_One ox) = ox.
  crush.
Qed.

Lemma from_to_One : forall A (e : Ext_One A), from_One (to_One e) = e.
  induction e; crush.
  unfold to_One.
  unfold from_One.
  (* f_equal : ∀ (A B : Type) (f : A → B) (x y : A), x = y → f x = f y *)
  apply f_equal.
  (* Extensionality:
     (∀x, f x = g x) -> f = g.

     Tactic wise, we have here
     λ p => body  =  a

     we have f = g; we can apply p to both side
     and introduce p into the goal;

    body = a p
    p applied to both side
   *)
  extensionality p.
  destruct p.
Qed.

Class Container F :=
  {
    Shape : Type;
    Pos   : Shape -> Type;
    to    : forall A, Ext Shape Pos A -> F A;
    from  : forall A, F A -> Ext Shape Pos A;
    to_from : forall A (fx : F A), to (from fx) = fx;
    from_to : forall A (e : Ext Shape Pos A), from (to e) = e
  }.

Instance C_One : Container One :=
  {
    Shape := Shape_One;
    Pos   := Pos_One;
    to    := to_One;
    from  := from_One;
    to_from := to_from_One;
    from_to := from_to_One
  }
