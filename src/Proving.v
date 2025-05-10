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
