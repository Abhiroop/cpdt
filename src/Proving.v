Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Fail Inductive List M A :=
| nil : List M A
| cons : M A -> M (List M A) -> List M A.

Fail Inductive NonStrictlyPos := con : (NonStrictlyPos -> nat) -> NonStrictlyPos.

Fail Inductive Mu A := mu : (Mu A -> A) -> Mu A.
