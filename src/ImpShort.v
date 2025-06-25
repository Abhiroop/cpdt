From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.

Require Import Maps Imp.

Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
  CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (CAsgn x y)
    (in custom com at level 0, x constr at level 0,
        y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (CSeq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (CIf x y z)
    (in custom com at level 89, x at level 99,
        y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (CWhile x y)
    (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(* ================================================================= *)
(** ** Example: Factorial *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
      Y := Y * Z;
      Z := Z - 1
     end }>.


(* ================================================================= *)
(** ** Imp Memory *)

(** The state of an [Imp] program is a _memory_ of type [mem]
  that maps variables to their current values.  *)

Definition mem := string -> nat.

(** We can use some notation to write some example memories: *)

Example mem_init := (_ !-> 0).

Example mem_ex2 := (X !-> 3; Y !-> 120).

Example mem_final := (Z !-> 0; X !-> 6; Y !-> 720).

(* ================================================================= *)

Fixpoint aeval (m : mem) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => m x
  | <{a1 + a2}> => (aeval m a1) + (aeval m a2)
  | <{a1 - a2}> => (aeval m a1) - (aeval m a2)
  | <{a1 * a2}> => (aeval m a1) * (aeval m a2)
  end.

Eval compute in (aeval mem_ex2 <{ X * Y }>).


(* ----------------------------------------------------------------- *)
(** *** Boolean expression interpreter *)

Fixpoint beval (m : mem) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval m a1) =? (aeval m a2)
  | <{a1 <> a2}>  => negb ((aeval m a1) =? (aeval m a2))
  | <{a1 <= a2}>  => (aeval m a1) <=? (aeval m a2)
  | <{a1 > a2}>   => negb ((aeval m a1) <=? (aeval m a2))
  | <{~ b1}>      => negb (beval m b1)
  | <{b1 && b2}>  => andb (beval m b1) (beval m b2)
  end.

(* ================================================================= *)


Inductive ceval : com -> mem -> mem -> Prop :=
| E_Skip : forall st,
    st =[ skip ]=> st
| E_Asgn  : forall st a n x,
    aeval st a = n ->
    st =[ x := a ]=> (x !-> n ; st)
| E_Seq : forall c1 c2 st st' st'',
    st  =[ c1 ]=> st'  ->
    st' =[ c2 ]=> st'' ->
    st  =[ c1 ; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    st =[ c1 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    st =[ c2 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_WhileFalse : forall b st c,
    beval st b = false ->
    st =[ while b do c end ]=> st
| E_WhileTrue : forall st st' st'' b c,
    beval st b = true ->
    st  =[ c ]=> st' ->
    st' =[ while b do c end ]=> st'' ->
    st  =[ while b do c end ]=> st''

where "st =[ c ]=> st'" := (ceval c st st').
