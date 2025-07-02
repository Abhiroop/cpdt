Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Require Import Monads.

Variant void : Type :=.
Variant voidE : Type -> Type :=.

Notation "E ~> F" := (forall X, E X -> F X) (at level 99, right associativity, only parsing).

Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
  | inl1 (_ : E1 X)
  | inr1 (_ : E2 X).
Arguments inr1 {E1 E2} [X].
Arguments inl1 {E1 E2} [X].

(** An infix notation for convenience. *)
Notation "E1 +' E2" := (sum1 E1 E2)
                         (at level 60, right associativity) : type_scope.


Module ITreeAlternative.

  CoInductive itree (E : Type -> Type) (R : Type) :=
  | Ret (r:R)
  | Tau (t : itree E R)
  | Vis  {X:Type} (e: E X) (k : X -> itree E R).

End ITreeAlternative.



Section itree.


  (** Our two parameters, domain of events and return type *)
  Context {E : Type -> Type} {R : Type}.

  Variant itreeF (itree : Type) :=
    | RetF (r : R)
    | TauF (t : itree)
    | VisF {X : Type} (e : E X) (k : X -> itree)
  .

  (** Note: this is a _coinductive_ definition *)
  CoInductive itree : Type := go
                                { _observe : itreeF itree }.

End itree.

Arguments itree : clear implicits.
Arguments itreeF : clear implicits.

Definition observe {E R} (t : itree E R) : itreeF E R (itree E R) := @_observe E R t.

Declare Scope itree_scope.
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Notation itree' E R := (@itreeF E R (itree E R)).
Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).

Ltac genobs x ox := remember (observe x) as ox.
Ltac desobs x    := destruct (observe x).

Section FirstExamples.

  Variant IOE : Type -> Type :=
    | Output (n : nat) : IOE unit
    | Input            : IOE nat.

  Definition aux_armes : itree IOE nat := Ret 1789.

  Definition double : itree IOE nat :=
    Vis Input (fun n => Ret (2 * n)).

  CoFixpoint echo : itree IOE void :=
    Vis Input (fun n => Vis (Output n) (fun _ => echo)).

  CoFixpoint spin_spec : itree IOE void :=
    Tau spin_spec. (* silent divergence *)

  (** *** Failure *)
  Variant Empty : Type -> Type :=
    | empty : Empty void.

  Definition fail {R} : itree Empty R :=
    Vis empty (fun x : void => match x with end).

End FirstExamples.
