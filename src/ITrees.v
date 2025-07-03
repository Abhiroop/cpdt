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

(* (t -> itree u) -> itree t -> itree u *)

Definition seq {E : Type -> Type} {T U : Type} (k : T -> itree E U)
  : itree E T -> itree E U :=
  cofix _seq (u : itree E T) : itree E U :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_seq t)
    | VisF e h => Vis e (fun x => _seq (h x))
    end.

(* the h type in Vis or the t type in TauF is not necessary a smaller term, so Coq wouldn't allow it to pass; instead we use cofixpoint _seq allowing the defnition by guarded corecursion rather than structural  recursion *)

Definition bind {E : Type -> Type} {T U : Type} (u : itree E T) (k : T -> itree E U)
  : itree E U := seq k u.


Definition trigger {E : Type -> Type} {A : Type} (e : E A) : itree E A :=
  Vis e (fun x => Ret x).


Module ITreeNotations.
  Open Scope itree_scope.

  Notation "t1 >>= k2" := (bind t1 k2)
                            (at level 58, left associativity) : itree_scope.
  Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2))
                                (at level 61, t1 at next level, right associativity) : itree_scope.
  Notation "' p <- t1 ;; t2" :=
    (bind t1 (fun x_ => match x_ with p => t2 end))
      (at level 61, t1 at next level, p pattern, right associativity) : itree_scope.
  Notation "t1 ;; t2" := (bind t1 (fun _ => t2))
                           (at level 61, right associativity) : itree_scope.
End ITreeNotations.
Import ITreeNotations.

Module Iter.

  Definition iter {E : Type -> Type} {R I: Type}
    (step : I -> itree E (I + R)) : I -> itree E R :=
    cofix iter_ init :=
      (* one step of the loop *)
      lr <- step init;;

      match lr with
      (* got updated state => jump back into loop *)
      | inl updated => Tau (iter_ updated)

      (* got a final result => terminate *)
      | inr result => Ret result
      end.

  (* The above allows writing potentially infinite loops where for   example while (true) {  skip; } will simply be an infinite
  sequence of Tau's generated *)


  Definition fact (n : nat) : itree voidE nat :=
    iter  (fun '(acc,n) =>
             match n with
             | O => Ret (inr acc)
             | S m => Ret (inl (n * acc, m))
             end) (1,n).


  Fixpoint burn (n : nat) {E R} (t : itree E R) :=
    match n with
    | O => t
    | S n =>
        match observe t with
        | RetF r => Ret r
        | VisF e k => Vis e k
        | TauF t' => burn n t'
        end
    end.

  (** You can test that your factorial computes what it should: *)
  Eval compute in burn 10 (fact 6).

  Definition repeat {E} (step : itree E (unit + unit)) : itree E unit :=
    iter (fun _ => step) tt.
End Iter.


From ExtLib Require Import
  Structures.Functor
  Structures.Monad.

From ITree Require Import
  Basics.Basics
  Core.ITreeDefinition
  Indexed.Relation.

Import Monads.

Definition interp {E M : Type -> Type}
  {MF : Functor M} {MM : Monad M} {IM : MonadIter M}
  (h : E ~> M) :
  itree E ~> M := fun R =>
                    iter (fun t =>
                            match observe t with
                            | RetF r => ret (inr r)
                            | TauF t => ret (inl t)
                            | VisF e k => fmap (fun x => inl (k x)) (h _ e)
                            end).

Definition interp_state {E M S}
  {FM : Functor M} {MM : Monad M}
  {IM : MonadIter M} (h : E ~> stateT S M) :
  itree E ~> stateT S M := interp h.
