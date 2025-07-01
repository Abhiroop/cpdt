From Coq Require Import String Nat.
From Coq Require Import ZArith Ascii List RelationClasses Eqdep.
Require Import Monads.
Import Monad.
Import ListNotations.
Import MonadLawsEqM.
Import MonadNotation.

Inductive Expr : Set :=
| Val (n : nat)
| Add (e1 e2 : Expr).

Fixpoint eval (e : Expr) : nat :=
  match e with
  | Val n => n
  | Add e1 e2 => eval e1 + eval e2
  end.

Example e : Expr := Add (Val 3) (Val 4).
Eval compute in eval e.

Module Free.

  Inductive FFree (E : Type -> Type) (R : Type) : Type :=
  | Ret (x : R)
  | Do {X} (op : E X) (k : X -> FFree E R).

  Arguments Ret {E R} x.
  Arguments Do {E R X} op k.

  Fixpoint fold_pure {E R} (h : forall X, E X -> X) (t : FFree E R) : R :=
    match t with
    | Ret x => x
    | Do op k => fold_pure h (k (h _ op))
    end.

  Fixpoint seq {E X Y} (e : FFree E X) (k : X -> FFree E Y) : FFree E Y :=
    match e with
    | Ret x   => k x
    | Do op h => Do op (fun n => seq (h n) k)
    end.

  #[export] Instance FFreeM {E} : Monad (FFree E) :=
    {|
      ret := @Ret E
    ; bind := @seq E
    |}.

  Inductive eq_FFree {E X} : FFree E X -> FFree E X -> Prop :=
  | eq_Ret : forall (x:X), eq_FFree (Ret x) (Ret x)
  | eq_Do  : forall {Y} (op : E Y) (k1 k2 : Y -> FFree E X)
                    (Heq: forall (y1 y2:Y), y1 = y2 -> eq_FFree (k1 y1) (k2 y2)),
      eq_FFree (Do op k1) (Do op k2).

  #[export]
    Instance eq_FFree_reflexive : forall {E X}, Reflexive (@eq_FFree E X).
  Proof.
    intros E X e.
    induction e; constructor; auto.
    intros; subst. apply H.
  Qed.

  #[export]
    Instance eq_FFree_symmetric : forall {E X}, Symmetric (@eq_FFree E X).
  Proof.
    intros E X e.
    induction e; intros f HF; inversion HF; subst; auto.
    apply inj_pair2 in H2. subst.
    apply inj_pair2 in H3. subst.
    constructor. intros y1 y2 EQ. subst.
    eapply H in Heq. apply Heq. reflexivity.
  Qed.

  #[export]
    Instance eq_FFree_transitive : forall {E X}, Transitive (@eq_FFree E X).
  Proof.
    intros E X e1.
    induction e1; intros e2 e3 HF HF2.
    - inversion HF. subst. inversion HF2. subst. constructor.
    - inversion HF. subst.
      apply inj_pair2 in H2. subst.
      apply inj_pair2 in H3. subst.
      inversion HF2. subst.
      apply inj_pair2 in H2. subst.
      apply inj_pair2 in H3. subst.
      constructor.
      intros y1 y2 EQ. subst.
      eapply H; auto.
  Qed.

  #[local] Instance eqM_FFree {E} : EqM (FFree E) :=
    fun A => (@eq_FFree E A).

  #[local] Instance eqM_FFree_Equiv {E} : EqMEquivalence (FFree E).
  Proof.
    constructor; typeclasses eauto.
  Qed.

  Inductive sumi (E1 E2 : Type -> Type) (X : Type) : Type :=
	| inli (_ : E1 X)
	| inri (_ : E2 X).
  Arguments inli {E1 E2} [X].
  Arguments inri {E1 E2} [X].

  Notation "Op1 +' Op2" := (sumi Op1 Op2) (at level 10).

  (** We can also "sum" _handlers_: *)

  Definition hpure_sum {Op1 Op2} (h1 : forall X, Op1 X -> X) (h2 : forall X, Op2 X -> X)
	  : forall X, (Op1 +' Op2) X -> X :=
	  fun _ op => match op with
	              | inli op => h1 _ op
	              | inri op => h2 _ op
	              end.


  Notation "E ~> F" := (forall X, E X -> F X) (at level 30).


  Fixpoint fold {E M} `{Monad M} (h : E ~> M) [R] (t : FFree E R) : M R :=
    match t with
    | Ret x => ret x
    | Do op k => x <- h _ op;; fold h (k x)
    end.


End Free.
