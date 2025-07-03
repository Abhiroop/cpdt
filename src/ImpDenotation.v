From Coq Require Import String Nat Program.
Require Import Imp Maps.



Definition mem := Imp.state.
Notation val := nat.

From Coq Require Import
     String.
From ITree Require Import
     ITree Events.State.
Import Monads.
Import ITreeNotations.
Open Scope itree.
Open Scope com_scope.

Variant MemE : Type -> Type :=
  | Read  (x : string)           : 	MemE val
  | Write (x : string) (v : val) : 	MemE unit
.

Definition rd x   := ITree.trigger (Read x).
Definition wr x v := ITree.trigger (Write x v).


Variant aop :=  | op_plus | op_minus | op_mult.


Definition aop_sem (op : aop) :=
  match op with
  | op_plus => add
  | op_minus => sub
  | op_mult => mult
  end.

Reserved Notation "⟦ a '⟧a'".
Fixpoint repr_aexp (a : aexp) : itree MemE val :=
  let aop op a b :=
    a <- ⟦ a ⟧a;;        (* We simply bind recursive calls *)
    b <- ⟦ b ⟧a;;
    Ret (aop_sem op a b)
  in
  match a with
  | ANum n      => Ret n (* Pure computation: we simply return n *)
  | AId x       => rd x  (* We put the responsibility on the environment:
                        we just "trigger" the read *)
  | APlus a b => aop op_plus a b
  | AMinus a b => aop op_minus a b
  | AMult a b => aop op_mult a b
  end
where "⟦ a '⟧a'" := (repr_aexp a)
.

Reserved Notation "⟦ b '⟧b'".
Fixpoint repr_bexp (b : bexp) : itree MemE bool :=
  match b with
  | <{ true  }>     => Ret true
  | <{ false }>     => Ret false

  | <{ a1 = a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (x =? y)

  | <{ a1 <> a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (negb(x =? y))

  | <{ a1 > a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (negb(x <=? y))

  | <{ a1 <= a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (x <=? y)

  | <{ b1 && b2 }> =>
      x <- ⟦ b1 ⟧b;;
      y <- ⟦ b2 ⟧b;;
      Ret (andb x y)

  | <{ ~ b }> =>
      x <- ⟦ b ⟧b;;
      Ret (negb x)
  end
where "⟦ b '⟧b'" := (repr_bexp b)
.



(* Redefining the iter combinators from ITrees.v *)


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

Definition repeat {E} (step : itree E (unit + unit)) : itree E unit :=
  iter (fun _ => step) tt.

Reserved Notation "⟦ c ⟧".
Fixpoint repr_com (c : com) : itree MemE unit :=
  match c with
  | <{ skip }> => Ret tt
  | <{ x := a }> => v <- ⟦ a ⟧a;; wr x v
  | <{ c1 ; c2 }> => ⟦c1⟧;; ⟦c2⟧

  | <{ if b then c1 else c2 end }> =>
      x <- ⟦ b ⟧b;;
      if x then ⟦c1⟧ else ⟦c2⟧

  | <{ while b do c end }> =>
      repeat (                   (* <== NOTE: use of _repeat_ *)
	  x <- ⟦b⟧b;;
	  if x
	  then ⟦c⟧;; Ret (inl tt)
	  else Ret (inr tt)
	)
  end
where "⟦ c ⟧" := (repr_com c)
.

Notation M := (stateT mem (itree void1)).

Example Mdef : M unit = (mem -> itree void1 (mem * unit)).
Proof. reflexivity. Qed.

(** The handler for [MemE] events *)
Definition handle_Mem : MemE ~> M :=
  fun _ e st => match e with
             | Read x    => Ret (st, st x)
             | Write x v => Ret (x !-> v; st, tt)
             end.



Notation "'ℑ'" := (interp_state handle_Mem)
                    (at level 0).

Definition model_com : com -> M unit :=
  fun c => ℑ ⟦ c ⟧.
Notation "'⟦{' c '}⟧'" := (model_com c).

(** *** Running Factorial *)

(** Now that we have a functional implementation of the [Imp] semantics,
 we can run it...

Unfortunately, the result has type [string -> nat], and Coq prints it
in a very ugly way, so we've cheated...*)

Eval compute in (burn 50 (⟦{ <{ X := 5 ; fact_in_coq }> }⟧ (fun _ => 0))).

(** ==>

Ret (fun v =>
     match v with
     | "Z" => 0
     | "Y" => 120
     | "X" => 5
     end.)  : itree mem unit
*)

Module ImpPrint.

(* ----------------------------------------------------------------- *)
(** *** Exercise *)

(** Challenge: add a "print" command to Imp. Use the following event signature. *)

Variant PrintE : Type -> Type :=
  | print (s:string) : PrintE unit.

(** Set up the semantics so that the new denotation of a command has the type: [MP unit]. *)

Definition MP := stateT mem (itree PrintE).

End ImpPrint.

