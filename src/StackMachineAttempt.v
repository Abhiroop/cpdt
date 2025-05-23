Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus  => plus
  | Times => mult
  end.


Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

Eval simpl in expDenote (Const 42).
Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iConst n => Some (n :: s)
  | iBinop b =>
      match s with
      | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
      | _ => None
      end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' =>
      match instrDenote i s with
      | None => None
      | Some s' => progDenote p' s'
      end
  end.

Fixpoint compile (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Eval simpl in compile (Const 42).
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
Eval simpl in progDenote (compile (Const 42)) nil.
Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.

Lemma compile_correct' : forall e p s,
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
  induction e.
  intros.
  unfold compile.
  unfold expDenote.
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.
  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.
  rewrite <- app_assoc.
  rewrite IHe2.
  rewrite <- app_assoc.
  rewrite IHe1.
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.
Qed.

Lemma compile_correct'' : forall e p s,
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

Theorem compile_correct :
  forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros.
  rewrite <- (app_nil_r (compile e)).
  rewrite compile_correct''.
  reflexivity.
  Qed.


(* Intrinsic typed compiler *)

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus  : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq    : forall t, tbinop t t Bool
| TLt    : tbinop Nat Nat Bool.


Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Definition typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus => plus
  | TTimes => mult
  | TEq Nat => Nat.eqb
  | TEq Bool => eqb
  | TLt => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2))
                            (TNConst 7)).

Definition tstack := list type.

(* Indexed datatype
   First tstack tells what is the shape of stack before op
   Second tstack tells what is the shape of stack after op
 *)
Inductive tinstr : tstack   -> tstack -> Set :=
| TiNConst : forall s, nat  -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiBinop : forall arg1 arg2 res s,
    tbinop arg1 arg2 res
    -> tinstr (arg1 :: arg2 :: s) (res :: s).


Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
    tinstr s1 s2
    -> tprog s2 s3
    -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
  | TiNConst _ n => fun s => (n, s)
  | TiBConst _ b => fun s => (b, s)
  | TiBinop _ _ _ _ b => fun s =>
                           let '(arg1, (arg2, s')) := s in
                           ((tbinopDenote b) arg1 arg2, s')
  end.

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
  | TNil _ => fun s => s
  | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
  | TNil _ => fun p' => p'
  | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
  | TNConst n => TCons (TiNConst _ n) (TNil _)
  | TBConst b => TCons (TiBConst _ b) (TNil _)
  | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
                              (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

Lemma tconcat_correct : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'')
                               (s : vstack ts),
    tprogDenote (tconcat p p') s
    = tprogDenote p' (tprogDenote p s).
  induction p; crush.
Qed.

Hint Rewrite tconcat_correct.

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
    tprogDenote (tcompile e ts) s = (texpDenote e, s).
  induction e; crush.
Qed.

Hint Rewrite tcompile_correct'.


Theorem tcompile_correct : forall t (e : texp t),
    tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.

Require Extraction.
Extraction Language Haskell.
Extraction tcompile.
