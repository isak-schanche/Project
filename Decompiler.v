Require Import List.
Import ListNotations.

Inductive unop := OSucc | OPred.
Inductive binop := OPlus | OMult.
Inductive exp :=
| ENat : nat -> exp
| EUnOp : unop -> exp -> exp
| EBinOp : binop -> exp -> exp -> exp.

(*Exercise 4.1*)

Fixpoint eval (e : exp) : nat :=
  match e with
  | ENat n => n
  | EUnOp o e =>
    match o with
    | OSucc => S (eval e)
    | OPred => pred (eval e)
    end
  | EBinOp o e1 e2 =>
    match o with
    | OPlus => eval e1 + eval e2
    | OMult => eval e1 * eval e2
    end
  end.

(*Exercise 4.2*)

Example eval_test_1 :
  eval (
    EBinOp OPlus (
      EUnOp OSucc(ENat 5)
      )(
      EUnOp OPred(ENat 16)
    )
  ) = 21.
Proof. reflexivity. Qed.

Example eval_test_2 :
  eval (
    EBinOp OMult (
      EUnOp OPred(ENat 13)
      )(
      EUnOp OSucc(ENat 3)
    )
  ) = 48.
Proof. reflexivity. Qed.

(*Exercise 4.3*)

Inductive instruction :=
| IPush : nat -> instruction
| IUnOp : unop -> instruction
| IBinOp : binop -> instruction.

Check [3].
Fixpoint compile (e : exp) : list instruction :=
  match e with
  | ENat n => [IPush n]
  | EUnOp o e => (compile e) ++ (IUnOp o)
  | EBinOp o e1 e2 => (compile e1) ++ (compile e2) ++ (IBinOp o)
  end.