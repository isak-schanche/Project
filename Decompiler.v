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

Definition example_1 :=
  EBinOp OPlus (
    EUnOp OSucc(ENat 5)
  )(
    EUnOp OPred(ENat 16)
  ).

Example eval_test_1 :
  eval example_1 = 21.
Proof. reflexivity. Qed.

Definition example_2 :=
  EBinOp OMult (
    EUnOp OPred(ENat 13)
  )(
    EUnOp OSucc(ENat 3)
  ).

Example eval_test_2 :
  eval example_2 = 48.
Proof. reflexivity. Qed.

(*Exercise 4.3*)

Inductive instruction :=
| IPush : nat -> instruction
| IUnOp : unop -> instruction
| IBinOp : binop -> instruction.

Fixpoint compile (e : exp) : list instruction :=
  match e with
  | ENat n => [IPush n]
  | EUnOp o e => (compile e) ++ [IUnOp o]
  | EBinOp o e1 e2 => (compile e1) ++ (compile e2) ++ [IBinOp o]
  end.

(*Exercise 4.4*)

Definition eval_unop (o : unop) (n : nat) : nat :=
  match o with
  | OSucc => S n
  | OPred => pred n
  end.

Definition eval_binop (o : binop) (n1 : nat) (n2 : nat) :=
  match o with
  | OPlus => n2 + n1
  | OMult => n2 * n1
  end.

Fixpoint run (stk : list nat) (instrs : list instruction) : list nat :=
  match instrs with
  | [] => stk
  | (IPush n) :: instrs' => run (n :: stk) instrs'
  | (IUnOp o) :: instrs' =>
    match stk with
    | n :: stk' => run ((eval_unop o n) :: stk') instrs'
    | _ => []
    end
  | (IBinOp o) :: instrs' =>
    match stk with
    | n1 :: n2 :: stk' => run ((eval_binop o n1 n2) :: stk') instrs'
    | _ => []
    end
  end.

Definition vm : list instruction -> option nat := fun instrs =>
  match (run [] instrs) with
  | n :: nil => Some n
  | _ => None
  end.

(*Exercise 4.5*)

Definition example_1_compiled := compile example_1.

Definition example_2_compiled := compile example_2.

Example vm_test_1 :
  vm example_1_compiled = Some 21.
Proof. reflexivity. Qed.

Example vm_test_2 :
  vm example_2_compiled = Some 48.
Proof. reflexivity. Qed.

Example vm_test_3 :
  vm [IBinOp OPlus; IPush 10] = None.
Proof. reflexivity. Qed.

Example vm_test_4 :
  vm [IUnOp OSucc] = None.
Proof. reflexivity. Qed.

(*Exercise 4.6*)

Lemma run_composite : forall e instrs' stk, run stk (compile e ++ instrs') = run ((eval e) :: stk) instrs'.
Proof.
  intros e.
  induction e; intros. {
    reflexivity.
  } {
    destruct u; simpl; rewrite <- app_assoc; rewrite IHe; reflexivity.
  } {
    destruct b; simpl; rewrite <- app_assoc; rewrite <- app_assoc; rewrite IHe1; rewrite IHe2; reflexivity.
  }
Qed.

Lemma vm_correct : forall e, vm (compile e) = Some (eval e).
Proof.
  induction e. {
    reflexivity.
  } {
    destruct u; simpl; unfold vm; rewrite run_composite; reflexivity.
  } {
    destruct b; simpl; unfold vm; rewrite run_composite; rewrite run_composite; reflexivity.
  }
Qed.

(* Exercise 4.7 *)

Fixpoint assemble (stk : list exp) (instrs : list instruction) : list exp :=
  match instrs with
  | [] => stk
  | (IPush n)::instrs' => assemble ((ENat n)::stk) instrs'
  | (IUnOp op)::instrs' => match stk with
    | n :: stk' => assemble ((EUnOp op n) :: stk') instrs'
    | _ => []
    end
  | (IBinOp op)::instrs' => match stk with
    | n1 :: n2 :: stk' => assemble ((EBinOp op n1 n2) :: stk') instrs'
    | _ => []
    end
  end.

Definition decompile : list instruction -> option exp := fun instrs => 
  match (assemble [] instrs) with
  | e :: nil => Some e
  | _ => None
  end.

(* Exercise 4.8 *)
Lemma decompile_correct : forall e, decompile (compile e) = Some e.