Require Import List.
Import ListNotations.

Inductive unop := OSucc | OPred.
Inductive binop := OPlus | OMult.
Inductive exp :=
| ENat : nat -> exp
| EUnOp : unop -> exp -> exp
| EBinOp : binop -> exp -> exp -> exp.

(*Exercise 4.1*)

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

Fixpoint eval (e : exp) : nat :=
  match e with
  | ENat n => n
  | EUnOp o e =>
    eval_unop o (eval e)
  | EBinOp o e1 e2 =>
    eval_binop o (eval e2) (eval e1)
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

Lemma run_composite : forall e instrs' stk,
  run stk (compile e ++ instrs') = run ((eval e) :: stk) instrs'.
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
  induction e; try reflexivity; [
    destruct u |
    destruct b
  ]; simpl; unfold vm; repeat rewrite run_composite; reflexivity.
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
    | n1 :: n2 :: stk' => assemble ((EBinOp op n2 n1) :: stk') instrs'
    | _ => []
    end
  end.

Definition decompile : list instruction -> option exp := fun instrs => 
  match (assemble [] instrs) with
  | e :: nil => Some e
  | _ => None
  end.

(* Exercise 4.8 *)

Lemma assemble_composite : forall e instrs' stk,
  assemble stk (compile e ++ instrs') = assemble (e :: stk) instrs'.
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

Lemma decompile_correct : forall e, decompile (compile e) = Some e.
Proof.
  induction e; try reflexivity; [
    destruct u |
    destruct b
  ]; simpl; unfold decompile; repeat rewrite assemble_composite; reflexivity.
Qed.

(*Exercise 4.9*)

(*Compile_decompile*)

Lemma map_concat {T1 T2 : Type}: forall (f : T1 -> T2) a b,
  map f (a ++ [b]) = (map f a) ++ [f b].
Proof.
  intros. induction a. {
    reflexivity.
  } {
    simpl. rewrite IHa. reflexivity.
  }
Qed.

Lemma assemble_singleton : forall e stk ins,
assemble stk ins = [e] -> compile e = concat (map compile (rev stk)) ++ ins.
Proof.
  intros. generalize dependent stk. induction ins; intros. {
    simpl. destruct stk; try discriminate.
    destruct stk; try discriminate. simpl in H. injection H as H'. subst.
    simpl. repeat rewrite app_nil_r. reflexivity.
  } {
    destruct a;
    [|
      destruct stk; try discriminate |
      destruct stk; try discriminate; destruct stk; try discriminate
    ];
    apply IHins in H;
    simpl in H; rewrite map_concat in H; rewrite concat_app in H; simpl in H;
    [|
      rewrite app_nil_r in H; rewrite <- app_assoc in H..
    ];
    repeat (rewrite <- app_assoc in H);
    [|
      simpl; repeat (rewrite map_concat, concat_app);
      simpl; repeat(rewrite app_nil_r, <- app_assoc)..
    ];
    assumption.
  }
Qed.

Lemma compile_decompile : forall ins e,
decompile ins = Some e -> compile e = ins.
Proof.
  intros.
  unfold decompile in H.
  destruct assemble eqn:Eass; try discriminate.
  destruct l; try discriminate.
  injection H as H'. subst.
  induction e;
  apply assemble_singleton in Eass; assumption.
Qed.

(*Abstraction*)

Class Algebra (T : Type) := {
  apply_const : nat -> T ;
  apply_unop : unop -> T -> T ;
  apply_binop : binop -> T -> T -> T ;
}.

Fixpoint trans {T} `{Algebra T} (stk : list T) (instrs : list instruction) : list T :=
  match instrs with
    | [] => stk
    | (IPush n) :: instrs' => trans ((apply_const n) :: stk) instrs'
    | (IUnOp op) :: instrs' =>
      match stk with
      | n :: stk' => trans ((apply_unop op n) :: stk') instrs'
      | _ => []
      end
    | (IBinOp op) :: instrs' =>
      match stk with
      | n1 :: n2 :: stk' => trans ((apply_binop op n1 n2) :: stk') instrs'
      | _ => []
      end
    end.

Instance vm_alg : Algebra nat := {
  apply_const n := n ;
  apply_unop op n := eval_unop op n ;
  apply_binop op n1 n2 := eval_binop op n1 n2
}.

Instance decompile_alg : Algebra exp := {
  apply_const n := ENat n ;
  apply_unop op n := EUnOp op n ;
  apply_binop op n1 n2 := EBinOp op n2 n1
}.

Definition interpret {T} `{Algebra T} : list instruction -> option T := fun instrs =>
  match (trans [] instrs) with
  | x :: nil => Some x
  | _ => None
  end.


Lemma trans_composite {T} `{Algebra T} : forall e instrs' stk,
  trans stk (compile e ++ instrs') = trans (e :: stk) instrs'.
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

Lemma interpret_correct {T} `{Algebra T} : forall e, interpret (compile e) = Some e.
Proof.
  induction e; try reflexivity; [
    destruct u |
    destruct b
  ]; simpl; unfold interpret; repeat rewrite trans_composite; reflexivity.
Qed.
