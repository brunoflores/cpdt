Require Import Bool Arith List Lib.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* ---------- Source language of our compiler ------------- *)

Inductive type : Set := Nat | Bool.

(* Map types of object language to Coq types. *)
Definition typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

(* Syntax of the source language. *)
Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool (* Polymorphism: allow equality of any two values of any type, as long as they have the same type. *)
| TLt : tbinop Nat Nat Bool.

(* Interpret with standard library. *)
Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus => plus
  | TTimes => mult
  | TEq Nat => beq_nat
  | TEq Bool => eqb
  | TLt => leb
  end.

(* Our type of arithmetic expressions. *)
Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

(* Evaluate examples. *)
Eval simpl in texpDenote (TNConst 41).
Eval simpl in texpDenote (TBConst true).
Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).

(* ---------- Target language of our compiler ------------- *)

(* Stack types classify sets of possible stacks. *)
Definition tstack := list type.

(* Instructions in terms of stack types.
   Every instruction's type tells what initial stack type it expects and
   what final stack type it will produce. *)
Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiBinop : forall arg1 arg2 res s,
    tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).

(* Stack machine programs must guarantee that intermediate stack types
   match within a program. *)
Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
    tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.

(* Value stacks at runtime. *)
Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
  | TiNConst _ n => fun s => (n ,s)
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

(* ---------- Compiler definition ------------- *)

(* Translation. *)

Fixpoint compile (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Eval simpl in compile (Const 42).
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

(* Run some compiled programs. *)

Eval simpl in progDenote (compile (Const 42)) nil.
Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) nil.

(* Show translation correctness. *)

Lemma compile_correct' : forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e;
    crush.
Qed.

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros e;
    rewrite (app_nil_end (compile e));
    rewrite compile_correct';
    reflexivity.
Qed.
